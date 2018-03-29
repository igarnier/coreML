(* Type inference. *)

(* The type inference module is of utmost importance. Its purpose is to
   reconstruct the type of an expression (as defined in [Ast]). When an expression is
   ill-formed following the typing rules of the language, the compiler emits
   an error. The usefulness of types is twofold:
   \begin{itemize}
   \item It allows to detect a great deal of errors (roughly, all "segfault" errors)
   \item Types are heavily used in the other passes of the compiler to
   perform various kind of optimizations or code transformation.
   \end{itemize}

   Our type inference module works along the lines edicted by Pottier et al.
   (and probably Milner originally). It is a constraint-based inference system. 
   This kind of system works in two phases~:

   1. A type constraint (see [constrnt]) is built from a source expression. This
   constraint is the (almost) direct expression of the typing rules of the language. 
   The  constraint construction (see [type_expression]) is quite straightforward and
   is implemented by a simple structural recursion on the expression.
   2. Once the constraint is obtained, it is converted in an unification problem
   on first-order terms (see [Unification]), that is a list of equations on
   non-ground first-order terms. The [Unification] module handles the resolution
   of this system, producing a /most general unifier/ if all goes well.

   Of course, this high-level view hides many quirks of the actual code. First
   of all, a yes-or-no answer to the typability of the expression is not enough:
   we must produce a mapping from program points to types. Moreover, we have
   to handle various features like algebraic datatypes (a.k.a. sum types) and
   Hindley-Milner polymorphism (\textbf{let}-polymorphism). Cf. the definition
   of the [constrnt] type to see how this is handled.
*)

open Printf
open Batteries

open Ast
open Terms

(*-----------------------------------------------------------------*)

exception AnalysisError of string

(*-----------------------------------------------------------------*)

(* The type of constraints is divided into simple 
   constraints ([constrnt]) and type /schemes/ ([scheme]) which allow
   polymorphic typing. The signification of each constructor is 
   explained thereafter. 

   True                    the empty constraint
   Conj(c1, ..., cn)       a conjunction of constraints
   Equality(t0, t1)        as the name indicates
   Exists(fun x => C)      creates a fresh type variable [x], existentially quantified in [C]
                           (HOAS style)
   Def(var, scheme, body)  declares [var] to be of type [scheme] in [body]
   Inst(var, id, inst)     Instantiates the scheme bound to [var] with type [inst].
                           [id] is a hook used to build the instantiation graph during
                           monomorphisation.
   Annot(id, typ)          Used to build a map from [uids] to types.

   Schemes are either simple ground types (GroundType constructor) or constrained type
   schemes. These schemes (TypeScheme(env, c)) are given to let-bindings only during polymorphic
   type inference. A type scheme can be seen as a set of all valid monomorphic types for a 
   function, i.e. as a kind of restricted universal quantification on its type. In practice,
   the type constraint [c] for the function is instantiated each time the function is used.
   We store the constraint-generation-time environment in order to properly
   generate the unification problem later on.

*)

module T = Types.Make(struct
    type debug = string
    type var   = int

    let default = ""

    let print_debug s =
      if String.length s = 0 then None
      else Some s

    let print_var = string_of_int
  end)

type constrnt =
  | True
  | Conj     of { cns : constrnt list }
  | Equality of { t0 : T.t; t1 : T.t }
  | Exists   of { ex : T.t -> constrnt }
  | Def      of { var : Ast.vvar; scheme : scheme; c : constrnt }
  | Inst     of { ident : Ast.ident; uid : Ast.unique_id; t : T.t }
  | Annot    of { uid : Ast.unique_id; t : T.t }

and scheme =
  | GroundType of { ground_type : T.t }
  | TypeScheme of { env : env; fa : T.t -> constrnt }

and env = scheme Env.t

(* Type schemes can be instantiated anywhere, not just inside their original module.
   That's why we must store the original environment along the scheme.
   We can't neither directly store the environment at constraint generation time,
   since the environment isn't known. So, we define env_schemes as schemes + env. *)

let enrich_scheme : scheme -> env -> scheme =
  function
  | GroundType { ground_type } -> 
    fun _ -> GroundType { ground_type }
  | TypeScheme { fa } ->
    fun env -> TypeScheme { env; fa }

(*s Follows some useful and heterogeneous bits. First, here are some combinators to create constraints. *)

let conj =
  function
  | [] ->
    True
  | [x] -> x
  | cns -> Conj { cns }

let (&:&) c1 c2 =
  match c1, c2 with
  | Conj  { cns = c1 }, Conj { cns = c2 } -> 
    Conj { cns = List.rev_append c1 c2 }
  | Conj { cns }, x
  | x, Conj { cns } ->
    Conj { cns = x :: cns }
  | x, y -> Conj { cns = [x; y] }

let (=:=) t0 t1 = Equality { t0; t1 }

let ground t = GroundType { ground_type = t }

let exists ex =
  Exists { ex }

let forall fa =
  TypeScheme { env = Env.empty; fa }

let def var scheme c =
  Def { var; scheme; c }

let rec def_list mapping constrnt =
  match mapping with
  | [] -> constrnt
  | (vv, ut) :: l ->
    def vv ut (def_list l constrnt)

let inst ident uid t = Inst { ident; uid; t }

let annot uid t = 
  Annot { uid; t }


(* The type inference is parameterized by the kind of analysis
   we wish to perform.

  * We may perform a /polymorphic/ type inference. This means that
    at let-bindings, the algorithm will let the functions
    have the most general polymorphic type.
  * Otherwise, we may perform a /monomorphic/ type inference. In this
    case, universal type quantification at let-bindings will be forbidden.

   In the first case, we may perform more analyses than just type inference. As said
   earlier, type inference is a core feature of the compiler and is used everywhere,
   not just for error-reporting but also to perform the compilation of the program
   to poorer and poorer subsets of the language, until we reach the backend. Checking
   that the program is well-typed at each pass catches a lot of bugs in
   the compiler.

   Type inference is also instrumented to boostrap another pass~:
   monomorphisation (cf [Monomorphisation]), avaiable only after
   polymorphic type inference.

*)

type analysis_kind =
  | Polymorphic of { for_monomorphisation : bool }
  | Monomorphic


(* Set of types. These sets are ordered by Pervasives.compare, 
   thus type variables are _relevant_ (no alpha-equivalence). *)
type typeset = T.t Pset.t

(* Instantiate the unifier with the type signature. c.f. type.ml and unification.ml *)
module TypeU = Unification.Make(T)

(* The unification state collects data when doing inference and constraint generation.
   * [benv] stores the unification data (i.e. the equations)
   * [annots] stores a map from program points to sets of types
   * [insts] stores monomorphisation data (cf. [Monomorphisation] and
     the instantiation graph)
*)
type unification_state = {
  benv    : TypeU.Build.build_env;
  annots  : typeset IntMap.t;
  (* insts  : Monomorphisation.Graph.t; *)  (* maps let bindings to instantiation types *)
}

(* module IG = Monomorphisation.Graph *)

(* Creates a fresh type variable. *)
let fresh (state : unification_state) =
  let benv, fv = TypeU.Build.fresh state.benv in
  { state with benv = benv }, fv


(* [constraint_to_equations env constrnt] performs the conversion of a constraint
   as defined earlier and as generated by [type_expression] to a list
   of equations between types. These equations are then fed
   to the unification module (but this is done separately).
   [constraint_to_equations] receives two arguments. The first one
   is an environment which is in fact an accumulator for the various data
   collected during the recursion (in particular, it stores the list of equations
   as well as useful data for the monomorphisation and for the algebraic
   datatype reconstruction). The second one is the constraint to convert.

   The conversion itself is performed as a structural recursion on the constraint.
   Still, some points deserve to be explained.

   * An Equality(t0, t1) constraint is handled by adding a corresponding equation in the 
     unification store.
   * Def(var, type-scheme, c) adds a mapping from var to type-scheme
     in env.
   * An Inst(var, id, inst-typ) will first lookup the scheme associated to [var] in the environment. 
    - If the scheme is a ground type, we enforce a simple equality constraint
      between the scheme and [inst-typ]. In case monomorphisation is activated, we record
      in the monomorphisation environment the fact that [var] is used with type [inst-typ].
    - If the scheme is a constrained type scheme (a polymorphic type), 
      the embedded constraint is converted again with [inst-typ]
      as an instantiation type. If monomorphisation is activated, then we update the
      monomorphisation environment.
*)

type constraint_generation =
  {
    var_env : scheme Env.t;
    u_state : unification_state;
  }

let constraint_to_equations analysis_kind (env : constraint_generation) constrnt =

  let add_usage, enter_in, leave =
    match analysis_kind with
    | Polymorphic { for_monomorphisation = true } ->
      failwith "monomorphisation not (re)implemented yet"
    (* IG.add_usage, IG.enter_in, IG.leave *)
    | _ ->
      (fun x _ _ -> x), (fun x _ _ -> x), (fun x -> x)
  in

  let rec constraint_to_equations ({ var_env; u_state } as env) constrnt =
    match constrnt with
    | True ->
      env
    | Conj { cns } ->
      List.fold_left constraint_to_equations env cns
    | Equality { t0; t1 } ->
      let u_state = { 
        u_state with benv = TypeU.Build.join u_state.benv t0 t1
      } in
      { var_env; u_state }
    | Exists { ex } ->
      let u_state, fv = fresh u_state in
      constraint_to_equations { var_env; u_state } (ex fv)
    | Def { var; scheme; c } ->
      let var_env'    = Env.add_binding var (enrich_scheme scheme var_env) var_env in
      let { u_state } = constraint_to_equations { var_env = var_env'; u_state } c in
      (* Local bindings are not visible outside their constraints. *)
      { var_env; u_state }
    | Inst { ident; uid; t } (*(vv, id, typ)*) ->
      let binder_scheme = Env.lookup ident var_env in
      (match binder_scheme with
       | GroundType { ground_type } ->
         (*let insts = add_usage unification_env.insts (vv, id) typ in*)
         let u_state = { u_state with
                         benv = TypeU.Build.join u_state.benv ground_type t;
                        (* insts = insts *) } 
         in
         { var_env; u_state }
       | TypeScheme { env; fa }(* (local_env, type_scheme) *) ->
         (* let insts = add_usage unification_env.insts (vv, id) typ in *)
         (* let insts = enter_in insts (vv, id) typ in *)
         (* let u_state = { u_state with insts } in *)
         let c = exists (fun v -> (fa v) &:& (t =:= v)) in
         let { u_state } = constraint_to_equations { var_env = env; u_state } c in
         (* let u_state = { u_state with  *)
         (*                 insts = leave unification_env.insts  *)
         (*               } in *)
         { var_env; u_state })
    | Annot { uid; t } ->
      let uid_annots =
        match IntMap.find_opt uid u_state.annots with
        | None -> Pset.empty
        | Some set -> set
      in
      let uid_annots = Pset.add t uid_annots in
      let annots = IntMap.remove uid u_state.annots in
      let annots = IntMap.add uid uid_annots annots in
      let u_state = { u_state with annots } in
      { var_env; u_state }

  in
  constraint_to_equations env constrnt

(* We often manipulate mappings from caml type variables to types. 
   Here are some useful functions. *)

type mapping = (string * T.t) list

(* union of mappings with disjoint domains *)
let mapping_compatible_union (m1 : mapping) (m2 : mapping) =
  let m = List.rev_append m1 m2 in
  let m = List.sort (fun (s0,_) (s1,_) -> String.compare s0 s1) m in
  if Utils.check_uniqueness (fun (s0,_) (s1,_) -> s0 = s1) m then
    m
  else
    failwith "mapping_compatible_union : mappings not compatible."

(* This function translates a type declaration into a type constraint. *)
let typedecl_to_constraint type_constructor typedecl parameters ~expected =
  let debug = "declaration" in
  match typedecl.tdecl_kind with
  | SumType _ ->
    (* This is a root type definition. *)
    let typ = T.make_userdef ~debug type_constructor parameters in
    expected =:= typ
  | Builtin ->
    if List.length parameters = 0 then
      failwith "typedecl_to_constraint: builtin types has nonempty parameter list"
    else
      let typ = T.make_userdef ~debug typedecl.tdecl_name [] in
      expected =:= typ

(* Helps typing expressions of the form Constructor(e_1, ..., e_n).
   Some terminology: in a data type definition of the form

   type typ ('a_1, ..., 'a_m) = C of t1 * ... * tn

   ('a_1, ..., 'a_m)$ are the type parameters,
   t_1 * ... * t_n is the /domain/ of the data constructor
   typ is the codomain of the data constructor.
*)

type inference_state =
  {
    debug_info : string;
    env        : env; (* = scheme Env.t *)
    an_kind    : analysis_kind;
  }

let type_variant ~state ~cons ~data_type ~expected =
  let { debug_info; env; an_kind } = state in
  (* lookup the type definition associated to [cons] *)
  let inductive_def, codomain = Env.lookup_datacons cons env in
  
  let rec aux ind_def mapping =
    match ind_def with
    | IndAbs { ind_type_var; ind_type } ->
      (* instantiate fresh variables for the parameter of the type *)
      exists (fun v -> aux ind_type ((ind_type_var, v) :: mapping))
    | IndIntros { ind_intros } ->
      (* build constraints on [expected] and on the data of the
         constructor, if any *)
      let mapping = List.rev mapping in
      let domain  = List.assoc cons ind_intros in
      let params  = List.map snd mapping in
      let expected_constraint =
        expected =:= (T.make_userdef ~debug:debug_info codomain params)
      in
      match data_type, domain with
      | None, None ->
        expected_constraint
      | Some ft, Some dom ->
        let data_constraint =
          let dom = Terms.term_lift (fun (x, _) -> (x, debug_info)) (fun x -> List.assoc x mapping) dom in
          (ft =:= dom)
        in
        data_constraint &:& expected_constraint
      | _ -> 
        let err = "Inference.type_variant: inconsistent env" in
        failwith (sprintf "%s (bad type for %s)." err cons)

  in aux inductive_def []

(* The following functions perform the constraint generation from an expression.
   Each of these functions is parameterised by an expected type (which for the top-level
   expression is a variable), to which the type of the expression is unified.
   They are also parameterized by an environment storing information about
   type declarations. *)

(* [type_pattern] types the [patt] pattern, transforming it into a type constraint. 
   The function is parametrized by a constraint [subconstraint], usually
   containing variables bound by [patt]. The pattern type is unified to [expected]. 
   [binding_type] allows to chose wether the names are locally or module bound.
*)

let type_pattern ~state ~patt ~expected ~subconstraint =

  let debug_info = sprintf "pattern {\n %s \n}" (print_pattern patt) in
  let state = { state with debug_info } in

  let rec type_patt ~subconstraint ~patt:{ patt_desc; uid } ~expected =
    begin match patt_desc with
      | Pany ->
        subconstraint &:& annot uid expected

      | Pvar v ->
        def v (ground expected) (subconstraint &:& annot uid expected)
          
      | Pconst const ->
        let t = match const with
          | CInt _ ->
            T.Predefined.int ~debug:debug_info ()
          | CChar _ ->
            T.Predefined.char ~debug:debug_info ()
          | CFloat _ ->
            T.Predefined.float ~debug:debug_info ()
        in
        subconstraint &:& (t =:= expected) &:& (annot uid t)

      | Pconstruct(cons, None) ->
        (type_variant ~state ~cons ~data_type:None ~expected)
        &:& subconstraint
        &:& annot uid expected

      | Pconstruct(cons, Some data_patt) ->
        let c = subconstraint &:& annot uid expected in
        exists (fun p_type -> 
            (type_patt ~subconstraint:c ~patt:data_patt ~expected:p_type)
            &:& (type_variant ~state ~cons ~data_type:(Some p_type) ~expected)
          )

      | Ptuple patts ->
        if List.length patts < 2 then
          let error_string = print_pattern { patt_desc; uid } in
          let error_string = "tuple with less than two components: "^error_string in
          raise (AnalysisError error_string)
        else
          (type_tuple_pattern ~subconstraint ~patts ~expected) &:& (annot uid expected)
    end

  and type_tuple_pattern ~subconstraint ~patts ~expected =
    let rec aux fields types c =
      match fields with
      | [] ->
        (expected =:= T.Predefined.tuple ~debug:debug_info (List.rev types)) &:& c
      | p :: l ->
        exists (fun p_type ->
            let c' = type_patt c p p_type in
            aux l (p_type :: types) c')
    in 
    aux patts [] subconstraint

  in 
  type_patt ~subconstraint ~patt ~expected


(* [binding_to_constraint] handles \textbf{let}-bindings. [inject_c]
     is the constraint of the body of the let. *)

let rec binding_to_constraint ~state ~binder ~(bound : Ast.expr) ~body_c =
  match state.an_kind with
  | Polymorphic _ ->
    (* Polymorphic *)
    let typ = 
      forall (fun var -> (* xvar is the type of binder *)
          (type_expression ~state ~expr:bound ~expected:var)
          &:& (annot bound.uid var)
        ) 
    in
    def binder typ body_c
  | Monomorphic ->
    (* Monomorphic *)
    exists (fun var -> (* xvar is the type of binder *)
        (type_expression ~state ~expr:bound ~expected:var)
        &:& (annot bound.uid var) 
        &:& (def binder (ground var) body_c)
      )

(* [type_expression] generates a constraint from an expression and
   an expected type. The rules for each term follow directly
   from the typing rules of the language. *)

and type_expression
 (* : state:inference_state -> expr:Ast.expr -> expected:T.t -> constrnt *) =
  fun ~state ~expr ~expected ->
    let { expr_desc; uid } = expr in
    let debug_info = sprintf "expr {\n %s\n}" (print_expr expr) in
    let state      = { state with debug_info } in
    let expected'  = T.set_debug debug_info expected in
    match expr_desc with
    | Eident { ident } ->
      (annot uid expected)
      &:& (inst ident uid expected')

    | Econstant { constant } ->
      let t = match constant with
        | CInt _ ->
          T.Predefined.int ~debug:debug_info ()
        | CChar _ ->
          T.Predefined.char ~debug:debug_info ()
        | CFloat _ ->
          T.Predefined.float ~debug:debug_info ()
      in
      (t =:= expected) &:& (annot uid t)

    | Elet { binder; bound; body } ->
      let body_c =
        (type_expression ~state ~expr:body ~expected:expected')
        &:& (annot uid expected)
      in
      binding_to_constraint ~state ~binder ~bound ~body_c

    | Efunction { arg; body }  ->
      exists (fun domtype ->
          exists (fun codomtype ->
              let self_t = T.Predefined.arrow ~debug:debug_info domtype codomtype in
              def arg (ground domtype) (
                (annot uid self_t)
                &:& (expected =:= self_t)
                &:& (type_expression ~state ~expr:body ~expected:codomtype)
              )
            ) )

    | Efixpoint { fix; arg; body } ->
      exists (fun domtype ->
          exists (fun codomtype ->
              let self_t = T.Predefined.arrow ~debug:debug_info domtype codomtype in
              def fix (ground self_t) (
                def arg (ground domtype) (
                  (annot uid self_t)
                  &:& (expected =:= self_t)
                  &:& (type_expression ~state ~expr:body ~expected:codomtype)
                ) )
            ) )

    | Eapply { f; args } ->
      let c = type_apply ~state ~f ~args ~expected:expected' in
      (annot uid expected) &:& c

    | Ematch { matched; matching } ->
      exists (fun matched_type ->
          let matched_c  = type_expression ~state ~expr:matched ~expected:matched_type in
          let matching_c = type_matching ~state ~matching ~matched_type ~expected:expected' in
          annot uid expected
          &:& matched_c
          &:& matching_c)

    | Etuple { exprs } ->
      if List.length exprs < 2 then
        let error_string = print_expr expr in
        let error_string = "tuple with less than two components : "^error_string in
        let _ = Utils.serr error_string in
        raise (AnalysisError "tuple arity error")
      else
        let c' = type_tuple ~state ~exprs ~expected:expected' in
        c' &:& annot uid expected

    | Econstruct { cons; data = None } ->
      (type_variant ~state ~cons ~data_type:None ~expected)
      &:& (annot uid expected)

    | Econstruct { cons; data = Some expr } ->
      exists (fun expr_type ->
          (type_expression ~state ~expr ~expected:expr_type)
          &:& (type_variant ~state ~cons ~data_type:(Some expr_type) ~expected)
          &:& (annot uid expected))

and type_apply ~state ~f ~args ~expected =
  let nary_arrow_type arguments_types codomtype constraints =
    List.fold_right begin fun argtype (codomtype, constraints) ->
      let t = T.Predefined.arrow ~debug:state.debug_info argtype codomtype in
      let c = constraints in
      (t, c)
    end arguments_types (codomtype, constraints)
  in
  let rec aux args argtype_acc constraint_acc =
    match args with
    | [] ->
      let vars = List.rev argtype_acc in
      let func_type, constraints = nary_arrow_type vars expected (conj constraint_acc) in
      let func_c = type_expression ~state ~expr:f ~expected:func_type in
      func_c &:& constraints
    | arg :: l ->
      (* Type each argument *)
      exists (fun argtype ->
          let arg_c = type_expression ~state ~expr:arg ~expected:argtype in
          aux l (argtype :: argtype_acc) (arg_c :: constraint_acc)
        )
  in aux args [] []

and type_tuple ~state ~exprs ~expected =
  let rec aux l types constraint_acc =
    match l with
    | [] -> 
      (conj constraint_acc) 
      &:& (expected =:= T.Predefined.tuple ~debug:state.debug_info (List.rev types))

    | x :: l ->
      exists (fun x_type ->
          let x_c = type_expression ~state ~expr:x ~expected:x_type in
          aux l (x_type :: types) (x_c :: constraint_acc))
  in aux exprs [] []

and type_matching ~state ~matching ~matched_type ~expected =
  let constraints = 
    List.fold_left (fun constraints { rpatt; rexpr } ->
        let c  = type_expression ~state ~expr:rexpr ~expected in
        let c' = type_pattern ~state ~patt:rpatt ~expected:matched_type ~subconstraint:c in
        c' :: constraints
      ) [] matching
  in
  conj constraints

and type_structure_items state items =
  match items with
  | [] -> state, True
  | { item_desc; uid } :: items_tail -> 
    begin match item_desc with
      | Iexternal { external_ident; external_type } ->
        let state', sub_constraint = type_structure_items state items_tail in
        let ct = Terms.term_lift 
            (fun (x, _) -> (x, "external: "^external_ident) )
            (fun x -> failwith "Inference error") external_type
        in
        let c = def external_ident (ground ct) sub_constraint in
        state', c
        
      | Itypedecl mutual_decls ->
        let state = List.fold_left (fun state decl ->
            { state with env = Env.add_typedecl decl state.env }
          ) state mutual_decls
        in
        type_structure_items state items_tail
    end

and type_program { program_decls; main } state = 
  let state, sub_constraint = type_structure_items state program_decls in
  let c = exists (fun t -> type_expression ~state ~expr:main ~expected:t) &:& sub_constraint in
  state, c

let time_it = fun label f -> Utils.time_it " " label f

let type_inference state program =
  (* Generate the typing constraint from the original program. 
     The updated state contains in particular type declarations.
  *)
  let state, root_constraint =
    time_it "type constraint generation" (fun () ->
        type_program program state
      )
  in
  (* Convert the constraint into a list of equations. This produces an environment
     from module-level bindings to types, and a typing environment
     containing the type equations *) 
  let constraint_gen_state =
    { var_env = state.env;
      u_state =
        {
          benv   = TypeU.Build.initial_build_env;
          annots = IntMap.empty
        }
    }
  in
  let { var_env; u_state } =
    time_it "type constraint conversion" (fun () ->
        constraint_to_equations state.an_kind constraint_gen_state root_constraint
      )
  in
  (* Perform type unification on the unification problem. *)
  let uf_state =
    time_it "type unification" (fun () ->
        TypeU.unify u_state.benv
      )
  in
  (* Instantiate the types shapes in the ast's annot & inst map *)
  let type_mgu =
    time_it "computation of most general unifier" (fun () ->
        TypeU.read_back u_state.benv uf_state
      ) 
  in
  (var_env, u_state, type_mgu)



(* [typecheck] performs type inference. It returns an environment
   mapping variables to types, and a typing function from program 
   points to types. *)
let typecheck analsis_kind env program =
  let state =
    {
      debug_info = ""; env; an_kind = analsis_kind
    }
  in
  let env, unification_state, mgu = type_inference state program in
  let unfold = TypeU.instantiate_term mgu in

  let annots = IntMap.fold (fun id typeset map ->
      let types = Pset.elements typeset in
      let types = List.map unfold types in
      match types with
        | [] ->
          (* no valid (ground) annotations for id. *)
          map
        | head :: _ ->
          IntMap.add id head map
    ) unification_state.annots IntMap.empty in

  let typing_function = fun caml_ast_id ->
    try Some (IntMap.find caml_ast_id annots)
    with Not_found -> None
  in
  env, typing_function



module AlphaTypeSet = Types.AlphaTypeSet(T)


(* [analyze] performs the whole type analysis, monomorphisation included. *)
(* let analyze env fresh_seed program = *)

(*   (\* --------------------------------------------------------------------------- *)
(*    * Second batch of type inference, this time to bootstrap the monomorphisation *)
(*    * -------------------------------------------------------------------------- *\) *)
(*   let var_env, unification_env, type_mgu = PolyInfMono.type_inference env program in *)
(*   let unfold = TypeU.instantiate_term type_mgu in *)

(*   (\* ---------------- *)
(*    * Monomorphisation  *)
(*    * ---------------- *\) *)
(*   let module Monomorphiser = Monomorphisation.Make *)
(*       (struct *)

(*         let subject_to_value_restriction expr = not (is_value expr) *)

(*         (\* Collect all the keys of the map in a list. *\) *)
(*         let inst_graph = Monomorphisation.quotient_graph unfold unification_env.PolyInfMono.insts *)

(*       end) in *)

(*   let monomorphise () = Monomorphiser.mm_program fresh_seed program in *)

(*   let fresh_seed, mono = Utils.chrono_apply "" monomorphise "monomorphisation" in *)

(*   (\* Bindings were duplicated but we still need unique IDs for upcoming passes. *\) *)
(*   let mono, fresh_seed = Ast.refresh_program fresh_seed mono in *)

(*   (\* Simply-typed inference. *\) *)
(*   let var_env, unification_env, type_mgu = MonoInf.type_inference env mono in *)

(*   let unfold = TypeU.instantiate_term type_mgu in *)

(*   let annots = IntMap.fold (fun id typeset map -> *)
(*       let types = Pset.elements typeset in *)
(*       let types = List.map unfold types in *)
(*       begin match types with *)
(*         | [] -> *)
(*           (\* no valid (ground) annotations for id. *\) *)
(*           map *)
(*         | head :: _ -> *)
(*           IntMap.add id head map *)
(*       end *)
(*     ) unification_env.MonoInf.annots IntMap.empty in *)

(*   let typing_function = fun caml_ast_id -> *)
(*     try Some (IntMap.find caml_ast_id annots) *)
(*     with Not_found -> None *)
(*   in *)

(*   (var_env, fresh_seed, typing_function, mono) *)



