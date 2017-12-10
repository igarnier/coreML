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

   Our type inference module works along the lines edicted by \cite{TODO}.
   It is a \textit{constraint-based} inference system. This kind of system works
   in two phases~:

   \begin{itemize}
   \item A type constraint (see [constrnt]) is built from a source expression. This
   constraint is the (almost) direct expression of the typing rules of the language. 
   The   constraint construction (see [type_expression]) is quite straightforward and
   is implemented by a simple structural recursion on the expression.
   \item Once the constraint is obtained, it is converted in an unification problem
   on first-order terms (see [Unification]), that is a list of equations on
   non-ground first-order terms. The [Unification] module handles the resolution
   of this system, and if all goes well the program is deemed well-typed.
   \end{itemize}

   Of course, this high-level view hides many quirks of the actual code. First
   of all, a yes-or-no answer to the typability of the expression is not enough:
   we must produce a mapping from programm points to types. Moreover, we have
   to handle various features like algebraic datatypes (a.k.a. sum types) and
   Hindley-Milner polymorphism (\textbf{let}-polymorphism). Cf. the definition
   of the [constrnt] type to see how this is handled.

*)

(*i*)
open Ast
open Utils
open Unification
open Printf
  (*i*)


(*s The type inference is parameterized by the kind of analysis
  we wish to perform.
  
  \begin{itemize}
  \item We may perform a \textit{polymorphic} type inference. This means that
  at \textbf{let}-bindings, the algorithm will try to let the functions
  have the most general polymorphic (i.e. \textit{generic}) type.
  \item Otherwise, we may perform a \textit{monomorphic} type inference. In this
  case, universal type quantification at \textbf{let}-bindings will not happen.
  \end{itemize}

  In either case, we may perform more analysis than just type inference. As said
  earlier, type inference is a core feature of the compiler and is used everywhere,
  not just for error-reporting but also to perform the compilation of the program
  to poorer and poorer subsets of the language, until we reach the backend.

  To this end, type inference is instrumented with two other analysis~:
  
  \begin{itemize}
  \item Monomorphisation (cf [Monomorphisation]), avaiable only after
  polymorphic type inference.
  \item Algebraic datatype type reconstruction. Some passes of the
  compiler change the type of some program fragments; and this may render
  the type declarations obsolete. We must have a means to update them. This
  pass collects the usages of data constructors in a \textbf{monomorphic} program.
  The usages form a mapping from data constructor to set of types (wich should
  be singleton sets if there is no bug, and if the program is monomorphic).
  \end{itemize}.

*)

type analysis_kind =
  | Polymorphic of monomorphisation_flag
  | Monomorphic of datacons_reconstruction

and monomorphisation_flag = bool
and datacons_reconstruction = bool

module type InferenceParameters =
sig
  val analysis_kind : analysis_kind
end

module Analyze(Params : InferenceParameters) =
struct

  (*i-----------------------------------------------------------------i*)

  exception AnalysisError of string

  (*i-----------------------------------------------------------------i*)

  (* The type of constraints is divided into simple 
     constraints ([constrnt]) and type \textit{schemes} ([scheme]) which allow
     polymorphic typing. The signification of each constructor is 
     explained thereafter. 

     $$
     \begin{array}{ll}
     True & \text{The empty constraint} \\
     Conj(c_1 \ldots c_n$ & \text{A conjunction of constraints}~c_1 \ldots c_n \\
     Equality($t_0$, $t_1$) & \text{Cconstraints the non-ground types $t_0$ and $t_1$ to be equal} \\
     Exists(\textbf{fun}~x \rightarrow$ C) & \text{Creates a fresh type variable $x$, existentially quantified in C} \\
     & \text{(in HOAS style)} \\
     Def(var, type-scheme, body) & \text{Declares $var$ to be of type $type-scheme$ in $body$} \\
     Inst(var, id, inst-typ) & \text{Instantiates the scheme bound to $var$ with $inst-typ$.} \\
     & \text{($id$ is just a hook used to build the instantiation} \\
     & \text{graph used during monomorphisation} \\
     Annot(id, point-typ) & \text{A clever (ugly ?) hook (hack ?) used to annot the ast during} \\
     & \text{constraint solving.} \\
     Datacons(cons, dom-typ) & \text{Records the usage of constructor $cons$ with an "argument" of type $dom-typ$}
     \end{array}
     $$

     Schemes are either simple ground types ($GroundType$ constructor) or constrained type
     schemes. These schemes ($TypeScheme(env, c)$) are given to \textbf{let}-bindings only during polymorphic
     type inference. A type scheme can be seen as a set of all valid monomorphic types for a 
     function, i.e. as a kind of restricted universal quantification on its type. In practice,
     the type constraint $c$ for the function is instantiated each time the function is used.
     We store the constraint-generation-time environment in order to be allow to properly
     generate the unification problem later on.
     
  *)

  type constrnt =
    | True
    | Conj of constrnt list
    | Equality of Types.term * Types.term
    | Exists of (Types.term -> constrnt)
    | Def of Ast.vvar * scheme *  constrnt
    | Inst of Ast.ident * Ast.unique_id * Types.term
    | Annot of Ast.unique_id * Types.term
    | Datacons of Ast.datacons * Types.term

  and scheme =
    | GroundType of Types.term                   
    | TypeScheme of env * (Types.term -> constrnt)

  and env = scheme Env.t

  (* Type schemes can be instantiated anywhere, not just inside their original module.
     That's why we must store the original environment along the scheme.
     We can't neither directly store the environment at constraint generation time,
     since the environment isn't known. So, we define env_schemes as schemes + env. *)

  let enrich_scheme : scheme -> env -> scheme =
    function
      | GroundType t -> 
	  (fun _ -> GroundType t)
      | TypeScheme(_, s) ->
	  (fun env -> TypeScheme(env, s))
	    
  (*s Follows some useful and heterogenous bits. First, here are some combinators to create constraints. *)

  let conj =
    function
      | [] ->
	  True
      | [x] -> x
      | l -> Conj l

  let (&:&) c1 c2 =
    match c1, c2 with
      | Conj c1, Conj c2 -> Conj (List.rev_append c1 c2)
      | Conj c, x
      | x, Conj c ->
	  Conj (x :: c)
      | x, y -> Conj [x; y] 

  let (=:=) t1 t2 = Equality(t1, t2)

  let ground t = GroundType t

  let exists c =
    Exists c

  let forall c =
    TypeScheme(Env.empty, c)

  let def vv typ constrnt =
    Def(vv, typ, constrnt)

  let rec def_list mapping constrnt =
    match mapping with
      | [] -> constrnt
      | (vv, ut) :: l ->
	  def vv ut (def_list l constrnt)

  let inst vv id typ = Inst(vv, id, typ)

  let annot id typ = 
    Annot(id, typ)

  (*i-----------------------------------------------------------------i*)

  (* Set of types. These sets are ordered by Pervasives.compare, thus
     type variables are _relevant_ (no alpha-equivalence). *)
  type typeset = Types.term Pset.t

  (* Instantiate the unifier with the type signature. c.f. type.ml and unification.ml *)
  module TypeU = Unification.Make(Types)

  (* Collects data when doing flow inference and constraint generation.
     \begin{itemize}
     \item [benv] stores the unification data (i.e. the equations)
     \item [annots] stores a map from program points to types
     \item [insts] stores monomorphisation data (cf. [Monomorphisation] and
     the instantiation graph)
     \item [dcons] stores a map from data constructors to types
     \end{itemize}
  *)
  type unification_env = {
    benv   : TypeU.Build.build_env;     (* type unification data (cf Unification.Build) *)
    annots : typeset IntMap.t;          (* maps ast nodes to type sets *)
    insts  : Monomorphisation.Graph.t;  (* maps let bindings to instantiation types *)
    dcons  : typeset StringMap.t
  }

  module IG = Monomorphisation.Graph

  (* Creates a fresh type variable. *)
  let fresh env =
    let benv, fv = TypeU.Build.fresh env.benv in
      { env with benv = benv }, fv
	
  (*i-----------------------------------------------------------------i*)

  (*s [constraint_to_equations env constrnt mm_flag] performs the conversion of a constraint
    as defined earlier and as generated by [type_expression] to a list
    of equations between types. These equations are then fed
    to the unification module (but this is done separately).
    [constraint_to_equations] receives three arguments. The first one
    is an environment which is in fact an accumulator for the various data
    collected during the recursion (in particular, it stores the list of equations
    as well as useful data for the monomorphisation and for the algebraic
    datatype reconstruction). The second one is the constraint to convert,
    and the third one is a flag telling if we should collect the data
    for the monomorphisation.

    The conversion itself is performed as a structural recursion on the constraint.
    Still, some points deserve to be explained.

    \begin{itemize}
    \item An $Equality(t_1, t_2)$ constraint is handled by
    adding a corresponding equation in the unification store.
    \item $Def(var, type-scheme, c)$ adds a mapping from $var$ to $type-scheme$
    in $env$.
    \item An $Inst(var, id, inst-typ)$ will first lookup the scheme
    associated to $var$ in the environment. 
    \begin{itemize}
    \item If the scheme is a ground type, we enforce a simple equality constraint
    between the scheme and $inst-typ$. In case $mm_flag$ is $true$, we record
    in the monomorphisation environment the fact that $var$ is used with type $inst-typ$.
    \item If the scheme is a constrained type scheme (a polymorphic type), 
    the embedded constraint is converted again with $inst-typ$
    as an instantiation type. If $mm_flag$ is set to $true$, then we update the
    monomorphisation environment.
    \end{itemize}
    \end{itemize}

  *)

  let constraint_to_equations env constrnt mm_flag =

    let add_usage, enter_in, leave =
      if mm_flag then
	IG.add_usage, IG.enter_in, IG.leave
      else
	(fun x _ _ -> x), (fun x _ _ -> x), (fun x -> x)
    in

    let rec constraint_to_equations env constrnt =
      let (var_env, unification_env) = env in
	match constrnt with
	  | True ->
	      env
	  | Conj constrnts ->
	      List.fold_left constraint_to_equations env constrnts
	  | Equality(t1, t2) ->
	      let unification_env = { 
		unification_env with benv = TypeU.Build.join unification_env.benv t1 t2 
	      } in
		(var_env, unification_env)
	  | Exists c ->
	      let unification_env, fv = fresh unification_env in
 		constraint_to_equations (var_env, unification_env) (c fv)
	  | Def(vv, typ, c) ->
	      let var_env' = Env.add_binding vv (enrich_scheme typ var_env) var_env in
	      let _, tenv  = constraint_to_equations (var_env', unification_env) c in
		(* Local bindings are not visible outside their constraints. *)
		(var_env, tenv)
	  | Inst(vv, id, typ) ->
	      let binder_scheme = Env.lookup vv var_env in
		(match binder_scheme with
		  | GroundType binder_type ->
		      let insts = add_usage unification_env.insts (vv, id) typ in
		      let unification_env = { unification_env with
			benv = TypeU.Build.join unification_env.benv binder_type typ;
			insts = insts } 
		      in
			(var_env, unification_env)
		  | TypeScheme(local_env, type_scheme) ->
		      let insts = add_usage unification_env.insts (vv, id) typ in
		      let insts = enter_in insts (vv, id) typ in
		      let unification_env = { unification_env with insts = insts } in
		      let c = exists (fun v -> (type_scheme v) &:& (typ =:= v)) in
		      let _, unification_env = constraint_to_equations (local_env, unification_env) c in
		      let unification_env = { unification_env with 
			insts = leave unification_env.insts 
		      } in
			(var_env, unification_env))
	  | Datacons(cons, typ) ->
	      (match Params.analysis_kind with
		| Monomorphic true ->
		    let usages =
		      match StringMap.find_opt cons unification_env.dcons with
			| None -> Pset.empty 
			| Some set -> set
		    in
		    let usages = Pset.add typ usages in
		    let usages = StringMap.remove cons unification_env.dcons in
		    let usages = StringMap.add cons typ annots in
		    let unification_env = { unification_env with dcons = usages } in
		      (var_env, unification_env)
		| _ ->
		    (var_env, unification_env))

	  | Annot(id, typ) ->
	      let annots =
		match IntMap.find_opt id unification_env.annots with
		  | None -> Pset.empty
		  | Some set -> set
	      in
	      let annots = Pset.add typ annots in
	      let annots_map = IntMap.remove id unification_env.annots in
	      let annots_map = IntMap.add id typ annots in
	      let unification_env = { unification_env with annots = annots_map } in
		(var_env, unification_env)

    in
      constraint_to_equations env constrnt
	
  (*i-----------------------------------------------------------------i*)

  (* We often manipulate mappings from caml type variables to types. 
     Here are some useful functions. *)

  type mapping = (string * Types.term) list

  let mapping_compatible_union (m1 : mapping) (m2 : mapping) =
    let m = List.rev_append m1 m2 in
    let m = List.sort (fun (s0,_) (s1,_) -> String.compare s0 s1) m in
      if check_uniqueness (fun (s0,_) (s1,_) -> s0 = s1) m then
	m
      else
	failwith "Inference.mapping_compatible_union : mappings not compatible."

  (*i-----------------------------------------------------------------i*)

  (* This function translates a type declaration into a type constraint. *)

  let rec typedecl_to_constraint type_constructor typedecl parameters env expected =
    match typedecl.tdecl_kind with
      | AliasType typ ->
	  let l1 = List.length typedecl.tdecl_parameters in
	  let l2 = List.length parameters in
	    if l1 != l2 then
	      let msg = "Inference.typedecl_to_constraint : invalid number \
 of arguments for type constructor "^(type_constructor)^"." in
		failwith msg
	    else
	      let mapping = List.combine typedecl.tdecl_parameters parameters in
		core_type_to_type env mapping typ expected
      | SumType _ ->
	  (* This is a root type definition. *)
	  expected =:= (TermCons(type_constructor, parameters))
      | Builtin ->
	  let _ = assert (List.length parameters = 0) in
	    (expected =:= (TermCons(typedecl.tdecl_name, [])))


  (*i-----------------------------------------------------------------i*)

  (* We need a function to convert core types to types (core types are used in annotations
     and declarations). 
     Instead of generating a type, [core_type_to_type] generates a type constraint
     reflecting the shape of the [core_type] and enforcing its equality with [expected]. 
     Type variables in caml types are not explicitly quantified ... So
     we must first grab all variables, existentially bind them and then proceed with the 
     conversion. [mapping] is an environment from type variables to types. While converting,
     we must ensure that no variable capture occur between [core_type]'s variables and [mapping]. *)
	      
  and core_type_to_type env mapping core_type expected =
    let rec grab_variables acc core_type =
      match core_type with
	| CoreVar v ->
	    (* If the variable is already bound in [mapping], no need to grab it. *)
	    if List.mem_assoc v mapping then
	      acc
	    else
	      v :: acc
	| CoreCons(_, types) ->
	    List.fold_left grab_variables acc types
    in
    let rec convert core_type mapping expected =
      match core_type with
	| CoreVar v ->
	    (List.assoc v mapping) =:= expected
	| CoreCons("->", [dom; codom]) ->
	    exists (fun dom_type ->
	      exists (fun codom_type ->
		(expected =:= Types.arrow_type dom_type codom_type)
		&:& (convert dom mapping dom_type)
		&:& (convert codom mapping codom_type)
	      ) )
	| CoreCons("*", fields) ->
	    convert_list fields mapping (fun fields ->
	      expected =:= Types.tuple_type fields) []
	| CoreCons(constr, type_params)  ->
	    convert_list type_params mapping (fun parameters ->
	      let typedecl = Env.lookup_typename constr env in
   		typedecl_to_constraint constr typedecl parameters env expected
	    ) []
    and convert_list type_list mapping enclosing_type_constraint aux =
      match type_list with
	| [] ->
	    enclosing_type_constraint (List.rev aux)
	| typ :: l ->
	    exists (fun t -> 
	      (convert typ mapping t)
	      &:& (convert_list l mapping enclosing_type_constraint (t :: aux)))
    in
    let rec quantify_variables vars acc =
      match vars with
	| [] ->
	    let m = mapping_compatible_union acc mapping in
	      convert core_type m expected
	| x :: l ->
	    exists (fun t -> quantify_variables l ((x, t) :: acc))
    in
    let variables = grab_variables [] core_type in
    let variables = Utils.filter_duplicates (=) variables in
      quantify_variables variables []

  (*i-----------------------------------------------------------------i*)

  (* Quantify a list of type variables and inject the resulting mapping
     trough f. *)

  let instantiate_type_parameters parameters f =
    let rec aux parameters mapping =
      match parameters with
	| [] ->
	    f (List.rev mapping)
	| param :: l ->
	    exists (fun v ->
	      aux l ((param, v) :: mapping))
    in aux parameters []

  (* Helps typing expressions of the form $Constructor(e_1, ..., e_n)$.
     Some terminology: in a data type definition of the form
     
     $$
     type\ typ\ ('a_1, \ldots, 'a_i) = C of t1 * ... * tn
     $$

     \begin{itemize}
     \item $('a_1, \ldots, 'a_i)$ are the type parameters,
     \item $t_1 * ... * t_n$ is the \textbf{domain} of the data constructor
     \item $typ$ is the \textbf{codomain} of the data constructor.
     \end{itemize}
  *)

  let type_data_cons env datacons fieldtype expected =
    let params, domain, codomain = Env.lookup_datacons datacons env in
      instantiate_type_parameters params (fun mapping ->
	let parameters = List.map snd mapping in
	let c = expected =:= TermCons(codomain, parameters) in
	  match fieldtype, domain with
	    | None, None -> c
	    | Some ft, Some dom ->
		(core_type_to_type env mapping dom ft)
		&:& c
	    | _ ->
		let err = "Inference.type_data_cons : inconsistent env" in
		  failwith (sprintf "%s (bad type for %s)." err datacons)
      )
	
  (*i-----------------------------------------------------------------i*)

  (*s The following functions perform the constraint generation from an expression.
    Each of these functions is parameterised by an expected type (which for the top-level
    expression is a variable), to which the type of the expression is unified.
    They are also parameterized by an environment storing information about
    type declarations.

    [type_pattern] types the [patt] pattern, transforming it into a type constraint. 
     The function is parametrized by a constraint [subconstraint], usually
    containing variables bound by [patt]. The pattern type is unified to [expected]. 
     [binding_type] allows to chose wether the names are locally or module bound.
  *)

  let type_pattern env whole_pattern expected subconstraint =
    let rec type_patt c (patt_desc, patt_id) expected =
      begin match patt_desc with
	| Pany ->
	    (c &:& annot patt_id expected)
	      
	| Pvar v ->
	    def v (ground expected) (c &:& annot patt_id expected)
	      
	| Pconst const ->
	    let t = match const with
	      | CInt _ ->
		  Types.int_type
	      | CChar _ ->
		  Types.char_type
	      | CFloat _ ->
		  Types.float_type
	    in
	      c &:& (t =:= expected) &:& (annot patt_id t)
		
	| Pconstruct(constr, None) ->
	    (type_data_cons env constr None expected)
	    &:& c &:& annot patt_id expected

	| Pconstruct(constr, Some patt) ->
	    let c = c &:& annot patt_id expected in
	      exists (fun p_type -> 
		(type_patt c patt p_type) 
		&:& (type_data_cons env constr (Some p_type) expected)
	      )

	| Ptuple fields ->
	    if List.length fields < 2 then
	      raise (AnalysisError "tuple with less than two components")
	    else
	      (type_tuple_pattern fields c expected) &:& (annot patt_id expected)
      end

    and type_tuple_pattern fields c expected =
      let rec aux fields types c =
	match fields with
	  | [] ->
	      (expected =:= Types.tuple_type (List.rev types)) &:& c
	  | p :: l ->
	      exists (fun p_type ->
		let c' = type_patt c p p_type in
		  aux l (p_type :: types) c')
      in aux fields [] c

    in type_patt subconstraint whole_pattern expected

	 

  (* [binding_to_constraint] handles \textbf{let}-bindings. [inject_c]
     is the constraint of the body of the let. I*)

  let rec binding_to_constraint env (binder, bound) inject_c =

    if is_value bound && not I.monomorphic then
      (* Polymorphic *)
      let typ = forall (fun xvar -> (* xvar is the type of binder *)
	let (_, bound_id) = bound in
	  (type_expression env bound xvar)
	  &:& (annot bound_id xvar)
      ) in
	def binder typ inject_c

    else
      (* Monomorphic *)
      exists (fun xvar -> (* xvar is the type of binder *)
	let (_, bound_id) = bound in
	let c = 
	  (type_expression env bound xvar)
	  &:& (annot bound_id xvar) 
	in
	  c &:& (def binder (ground xvar) inject_c)
      )

  (* [type_expression] generates a constraint from an expression and
     an expected type. I*)

  and type_expression : env -> Ast.expr -> Types.term -> constrnt =
    fun env (expr_desc, expr_id) expected ->
      match expr_desc with
	| Eident ident ->
	    (annot expr_id expected)
	    &:& (inst ident expr_id expected)
	      
	| Econstant c ->
	    let t = match c with
	      | CInt _ ->
		  Types.int_type
	      | CChar _ ->
		  Types.char_type
	      | CFloat _ ->
		  Types.float_type
	    in
	      (t =:= expected) &:& (annot expr_id t)

	| Elet(var, bound, body) ->
	    let sub_c =
	      (type_expression env body expected)
	      &:& (annot expr_id expected)
	    in
	      binding_to_constraint env (var, bound) sub_c

	| Efunction(var, body) ->
	    exists (fun domtype ->
	      exists (fun codomtype ->
		let self_t = Types.arrow_type domtype codomtype in
		  def var (ground domtype) (
		    (annot expr_id self_t)
		    &:& (expected =:= self_t)
		    &:& (type_expression env body codomtype)
		  )
	      ) )

	| Efixpoint(vfix, var, body) ->
	    exists (fun domtype ->
	      exists (fun codomtype ->
		let self_t = Types.arrow_type domtype codomtype in
		  def vfix (ground self_t) (
		    def var (ground domtype) (
		      (annot expr_id self_t)
		      &:& (expected =:= self_t)
		      &:& (type_expression env body codomtype)
		    ) )
	      ) )

	| Eapply(func, args) ->
	    let c = type_apply env func args expected in
	      (annot expr_id expected) &:& c
		
	| Ematch(matched_expr, matching) ->
	    exists (fun matched_type ->
	      let matched_c  = type_expression env matched_expr matched_type in 
	      let matching_c = type_matching env matching matched_type expected in
		annot expr_id expected
		&:& matched_c
		&:& matching_c)

	| Etuple fields ->
	    let c' = type_tuple env fields expected in
	      c' &:& annot expr_id expected

	| Econstruct(constr, None) ->
	    (type_data_cons env constr None expected)
	    &:& (annot expr_id expected)

	| Econstruct(constr, Some expr) ->
	    exists (fun e_type ->
	      (type_expression env expr e_type)
	      &:& (type_data_cons env constr (Some e_type) expected)
	      &:& (annot expr_id expected))

  and type_apply env func args expected =
    let nary_arrow_type arguments_types codomtype constraints =
      List.fold_right begin fun argtype (codomtype, constraints) ->
	let t = Types.arrow_type argtype codomtype in
	let c = constraints in
	  (t, c)
      end arguments_types (codomtype, constraints)
    in
    let rec aux args argtype_acc constraint_acc =
      match args with
	| [] ->
	    let vars = List.rev argtype_acc in
	    let func_type, constraints = nary_arrow_type vars expected (conj constraint_acc) in
	    let func_c = type_expression env func func_type in
	      func_c &:& constraints
	| x :: l ->
	    (* Type each argument *)
	    exists (fun argtype ->
	      let arg_c = type_expression env x argtype in
		aux l (argtype :: argtype_acc) (arg_c :: constraint_acc)
	    )
    in aux args [] []

  and type_tuple env fields expected =
    let rec aux l types constraint_acc =
      match l with
	| [] -> 
	    (conj constraint_acc) 
	    &:& (expected =:= Types.tuple_type (List.rev types))
	      
	| x :: l ->
	    exists (fun x_type ->
	      let x_c = type_expression env x x_type in
		aux l (x_type :: types) (x_c :: constraint_acc))
    in aux fields [] []

  and type_matching env matching domain codomain =
    let constraints = 
      List.fold_left (fun constraints (patt, branch_expr) ->
	let c  = type_expression env branch_expr codomain in
	let c' = type_pattern env patt domain c in
	  c' :: constraints
      ) [] matching
    in
      conj constraints

  and type_structure_items items env =
    match items with
      | [] -> env, True
      | (item_desc, item_id) :: l -> 
	  begin match item_desc with
	    | Iexternal(name, core_type) ->
		let env', sub_constraint = type_structure_items l env in
		let c = exists (fun expected ->
		  (core_type_to_type env [] core_type expected) &:&
		    (def name (ground expected) sub_constraint)) in
		  env', c
		    
	    | Itypedecl decl ->
		let env = List.fold_left (fun env decl ->
		  Env.add_typedecl decl.tdecl_name decl env
		) env decl
		in
		  type_structure_items l env
	  end

  and type_program (decls, main) env = 
    let env', sub_constraint = type_structure_items decls env in
    let c = exists (fun t -> type_expression env' main t) &:& sub_constraint in
      env', c

  (*i-----------------------------------------------------------------i*)

  (*s The following functions peform the bulk of the work using the
    previously defined functions. *)

  (* [type_inference] perform polymorphic type inference. It
     generates the following data:

     \begin{itemize}
     \item A mapping from variables to types
     \item A record containing:
         \begin{itemize}
         \item The unification data
         \item A mapping from program points to types
         \item The instantiation graph for monomorphisation
          (empty if the corresponding flag is false)
         \item The result of the algebraic datatype reconstruction,
          (empty if the corresponding flag is false)
         \end{itemize}
     \item The most general unificator
     \end{itemize}
  *)

  let type_inference env program kind mm_flag =
    let unification_env = { 
      benv   = TypeU.Build.initial_build_env;
      annots = IntMap.empty;
      insts  = IG.initial;
      dcons  = StringMap.empty
    } in
      (* Generate the typing constraint from the original program. *)
    let constraint_gen = fun () -> 
      match kind with
	| Polymorphic -> PolymorphicInference.type_program program env
	| Monomorphic -> MonomorphicInference.type_program program env
    in
    let var_env, root_constraint  = chrono_apply constraint_gen "type constraint generation" in
      (* Convert the constraint into a list of equations. This produces an environment [vvenv]
       * from module-level bindings to types, and a typing environment [unification_env] 
       * containing the type equations (in [unification_env.benv]) *) 
    let conversion       = fun () -> constraint_to_equations (var_env, unification_env) root_constraint mm_flag in
    let venv, unification_env   = chrono_apply conversion "type constraint conversion" in
      (* Perform type unification on the unification problem [type.benv]. *)
    let unification      = fun () -> TypeU.unify unification_env.benv in
    let uf_state, benv   = chrono_apply unification "type unification and constraint generation" in
      (* Instantiate the types shapes in the ast's annot & inst map *)
    let get_mgu          = (fun () -> TypeU.read_back unification_env.benv uf_state) in
    let type_mgu         = chrono_apply get_mgu "most general unificator computation" in
    let unification_env = { unification_env with benv = benv } in
      (venv, unification_env, type_mgu)


  (* [typecheck] performs type inference  *)
  let typecheck env program kind =

    let env, unification_env, mgu = type_inference env program kind false in
    let unfold = TypeU.instantiate_term mgu in

    let annots = IntMap.fold (fun id typeset map ->
      let types = Pset.elements typeset in
      let types = List.map unfold types in
	begin match types with
	  | [] ->
	      (* no valid (ground) annotations for id. *)
	      map
	  | head :: _ ->
	      IntMap.add id head map
	end
    ) unification_env.annots IntMap.empty in

    let typing_function = fun caml_ast_id ->
      try Some (lookup_int annots caml_ast_id)
      with Not_found -> None
    in
      env, typing_function

end

module MonomorphicInference = Analyze(struct
  let analysis_kind = Monomorphic true
end)

module PolymorphicInference = Analyze(struct 
  let analysis_kind = Polymorphic true
end)


(* ----------------------------------------------------------------- *)
(* Perform the whole analysis. *)

module AlphaTypeSet = Types.AlphaTypeSet(Types.Default)

let analyze env fresh_seed program =

  (* ---------------------------------------------------------------------------
   * Second batch of type inference, this time to bootstrap the monomorphisation
   * -------------------------------------------------------------------------- *)
  let _ = Ast.print_program program in

  let var_env, unification_env, type_mgu = type_inference env program Polymorphic true in
  let unfold = TypeU.instantiate_term type_mgu in

  (* ----------------
   * Monomorphisation 
   * ---------------- *)
  let module Monomorphiser = Monomorphisation.Make
    (struct

      let subject_to_value_restriction expr = not (is_value expr)
	
      (* Collect all the keys of the map in a list. *)
      let inst_graph = Monomorphisation.quotient_graph unfold unification_env.insts

    end) in    
  let monomorphise () = Monomorphiser.mm_program fresh_seed program in

  let fresh_seed, mono = chrono_apply monomorphise "monomorphisation" in

  (* Simply-typed inference. *)
  let var_env, unification_env, type_mgu = type_inference env mono Monomorphic false in

  let unfold = TypeU.instantiate_term type_mgu in

  let annots = IntMap.fold (fun id typeset map ->
    let types = Pset.elements typeset in
    let types = List.map unfold types in
      begin match types with
	| [] ->
	    (* no valid (ground) annotations for id. *)
	    map
	| head :: _ ->
	    IntMap.add id head map
      end
  ) unification_env.annots IntMap.empty in

  let typing_function = fun caml_ast_id ->
    try Some (lookup_int annots caml_ast_id)
    with Not_found -> None
  in

    (var_env, fresh_seed, typing_function, mono)


      
