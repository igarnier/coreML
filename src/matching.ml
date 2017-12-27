(** This module handles pattern-matching compilation. The aim is to
    transform complex pattern-matchings with possibly deeply nested
    patterns into a simple tree of tests on constructors. *)

open Batteries

(** Vectors *)
module Vector =
  struct
    
    type 'a t = 'a list

    let length vector = List.length vector

    let of_list : 'a list -> 'a t = fun x -> x

    let get : vector:'a t -> i:int -> 'a =
      fun ~vector ~i ->
        List.nth vector i

    let modify : vector:'a t -> i:int -> f:('a -> 'a) -> 'a t =
      fun ~vector ~i ~f ->
        List.modify_at i f vector

    let set : vector:'a t -> i:int -> elt:'a -> 'a t =
      fun ~vector ~i ~elt ->
        modify ~vector ~i ~f:(fun _ -> elt)

    let slice_line l n =
      let rec aux n acc l =
        match l with
        | [] ->
          failwith "slice_line : line too short."
        | x :: l'' ->
          if n = 0 then
            (List.rev acc, x, l'')
          else
            aux (n-1) (x :: acc) l''
      in aux n [] l

    let kleisli_modify : vector:'a t -> i:int -> f:('a -> 'a t) -> 'a t =
      fun ~vector ~i ~f ->
        let prefix, x, suffix = slice_line vector i in
        List.concat [prefix; f x; suffix]

    let remove : vector:'a t -> i:int -> 'a t =
      fun ~vector ~i ->
        List.remove_at i vector

    let fold : vector:'a t -> acc:'b -> f:('b -> 'a -> 'b) -> 'b =
      fun ~vector ~acc ~f ->
        List.fold_left f acc vector

    let fold2 : v1:'a t -> v2:'b t -> acc:'c -> f:('c -> 'a -> 'b -> 'c) -> 'c =
      fun ~v1 ~v2 ~acc ~f ->
        List.fold_left2 f acc v1 v2

  end

(** Matrices of patterns *)
module Matrix =
  struct

    type elt    = Ast.pattern
    type row    = { patts : elt Vector.t; action : Ast.expr }
    type matrix = row list

    let is_empty : matrix -> bool =
      function 
      | [] -> true
      | _  -> false

    let get_row : mat:matrix -> i:int -> row  =
      fun ~mat ~i ->
        List.nth mat i

    (* let row_to_vector : row:row -> elt Vector.t =
     *   fun ~row -> row.patts *)

    let get_col : mat:matrix -> i:int -> elt Vector.t =
      fun ~mat ~i ->
        List.map (fun row -> Vector.get ~vector:row.patts ~i) mat

    (* let remove_row : mat:matrix -> i:int -> matrix =
     *   fun ~mat ~i ->
     *     List.remove_at i mat *)
        
    let remove_col : mat:matrix -> i:int -> matrix =
      fun ~mat ~i ->
        List.map (fun row -> { row with patts = Vector.remove ~vector:row.patts ~i }) mat

    let filter_rows : mat:matrix -> pred:(elt Vector.t -> bool) -> matrix =
      fun ~mat ~pred ->
        List.filter (fun { patts } -> pred patts) mat

    let map_rows : mat:matrix -> f:(row -> row) -> matrix =
      fun ~mat ~f ->
        List.map f mat

    let kleisli_map_column : mat:matrix -> i:int -> f:(elt -> elt Vector.t) -> matrix =
      fun ~mat ~i ~f ->
        List.map (fun row ->
            { row with patts = Vector.kleisli_modify ~vector:row.patts ~i ~f }
          ) mat
        
  end


(** The pattern matching algorithm generates a [tree], wich is
    itself converted into an expression containing only simple matches. 
    Note that there is no explicit sharing of identical sub-trees -- this can be done
    once thte tree is produced. *)
type tree =
  | UnfoldTuple of { tuple_var    : Ast.vvar;
                     tuple_fields : Ast.vvar list;
                     subtree      : tree }
  | SwitchConstruct of { construct_var : Ast.vvar;
                         cases : datacons_case list;
                         deflt : tree option }
  | SwitchConstant of { constant_var : Ast.vvar;
                        cases : constant_case list;
                        deflt : tree option }
  | Leaf of Ast.expr
and datacons_case = 
  { constr : Ast.datacons; 
    data : Ast.vvar option; 
    constr_subtree : tree }
and constant_case = 
  { cst : Ast.constant; 
    cst_subtree : tree }


(** Error raised in case something goes awry *)
exception MatchingError of string

let matching_error s = raise (MatchingError s)

(** Substitutes all variables in column [col] of [matrix] in the corresponding actions
    by the variable [Vector.get ~vector:vars ~i:col]. *)
let subst_variables_of_col ~vars ~mat ~col =
  let matched_variable = Vector.get ~vector:vars ~i:col in
  Matrix.map_rows ~mat ~f:(fun row ->
      let patt = Vector.get ~vector:row.Matrix.patts ~i:col in
      match patt.Ast.patt_desc with
      | Ast.Pvar v ->
        { patts  = Vector.set ~vector:row.Matrix.patts ~i:col ~elt:Ast.P.any;
          action = Ast.subst v (Ast.Eident { ident = matched_variable }) row.action }
      | _ -> row
    )

(** Substitutes all variables in the given [row] by the matching variables in [vars] in
    the corresponding action. *)
let subst_variables_of_row ~vars ~row =
  let patts  = row.Matrix.patts in
  let action = row.Matrix.action in
  Vector.fold2
    ~v1:patts ~v2:vars ~acc:action ~f:(fun action patt var ->
      match patt.Ast.patt_desc with
      | Ast.Pvar v ->
        Ast.subst v (Ast.Eident { ident = var }) action
      | _ -> action
    )

(** Selects rows that satisfy a predicate on column [col]. *)  
let filter_by_predicate ~mat ~col ~pred =
  Matrix.filter_rows ~mat ~pred:(fun row ->
      let patt = Vector.get ~vector:row ~i:col in
      pred patt.patt_desc
    )

(** Returns the rows of [mat] such that the patterns on column [i] are 
    either Pvar or Pany (i.e. catch-all) *)
let catch_all_submatrix ~mat ~col =
  filter_by_predicate ~mat ~col ~pred:(function
      | Ast.Pany   -> true
      | Ast.Pvar _ -> true
      | _ -> false
    )

(** Keep all the lines compatible with constant [cst], and substitute
    variables for catch_all when found. *)
let simplify_by_constant ~vars ~mat ~col ~cst =
  let mat =
    filter_by_predicate ~mat ~col
      ~pred:(function
          | Ast.Pany   -> true
          | Ast.Pvar _ -> true
          | Ast.Pconst c -> c = cst
          | _ -> false
        )
  in
  subst_variables_of_col ~vars ~mat ~col

(** Keep all the lines compatible with constructor [constr], and substitute
    variables for catch-all when found. *)
let simplify_by_constructor ~vars ~mat ~col ~constr =
  let mat =
    filter_by_predicate ~mat ~col
      ~pred:(function
          | Ast.Pany   -> true
          | Ast.Pvar _ -> true
          | Ast.Pconstruct(c, _) -> c = constr
          | _ -> false
        )
  in
  subst_variables_of_col ~vars ~mat ~col

(** Return all constructors of column i. *)
let constructors_of_column ~mat ~col =
  let col = Matrix.get_col ~mat ~i:col in
  Vector.fold ~vector:col ~acc:[] ~f:(fun acc patt ->
      match patt.Ast.patt_desc with
      | Ast.Pconstruct(c, patt_opt) -> 
        if List.mem_assoc c acc then
          acc
        else
          (c, patt_opt) :: acc
      | _ -> acc
    )

(** Return all constants of column i. *)
let constants_of_column ~mat ~col =
  let col = Matrix.get_col ~mat ~i:col in
  Vector.fold ~vector:col ~acc:[] ~f:(fun acc patt ->
      match patt.Ast.patt_desc with
      | Ast.Pconst c -> 
        if List.mem c acc then
          acc
        else
          c :: acc
      | _ -> acc
    )

(** Return [Some] non-trivial pattern of column i, or [None] if there isn't one. *)
let get_nontrivial_element ~column =
  Vector.fold ~vector:column ~acc:None ~f:(fun acc patt ->
      match acc with
      | None ->
        (match patt.Ast.patt_desc with
         | Ast.Pconst _
         | Ast.Pconstruct(_, _)
         | Ast.Ptuple _ -> Some patt
         | _ -> acc)
      | Some _ -> acc
    )

(** Returns true if the given line matches everything. *)
let vector_matches_all vec =
  Vector.fold ~vector:vec ~acc:true ~f:(fun acc patt ->
      match patt.Ast.patt_desc with
      | Ast.Pany
      | Ast.Pvar _ -> acc
      | _ -> false
    )

(** Makes a list of [length] "Pany" *)
let make_catch_all length =
  List.make length Ast.P.any

(** Makes a list of [length] fresh variables. *)
let make_fresh_variables freshgen length =
  let rec mkvars freshgen variables length =
    if length = 0 then
      freshgen, variables
    else
      let gen, fresh = Fresh.next freshgen in
      let v'         = Fresh.var fresh in
      mkvars gen (v' :: variables) (length - 1)
  in
  mkvars freshgen [] length

(** A generic exploration function, trying to find the element minimizing the [cost]
    of the given function [f] *)
let minimize cost_measure compute left right =
  let indices = List.range left `To right in
  let (result, _) =
    List.fold_left (fun ((best_sol, min_cost) as acc) index ->
        let solution = compute index in
        let c = cost_measure (snd solution) in
        if c < min_cost then
          (Some solution, min_cost)
        else
          acc
      ) (None, max_int) indices
  in
  match result with
  | Some res -> res
  | None ->
    failwith "minimize: empty search space"


let rec compile ~cost ~vars ~mat ~fg =
  let first_line = Matrix.get_row ~mat ~i:0 in
  let patts      = first_line.Matrix.patts in
  if vector_matches_all patts then
    (* The first line matches everything. The first action
       will thus be executed. Matching compilation ends. *)
    let action = subst_variables_of_row ~vars ~row:first_line in
    (fg, Leaf action)
  else
    (* There must exist one non-trivial column *)
    let compile_col i = compile_target_column ~cost ~vars ~mat ~fg ~i in
    minimize cost compile_col 0 (Vector.length patts - 1)

and compile_target_column ~cost ~vars ~mat ~fg ~i =
  let column = Matrix.get_col ~mat ~i in
  if vector_matches_all column then
    let mat  = subst_variables_of_col ~vars ~mat ~col:i in
    let mat  = Matrix.remove_col ~mat ~i in
    let vars = Vector.remove ~vector:vars ~i in
    compile ~cost ~vars ~mat ~fg
  else
    (* The column is non-trivial, there must exist one non-trivial pattern inside *)
    match get_nontrivial_element ~column with
    | None ->
      matching_error "compile_target_column: impossible branch reached"
    | Some patt ->
      match patt.Ast.patt_desc with
      | Ast.Pconst cst ->
        compile_constant ~cost ~vars ~mat ~fg ~i
      | Ast.Pconstruct(datacons, opt_patt) ->
        compile_construct ~cost ~vars ~mat ~fg ~i
      | Ast.Ptuple patts  ->
        compile_tuple ~cost ~vars ~mat ~fg ~i ~arity:(List.length patts)
      | _ ->
        matching_error "compile_target_column: impossible branch reached"

and compile_constant ~cost ~vars ~mat ~fg ~i =
  let constants = constants_of_column ~mat ~col:i in
  let fg, cases =
    List.fold_left (fun (fg, cases) cst ->
        let mat  = simplify_by_constant ~vars ~mat ~col:i ~cst in
        let mat  = Matrix.remove_col ~mat ~i in
        let vars = Vector.remove ~vector:vars ~i in
        let fg, tree = compile ~cost ~vars ~mat ~fg in
        (fg, { cst; cst_subtree = tree } :: cases)
      ) (fg, []) constants
  in
  let default_mat = catch_all_submatrix ~mat ~col:i in
  if Matrix.is_empty default_mat then
    let tree = SwitchConstant { constant_var = Vector.get ~vector:vars ~i
                              ; cases
                              ; deflt = None } in
    fg, tree
  else
    let fg, default_tree = compile ~cost ~vars ~mat:default_mat ~fg in
    let tree = SwitchConstant { constant_var = Vector.get ~vector:vars ~i
                              ; cases
                              ; deflt = Some default_tree } in
    fg, tree

and compile_construct ~cost ~vars ~mat ~fg ~i =
  let constructors = constructors_of_column ~mat ~col:i in
  let fg, cases =
    List.fold_left (fun (fg, cases) (constr, patt_opt) ->
        let mat  = simplify_by_constructor ~vars ~mat ~col:i ~constr in
        match patt_opt with
        | None ->
          let mat  = Matrix.remove_col ~mat ~i in
          let vars = Vector.remove ~vector:vars ~i in
          let fg, tree = compile ~cost ~vars ~mat ~fg in
          (fg, { constr; data = None; constr_subtree = tree } :: cases)
        | Some patt ->
          let fg, fresh = Fresh.next fg in
          let v'        = Fresh.var fresh in
          let vars      = Vector.set ~vector:vars ~i ~elt:v' in
          let mat       =
            Matrix.kleisli_map_column ~mat ~i ~f:(fun patt ->
                match patt.Ast.patt_desc with
                | Ast.Pconstruct(cons, Some subpatt) -> Vector.of_list [subpatt]
                | Ast.Pany -> Vector.of_list [Ast.P.any]
                | _ -> matching_error "compile_construct: impossible case reached"
              ) in
          let fg, tree = compile ~cost ~vars ~mat ~fg in
          (fg, { constr; data = Some v'; constr_subtree = tree } :: cases)
      ) (fg, []) constructors
  in
  let default_mat = catch_all_submatrix ~mat ~col:i in
  if Matrix.is_empty default_mat then
    let tree = SwitchConstruct { construct_var = Vector.get ~vector:vars ~i
                               ; cases
                               ; deflt = None } in
    fg, tree
  else
    let fg, default_tree = compile ~cost ~vars ~mat:default_mat ~fg in
    let tree = SwitchConstruct { construct_var = Vector.get ~vector:vars ~i
                               ; cases
                               ; deflt = Some default_tree } in
    fg, tree

and compile_tuple ~cost ~vars ~mat ~fg ~i ~arity =
  let matched_var = Vector.get ~vector:vars ~i in
  let fg, fvs = make_fresh_variables fg arity in
  let vars    = Vector.kleisli_modify ~vector:vars ~i ~f:(fun _ -> fvs) in
  let mat     =
    Matrix.kleisli_map_column ~mat ~i ~f:(fun patt ->
        match patt.Ast.patt_desc with
        | Ast.Ptuple patts -> patts
        | Ast.Pany         -> make_catch_all arity
        | _ -> failwith "compile_tuple: impossible case reached"
      )
  in
  let fg, tree = compile ~cost ~vars ~mat ~fg  in
  let tree = UnfoldTuple {
      tuple_var = matched_var;
      tuple_fields = fvs;
      subtree = tree
    } in
  fg, tree


(* After pattern matching compilation, we use [tree_to_expr] to convert a
   test tree back into a now simple match construct. *)
let rec tree_to_expr tree =
  match tree with
  | UnfoldTuple { tuple_var; tuple_fields; subtree } ->
    let open Ast in
    let pattvars = List.map P.var tuple_fields in
    let patts    = P.tpl pattvars in
    E.mtch (E.id tuple_var) [patts |-> (tree_to_expr subtree)]

  | SwitchConstruct { construct_var; cases; deflt } ->
    let open Ast in
     let cases =
       List.map
         (fun { constr; data; constr_subtree } ->
            match data with
            | None ->
              (P.cns0 constr) |-> (tree_to_expr constr_subtree)
            | Some v ->
              (P.cns1 constr (P.var v)) |-> (tree_to_expr constr_subtree)
         ) cases 
     in
    let cases = 
      match deflt with
      | None -> cases
      | Some tree ->
        cases @ [ P.any |-> (tree_to_expr tree) ]
    in
    E.mtch (E.id construct_var) cases

  | SwitchConstant { constant_var; cases; deflt } ->
    let open Ast in
    let cases = List.map (fun { cst; cst_subtree } ->
        P.cst cst |-> (tree_to_expr cst_subtree)
      ) cases
    in
    let cases = match deflt with
      | None -> cases
      | Some tree ->
        cases @ [ P.any |-> (tree_to_expr tree) ]
    in
    E.mtch (E.id constant_var) cases

  | Leaf e -> e

let rec test_count tree =
  match tree with
  | UnfoldTuple { subtree } ->
    (test_count subtree)
  | SwitchConstruct { cases; deflt } ->
    let res = List.fold_left (fun count { constr_subtree } ->
        (test_count constr_subtree) + count
      ) 1 cases in
    (match deflt with
     | None -> res
     | Some tr ->
       res + (test_count tr))
  | SwitchConstant { cases; deflt } ->
    let res = List.fold_left (fun count { cst_subtree } ->
        (test_count cst_subtree) + count
      ) 1 cases in
    (match deflt with
     | None -> res
     | Some tr ->
       res + (test_count tr))
  | Leaf _ -> 0




(* The match compilation algorithm is functorized. *)

module type InputSig =
sig

  (* [sig_of x] returns the list of all constructors defined along [x],
     including [x]. *)
  val sig_of : Ast.datacons -> Ast.datacons list

end


module Make(I : InputSig)
=
struct

  open Ast

  let compile = compile ~cost:test_count

  let rec matching_to_matrix matching =
    List.map (fun { rpatt; rexpr } -> { Matrix.patts = Vector.of_list [rpatt]; action = rexpr }) matching
      
  let rec compile_matching matched_expr matching fg =
    match matched_expr.expr_desc with
    | Eident { ident } ->
      let matrix   = matching_to_matrix matching in
      let fg, tree = compile [ident] matrix fg in
      let matching = tree_to_expr tree in
      fg, matching
    | _ ->
      (* if the matched expression is not a variable, we introduce
         a fresh let binding to make it so. *)
      let fg, fresh = Fresh.next fg in
      let v'        = Fresh.var fresh in
      let matrix    = matching_to_matrix matching in
      let fg, tree  = compile [v'] matrix fg in
      let matching  = tree_to_expr tree in
      let result    = mklet v' matched_expr matching in
      fg, result

  let rec compile_expr { expr_desc; uid } freshgen =
    let freshgen, expr_desc = match expr_desc with
      | Eident _
      | Econstant _
      | Econstruct { data = None } ->
        freshgen, expr_desc
      | Elet { binder; bound; body } ->
        let freshgen, bound = compile_expr bound freshgen in
        let freshgen, body  = compile_expr body freshgen in
        freshgen, Elet { binder; bound; body }
      | Efunction { arg; body } ->
        let freshgen, body  = compile_expr body freshgen in
        freshgen, Efunction { arg; body }
      | Efixpoint { fix; arg; body } ->
        let freshgen, body  = compile_expr body freshgen in
        freshgen, Efixpoint { fix; arg; body }
      | Eapply { f; args } ->
        let freshgen, f    = compile_expr f freshgen in
        let freshgen, args = List.fold_right (fun arg (freshgen, args) ->
            let freshgen, arg = compile_expr arg freshgen in
            (freshgen, arg :: args)
          ) args (freshgen, []) in
        freshgen, Eapply { f; args }
      | Ematch { matched; matching } ->
        let freshgen, matched_expr = compile_expr matched freshgen in
        let freshgen, matching = List.fold_right 
            (fun { rpatt; rexpr } (freshgen, matching) ->
               let freshgen, rexpr = compile_expr rexpr freshgen in
               (freshgen, { rpatt; rexpr } :: matching)
            ) matching (freshgen, [])
        in
        let freshgen, result =
          compile_matching matched_expr matching freshgen
        in
        freshgen, result.expr_desc
      | Etuple { exprs } ->
        let freshgen, fields = List.fold_right 
            (fun field (freshgen, fields) ->
               let freshgen, field = compile_expr field freshgen in
               (freshgen, field :: fields)
            ) exprs (freshgen, []) in
        freshgen, (Etuple { exprs })
      | Econstruct { cons; data = Some e } ->
        let freshgen, e = compile_expr e freshgen in
        freshgen, Econstruct { cons; data = Some e }
    in
    freshgen, { expr_desc; uid }

  let rec compile_program { program_decls; main } freshgen =
    let freshgen, main = compile_expr main freshgen in
    freshgen, { program_decls; main }


end

