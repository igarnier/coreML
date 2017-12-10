(* This module handles pattern-matching compilation. The aim is to
   transform complex pattern-matchings with possibly deeply nested
   patterns into a simple tree of tests on constructors. *)

open Batteries

open Ast

(* The pattern matching algorithm works on a matrix of patterns.
   We use a very inefficient but handy representation of matrices: 
   lists of lists. *)
type line   = (Ast.pattern list * Ast.expr) (* patterns * action *)
type matrix = line list

(* We will need a way to distinguish between the various patterns.
   This type is used to this end. *)
type 'a constructor_kind =
  | Algebraic of string * 'a
  | Constant  of Ast.constant

(* The pattern matching algorithm generates a [tree], wich is
   itself converted into an expression containing only simple matches. 
   Note that there is no sharing of identical sub-trees. *)
type tree =
  | UnfoldTuple     of Ast.vvar * Ast.vvar list * tree
  | SwitchConstruct of Ast.vvar * datacons_case list * default_case
  | SwitchConstant  of { matched_variable : Ast.vvar; 
                         cases : constant_case list;
                         default_code : tree option }
  | Leaf of expr
and datacons_case = Ast.datacons * Ast.vvar option * tree
and constant_case = Ast.constant * tree
and default_case = tree option

(* We will need various tools to manipulate matrices. *)

(* [slice_line] slices a line [l] into $[l']|[x]|[l'']$ where [x] is the n-th element. 
   Indices start from 1. *)
let slice_line l n =
  let rec aux n acc l =
    match l with
    | [] ->
      failwith "slice_line : line too short."
    | x :: l'' ->
      if n = 1 then
        (List.rev acc, x, l'')
      else
        aux (n-1) (x :: acc) l''
  in aux n [] l

(* Slice a matrix m into m'|c|m'' where c is the n-th column. *)
let slice_column m n =
  let sliced_lines = List.map (fun l -> slice_line l n) m in
  let m', c, m''    = List.fold_right (fun (l', x, l'') (m', c, m'') ->
      (l' :: m', x :: c, l'' :: m'')
    ) sliced_lines ([], [], []) in
  (m', c, m'')

(* Merges a left list l', a middle _list_ x and a right list l'' into a single list *)
let unslice_line l' x l'' = l' @ (x @ l'')

(* Merges a left matrix m', a middle _matrix_ c and a right matrix m'' into a new matrix *)
let unslice_column m' c m'' =
  let sliced_lines = List.combine (List.combine m' c) m'' in
  List.fold_right (fun ((l', x), l'') m ->
      (unslice_line l' x l'') :: m
    ) sliced_lines []

(* Removes an element. Indexing starts at 1. *)
let rec remove_at idx l =
  if idx = 1 then
    List.tl l
  else match l with
    | [] ->
      failwith "remove_at : out of list bounds"
    | x :: l' ->
      x :: (remove_at (idx - 1) l')

let get_column matrix column =
  let idx = column - 1 in (* List.nth counts from 0 *)
  List.map (fun (line, _) -> List.nth line idx) matrix

(* ------------------------------------------------------------ *)
(* Various functions useful in the match compilation algorithm. *)

let rec pattern_matches_all { patt_desc } =
  match patt_desc with
  | Pany -> true
  | Pvar _ -> true
  | Ptuple patts -> false
  (* List.for_all pattern_matches_all patts *)
  | _ -> false

(* Returns true iff a line or a column matches everything. *)
let rec list_matches_all list =
  List.for_all pattern_matches_all list

(* Returns true iff a given column of a matrix matches everything. *)
let column_matches_all (matrix : matrix) column =
  list_matches_all (get_column matrix column)

(* Makes a list of [length] "Pany", i.e. a line of [length] catch-alls *)
let make_catch_all length =
  List.make length Ast.mkpany

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

(* Makes a list of [length] fresh variables. *)
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

let rec test_count tree =
  match tree with
  | UnfoldTuple(_, _, tr) ->
    (test_count tr)
  | SwitchConstruct(_, cases, default) ->
    let res = List.fold_left (fun count (_, _, tr) ->
        (test_count tr) + count
      ) 1 cases in
    (match default with
     | None -> res
     | Some tr ->
       res + (test_count tr))
  | SwitchConstant { cases; default_code } ->
    let res = List.fold_left (fun count (_, tr) ->
        (test_count tr) + count
      ) 1 cases in
    (match default_code with
     | None -> res
     | Some tr ->
       res + (test_count tr))
  | Leaf _ -> 0

let cost_measure = test_count

(* [backtrack_minimize compute cost left right] is used
   to decide which column to split. Columns are numbered
   and their indices run in the interval [left;right].
   The [compute] function embodies the search.
   Given a column index, it returns either None (e.g. 
   the column does not yield any split) or Some solution.
*)
let backtrack_minimize : (int -> 'a option) -> ('a -> int) -> int -> int -> 'a option =
  fun compute cost_measure left right ->
    let indices = List.range left `To right in
    let (result, _) =
      List.fold_left (fun ((best_sol, min_cost) as acc) index ->
          let solution = compute index in
          match solution with
          | None     -> acc
          | Some sol ->
            let c = cost_measure sol in
            if c < min_cost then
              (solution, min_cost)
            else
              acc
        ) (None, max_int) indices
    in
    result


(* The match compilation algorithm is functorized. *)

module type InputSig =
sig

  (* [sig_of x] returns the list of all constructors defined along [x],
   * including [x]. *)
  val sig_of : Ast.datacons -> Ast.datacons list

end


module Make(I : InputSig)
=
struct

  (* Simplify a matrix knowing that on [column] of [matrix],
   * the matched term is equal to [constant].  *)
  let simplify_constant matched_variable constant column matrix =
    List.fold_right (fun (line, action) new_matrix ->
        let l', { patt_desc }, l'' = slice_line line column in
        match patt_desc with
        | Pany ->
          let line = remove_at column line in
          (line, action) :: new_matrix
        | Pvar v ->
          let action = subst v (Eident { ident = matched_variable }) action in
          let line = remove_at column line in
          (line, action) :: new_matrix
        | Pconst c ->
          if c = constant then
            let line = remove_at column line in
            (line, action) :: new_matrix
          else
            (* The current line is incompatible with [constant], get rid of it *)
            new_matrix
        | Pconstruct(_, _) ->
          (* The current line is incompatible with [constant], get rid of it *)
          new_matrix
        | Ptuple _ ->
          failwith "badly flattened matrix"
      ) matrix []


  (* Simplify a matrix knowing that on [column] of [matrix],
     the matched term is of shape [constructor](..).
     [arity] is either 0 or 1. *)
  let simplify_algebraic matched_variable constructor arity column matrix =
    List.fold_right (fun (line, action) new_matrix ->
        let l', { patt_desc }, l'' = slice_line line column in
        match patt_desc with
        | Pany ->
          let catch_all = make_catch_all arity in
          let line = unslice_line l' catch_all l'' in
          (line, action) :: new_matrix
        | Pvar v ->      
          let action = subst v (Eident { ident = matched_variable }) action in
          let catch_all = make_catch_all arity in
          let line = unslice_line l' catch_all l'' in
          (line, action) :: new_matrix
        | Pconst _ ->
          (* Incompatible line. *)
          new_matrix
        | Pconstruct(cons, None) ->
          if cons = constructor then
            let line = remove_at column line in
            (line, action) :: new_matrix
          else
            (* Incompatible line. *)
            new_matrix
        | Pconstruct(cons, Some field) ->
          if cons = constructor then
            let line = unslice_line l' [field] l'' in
            (line, action) :: new_matrix
          else
            (* Incompatible line. *)
            new_matrix
        | Ptuple _ ->
          failwith "badly flattened matrix"
      ) matrix []


  (* Simplify a matrix keeping all the lines where the pattern
     on [column] is a catch-all or a variable. *)
  let default matched_variable column (matrix : matrix) =
    List.fold_right (fun (line, action) new_matrix ->
        let l', { patt_desc }, l'' = slice_line line column in
        match patt_desc with
        | Pany ->
          let line = remove_at column line in
          (line, action) :: new_matrix
        | Pvar v ->
          let action = subst v (Eident { ident = matched_variable }) action in
          let line = remove_at column line in
          (line, action) :: new_matrix
        | Pconst _ 
        | Pconstruct(_, _) ->
          new_matrix
        | Ptuple _ ->
          failwith "badly flattened matrix"
      ) matrix []

  
  let collect_constructors column =
    List.fold_left (fun acc { patt_desc } ->
        match patt_desc with
        | Pany | Pvar _ -> acc
        | Pconst c ->
          let cst = Constant c in
          if List.mem cst acc then
            acc
          else
            cst :: acc
        | Ptuple _ ->
          failwith "badly flattened matrix"
        | Pconstruct(cons, field) ->
          let arity =
            if field = None then 0 else 1
          in
          let cst = Algebraic(cons, arity) in
          if List.mem cst acc then
            acc
          else
            cst :: acc
      ) [] column

  (* Pattern-matching compilation algorithm. 
     [compile vars matrix freshgen] produces a decision tree. 
     The tree consists in a hierarchy of
     actions on these variables: unfold a variable of a product type into
     fresh sub-variables, switch on constructors or a switch on constants.     
  *)
  let rec compile vars (matrix : (Ast.pattern list * Ast.expr) list) freshgen =
    let first_line, first_action = 
      match matrix with
      | [] ->
        failwith "Empty pattern matrix."
      | (line, act) :: _ -> 
        (line, act)
    in
    if list_matches_all first_line then
      (* The first line matches everything. The first action
         will thus be executed. Matching compilation ends. *)
      let action = List.fold_left (fun action (var, { patt_desc }) ->
          match patt_desc with
          | Pany -> action
          | Pvar v ->
            subst v (Eident { ident = var }) action
          | _ ->
            failwith "bug in Matching"
        ) first_action (List.combine vars first_line) 
      in
      freshgen, (Leaf action)
    else
      (*backtrack_minimize f cost 0 width*)
      let try_column column_idx =
        match List.nth first_line (column_idx-1) with
        | { patt_desc = Ptuple exprs } ->
          (* Column [column_idx] is a tuple, unfold it *)
          Some (compile_tuple vars matrix exprs column_idx freshgen)
        | _ ->
          compile_target_column vars matrix freshgen column_idx
      in
      let cost (_, tree) = cost_measure tree in
      match backtrack_minimize try_column cost 1 (List.length first_line) with
      | None ->
        failwith "no solution found while compiling matching"
      | Some res ->
        res

  and compile_target_column vars matrix freshgen column_idx =
    (* Not a tuple pattern column. 
     * Get all the constructors used in the column. *)
    let column = get_column matrix column_idx in
    if list_matches_all column then
      (* This column does not discriminate the data. *)
      None
    else
      (* At this stage, the column must contain constants of variants. Collect them. *)
      let constructors = collect_constructors column in
      (* Build the switch for the constructors *)
      let result = 
        match constructors with
        | [] -> failwith "no constructors in column"
        | (Constant _) :: _ ->
          (* We match on constants. *)
          let constructors = 
            List.map (function
                | Constant const -> const
                | _ -> failwith "non-constant case in constant match"
            ) constructors
          in
          compile_constant vars matrix constructors column_idx freshgen
        | _ ->
          (* We match on an algebraic datatype *)
          let constructors = 
            List.map (function 
                | Algebraic(cons, 0) -> (cons, 0)
                | Algebraic(cons, 1) -> (cons, 1)
                | _ -> failwith "non-algebraic case in constant match"
              ) constructors 
          in
          compile_algebraic vars matrix constructors column_idx freshgen
      in
      Some result

  and compile_tuple vars matrix fields column_idx freshgen =
    (* If the chosen column is a tuple pattern, just unfold 
       the pattern using a dummy match. *)
    let arity      = List.length fields in
    let gen, fvs   = make_fresh_variables freshgen arity in
    let l', x, l'' = slice_line vars column_idx in
    let vars       = unslice_line l' fvs l'' in
    let mat, acts  = List.split matrix in
    let m', c, m'' = slice_column mat column_idx in
    let new_column = List.map (fun { patt_desc } ->
        match patt_desc with
        | Ptuple fields -> 
          fields
        | Pany ->
          make_catch_all arity
        | _ -> failwith "Matching is not well-typed."
      ) c in
    let columns   = unslice_column m' new_column m'' in
    let matrix    = List.combine columns acts in
    let gen, code = compile vars matrix gen in
    let code      = UnfoldTuple(x, fvs, code) in
    gen, code

  and compile_constant vars matrix constants column_idx freshgen =
    let l', matched_variable, l'' = slice_line vars column_idx in
    let vars = unslice_line l' [] l'' in
    let default_matrix = default matched_variable column_idx matrix in
    let freshgen, default_code = 
      match default_matrix with
      | [] -> (* Empty default matrix, no default branch *)
        freshgen, None
      | _ ->
        let freshgen, result = compile vars default_matrix freshgen in
        freshgen, (Some result)
    in
    let freshgen, cases = 
      List.fold_left (fun (freshgen, cases) const ->
          let matrix    = simplify_constant matched_variable const column_idx matrix in
          let gen, code = compile vars matrix freshgen in
          (gen, (const, code) :: cases)
        ) (freshgen, []) constants
    in
    let code = SwitchConstant { matched_variable; cases; default_code } in
    freshgen, code

  and compile_algebraic vars matrix constructors column_idx freshgen =
    let l', matched_variable, l'' = slice_line vars column_idx in
    let vars = unslice_line l' [] l'' in
    let default_matrix = default matched_variable column_idx matrix in
    let freshgen, default_code = match default_matrix with
      | [] -> (* Empty default matrix, no default branch *)
        freshgen, None
      | _ ->
        let freshgen, result = compile vars default_matrix freshgen in
        freshgen, (Some result)
    in
    let freshgen, cases = 
      List.fold_left (fun (freshgen, cases) (cons, arity) ->
          if arity = 0 then
            let matrix    = simplify_algebraic matched_variable cons 0 column_idx matrix in
            let gen, code = compile vars matrix freshgen in
            (gen, (cons, None, code) :: cases)
          else
            (* arity = 1 *)
            let matrix     = simplify_algebraic matched_variable cons 1 column_idx matrix in
            let gen, fresh = Fresh.next freshgen in
            let v'         = Fresh.var fresh in
            let vars       = unslice_line l' [v'] l'' in
            let gen, code  = compile vars matrix gen in
            (gen, (cons, (Some v'), code) :: cases)
        ) (freshgen, []) constructors
    in
    let code = SwitchConstruct(matched_variable, cases, default_code) in
    freshgen, code


  (* After pattern matching compilation, we use [tree_to_expr] to convert a
     test tree back into a now simple match construct. *)
  let rec tree_to_expr tree =
    match tree with
    | UnfoldTuple(var, tuplevars, subnode) ->
      let pattvars = List.map Ast.mkpvar tuplevars in
      let patts    = mkptuple pattvars in
      mkmatch (mkident var)
        [ { rpatt = patts; rexpr = tree_to_expr subnode } ]
    | SwitchConstruct(var, cases, default) ->
      let cases = List.map (fun (datacons, content, action) ->
          match content with
           | None ->
             { rpatt = mkpconstruct datacons None; rexpr = tree_to_expr action }
           | Some v ->
             { rpatt = mkpconstruct datacons (Some (mkpvar v)); rexpr = tree_to_expr action }
        ) cases 
      in
      let cases = match default with
        | None -> cases
        | Some code ->
          cases @ [{ rpatt = mkpany; rexpr = tree_to_expr code }]
      in
      mkmatch (mkident var) cases
    | SwitchConstant { matched_variable; cases; default_code } ->
      let cases = List.map (fun (constant, action) ->
          { rpatt = mkpconst constant; rexpr = tree_to_expr action }
        ) cases in
      let cases = match default_code with
        | None -> cases
        | Some code ->
          cases @ [ { rpatt = mkpany; rexpr = tree_to_expr code } ]
      in
      mkmatch (mkident matched_variable) cases
    | Leaf e -> e

  let rec matching_to_matrix matching =
    List.map (fun { rpatt; rexpr } -> ([rpatt], rexpr)) matching

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

