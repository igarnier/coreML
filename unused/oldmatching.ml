open Ast

(* Pattern matching compilation. *)

(* Very inefficient way to implement matrices: lists of lists. *)

type 'a matrix = 'a line list
and  'a line   = 'a list

type constructor_kind =
  | Algebraic of string * arity
  | Constant of Ast.constant
and arity = int

type node = 
    SwitchConstruct of (Ast.datacons * Ast.vvar option * int) list
  | SwitchConstant  of (Ast.constant * int) list

type automaton =
    { nodes : (int * node) list ; card : int }

(* ------------------------------------------------ *)
(* Helper function to build the matching automaton. *)

let empty = { nodes = []; card = 0 }

let get_node_id node automaton =
  let rec find nodes index =
    match nodes with
      | [] -> None
      | x :: l ->
	  if x = node then
	    Some index
	  else
	    find nodes (index+1)
  in
    find automaton.nodes 0

let add_datacons_switch node automaton =
  let id = automaton.card in
    { nodes = (id, node) :: automaton.nodes;
      card  = card + 1 }

let add_constant_switch node automaton =
  let id = automaton.card in
    { nodes = (id, node) :: automaton.nodes;
      card  = card + 1 }


(* -------------------------------------------------- *)
(* We will need various tools to manipulate matrices. *)

(* Slice a line l into l'|x|l'' where x is the n-th element. *)
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

(* Merges a left list l', a middle _line_ x and a right list l'' into a single list *)
let unslice_line l' x l'' = l' @ (x @ l'')

(* Merges a left matrix m', a middle _matrix_ c and a right matrix m'' into a new matrix *)
let unslice_column m' c m'' =
  let sliced_lines = List.combine (List.combine m' c) m'' in
    List.fold_right (fun ((l', x), l'') m ->
      (unslice_line l' x l'') :: m
    ) sliced_lines []

let rec remove_at idx l =
  if idx = 0 then
    List.tl l
  else match l with
    | [] ->
	failwith "remove_at : out of list bounds"
    | x :: l' ->
	x :: (remove_at (idx - 1) l')

(* ------------------------------------------------------------ *)
(* Various functions useful in the match compilation algorithm. *)

(* Returns true iff a line matches anything. *)
let rec pattern_matches_all (patt_desc, _) =
  match patt_desc with
    | Pany -> true
    | Pvar _ -> true
    | Ptuple patts ->
	List.for_all pattern_matches_all patts
    | _ -> false

let rec line_matches_all line =
  List.for_all pattern_matches_all line

(* Makes a list of [length] "Pany", i.e. a line of [length] catch-alls *)
let rec make_catch_all length =
  if length = 0 then
    []
  else
    Ast.mkpany :: (make_catch_all (length - 1))

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


(* The match compilation algorithm is functorized. *)

module type InputSig =
sig

  (* [sig_of x] returns the list of all constructors defined along [x],
   * including [x].  *)
  val sig_of : Ast.datacons -> Ast.datacons list
end


module Make(I : InputSig)
  =
struct

  (* Simplify a matrix knowing that on [column] of [matrix],
   * the matched term for [var] is [constant].  *)
  let simplify_constant constant var column matrix =
    List.fold_right (fun (line, action) new_matrix ->
      let l', (x, _), l'' = slice_line line column in
	match x with
	  | Pany ->
	      let line = remove_at column line in
		(line, action) :: new_matrix
	  | Pvar var' ->
	      (* Replace [var'] by a catch-all, and replace
	       * references to [var'] in [act] by a reference to
	       * [var] *)
	      let line = remove_at column line in
	      let act = Ast.subst var' (Eident var) action in
		(line, act) :: new_matrix
	  | Pconst c ->
	      if c = constant then
		let line = remove_at column line in
		  (line, action) :: new_matrix
	      else
		new_matrix
	  | Pconstruct(_, _) ->
	      new_matrix
	  | Ptuple _ ->
	      failwith "badly flattened matrix"
    ) matrix []


  (* Simplify a matrix knowing that on [column] of [matrix],
   * the matched term for [var] is of shape constructor(..).
   * [arity] is either 0 or 1. *)
  let simplify_algebraic constructor arity var column matrix =
    List.fold_right (fun (line, action) new_matrix ->
      let l', (x, _), l'' = slice_line line column in
	match x with
	  | Pany ->
	      let catch_all = make_catch_all arity in
	      let line = unslice_line l' catch_all l'' in
		(line, action) :: new_matrix
	  | Pvar var' ->
	      (* Replace [var'] by a catch-all, and replace
	       * references to [var'] in [act] by a reference to
	       * [var] *)
	      let catch_all = make_catch_all arity in
	      let line = unslice_line l' catch_all l'' in
	      let act = Ast.subst var' (Eident var) action in
		(line, act) :: new_matrix
	  | Pconst _ ->
	      new_matrix
	  | Pconstruct(cons, None) ->
	      if cons = constructor then
		let line = remove_at column line in
		  (line, action) :: new_matrix
	      else
		new_matrix
	  | Pconstruct(cons, Some field) ->
	      if cons = constructor then
		let line = unslice_line l' [field] l'' in
		  (line, action) :: new_matrix
	      else
		new_matrix
	  | Ptuple _ ->
	      failwith "badly flattened matrix"
    ) matrix []


  (* Pattern-matching compilation algorithm. *)
  let rec compile vars matrix freshgen =
    match matrix with
      | [] ->
	  (* No line to match. Let's fail. *)
	  let code = mkapp (mkident "fail") (mkconst (CInt (-1))) in
	    freshgen, code
      | (line, act) :: matrix' ->
	  if line_matches_all line then
	    freshgen, act
	  else
	    (* Choose a column which is not all-wilcard *)
	    let column_idx = 0 in (* todo_heuristic in *)
	      
	      match List.nth line column_idx with
		| (Ptuple fields, _) ->
		    (* If the chosen column is a tuple pattern, just unfold the pattern
		     * using a dummy match. *)
		    let arity     = List.length fields in
		    let gen, fvs  = make_fresh_variables freshgen arity in
		    let pattern   = mkptuple (List.map Ast.mkpvar fvs) in
		    let l', x, l'' = slice_line vars column_idx in
		    let vars      = unslice_line l' fvs l'' in
		    let mat, acts = List.split matrix in
		    let m', c, m'' = slice_column mat column_idx in
		    let c         = List.map2 (fun patt act ->
		      match patt with
			| (Ptuple fields, _) -> 
			    (fields, act)
			| (Pany, _) -> 
			    (make_catch_all arity, act)
			| (Pvar v', _) ->
			    (make_catch_all arity, Ast.subst v' (Eident x) act)
			| _ -> failwith "bug in matching compilation."
		    ) c acts in
		    let patterns, acts = List.split c in
		    let patterns  = unslice_column m' patterns m'' in
		    let matrix    = List.combine patterns acts in
		    let gen, code = compile vars matrix gen in
		    let code = mkmatch (mkident x) [ (pattern, code) ] in
		      gen, code
		| _ ->
		    (* Not a tuple pattern column. 
		     * Get all the constructors used in the column. *)
		    let column = List.map (fun (line, _) -> List.nth line column_idx) matrix in
		    let constructors = List.fold_left (fun acc (patt_desc, _) ->
		      match patt_desc with
			| Pany | Pvar _ -> acc
			| Pconst c ->
			    if List.mem (Constant c) acc then
			      acc
			    else
			      (Constant c) :: acc
			| Ptuple _ ->
			    failwith "badly flattened matrix"
			| Pconstruct(cons, field) ->
			    let arity =
			      if field = None then 0 else 1
			    in
			      if List.mem (Algebraic(cons, arity)) acc then
				acc
			      else
				(Algebraic(cons, arity)) :: acc
		    ) [] column in
		      
		    (* Build the switch for the constructors *)
		    let l', x, l'' = slice_line vars column_idx in
		    let freshgen, cases = List.fold_left (fun (freshgen, cases) cons ->
		      match cons with
			| Constant const ->
			    let pattern   = mkpconst const in
			    let matrix    = simplify_constant const x column_idx matrix in
			    let vars      = unslice_line l' [] l'' in
			    let gen, code = compile vars matrix freshgen in
			      (gen, (pattern, code) :: cases)
			| Algebraic(cons, 0) ->
			    let pattern   = mkpconstruct cons None in
			    let matrix    = simplify_algebraic cons 0 x column_idx matrix in
			    let vars      = unslice_line l' [] l'' in
			    let gen, code = compile vars matrix freshgen in
			      (gen, (pattern, code) :: cases)
			| Algebraic(cons, _) ->
			    let pattern    = mkpconstruct cons None in
			    let matrix     = simplify_algebraic cons 1 x column_idx matrix in
			    let gen, fresh = Fresh.next freshgen in
			    let v'         = Fresh.var fresh in
			    let vars       = unslice_line l' [v'] l'' in
			    let gen, code  = compile vars matrix freshgen in
			      (gen, (pattern, code) :: cases)
		    ) (freshgen, []) constructors in
		    let code = mkmatch (mkident x) cases in
		      freshgen, code

end
