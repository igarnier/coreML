(* Purely functional union-find module. *)

(*
  We simulate mutability in a monadic fashion.
  Each union-find node is associated to an unique id (= a pointer).
  A union-find node is either a Root or subnode, containing a pointer
  to its representative. Pseudo-mutability is achieved by re-mapping a pointer
  to a node.
*)

type variable = int

(* each element is linked to a unique key *)
type key = variable
    
type weight = int

type 'a node = {
  elt      : 'a;
  id       : key
}
	
type 'a node_info =
  | Root of 'a node * weight
  | UpLink of 'a node * key

type ('elt, 'acc) t = {
  repr_map  : ('elt node_info) IntMap.t;
  join_func : 'elt -> 'elt -> 'acc -> 'elt * 'acc
}

let make : ('elt -> 'elt -> 'acc -> 'elt * 'acc) -> ('elt,'acc) t =
  fun join_func ->
    { 
      repr_map = IntMap.empty;
      join_func = join_func
    }

(* [mkroot x k state] builds a root node and maps [k] to this root. *)
let mkroot : 'elt -> key -> ('elt,'acc) t -> ('elt,'acc) t =
  fun x k state ->
    let node = { elt = x; id = k } in
    let node_info = Root(node, 1) in
      { state with
	  repr_map = IntMap.add k node_info state.repr_map }
 
(* [find node state] 'dereferences' the [node] key. *)
let find : key -> ('elt,'acc) t -> ('elt node_info) = 
  fun node state ->
    try IntMap.find node state.repr_map
    with Not_found ->
      failwith "UnionFind.Make.repr : Inconsistent map, bug found ?"

(* [get node state] 'derefences' the [node] key, and returns the stored data. *)
let get : key -> ('elt,'acc) t -> 'elt = 
  fun node state ->
    let Root(n,_) =
      try IntMap.find node state.repr_map
      with Not_found ->
	failwith "UnionFind.Make.repr : Inconsistent map, bug found ?"
    in n.elt

let set : key -> 'elt -> ('elt,'acc) t -> ('elt,'acc) t =
  fun key repr state ->
    { state with
      repr_map = IntMap.add key (Root({ elt = repr; id = key },1)) state.repr_map }

(* [repr node state] follows the uplink up to the representative of [node].a
   We implement path compression on the fly. *)
let repr : key -> ('elt,'acc) t -> key * ('elt,'acc) t =
  fun node state ->
    let rec aux node state (acc : ('elt node) list) =
      match find node state with
	| Root (_, _) ->
	    (* do the path compression *)
	    let state = List.fold_left
	      begin fun state subnode ->
		{ state with
		  repr_map = IntMap.add subnode.id (UpLink(subnode,node)) state.repr_map }
	      end state acc
	    in node, state
	| UpLink (self, up_ptr) ->
	    aux up_ptr state (self :: acc)
    in
      aux node state []

	
(* [union x1 x2 state] merges the representatives of [x1] and [x2] *)
let union : key -> key -> ('elt,'acc) t -> 'acc -> ('elt,'acc) t * 'acc =
  fun x1 x2 state acc ->
    let node_info_1, state = repr x1 state in
    let node_info_2, state = repr x2 state in
    if node_info_1 == node_info_2 then
      (* the two representatives are the same, nothing to do *)
      state, acc
    else
      (* FIXME : here, the compiler whines because of the irrefutable pattern *)
      let Root(node1, w1) = find node_info_1 state in
      let Root(node2, w2) = find node_info_2 state in
      (* join the two elements; i.e. make a representative *)
      let elt, acc = state.join_func node1.elt node2.elt acc in
      if w1 > w2 then
	let new_root = Root({ elt = elt; id = node1.id}, w1 + w2) in
	let uplink = UpLink(node2,node_info_1) in
	let map = IntMap.add node_info_1 new_root state.repr_map in
	let map = IntMap.add node_info_2 uplink map in
	{ state with repr_map = map }, acc
      else
	let new_root = Root({ elt = elt; id = node2.id}, w1 + w2) in
	let uplink = UpLink(node1,node_info_2) in
	let map = IntMap.add node_info_2 new_root state.repr_map in
	let map = IntMap.add node_info_1 uplink map in
	{ state with repr_map = map }, acc		
	  
