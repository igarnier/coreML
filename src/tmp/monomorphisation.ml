(* Monomorphisation *)

(* This module handles type monomorphisation. This is done by creating one
   version of each let-bound function for each instantiation type (roughly).
   In the worst-case scenario, the code size grows exponentially in the number of
   functions. Practical experiences (MLton) suggest that monomorphisation
   incurs a 30% growth of the source.

   This module works assuming that an alpha-conversion pass has been performed.
*)

open Printf

open Ast
open Utils
open Unification

exception Types_not_compatible of string
exception Monomorphisation_error of string

(* An "instantiation" is the fact of using a polymorphic function
   (uniquely represented by the uid of its binder, say X) with a type T. To
   each instantiation, we associate the instantiations which are
   performed in the body of X when instantiated with type T.
   The obtained structure is an instantiation tree,
   represented as a zipper.
*)

(* The structure of the instantiation graph is that of two mutually 
   recursive maps. The first layer is a binder map, associating each 
   binder to another map from types to string maps. This is a simple
   way to keep track of the context in which a polymorphic
   function is instantiated. In order to travel within this data
   structure, we embed it in a zipper. We store an unique id
   along the binders. These ids are not the ones of the binders
   but the ids of the locations where the binder is used. 
   Moreover, our type maps are quotiented with alpha-equivalence. 
*)

module InstGraph(I : Types.TypeSig) =
struct


  module AlphaTypeMap = Types.AlphaTypeMap(I)
  module AlphaTypeSet = Types.AlphaTypeSet(I)

  type binder = Ast.vvar * Ast.unique_id

  module BinderMap    = ExtMap.Make
    (struct
      type t = binder

      let compare = Pervasives.compare
    end)

  type map =
      Node of (map AlphaTypeMap.t) BinderMap.t
	
  type path =
      (binder * I.term * map) list
	
  type zipper = Zip of map * path
    
  type t = zipper

  let initial = Zip(Node BinderMap.empty, [])


  let print =
    let rec prsmap indent (Node smap) =
      BinderMap.iter (fun (binder, id) elt ->
	let line = sprintf "%s %s,%d\n" (String.make indent ' ') binder id in
	let _    = printf "%s\n" line in
	prtmap (indent+(String.length line)) elt
      ) smap
    and prtmap indent tmap =
      AlphaTypeMap.fold (fun typ elt () ->
	let ts = I.print typ in
	  printf "%s %s" (String.make indent ' ') ts;
	  prsmap indent elt;
	  printf "\n"
      ) tmap ()
    in
      fun (Zip(map, _)) ->
	prsmap 0 map

  (*s Traveling into the zipper is done trough the functions [enter_in]
    and [leave]. When an instantiation doesn't exist, [enter_in] creates 
    an empty one. These functions are used during type inference to build
    the instantiation graph. 
  *)

  let enter_in (Zip(map, path)) binder typ =
    let Node smap = map in
      match BinderMap.find_opt binder smap with
	| None ->
	    Zip(Node BinderMap.empty, (binder, typ, map) :: path)
	| Some tmap ->
	    (match AlphaTypeMap.find_opt typ tmap with
	      | None ->
		  Zip(Node BinderMap.empty, (binder, typ, map) :: path)
	      | Some sub_map ->
		  Zip(sub_map, (binder, typ, map) :: path))

  let enter_in_preexistent (Zip(map, path)) binder typ =
    let Node smap = map in
    let bind, id  = binder in
      match BinderMap.find_opt binder smap with
	| None ->
	    let s = sprintf "Binder %s,%d not in current instantiation graph." bind id in
	      raise (Monomorphisation_error s)
	| Some tmap ->
	    (match AlphaTypeMap.find_opt typ tmap with
	      | None ->
		  Zip(Node BinderMap.empty, (binder, typ, map) :: path)
	      | Some sub_map ->
		  Zip(sub_map, (binder, typ, map) :: path))

  let leave = function
    | Zip(map, []) ->
	raise (Monomorphisation_error "zipper : empty_path")
    | Zip(Node map, (var, typ, Node enclosing_map) :: l) ->
	let usages   = BinderMap.find var enclosing_map in
	let type_map = AlphaTypeMap.add typ (Node map) usages in
	  Zip(Node (BinderMap.add var type_map enclosing_map), l)

  (*s When instantiating a polymorphic function with a given type (e.g. at
     call sites) we use [add_usage] to record this usage in the current
     context as defined by the zipper. 
  *)

  let add_usage (Zip(Node map, path)) binder typ =
    match BinderMap.find_opt binder map with
      | None ->
	  (* binder not present. Add it, with an empty sub-tree. *)
	  let type_map   = AlphaTypeMap.add typ (Node BinderMap.empty) AlphaTypeMap.empty in
	  let binder_map = BinderMap.add binder type_map map in
	    Zip(Node binder_map, path)
      | Some typemap ->
	  (match AlphaTypeMap.find_opt typ typemap with
	    | None ->
		(* Binder already instanciated, but not with this type. *)
		let type_map   = AlphaTypeMap.add typ (Node BinderMap.empty) typemap in
		let binder_map = BinderMap.add binder type_map map in
		  Zip(Node binder_map, path)
	    | Some _ ->
		(* Binder not already instanciated with this type. *)
		Zip(Node map, path))

  (*s After building the instantiation graph, When performing monomorphisation, 
    we need to find all types with which a given binding is used. This is done 
    using [find_usages]. We recursively run trough the instantiation graph, 
    filling an accumulator with all instantiations of [let_binding]. 
  *)

  let rec find_usages let_binding (Zip(tree, _)) =
    let rec find_usages let_binding (Node map) =
      BinderMap.fold (fun binder (typemap : map AlphaTypeMap.t) usages ->
	if binder = let_binding then
	  (* No polymorphic recursion, so no need to recurse on
	   * the typemaps. *)
	  let domain = AlphaTypeMap.domain typemap in
	    List.rev_append domain usages
	else
	  AlphaTypeMap.fold (fun _ map acc ->
	    List.rev_append (find_usages let_binding map) acc
	  ) typemap usages
	) map []
    in
    let type_list = find_usages let_binding tree in
      (* Suppress duplicates. We could be smarter by avoiding
       * inserting them in the first place. Too much work. *)
    let eq = I.types_equivalent in
      Utils.filter_duplicates eq type_list



  (*s When performing monomorphisation, we will need to compute
    the view of an instantiation graph restricted to a given binding.
    This is performed by [rebuild_graph], wich computes from an
    instantiation graph a type map for [let_binding] by recursing
    on the instantiation graph. We encountering an usage, we fuse
    the usage's type map with the returned result.
  *)

  let rebuild_graph let_binding (Zip(tree, _)) =
    let rec find_usages (Node map) =
      BinderMap.fold (fun (binder, _) typemap merged_map ->
	if binder = let_binding then
	  (* No polymorphic recursion, so no need to recurse on
	   * the typemaps. *)
	  AlphaTypeMap.fusion (fun x _ -> x) typemap merged_map
	else
	  AlphaTypeMap.fold (fun _ map acc ->
	    AlphaTypeMap.fusion (fun x _ -> x) (find_usages map) acc
	  ) typemap merged_map
      ) map AlphaTypeMap.empty
    in
    find_usages tree
      
end

module Graph = InstGraph(Types.Default)

(*s While building the instantiation graph, during polymorphic type inference,
  the types used to create the nodes of the graph are not fully instantiated,
  since unification is done afterwards. Once unification is done, after type
  inference, we must ''quotient´´ the graph using the relation which unfolds
  the types using the most general unifier. This quotienting is performed
  by [quotient_graph]. *)

let quotient_graph : 
    (Types.Default.term -> Types.Default.term) -> Graph.t -> Graph.t =
  fun unfold ->

  let rec quotient_smap (Graph.Node map) =
    Graph.Node(Graph.BinderMap.map quotient_tmap map)

  and quotient_tmap tmap =
    let module AMap = Graph.AlphaTypeMap in
      AMap.fold (fun folded_key elt new_map ->
	let unfolded_key = unfold folded_key in
	  if (not (Types.is_ground unfolded_key)) && (elt = Graph.Node Graph.BinderMap.empty) then
	    new_map
	  else
	    match AMap.find_opt unfolded_key new_map with
	      | None ->
		  AMap.add unfolded_key (quotient_smap elt) new_map
	      | Some prev_elt ->
		  AMap.add unfolded_key (merge_smap prev_elt (quotient_smap elt)) new_map
      ) tmap AMap.empty

  and merge_smap (Graph.Node map1) (Graph.Node map2) =
    Graph.Node (Graph.BinderMap.fusion merge_tmap map1 map2)

  and merge_tmap map1 map2 =
    Graph.AlphaTypeMap.fusion merge_smap map1 map2
    
  in fun vargraph ->
    match vargraph with
	Graph.Zip(map, path) ->
	  Graph.Zip(quotient_smap map,
	  List.map (fun (s, t, map) -> (s, unfold t, quotient_smap map)) path)

(*i ----------------------------------------------------------------- i*)

(*s The [AltEnv] module maps a source let-bound expression to
  a list of alternatives (one alternative for each instantiation type). *)
module AltEnv =
struct

  type t = ((string * Types.Default.term) * string) list
      
  let initial = []

  let rec mem (s, t) (map : t) =
    match map with
      | [] -> false
      | ((s', t'), _) :: tl ->
	  if s = s' && (Types.Default.types_equivalent t t') then
	    true
	  else
	    mem (s, t) tl

  let rec find_opt (s, t) map =
    match map with
      | [] -> None
      | ((s', t'), elt) :: tl ->
	  if s = s' && (Types.Default.types_equivalent t t') then
	    Some elt
	  else
	    find_opt (s, t) tl
	      
  let add key elt map =
    (key, elt) :: map

  let rec fold f map acc =
    match map with
      | [] -> acc
      | (x, y) :: l ->
	  fold f l (f x y acc)

  let domain map = List.map fst map

  let codomain map = List.map snd map
    
end

(*s The input signature for the monomorphisation functor contains
  the instantiation graph [inst_graph] built during type inference,
  and a function [subject_to_value_restriction] indicating wether a given 
  expression should be duplicated or not. Note that the instantiation
  graph should be quotiented using [quotient_graph] beforehand.
  In our case, this is done in the [Inference] module.
*)
module type InputSig =
sig

  (* [subject_to_value_restriction] returns [true] if the given expression is
     either not a value or a tainted (mutable) value. *)
  val subject_to_value_restriction : Ast.expr -> bool

  (* The \textit{quotiented} instantiation graph. *)
  val inst_graph : Graph.t

end


(* This functor instantiates a new monomorphiser for a given instantiation graph. *)
module Make(I : InputSig) =
struct
   
  (*s [mm_structure_item] monomorphises a structure item (only expressions, of course).
    [alt_env] contains the alternatives, [freshgen] is used to produce fresh 
    names in a monadic and pure fashion, and [item] is the structure item 
    itself. Since structure items are top-level, the instantiation context 
    is empty and thus not represented at all. *)
  let rec mm_structure_item alt_env freshgen (item_desc, item_id) =
    let alt_env, freshgen, desc = begin match item_desc with
      | Itypedecl _ | Iexternal(_, _) ->
	  alt_env, freshgen, item_desc
    end in
      alt_env, freshgen, (desc, item_id)

  (*s [mm_binding] monomorphises a binding (e.g. a \textbf{let}).
    The binding is represented as a couple \textit{([binder],[expr])}
    where [expr] is the expression bound to [binder]. Two cases
    may arise:
    \begin{itemize}
    \item whenever [expr] is subject to the value restriction, we
    don't bother duplicating anything since we know that the binding
    was typed in a monomorphic fashion. We simply recurse on [expr].
    \item Otherwise, we proceed as follows:
      \begin{enumerate}
      \item we search all usages of [binder] in [inst_graph], the current
        instantiation graph; if there are no usages then the binding is
        dead code and we supress it.
      \item In the other case, we create a fresh binding for each usage,
        updating the alternatives in [alt_env] and recursing on
        [expr] using this new [alt_env] and the local [inst_graph].
      \end{enumerate}
    \end{itemize}
  *)
  and mm_binding alt_env inst_graph freshgen (binder, expr) =

    if not (I.subject_to_value_restriction expr) then

      let usages = Graph.rebuild_graph binder inst_graph in
	if usages = Graph.AlphaTypeMap.empty then
	  (* No usages at all for the binding. *)
	  alt_env, freshgen, []
	else
 	  Graph.AlphaTypeMap.fold (fun domtype smap (alt_env, freshgen, bindings) ->
	    (* For each usage of this binding, produce a fresh binder. *)
	    let gen, fresh = Fresh.next freshgen in
	    let fresh_var  = binder^^(Fresh.var fresh) in
	    let alt_env    = AltEnv.add (binder, domtype) fresh_var alt_env in
	    let gen, expr  = mm_expr alt_env (Graph.Zip(smap,[])) gen expr in
	      (* modify the binding pattern accordingly *)
	      (alt_env, gen, (fresh_var, expr) :: bindings)
	  ) usages (alt_env, freshgen, []) 
    else
      let freshgen, expr = mm_expr alt_env inst_graph freshgen expr in
	alt_env, freshgen, [(binder, expr)]

  (*s [mm_expr] monomorphises expressions. The only interesting case is the first one,
     for handling the variables. We must search the relevant usage (there can
     be only one if [mm_binding] did a correct job at updating the [inst_graph]), 
     and using [alt_env] we can find the new binder for the identifier.
     The other cases are simple recursions on the AST.
  *)
  and mm_expr (alt_env : AltEnv.t) (inst_graph : Graph.t) freshgen (expr_desc, expr_id) =
    let freshgen, desc = 
      begin match expr_desc with
	| Eident id ->
	    (* Here, we must replace variables by their monomorphised counterpart (since the
	     * orignal binder may have been duplicated with a new name) *)
	    (match Graph.find_usages (id, expr_id) inst_graph with
	      | [] ->
		  raise (Monomorphisation_error ("no typing for "^id))
	      | [typ] ->
		  (match AltEnv.find_opt (id, typ) alt_env with
		    | None ->
			freshgen, (Eident id)
		    | Some new_ident ->
			freshgen, (Eident new_ident))
	      | _ ->
		  raise (Monomorphisation_error ("more than one typing for "^id)))	      
	| Econstant _ ->
	    freshgen, expr_desc
	| Elet(var, bound, body) ->
	    let alt_env, freshgen, bindings = 
	      mm_binding alt_env inst_graph freshgen (var, bound) in
	    let freshgen, body = mm_expr alt_env inst_graph freshgen body in
	      if bindings = [] then
		freshgen, (desc body)
	      else
		let freshgen, expr = List.fold_right (fun (var, bound) (freshgen, sub_expr) ->
		  let gen, fresh_id = Fresh.next freshgen in
		  let expr = (Elet(var, bound, sub_expr), fresh_id) in
		    gen, expr
		) bindings (freshgen, body)
		in
		let expr_desc, _ = expr in
		  freshgen, expr_desc
	| Efunction(var, body) ->
	    let freshgen, body = mm_expr alt_env inst_graph freshgen body in
	      freshgen, (Efunction(var, body))
	| Efixpoint(vfix, var, body) ->
	    let freshgen, body = mm_expr alt_env inst_graph freshgen body in
	      freshgen, (Efixpoint(vfix, var, body))
	| Eapply(func, args) ->
	    let freshgen, func = mm_expr alt_env inst_graph freshgen func in
	    let freshgen, args = List.fold_right
	      (fun arg (freshgen, args) ->
		let freshgen, arg =
		  mm_expr alt_env inst_graph freshgen arg in
		  (freshgen, arg :: args)
	      ) args (freshgen, []) in
	    let desc = Eapply(func, args) in
	      freshgen, desc
	| Ematch(matched_expr, matching) ->
	    let freshgen, matched_expr = 
	      mm_expr alt_env inst_graph freshgen matched_expr in
	    let freshgen, matching =
	      mm_matching alt_env inst_graph freshgen matching in
	    let desc = Ematch(matched_expr, matching) in
	      freshgen, desc
	| Etuple fields ->
	    let freshgen, fields = List.fold_right
	      (fun field (freshgen, fields) ->
		let freshgen, field =
		  mm_expr alt_env inst_graph freshgen field in
		  (freshgen, field :: fields)
	      ) fields (freshgen, []) in
	      freshgen, (Etuple fields)
	| Econstruct(constr, None) ->
	    freshgen, expr_desc
	| Econstruct(constr, Some e) ->
	    let freshgen, e = 
	      mm_expr alt_env inst_graph freshgen e in
	    let desc = Econstruct(constr, Some e) in
	      freshgen, desc
      end
    in
      freshgen, (desc, expr_id)

  and mm_matching alt_env inst_graph freshgen matching =
    List.fold_right
      (fun (patt, expr) (freshgen, matching) ->
	let freshgen, expr =
	  mm_expr alt_env inst_graph freshgen expr in
	  (freshgen, (patt, expr) :: matching)
      ) matching (freshgen, [])

  let rec mm_program freshgen (decls, main) =
    let freshgen, main = mm_expr AltEnv.initial I.inst_graph freshgen main in
      freshgen, (decls, main)

end
