(* Defunctionalization. We require all AST nodes to be
   uniquely identified. *)

open Utils

module FunctionMap =
  ExtMap.Make(struct
    type t = (int * string * Types.term option)
    let  compare : (int * 'a * 'b) -> (int * 'a * 'b) -> int =
      fun (x, _, _) (y, _, _) ->
	Pervasives.compare x y
  end)

let add   = FunctionMap.add
let empty = FunctionMap.empty

let env_type free_vars =
  let free_vars = List.sort (fst ++ String.compare) free_vars in
  let free_vars = Utils.filter_duplicates (fun (x, _) (y, _) -> x = y) free_vars in
    match free_vars with
      | [] -> None
      | [(_, id)] ->
	  let typ = typing id in
	    Some (Types.to_core_type typ)
      | _ -> 
	  let typ = Types.tuple_type (List.map (snd ++ typing) free_vars) in
	    Some (Types.to_core_type typ)

let rec defunc_lambdas map expression =
  let (expr_desc, expr_id) = expression in
  let map, desc = match expr_desc with
    | Eident _
    | Econstant _
    | Econstruct(_, None) ->
	map, expr_desc
    | Elet(var, bound, body) ->
	let map, bound = defunc_lambdas map bound in
	let map, body  = defunc_lambdas map body in
	  map, Elet(var, bound, body)
    | Efunction(var, body) ->
	let free_vars = Ast.free_variables (expr_desc, expr_id) in
	let env_type  = env_type free_vars in
	let id = "__MAO_function_"^expr_id in
	let map, body = defunc_lambdas map body in
	let map = add (expr_id, id, env_type) expression in
	  map, Econstruct(id, Some (mktuple (List.map Ast.mkident free_vars)))
    | Efixpoint(fixvar, var, body) ->
	let free_vars = Ast.free_variables (expr_desc, expr_id) in
	let env_type  = env_type free_vars in
	let id = "__MAO_function_"^expr_id in
	let map, body = defunc_lambdas map body in
	let map = add (expr_id, id, env_type) expression in
	  map, Econstruct(id, Some (mktuple (List.map Ast.mkident free_vars)))
    | Eapply(func, args) ->
	let map, func = defunc_lambdas map func in
	let map, args = List.fold_right (fun arg (map, args) ->
	  let map, arg = defunc_lambdas map arg in
	    (map, arg :: args)
	) args (map, []) in
	  map, (Eapply(func, args))
    | Ematch(matched_expr, matching) ->
	let map, matched_expr = defunc_lambdas map matched_expr in
	let map, matching = List.fold_right
	  (fun (pattern, action) (map, matching) ->
	    let map, action = defunc_lambdas map action in
	      (map, (pattern, action) :: matching)
	  ) matching (map, [])
	in
	  map, (Ematch(matched_expr, matching))
    | Etuple fields ->
	let map, fields = List.fold_right (fun field (map, fields) ->
	  let map, field = defunc_lambdas map field in
	    (map, field :: fields)
	) fields (map, [])
	in
	  map, (Etuple fields)
    | Econstruct(datacons, Some e) ->
	let map, e = defunc_lambdas map e in
	  map, Econstruct(datacons, Some e)

let produce_typedecl map =
  let keys = FunctionMap.domain map in
  let constructors = 
    List.map (fun (id, cons, typ) ->
      (cons, typ)
    ) keys
  in
  let kind = SumType constructors in
    { tdecl_parameters = [];
      tdecl_name = "__MAO_environments";
      tdecl_kind = kind }

let mkapply constructors env =
  let matching = FunctionMap.fold (fun (id, cons, typ)
      

  
