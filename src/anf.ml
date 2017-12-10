open Ast

(* Transformation to administrative normal form *)
let rec flatten fg expr context =
  let (expr_desc, expr_id) = expr in
    match expr_desc with
      | Eident _
      | Econstant _ ->
	  context fg expr
      | Elet(var, bound, body) ->
	  (match desc bound with
	    | Ematch(matched_expr, matching) ->
		flatten fg matched_expr (fun fg x_matched_expr ->
		  let (fg, fresh) = Fresh.nextvar fg in
		  let matching =
		    List.map (fun (pattern, action) ->
		      let action = 
			flatten fg action (fun fg x_action -> mkapp (mkident fresh) x_action)
		      in
			(pattern, action)
		    ) matching
		  in
		  let match_expr = mkmatch x_matched_expr matching in
		  let body       = flatten fg body context in
		  let func       = mkfun var body in
		    mklet fresh func match_expr)
	    | bound_expr ->
		flatten fg bound (fun fg x_bound ->
		  let body = flatten fg body context in
		    mklet var x_bound body)
	  )
      | Efunction(var, body) ->
	  let body        = flatten fg body (fun fg x_body -> x_body) in
	  let (fg, fresh) = Fresh.nextvar fg in
	  let let_body    = context fg (mkident fresh) in
	    mklet fresh (mkfun var body) let_body
      | Efixpoint(vfix, var, body) ->
	  let body        = flatten fg body (fun fg x_body -> x_body) in
	  let (fg, fresh) = Fresh.nextvar fg in
	  let let_body    = context fg (mkident fresh) in
	    mklet fresh (mkfix vfix var body) let_body
      | Eapply(func, args) ->
	  flatten fg func (fun fg x_func ->
	    let (fg, fresh) = Fresh.nextvar fg in
	      flatten_apply fg x_func args (fun fg args ->
		let let_bound = mkexpr (Eapply(x_func, args)) in
		  mklet fresh let_bound (context fg (mkident fresh))) [])
      | Ematch(matched_expr, matching) ->
	  (match desc matched_expr with
	    | Ematch(matched_expr', matching') ->
		let outer_matching = matching in
		let inner_matching = matching' in
		let (fg, func_arg) = Fresh.nextvar fg in
		let (fg, func_id)  = Fresh.nextvar fg in
		  (* avoid outer matching duplication by factorizing it in a lambda *)
		let o_matching = List.map (fun (patt, action) ->
		  (patt, flatten fg action context)
		) outer_matching in
		let func_body   = mkmatch (mkident func_arg) o_matching in
		let func        = mkfun func_arg func_body in
		  (* transform the inner matching *)
		let i_matching  = List.map (fun (patt, action) ->
		  (patt, flatten fg action (fun fg x_action -> 
		    mkapp (mkident func_id) x_action))
		) inner_matching in
		let let_body = flatten fg matched_expr' (fun fg x_matched ->
		  mkmatch x_matched i_matching)
		in
		  mklet func_id func let_body
	    | _ ->
		let matching = List.map (fun (patt, action) ->
		  (patt, flatten fg action context)
		) matching in
		  flatten fg matched_expr (fun fg x_matched ->
		    mkmatch x_matched matching))
		      
      | Etuple fields ->
	  flatten_tuple fg fields context []
      | Econstruct(cons, None) ->
	  let (fg, fresh) = Fresh.nextvar fg in
	    mklet fresh (mkconstruct cons None) (context fg (mkident fresh))
      | Econstruct(cons, Some data) ->
	  flatten fg data (fun fg x_data ->
	    let (fg, fresh) = Fresh.nextvar fg in
	      mklet fresh (mkconstruct cons (Some x_data)) 
		(context fg (mkident fresh)))


and flatten_apply fg func args context acc =
  match args with
    | [] ->
	context fg (List.rev acc)
    | arg :: l ->
	flatten fg arg (fun fg x_arg ->
	  flatten_apply fg func l context (x_arg :: acc)
	)

and flatten_tuple fg fields context acc =
  match fields with
    | [] ->
	context fg (mktuple (List.rev acc))
    | field :: l ->
	flatten fg field (fun fg x_field ->
	  flatten_tuple fg l context (x_field :: acc)
	)

let perform_anf (decls, main) fg =
  (decls, flatten fg main (fun _ x -> x))
