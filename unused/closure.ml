(*
[fun x => e : Tx -> Te] = 
    let F = fun (c,x) => 
      let fv1 = field1(c) in
      let fv2 = field2(c) in
        ...
      let fvn = fieldn(c) in
        [e]
    in
      Closure(F, fv1, ..., fvn)

: muX.((X * Tx) -> [[B]], d1 * ... * dn)

type t ('tx,'tb,'tfv) =
 | Closure of ((t * 'tx) -> 'tb) * 'tfv

[a b] = avec (a : t -> u) et (b : t)
    clos : mu X.(((X x [t]) -> [u]) x d1 x ... x dn)
    let clos = [a] in    
    field0(clos)(clos, [b]) *)

open Ast
	    
let apply fn arg =
  let mao_fn   = mkident "__MAO_fn" in
  let mao_code = mkident "__MAO_code" in
  let action = mkapp mao_code (mktuple [mao_fn; arg]) in
  let pattern = 
    mkpconstruct "__MAO_closure" (Some (mkptuple [mkpvar "__MAO_code"; mkpany]))
  in
    mklet "__MAO_fn" fn (mkmatch mao_fn [ (pattern, action) ])

let closconv_function fun_arg body id free_vars =
  match free_vars with
    | [] ->
	let new_arg     = "__mao_argument" in	
	let arg_pattern = mkptuple [mkpany; mkpvar fun_arg] in
	let func = mkfun new_arg
	  (mkmatch (mkident new_arg)
	    [ (arg_pattern, body) ]) in
	let closure = 
	  mkconstruct "__MAO_closure" (Some (mktuple [func; mkconstruct "Stub" None]))
	in
	  (closure, [])
    | _ ->
	let free_vars = List.sort (fun (x, _) (y, _) -> String.compare x y) free_vars in
	let free_vars = Utils.filter_duplicates (fun (x, _) (y, _) -> x = y) free_vars in
	let free_vars = List.map (fun (var, var_id) -> (var, typing var_id)) free_vars in
	let fv_tuple  = mktuple (List.map (fun (var, _) -> mkident var) free_vars) in
	let fv_ptuple = mkptuple (List.map (fun (var, _) -> mkpvar var) free_vars) in
	let constr    = sprintf "__MAO_env_%s" id in
	let new_arg   = "__mao_arg" in
	let env_var   = "__mao_env" in
	let clos_var  = "__mao_clos" in
	let fv_intro  = mkconstruct constr (Some fv_tuple) in
	let fv_elim   = 
	  mkmatch (mkident env_var) 
	    [(mkpconstruct constr (Some fv_ptuple), body)]
	in
	let clos_elim =
	  mkmatch (mkident clos_var)
	    [(mkpconstruct "__MAO_closure" (Some (mkptuple [mkpany; mkpvar env_var])), fv_elim)]
	in
	let arg_elim =
	  mkmatch (mkident new_arg)
	    [(arg_mkptuple [mkpvar clos_var; mkpvar arg], clos_elim)]
	in
	let func = mkfun new_arg arg_elim in
	let closure = mkconstruct "__MAO_closure" (Some (mktuple [func; fv_intro])) in
	  (closure, [(constr, List.map snd free_vars)])


let closconv_fixpoint fixvar fun_arg body id free_vars =
  match free_vars with
    | [] ->
	let new_arg     = "__mao_argument" in	
	let arg_pattern = mkptuple [mkpany; mkpvar fun_arg] in
	let fixpoint_closure = 
	  mkconstruct "__MAO_closure" (Some (mktuple [mkident fixvar; mkconstruct "Stub" None]))
	in
	let body = Ast.subst fixvar fixpoint_closure body in
	let func = mkfix fixvar new_arg (mkmatch (mkident new_arg) [ (arg_pattern, body) ]) in
	let closure =
	  mkconstruct "__MAO_closure" (Some (mktuple [func; mkconstruct "Stub" None]))
	in
	  (closure, [])
    | _ ->
	let free_vars = List.sort (fun (x, _) (y, _) -> String.compare x y) free_vars in
	let free_vars = Utils.filter_duplicates (fun (x, _) (y, _) -> x = y) free_vars in
	let free_vars = List.map (fun (var, var_id) -> (var, typing var_id)) free_vars in
	let fv_tuple  = mktuple (List.map (fun (var, _) -> mkident var) free_vars) in
	let fv_ptuple = mkptuple (List.map (fun (var, _) -> mkpvar var) free_vars) in
	let constr    = sprintf "__MAO_env_%s" id in
	let new_arg   = "__mao_arg" in
	let env_var   = "__mao_env" in
	let clos_var  = "__mao_clos" in
	let fv_intro  = mkconstruct constr (Some fv_tuple) in
	let fixpoint_closure = 
	  mkconstruct "__MAO_closure" (Some (mktuple [mkident fixvar; mkident env_var]))
	in
	let body      = Ast.subst fixvar fixpoint_closure body in
	let fv_elim   = 
	  mkmatch (mkident env_var) 
	    [(mkpconstruct constr (Some fv_ptuple), body)]
	in
	let clos_elim =
	  mkmatch (mkident clos_var)
	    [(mkpconstruct "__MAO_closure" (Some (mkptuple [mkpany; mkpvar env_var])), fv_elim)]
	in
	let arg_elim =
	  mkmatch (mkident new_arg)
	    [(arg_mkptuple [mkpvar clos_var; mkpvar arg], clos_elim)]
	in
	let func = mkfun new_arg arg_elim in
	let closure = mkconstruct "__MAO_closure" (Some (mktuple [func; fv_intro])) in
	  (closure, [(constr, List.map snd free_vars)])


let rec closconv env (expr_desc, expr_id) =
  let desc, env = match expr_desc with
    | Eident _
    | Econstant _
    | Econstruct(_, None) ->
	expr_desc, env
    | Elet(var, bound, body) ->
	let bound, env = closconv env bound in
	let body,  env = closconv env body in
	  Elet(var, bound, body), env
    | Efunction(var, body) ->
	let free_vars  = Ast.free_variables (expr_desc, expr_id) in
	let body, env  = closconv env body in
	let code, decl = closconv_function var body expr_id free_vars in
	  (desc code), (decl @ env)
    | Efixpoint(vfix, var, body) ->
	let free_vars  = Ast.free_variables (expr_desc, expr_id) in
	let body, env  = closconv env body in
	let code, decl = closconv_fixpoint vfix var body expr_id free_vars in
	let env        = decl @ env in
	  (desc code), (decl @ env)
    | Eapply(func, args) ->
	let func, env   = closconv env func in
	let result, env = List.fold_left (fun (result, env) arg ->
	  let arg, env = closconv env arg in
	    (apply result arg, env)
	  ) (func, env) args in
	  desc result, env
    | Ematch(matched_expr, matching) ->
	let matched_expr, env = closconv env matched_expr in
	let matching, env = List.fold_right
	  (fun (pattern, action) (matching, env) ->
	    let action, env = closconv env action in
	      ((pattern, action) :: matching, env)
	  ) ([], env)
	in
	  Ematch(matched_expr, matching), env
    | Etuple fields ->
	let fields, env = List.fold_right (fun elt (fields, env) ->
	  let elt, env = closconv env elt in
	    (elt :: fields, env)
	) fields ([], env) in
	  (Etuple fields), env
    | Econstruct(datacons, Some e) ->
	let e, env = closconv env e in
	Econstruct(datacons, Some e), env
  in
    (desc, expr_id), env
