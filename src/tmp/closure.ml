
(* Closure conversion makes explicit the handling of the
   environment when dealing with first class functions.
   Closure conversion is a typed transformation.
   The interesting cases are that of functions and applications.
   
   Functions are parameterised by their environment, so that they are closed.
   The environment is packed together with the modified function.
   
[fun x => e : Tx -> Te] = 
    let F = fun (env,x) => 
      let fv1 = field1(env) in
      let fv2 = field2(env) in
        ...
      let fvn = fieldn(env) in
      [e]
    in
      Closure(F, fv1, ..., fvn)

   Closure conversion is well-behaved typewise. The product
   of converting a function as above has type:

muX.((X * Tx) -> [[B]], d1 * ... * dn)

   A type which can be represented as

type t ('tx,'tb,'tfv) =
 | Closure of ((t * 'tx) -> 'tb) * 'tfv

   Application of a function consists in unpacking
   the closure and its environment and applying its environment
   together with the argument.

[a b] = 
    let clos = [a] in    
    field0(clos) (clos, [b]) 

    where
(a : t -> u) and (b : t)
    and
clos : mu X.(((X * [t]) -> [u]) * d1 * ... * dn)

*)

open Printf

open Ast
open Types.NoDebug
open Types
open Terms

(* The input signature for the closure conversion functor contains a typing 
   function [id_typing] mapping the nodes' unique ids to their _monomorphic_
   type. *)

module type InputSig =
sig
  val id_typing : Ast.unique_id -> Types.NoDebug.term
end

module Make(I : InputSig) =
struct

  let stub_cons    = "Stub"
        
  let closure_cons = "Closure"
    
  let closure_type_name = "closure_type"
    
  let env_type_name = "environments_type"
        
  (* [fn arg] =
     let closure_name = [fn] in
     match closure_name with
     [ Closure (code, _) =>
       code (closure_name, [arg])
     ]

     We introduce closure_name in order to avoid code duplication.
   *)
  let apply fg fn arg =
    let fg, closure_name = fresh fg "closure" in
    let fg, code = fresh fg "code" in
    let result =
      E.letb closure_name fn 
        (E.mtch (E.id closure_name) 
           [
             P.cns1 closure_cons (P.tpl [P.var code; P.any]) |->
                E.app (E.id code) (E.tpl [E.id closure_name; arg])
           ]
        )
    in
    (fg, result)

  (* [fun arg => body] =
     if the function has no free variables, letting arg' be fresh:
        Closure(fun arg' => match arg' with [ (_, arg) => body ], Stub)
     else, if the function has free variables fv1, ..., fvn
        Closure(fun arg' =>
                  match arg' with
                  [
                    (closure, arg) =>
                    match closure with
                    [
                      Closure(_, env) =>
                        match env with
                        [
                          Env(fv1,...,fvn) =>
                             body
                        ]
                    ]
                  ],
               Env(fv1,...,fvn)
              )

     Here, the arg', closure, and Env identifiers/constructors are fresh.
     We return Env together with its arity to add it back in the type
     declarations.
  *)

  let closconv_function fg arg body free_vars =
    match free_vars with
    | [] ->
      let fg, arg' = fresh fg arg in
      let func = 
        E.lam arg'
          (E.mtch (E.id arg')
             [ 
               (P.tpl [P.any; P.var arg]) |-> body
             ]) 
      in
      let closure = 
        E.cns1 closure_cons (E.tpl [func; E.cns0 stub_cons])
      in
      (fg, closure, None)
    | _ ->
      let free_vars = List.map (fun (var, var_id) -> (var, I.id_typing var_id)) free_vars in
      let fv_expr, fv_patt =
        match free_vars with
        | [] -> failwith "impossible case"
        | [(fv, _)] ->
          E.id fv, P.var fv
        | _ ->
          let fv_expr = E.tpl (List.map (fun (var, _) -> E.id var) free_vars) in
          let fv_patt = P.tpl (List.map (fun (var, _) -> P.var var) free_vars) in
          fv_expr, fv_patt
      in
      let fg, env_constr = fresh fg "Env" in
      let fg, arg'       = fresh fg arg in
      let fg, env_var    = fresh fg "env" in
      let fg, clos_var   = fresh fg "closure" in
      let fv_intro       = E.cns1 env_constr fv_expr in
      let arg_elim =
        E.mtch (E.id arg')
          [
            P.tpl [P.var clos_var; P.var arg] |->
              E.mtch (E.id clos_var)
                [
                  P.cns1 env_constr (P.tpl [P.any; P.var env_var]) |->
                    E.mtch (E.id env_var)
                      [
                        P.cns1 env_constr fv_patt |-> body
                      ]
                ]
          ]
      in
      let func    = E.lam arg' arg_elim in
      let closure = E.cns1 closure_cons (E.tpl [func; fv_intro]) in
      (fg, closure, Some (env_constr, List.map snd free_vars))


  let closconv_fixpoint fg fix arg body free_vars =
    match free_vars with
    | [] ->
      let fg, arg' = fresh fg arg in
      let fixpoint_closure =
        E.cns1 closure_cons (E.tpl [E.id fix; E.cns0 stub_cons])
      in
      let func =
        E.fix fix arg'
          (E.mtch (E.id arg')
             [
               P.tpl [P.any; P.var arg] |->
                 (Ast.subst fix fixpoint_closure.expr_desc body)
             ]
          )
      in
      let closure =
        E.cns1 closure_cons (E.tpl [func; E.cns0 stub_cons])
      in
      (fg, closure, None)
    | _ ->
      let free_vars = List.map (fun (var, var_id) -> (var, I.id_typing var_id)) free_vars in
      let fv_expr, fv_patt =
        match free_vars with
        | [] -> failwith "impossible case"
        | [(fv, _)] ->
          E.id fv, P.var fv
        | _ ->
          let fv_expr = E.tpl (List.map (fun (var, _) -> E.id var) free_vars) in
          let fv_patt = P.tpl (List.map (fun (var, _) -> P.var var) free_vars) in
          fv_expr, fv_patt
      in
      let fg, env_constr = fresh fg "Env" in
      let fg, arg'       = fresh fg arg in
      let fg, env_var    = fresh fg "env" in
      let fg, clos_var   = fresh fg "closure" in
      let fv_intro       = E.cns1 env_constr fv_expr in
      let fixpoint_closure = 
        E.cns1 closure_cons (E.tpl [E.id fix; E.id env_var])
      in
      let arg_elim =
        E.mtch (E.id arg')
          [
            P.tpl [P.var clos_var; P.var arg] |-> 
              E.mtch (E.id clos_var)
                [
                  P.cns1 closure_cons (P.tpl [P.any; P.var env_var]) |-> 
                    E.mtch (E.id env_var) 
                      [
                        P.cns1 env_constr fv_patt |->
                           (Ast.subst fix fixpoint_closure.expr_desc body)
                      ]
                ]
          ]
      in
      let func = E.fix fix arg' arg_elim in
      let closure = E.cns1 closure_cons (E.tpl [func; fv_intro]) in
      (fg, closure, Some (env_constr, List.map snd free_vars))


  let rec closconv fg env ({ expr_desc; uid } as expr) =
    let fg, env, expr_desc = 
      match expr_desc with
      | Eident _
      | Econstant _
      | Econstruct { data = None } ->
        fg, env, expr_desc
      | Elet { binder; bound; body } ->
        let fg, env, bound = closconv fg env bound in
        let fg, env, body  = closconv fg env body in
        fg, env, Elet { binder; bound; body }
      | Efunction { arg; body } ->
        let free_vars      = Ast.free_variables expr in
        let fg, env, body  = closconv fg env body in
        let fg, code, decl = closconv_function fg arg body free_vars in
        let env =
          match decl with
          | None -> env
          | Some env_constr -> env_constr :: env
        in
        fg, env, code.expr_desc
      | Efixpoint { fix; arg; body } ->
        let free_vars      = Ast.free_variables expr in
        let fg, env, body  = closconv fg env body in
        let fg, code, decl = closconv_fixpoint fg fix arg body free_vars in
        let env =
          match decl with
          | None -> env
          | Some env_constr -> env_constr :: env
        in
        fg, env, code.expr_desc
      | Eapply { f; args } ->
        let fg, env, func   = closconv fg env f in
        let fg, env, result = List.fold_left (fun (fg, env, result) arg ->
            let fg, env, arg = closconv fg env arg in
            (fg, env, E.app result arg)
          ) (fg, env, func) args in
        fg, env, result.expr_desc
      | Ematch { matched; matching } ->
        let fg, env, matched = closconv fg env matched in
        let fg, env, matching = List.fold_right
            (fun { rpatt; rexpr } (fg, env, matching) ->
               let fg, env, rexpr = closconv fg env rexpr in
               (fg, env, { rpatt; rexpr } :: matching)
            ) matching (fg, env, [])
        in
        fg, env, Ematch { matched; matching }
      | Etuple { exprs } ->
        let fg, env, exprs = List.fold_right (fun elt (fg, env, fields) ->
            let fg, env, elt = closconv fg env elt in
            (fg, env, elt :: fields)
          ) exprs (fg, env, []) in
        fg, env, Etuple { exprs }
      | Econstruct { cons; data = Some e } ->
        let fg, env, e = closconv fg env e in
        fg, env, Econstruct { cons; data = Some e }
    in
    fg, env, { expr_desc; uid }

  let closure_type domain codomain =
    TermCons(closure_type_name, [domain; codomain])

  let rec closify_type typ =
    match typ with
    | TermVar _ -> typ
    | TermCons("->", [domain; codomain]) ->
      closure_type (closify_type domain) (closify_type codomain)
    | TermCons("->", _) ->
      failwith "inconsistent arrow type in closure conversion"
    | TermCons(tc, subtypes) ->
      TermCons(tc, List.map closify_type subtypes)

  let closify_kind kind =
    match kind with
    | Builtin -> kind
    | SumType (IndIntros { ind_intros }) ->
      let ind_intros = List.map (function
          | (datacons, None) -> 
            (datacons, None)
          | (datacons, Some typ) ->
            (datacons, Some (closify_type typ))
        ) ind_intros in
      SumType (IndIntros { ind_intros })
    | SumType IndAbs _ ->
      failwith "Closure : bug found in closify_kind"

  let closify_decl decl =
    { decl with
      tdecl_kind = closify_kind decl.tdecl_kind }

  let rec closify_item { item_desc; uid } =
    let item_desc = match item_desc with
      | Iexternal _ ->
        item_desc
      | Itypedecl decls ->
        Itypedecl (List.map closify_decl decls)
    in
    { item_desc; uid }


  let pseudo_cast =
    Terms.remap_term
      (fun x -> x)
      (fun _ -> failwith "Closure.pseudo_cast : bug found, type variable in inductive definition.")

  let closure_conversion fg { program_decls; main } =
    let fg, new_decls, main = closconv fg [] main in
    (* let new_decls = List.sort (fun (x,_) (y,_) -> String.compare x y) new_decls in *)
    (* let new_decls = Utils.filter_duplicates (fun (x,_) (y,_) -> x = y) new_decls in *)
    let sumtype = List.map (fun (cons, domain) ->
        let domtype = match domain with
          | [] -> None
          | [dom] -> 
            Some (pseudo_cast dom)
          | _ ->
            let domain = tuple_type domain in
            let domain = pseudo_cast domain in
            Some domain
        in
        (cons, domtype)
      ) new_decls in
    let sumtype = (stub_cons, None) :: sumtype in
    let env_decl = { 
      tdecl_name = environments_type;
      tdecl_kind = SumType (IndIntros { ind_intros = sumtype })
    } in
    let env_decl = closify_decl env_decl in
      (*
type closure ('a, 'b) = 
[ Closure of (((closure ('a, 'b))  * 'a) -> 'b) * foo ]
      *)
    let clos_domtype =
      tuple_type
        [arrow_type
           (tuple_type [(mktype closure_type_name [mkvar "a0"; mkvar "a1"]); mkvar "a0"])
           (mkvar "a1");
         mk0ary env_type_name]
    in
    let clos_decl = {
      tdecl_name = closure_type_name;
      tdecl_kind = 
        SumType (IndAbs { ind_type_var = "a0";
                          ind_type = 
                            IndAbs { ind_type_var = "a1";
                                     ind_type = 
                                       IndIntros { ind_intros = [(closure_cons, Some clos_domtype)] } 
                                   }
                        }
                )
    } in
    let decls = List.map closify_item decls in
    let decls = (Itypedecl [env_decl], 0) :: (Itypedecl [clos_decl], 0) :: decls in
    (decls, main)

end
