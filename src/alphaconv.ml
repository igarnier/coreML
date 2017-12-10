(* Alpha-conversion *)

(* This module performs an alpha-conversion pass of Ast.t. 
   We freshly rename all binders and data constructors. *)

open Printf

open Ast
open Utils

(* The module Env maps old identifiers to fresh ones.
   We distinguish variables, data constructors, type names and type variables. *)

module Smap = Map.Make(String)

type map = string Smap.t

type renaming = {
  idents : map; (* variables *)
  cons   : map; (* algebraic data types *)
  tnames : map; (* typenames *)
  tvars  : map; (* type variables *)
}

let lookup_idents env x =
  try Smap.find x env.idents with
  | Not_found ->
    failwith (sprintf "lookup_idents: %s not found" x)

let lookup_cons env x =
  try Smap.find x env.cons with
  | Not_found ->
    failwith (sprintf "lookup_cons: %s not found" x)

let lookup_tnames env x =
  try Smap.find x env.tnames with
  | Not_found ->
    failwith (sprintf "lookup_tnames: %s not found" x)

let lookup_tvars env x =
  try Smap.find x env.tvars with
  | Not_found ->
    failwith (sprintf "lookup_tvars: %s not found" x)

type mapping =
    Var  of { old : string; fresh : string }
  | Cons of { old : string; fresh : string }
  | Type of { old : string; fresh : string }
  | Tvar of { old : string; fresh : string }

let add_mapping ({ idents; cons; tnames; tvars } as env) mapping =
  match mapping with
  | Var  { old; fresh } ->
    { env with idents = Smap.add old fresh idents }
  | Cons { old; fresh } ->
    { env with cons = Smap.add old fresh cons }
  | Type { old; fresh } ->
    { env with cons = Smap.add old fresh tnames }
  | Tvar { old; fresh } ->
    { env with tvars = Smap.add old fresh tnames }

let initial = {
  idents = Smap.empty;
  cons   = Smap.empty;
  tnames = Smap.empty;
  tvars  = Smap.empty;
}

(* Updates a core type using the mapping given by the environment *)
let update_core_type env typ =
  remap_core_type (lookup_tnames env) (lookup_tvars env) typ

let rec alpha_convert_structure_item env fg { item_desc; uid } =
  let env, fg, item_desc = 
    match item_desc with
    | Iexternal _ ->      
      env, fg, item_desc
    | Itypedecl decls ->
      let env, fg, decls = alpha_convert_typedecl env fg decls in
      env, fg, (Itypedecl decls)
  in
  env, fg, { item_desc; uid }

and alpha_convert_pattern env fg { patt_desc; uid } =
  let env, fg, patt_desc =
    match patt_desc with
    | Pany
    | Pconst _ ->
      env, fg, patt_desc
    | Pvar v ->
      let fg, v' = fresh fg v in
      let env    = add_mapping env (Var { old = v; fresh = v' }) in
      env, fg, (Pvar v')
    | Ptuple patterns ->
      let env, fg, patterns = 
        List.fold_right 
          (fun patt (env, fg, patterns) ->
             let e, fg, p = alpha_convert_pattern env fg patt in
             (e, fg, p :: patterns)
          ) patterns (env, fg, [])
      in
      env, fg, (Ptuple patterns)
    | Pconstruct(cons, None) ->
      let cons' = lookup_cons env cons in
      (* let cons' = match lookup_cons env cons with *)
      (*   | None -> cons *)
      (*   | Some x -> x *)
      (* in *)
      env, fg, (Pconstruct(cons', None))
    | Pconstruct(cons, Some patt) ->
      let cons' = lookup_cons env cons in
      (* let cons' = match lookup_cons env cons with *)
      (*   | None -> cons *)
      (*   | Some x -> x *)
      (* in *)
      let env, fg, patt = alpha_convert_pattern env fg patt in
      env, fg, Pconstruct(cons', Some patt)
  in
  env, fg, { patt_desc; uid }

and alpha_convert_matching env fg bindings =
  match bindings with
  | [] -> env, fg, []
  | { rpatt; rexpr } :: l ->
    let fg, binding =
      let env', fg, rpatt = 
        alpha_convert_pattern env fg rpatt in
      let fg, rexpr = 
        alpha_convert_expression env' fg rexpr 
      in
      fg, { rpatt; rexpr }
    in 
    let env, fg, bindings = 
      alpha_convert_matching env fg l 
    in
    env, fg, (binding :: bindings)

and alpha_convert_expression env fg { expr_desc; uid } =
  let fg, expr_desc = 
    match expr_desc with
    | Eident { ident } ->
      let ident' = lookup_idents env ident in
      fg, (Eident { ident = ident' })
    | Elet { binder; bound; body } ->
      let fg, bound   = alpha_convert_expression env fg bound in
      let fg, binder' = fresh fg binder in 
      let env         = add_mapping env (Var { old = binder; fresh = binder' }) in
      let fg, body    = alpha_convert_expression env fg body in
      fg, (Elet { binder = binder'; bound; body })
    | Efunction { arg; body } ->
      let fg, arg' = fresh fg arg in
      let env      = add_mapping env (Var { old = arg; fresh = arg' }) in
      let fg, body = alpha_convert_expression env fg body in
      fg, (Efunction { arg = arg'; body })
    | Efixpoint { fix; arg; body } ->
      let fg, fix' = fresh fg fix in
      let fg, arg' = fresh fg arg in
      let env      = add_mapping env (Var { old = fix; fresh = fix' }) in
      let env      = add_mapping env (Var { old = arg; fresh = arg' }) in
      let fg, body = alpha_convert_expression env fg body in
      fg, (Efixpoint { fix = fix'; arg = arg'; body })
    | Eapply { f; args } ->
      let fg, args = List.fold_right 
          (fun arg (fg, args) ->
             let fg, arg = 
               alpha_convert_expression env fg arg
             in
             (fg, arg :: args)
          ) args (fg, []) in
      let fg, f =
        alpha_convert_expression env fg f
      in
      fg, (Eapply { f; args })
    | Ematch { matched; matching } ->
      let fg, matched =
        alpha_convert_expression env fg matched
      in
      let _, fg, matching = 
        alpha_convert_matching env fg matching
      in
      fg, (Ematch { matched; matching })
    | Etuple { exprs } ->
      let fg, exprs = List.fold_right 
          (fun field (fg, fields) ->
             let fg, field = 
               alpha_convert_expression env fg field
             in
             (fg, field :: fields)
          ) exprs (fg, []) in
      fg, (Etuple { exprs })
    | Econstruct { cons; data = None } ->
      let cons = lookup_cons env cons in
      (* let cons = match lookup_cons env cons with *)
      (*   | None -> cons *)
      (*   | Some x -> x *)
      (* in *)
      fg, (Econstruct { cons; data = None })
    | Econstruct { cons; data = Some e } ->
      let cons = lookup_cons env cons in
      (* let cons = match lookup_cons env cons with *)
      (*   | None   -> cons *)
      (*   | Some x -> x *)
      (* in *)
      let fg, e =
        alpha_convert_expression env fg e
      in
      fg, (Econstruct { cons; data = Some e })
    | Econstant _ ->
      fg, expr_desc
  in
  fg, { expr_desc; uid }

and alpha_convert_typedecl env fg mutual_decls =

  (* construct a mapping from old typenames to fresh ones. *)
  let env, fg = List.fold_left (fun (env, fg) decl ->
      match decl.tdecl_kind with
      | SumType _ ->
        let fg, typename' = fresh fg decl.tdecl_name in
        let env = add_mapping env (Type { old = decl.tdecl_name; fresh = typename' }) in
        (env, fg)
      | Builtin ->
        (env, fg)
    ) (env, fg) mutual_decls in

  (* perform substitution *)
  let rec loop env fg mutual_decls =
    match mutual_decls with
    | [] -> env, fg, []
    | decl :: l ->
      let env, fg, kind = 
        match decl.tdecl_kind with
        | SumType inductive_def ->
          let env, fg, datacons = 
            convert_inductive_def env fg inductive_def 
          in
          env, fg, (SumType datacons)
        | Builtin ->
          env, fg, Builtin
      in
      let env, fg, decls = loop env fg l in
      let typename = lookup_tnames env decl.tdecl_name in
      (*   match lookup_tnames env decl.tdecl_name with *)
      (*   | None -> failwith "alpha_convert_typedecl: substitute typename not found." *)
      (*   | Some typename -> typename *)
      (* in *)
      let decl = {
        tdecl_name = typename;
        tdecl_kind = kind
      } in
      env, fg, (decl :: decls)
  in
  loop env fg mutual_decls

and convert_inductive_def env fg inductive_def =
  match inductive_def with
  | IndAbs { ind_type_var; ind_type } ->
    let fg, tvar'      = fresh fg ind_type_var in
    let env            = add_mapping env (Tvar { old = ind_type_var; fresh = tvar' }) in
    let env, fg, body  = convert_inductive_def env fg ind_type in
    env, fg, (IndAbs { ind_type_var = tvar'; ind_type })
  | IndIntros { ind_intros } ->
    let env, fg, ind_intros = convert_inductive_constructors env fg ind_intros in
    env, fg, (IndIntros { ind_intros })

and convert_inductive_constructors env fg constructors =
  match constructors with
  | [] -> env, fg, []
  | (cons, domain) :: l ->
    let domain    = Batteries.Option.map (update_core_type env) domain in
    let fg, cons' = fresh fg cons in
    let env       = add_mapping env (Cons { old = cons; fresh = cons' }) in
    let env, fg, constructors = convert_inductive_constructors env fg l in
    env, fg, ((cons', domain) :: constructors)

let alpha_convert_program env fg { program_decls; main } =
  let env, fg, program_decls = 
    List.fold_left (fun (env, fg, decls) decl ->
        let env, fg, decl = alpha_convert_structure_item env fg decl in
        (env, fg, decl :: decls)
      ) (env, fg, []) program_decls
  in
  let fg, main = alpha_convert_expression env fg main in
  (env, fg, { program_decls; main })

let alpha_conversion fg program =
  let _, fg, program = alpha_convert_program initial fg program in
  fg, program
