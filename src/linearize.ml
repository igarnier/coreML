open Ast

(* Linearization aims at unnesting let-defs. 
   It is a limited form of CPS transform. *)

let rec linearize fg expr k =
  let { expr_desc; uid } = expr in
  match expr_desc with
  | Eident { ident } -> 
    k fg (mkident ident)
  | Econstant const ->
    let fg, fresh = fresh fg "_" in
    mklet fresh expr (k fg (mkident fresh))
  | Elet { binder; bound; body } ->
    linearize fg bound (fun fg boundv ->
        mklet binder boundv (linearize fg body k)
      )
  | Efunction { arg; body } ->
    let body      = linearize fg body (fun _ x -> x) in
    let fg, fresh = fresh fg "_" in
    mklet fresh (mkfun arg body) (k fg (mkident fresh))
  | Efixpoint { fix; arg; body } ->
    let body      = linearize fg body (fun _ x -> x) in
    let fg, fresh = fresh fg "_" in
    mklet fresh (mkfix fix arg body) (k fg (mkident fresh))
  | Eapply { f; args } ->
    let fg, fresh = fresh fg "_" in
    linearize fg f (fun fg func_ident ->
        linearize_apply fg args [] (fun fg args ->
            let let_bound = mkexpr (Eapply { f = func_ident; args }) in
            mklet fresh let_bound (k fg (mkident fresh))))
  | Ematch { matched; matching } ->
    let fg, fresh = fresh fg "_" in
    let matching  = List.map (fun { rpatt; rexpr } ->
        { rpatt; rexpr = linearize fg rexpr (fun _ x -> x) }
      ) matching in
    linearize fg matched (fun fg x ->
        mklet fresh (mkmatch x matching) (k fg (mkident fresh))
      )
  | Etuple { exprs } ->
    let fg, fresh = fresh fg "_" in
    linearize_tuple fg exprs [] (fun fg fields ->
        mklet fresh (mktuple fields) (k fg (mkident fresh))
      )
  | Econstruct { cons; data = None } ->
    let fg, fresh = fresh fg "_" in
    mklet fresh expr (k fg (mkident fresh))  
  | Econstruct { cons; data = Some e } ->
    let fg, fresh = fresh fg "_" in
    linearize fg e (fun fg x ->
        mklet fresh (mkconstruct cons (Some x))
          (k fg (mkident fresh)))


and linearize_apply fg args acc k =
  match args with
  | [] ->
    k fg (List.rev acc)
  | a :: tl ->
    linearize fg a (fun fg a_ident ->
        linearize_apply fg tl (a_ident :: acc) k
      )

and linearize_tuple fg fields acc k =  
  match fields with
  | [] ->
    k fg (List.rev acc)
  | a :: tl ->
    linearize fg a (fun fg a_ident ->
        linearize_tuple fg tl (a_ident :: acc) k
      )

let perform_linearization { program_decls; main } fg =
  { program_decls; 
    main = linearize fg main (fun _ x -> x) }
