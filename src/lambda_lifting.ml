(* lambda-lifting *)

open Ast

let is_lambda { expr_desc } =
  match expr_desc with
  | Efunction _
  | Efixpoint _ -> true
  | _ -> false

type context =
  | UnderLambda
  | LetBound
  | Unprotected

(* [name] transforms an Ast in a type and semantic-preserving way,
   ensuring that all "lambdas" (i.e. functions and fixpoints) are let-bound,
   i.e. explicitly named. *)
let rec name fg context { expr_desc; uid } =
  let expr_desc, fg =
    match expr_desc with
      | Eident _
      | Econstant _
      | Econstruct { data = None } ->
        expr_desc, fg
      | Elet { binder; bound; body } ->
        let bound, fg = name fg LetBound bound in
        let body, fg  = name fg Unprotected body in
        Elet { binder; bound; body }, fg
      | Efunction { arg; body } ->
        let body, fg = name fg UnderLambda body in
        (match context with
         | UnderLambda | LetBound ->
           Efunction { arg; body }, fg
         | Unprotected ->
           let fg, id = Fresh.next fg in
           let fv     = Fresh.var id in
           let result = mklet fv (mkfun arg body) (mkident fv) in
           result.expr_desc, fg)
      | Efixpoint { fix; arg; body } ->
        let body, freshgen = name fg UnderLambda body in
        (match context with
         | UnderLambda | LetBound ->
           Efixpoint { fix; arg; body }, fg
         | Unprotected ->
           let fg, id = Fresh.next fg in
           let fv     = Fresh.var id in
           let result = mklet fv (mkfix fix arg body) (mkident fv) in
           result.expr_desc, fg)
      | Eapply { f; args } ->
        let f, fg    = name fg Unprotected f in
        let args, fg = name_list fg args in
        Eapply { f; args }, fg
      | Ematch { matched; matching } ->
        let matched, fg  = name fg Unprotected matched in
        let matching, fg = name_matching fg matching in
        Ematch { matched; matching }, fg
      | Etuple { exprs } ->
        let exprs, fg = name_list fg exprs in
        Etuple { exprs }, fg
      | Econstruct { cons; data = Some e } ->
        let e, fg = name fg Unprotected e in
        Econstruct { cons; data = Some e}, fg
  in
  { expr_desc; uid }, fg

and name_list fg exprs =
  List.fold_right (fun expr (exprs, fg) ->
      let expr, fg = name fg Unprotected expr in
      (expr :: exprs, fg)
    ) exprs ([], fg)

and name_matching fg matching =
  List.fold_right 
    (fun { rpatt; rexpr } (matching, fg) ->
       let rexpr, fg = name fg Unprotected rexpr in
       ({ rpatt; rexpr } :: matching, fg)
    ) matching ([], fg)


(* [box_expr with_lambdas expr [v_1;...;v_n]] = fun v_1 => fun v_2 => ... fun v_n => expr *)
let rec box_expr_with_lambdas expr variables =
  match variables with
  | [] ->
    expr
  | x :: l ->
    let res = box_expr_with_lambdas expr l in
    mkfun x res

(* [apply_free_variables expr [v_1;...;v_n]] = expr v_1 v_2 ... v_n *)
let rec apply_free_variables expr variables =
  match variables with
  | [] ->
    expr
  | x :: l ->
    apply_free_variables (mkapp expr (mkident x)) l

let rec lift { expr_desc; uid } acc =
  let expr_desc, lifted = match expr_desc with
    | Eident _
    | Econstant _
    | Econstruct { data = None } ->
      expr_desc, acc
    | Elet { binder; bound; body } ->
      let bound, lifted = lift bound acc in
      let body, lifted  = lift body lifted in
      if is_lambda bound then
        (* upon encountering a lambda bound to a binder:
           (let binder = fun x_1, ..., x_n => foo in body)
           1. extract the free variables fv1,...,fvn of the lambda
           2. add lambdas to bind them, yielding a lambda
              fun fv_1 ... fv_n ... x_1 ... x_n => foo
           3. replace all calls to [binder] by [binder fv_1 ... fv_n].
           4. add the pair (binder, fun fv_1 ... fv_n x_1 ... x_n => foo) to the
              list of lifted lambdas.
        *)
         let fvs = List.map fst (free_variables bound) in
         let combinator = box_expr_with_lambdas bound fvs in
         let call_point = apply_free_variables (mkident binder) fvs in
         let body       = subst binder call_point.expr_desc body in
         let lifted     = (binder, combinator) :: lifted in
         body.expr_desc, lifted
      else
        Elet { binder; bound; body }, lifted
    | Efunction { arg; body } ->
      let body, lifted = lift body acc in
      Efunction { arg; body }, lifted
    | Efixpoint { fix; arg; body } ->
      let body, lifted = lift body acc in
      Efixpoint { fix; arg; body }, lifted
    | Eapply { f; args } ->
      let f, lifted    = lift f acc in
      let args, lifted = List.fold_right (fun arg (args, lifted) ->
          let arg, lifted = lift arg lifted in
          (arg :: args, lifted)
        ) args ([], lifted) in
      Eapply { f; args }, lifted
    | Ematch { matched; matching } ->
      let matched, lifted  = lift matched acc in
      let matching, lifted = List.fold_right
          (fun { rpatt; rexpr } (matching, lifted) ->
             let rexpr, lifted = lift rexpr lifted in
             ({ rpatt; rexpr } :: matching, lifted)
          ) matching ([], lifted) in
      Ematch { matched; matching }, lifted
    | Etuple { exprs } ->
      let exprs, lifted = List.fold_right
          (fun field (fields, lifted) ->
             let field, lifted = lift field lifted in
             (field :: fields, lifted)
          ) exprs ([], acc) in
      Etuple { exprs }, lifted
    | Econstruct { cons; data = Some e } ->
      let e, lifted = lift e acc in
      Econstruct { cons; data = Some e }, lifted
  in
  { expr_desc; uid }, lifted

let lambda_lift { program_decls; main } freshgen =
  let named, freshgen = name freshgen Unprotected main in 
  let main, lifted = lift named [] in
  let main = List.fold_left (fun expr (binder, combinator) ->
      mklet binder combinator expr
    ) main lifted in
  freshgen, { program_decls; main }
