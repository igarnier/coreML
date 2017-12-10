
(* ASTs in locally nameless notation. This representation
   allows to avoid variable capture while doing
   substitutions. *)

open Batteries
open Printf

open Ast
open Utils


type level = int
type arity = int

type dexpr =
  | DBident     of { level : level }
  | DBfree      of { free_var : string }
  | DBconstant  of { constant : constant }
  | DBlet       of { bound : dexpr; body : dexpr }
  | DBfunction  of { body : dexpr }
  | DBfixpoint  of { body : dexpr }
  | DBapply     of { f : dexpr; args : dexpr list }
  | DBmatch     of { matched : dexpr; matching : dmatching }
  | DBtuple     of { exprs : dexpr list }
  | DBconstruct of { cons : datacons; data : dexpr option }

(* We re-use the same patterns, just ignoring the variables
   when evaluating. *)
and dmatching = (pattern * dexpr) list

(* Convert from parsed tree to locally nameless representation *)
let rec from_expr vars { expr_desc } =
  match expr_desc with
  | Eident { ident } ->
    (match List.index_of ident vars with
     | None   -> DBfree { free_var = ident }
     | Some i -> DBident { level = i })
  | Econstant { constant } ->
    DBconstant { constant }
  | Elet { binder; bound; body } ->
    DBlet { bound = from_expr vars bound;
	    body  = from_expr (binder :: vars) body }
  | Efunction { arg; body } ->
    DBfunction { body = from_expr (arg :: vars) body }
  | Efixpoint { fix; arg; body } ->
    (* note that arg shadows fix, in case one does fix x x -> x ... *)
    DBfixpoint { body = from_expr (arg :: fix :: vars) body }
  | Eapply { f; args } ->
    DBapply { f    = from_expr vars f;
	      args = List.map (from_expr vars) args }
  | Ematch { matched; matching } ->
    let matching = from_matching vars matching in
    let matched  = from_expr vars matched in
    DBmatch { matched; matching }
  | Etuple { exprs } ->
    let exprs = List.map (from_expr vars) exprs in
    DBtuple { exprs }
  | Econstruct { cons; data = None } ->
    DBconstruct { cons; data = None }
  | Econstruct { cons; data = Some e } ->
    DBconstruct { cons; data = Some (from_expr vars e ) }

and from_matching vars matching =
  List.map (fun { rpatt; rexpr } ->
      (* /!\ Warning : the indexing is done according to
         the tree run of variables_of_pattern; that is
         depth-first, left-to-right. Cf [Ast] module. *)
      let pattvars = variables_of_pattern rpatt in
      (rpatt, from_expr (pattvars @ vars) rexpr)
    ) matching

(* [is_instance_of] is used to naively evaluate pattern matchings. 
   The result of a successful match is an environment enriched
   by the new bindings corresponding to the values obtained by
   destructuring [matched].
*)
let rec is_instance_of env matched { patt_desc } =
  match matched, patt_desc with
  | _, Pany   -> Some env
  | _, Pvar _ -> Some (matched :: env)
  | DBconstant { constant = c }, Pconst c' ->
    if c = c' then
      Some env
    else
      None
  | DBtuple { exprs }, Ptuple patts ->
    (* We assume that the program is well-typed. No need to
       check arity. *)
    let l = List.combine exprs patts in
    List.fold_left (fun env (field, patt) ->
	match env with
	| None     -> None
	| Some env ->
	  is_instance_of env field patt
      ) (Some env) l
  | DBconstruct { cons; data = None }, Pconstruct(cons', None) ->
    if cons = cons' then
      Some env
    else
      None
  | DBconstruct { cons; data = Some e }, Pconstruct(cons', Some e') ->
    if cons = cons' then
      is_instance_of env e e'
    else
      None
  | _ -> None

(* Printing locally nameless terms, for debugging. *)
let rec print e =
  match e with
  | DBident { level } ->
    Printf.sprintf "[%d]" level
  | DBfree { free_var } ->
    Printf.sprintf "<%s>" (Ast.printable free_var)
  | DBconstant { constant } ->
    (match constant with
     | CInt i ->
       string_of_int i
     | CChar c ->
       String.make 1 c
     | CFloat f ->
       string_of_float f)
  | DBlet { bound; body } ->
    Printf.sprintf "let = %s in\n%s" (print bound) (print body)
  | DBfunction { body } ->
    Printf.sprintf "(fun -> %s)" (print body)
  | DBfixpoint { body } ->
    Printf.sprintf "(fix -> %s)" (print body)
  | DBconstruct { cons; data = None } ->
    Ast.printable cons
  | DBconstruct { cons; data = Some e } ->
    Printf.sprintf "(%s(%s))" (Ast.printable cons) (print e)
  | DBapply { f; args } ->
    let f   = print f in
    let app = List.fold_left (fun acc arg -> "("^acc^(print arg)^")") f args in
    app
  | DBtuple { exprs } ->
    let args = Utils.print_list "," print exprs in
    "("^args^")"
  | DBmatch { matched; matching } ->
    let e = print matched in
    let m = print_matching matching in
    sprintf "match %s with [ %s ]" e m

and print_matching m =
  print_list "\n|" (fun (patt, e) ->
    sprintf "%s => %s" (Ast.print_pattern patt) (print e)
  ) m

let rec subst x i e = (* [x/[i]]e, assuming x is locally closed *)
  match e with
  | DBident { level } ->
    if i = level
    then x
    else e
  | DBfree _
  | DBconstant _
  | DBconstruct { data = None } -> e
  | DBfunction { body } ->
    DBfunction { body = subst x (i+1) body }
  | DBfixpoint { body } ->
    DBfixpoint { body = subst x (i+2) body }
  | DBconstruct { cons; data = Some e } ->
    DBconstruct { cons; data = Some (subst x i e ) }
  | DBlet { bound; body } ->
    DBlet { bound = subst x i bound;
            body  = subst x (i+1) body }
  | DBapply { f; args } ->
    DBapply { f    = subst x i f;
              args = List.map (subst x i) args }
  | DBmatch { matched; matching } ->
    DBmatch { matched  = subst x i matched;
	      matching = subst_matching x i matching }
  | DBtuple { exprs } ->
    DBtuple { exprs = List.map (subst x i) exprs }

and subst_matching x i matching =
  List.map (fun (pattern, action) ->
      let vars = Ast.variables_of_pattern pattern in
      let len  = List.length vars in
      (pattern, subst x (i+len) action)
    ) matching


(* big-step call-by-value reduction for De-Bruijn terms. *)
let rec eval expr =
  match expr with
  | DBident _ ->
    failwith "dangling de Bruijn variable found"
  | DBfree _
  | DBconstant _
  | DBfunction _
  | DBfixpoint _
  | DBconstruct { data = None } ->
    expr
  | DBlet { bound; body } ->
    let bound = eval bound in
    let body  = subst bound 0 body in
    eval body
  | DBapply { f; args } ->
    let args = List.map eval args in
    eval_app f args
  | DBmatch { matched; matching } ->
    eval_match matched matching
  | DBtuple { exprs } ->
    DBtuple { exprs = List.map eval exprs }
  | DBconstruct { cons; data = Some e } ->
    DBconstruct { cons; data = Some (eval e) }

and eval_app func args =
  match args with
  | [] ->
    eval func
  | x :: l ->
    let nf = eval func in
    (match nf with
     | DBfunction { body } ->
       let body = subst x 0 body in
       eval_app body l
     | DBfixpoint { body } ->
       let body = subst nf 1 body in
       let body = subst x 0 body in
       eval_app body l
     | _ ->
       let term = print (DBapply { f = func; args }) in
       failwith (sprintf "runtime error in eval_app with %s" term)
    )

and eval_match matched matching =
  let matched = eval matched in
  let rec do_match cases =
    match cases with
    | [] ->
      failwith "failed matching"
    | (pattern, action) :: l ->
      (match is_instance_of [] matched pattern with
       | None ->
	 do_match l
       | Some env ->
	 let (result, _) = List.fold_left (fun (expr, lvl) elt ->
	     (subst elt lvl expr, lvl+1)
	   ) (action, 0) env in
	 eval result
      )
  in
  do_match matching


(* let f =  *)
(*   mkfun "x" (mkconstruct "Test" (Some (mkconstruct "Foo" (Some (mkident "x"))))) *)

(* let f = mkfun "x" (mkapp (mkident "x") (mkident "x")) *)

(* let omega = mkapp f f *)

(* let test = mkapp f (mkconst (CInt 3)) *)

(*  let _ = *)
(*    let e = (from_expr [] omega) in *)
(*    let _ = print_string (print e) in *)
(*    let s = print (eval [] e) in *)
(*      print_string s *)

