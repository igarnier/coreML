open Printf

(* First order term, polymorphic w.r.t. its constructor. *) 
type ('cons, 'var) t =
    | TermVar of 'var
    | TermCons of 'cons * ((('cons, 'var) t) list)

(* Maps a function over a first order term.
 * Useful e.g. to instantiate variables. *)
let rec term_lift labelfunc varfunc = function
  | TermVar x ->
      varfunc x
  | TermCons(dc, ts) ->
      TermCons(labelfunc dc, List.map (term_lift labelfunc varfunc) ts)

let label_of_term =
  function
    | TermCons(l, _) -> l
    | TermVar v ->
	failwith (sprintf "Terms.label_of_term : term is a variable = %d." v)

let rec term_subst var arg term =
  match term with
    | TermVar var' ->
	if var' = var then
	  arg
	else
	  term
    | TermCons(constr, subterms) ->
	TermCons(constr, List.map (term_subst var arg) subterms)

let rec remap_term cons_renaming var_renaming typ =
  match typ with
    | TermVar var -> 
	TermVar (var_renaming var)
    | TermCons(cons, domain) ->
	TermCons(cons_renaming cons,
	         List.map (remap_term cons_renaming var_renaming) domain)

let string_of_term pv pl t =
  let rec print = function
    | TermVar v ->
        sprintf "%s" (pv v)
    | TermCons(cstr, []) ->
        sprintf "%s" (pl cstr)
    | TermCons(cstr, [t1]) ->
        sprintf "%a %s" (fun _ -> print) t1 (pl cstr)
    | TermCons(cstr, t1 :: tl) ->
        ((sprintf "(%a" (fun _ -> print) t1)^
            (List.fold_left (fun s t -> s^(sprintf ", %a" (fun _ -> print) t)) "" tl)^
           sprintf ") %s" (pl cstr))
	  
  in print t

