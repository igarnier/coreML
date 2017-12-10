let print_list sep pr_el l =
  let rec pr_aux l =
    match l with
      | [] -> ""
      | x :: l ->
	  sep^(pr_el x)^(pr_aux l)
  in match l with
    | [] -> ""
    | [ x ] -> pr_el x
    | x :: l ->
	(pr_el x) ^ (pr_aux l)

(* fresh name generator *)
let gensym =
  let id = ref (-1) in
    function () ->
      incr id;
      "a"^(string_of_int !id)




module FreshGen =
struct

  type 'var acc = {
    succ : 'var -> 'var;
    generated : 'var list;
    current : 'var
  }
      
  let initial zero succ = {
    succ      = succ;
    generated = [];
    current   = zero
  }
      
  let fresh : 'var acc -> 'var acc * 'var =
    fun acc ->
      let v = acc.current in
      { acc with
	  generated = v :: acc.generated;
	  current = acc.succ acc.current }, v

  let variables acc = acc.generated
    
end

let serr s = Printf.eprintf "%s\n%!" s

let index_list l =
  let rec aux l idx = 
    match l with
      | [] -> []
      | x :: l -> (x, idx) :: (aux l (idx+1))
  in
    aux l 0

let foldi_left acc a f =
  let rec loop acc i =
    if i = Array.length a then
      acc
    else
      loop (f i acc a.(i)) (i + 1)
  in
    loop acc 0

(* Assuming that the argument is a sorted list, [check_uniqueness] returns
   true if each element appears only once. The [eq] parameter is
   a user-defined equality. *)
let rec check_uniqueness eq = function
  | []
  | [ _ ] -> true
  | x :: (y :: l as tl) ->
      if eq x y then
	false
      else
	(check_uniqueness eq tl)

let rec check_equality eq = function
  | []
  | [ _ ] -> true
  | x :: y :: l ->
      if eq x y then
	check_equality eq (y :: l)
      else
	false

let abort () = failwith "aborted."

let is_some =
  function
    | Some _ -> true
    | _ -> false

let no_some =
  function
    | Some x -> x
    | _ -> failwith "Utils.no_some : argument is None" 

let opt_app f =
  function
    | None -> None
    | Some x -> Some (f x)

let opt_lift f =
  function
    | None -> None
    | Some x -> Some (f x)

let opt_map = opt_lift

let proj_1 : 'a * 'b * 'c -> 'a =
  fun (a, _, _) -> a

let proj_2 : 'a * 'b * 'c -> 'b =
  fun (_, b, _) -> b

let proj_3 : 'a * 'b * 'c -> 'c =
  fun (_, _, c) -> c

let apply_1 f (a, b, c) = (f a, b, c)

let apply_2 f (a, b, c) = (a, f b, c)

let apply_3 f (a, b, c) = (a, b, f c)

let (++) b a = fun x -> a (b x)

let time_it prefix label f =
  Printf.eprintf "%sPerforming %s ... %!" prefix label;
  let t = Sys.time () in
  let r = f () in
  Printf.eprintf "Completed in %f seconds.\n%!" ((Sys.time ()) -. t);
  r

let gather f l =
  List.fold_left (fun acc elt ->
    List.rev_append acc (f elt)
  ) [] l

let rec filter_duplicates' cmp = function
  | [] -> []
  | [ x ] -> [ x ]
  | x :: y :: l ->
      if cmp x y then
	filter_duplicates' cmp (y :: l)
      else
	x :: (filter_duplicates' cmp (y :: l))
	  
let refine l map compare =
  let l = List.map map l in
  let sorted = List.sort compare l in
    filter_duplicates' (fun x y -> compare x y = 0) sorted

let slice f l = 
  let rec aux last acc = function
    | [] -> [acc]
    | x :: l ->
	if f x last then
	  aux x (x :: acc) l
	else
	  acc :: (aux x [x] l)
  in
    match l with
      | [] -> []
      | x :: l ->
	  aux x [x] l

let foldl = List.fold_left

let foldr = List.fold_right

let fksort : int -> ('a -> int) -> 'a list -> 'a list =
  (* keys are in [0; bound[ *)
  fun bound clfun l ->
    let buckets = Array.create bound [] in
    let rec shovel l =
      match l with
	| [] -> ()
	| x :: l ->
	    let key = clfun x in
	      buckets.(key) <- x :: buckets.(key)
    in
      shovel l;
      (Array.to_list ++ List.flatten) buckets

let classify : ('a -> 'a -> bool) -> 'a list -> 'a list list =
  fun eq l ->
    let rec classify l =
      match l with
	| [] -> []
	| repr :: elements ->
	    let equiv, not_equiv = 
	      foldl (fun (equiv_elts, not_equiv_elts) elt ->
		if eq elt repr then
		  (elt :: equiv_elts, not_equiv_elts)
		else
		  (equiv_elts, elt :: not_equiv_elts)
	      ) ([repr],[]) elements
	    in
	      equiv :: (classify not_equiv)
    in classify l

let topsort pr l =
  try 
    Some (List.sort (fun x y ->
      let a = pr x y in
      let b = pr y x in
	if a && b || (not (a || b)) then
	  raise (Failure "")
	else if a then
	  -1
	else
	  1
    ) l)
  with
    | (Failure _) -> None

let rec filter_duplicates eq =
  function
    | [] -> []
    | x :: l ->
	x :: (filter_duplicates eq (List.filter (fun y -> not (eq x y)) l))
