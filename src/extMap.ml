module type OrderedType =
  sig

    type t
    val compare : t -> t -> int

  end


module Make(I : OrderedType) =
  struct

    include Map.Make(I)
      
    let search neutral key map =
      try find key map with
	| Not_found -> neutral

    let domain map = 
      fold (fun domain _ res ->
	match res with
	  | [] -> [ domain ]
	  | dom :: _ ->
	      if dom = domain then
		res
	      else
		domain :: res
      ) map []

    let codomain map = 
      fold (fun _ codomain res ->
	codomain :: res
      ) map []
	
    let merge map1 map2 =
      fold (fun domain codomain map ->
	add domain codomain map
      ) map1 map2

    let fusion op map1 map2 =
      fold (fun domain codomain map ->
	if mem domain map then
	  add domain (op (find domain map) codomain) map
	else
	  add domain codomain map
      ) map1 map2

    let find_opt key map =
      try Some (find key map) with
	| Not_found -> None

  end
