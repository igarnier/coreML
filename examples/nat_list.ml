type nat =
[ Z
| S of nat ];

type list = 
[ Nil
| Cons of (nat * list)];

main =
let map = 
  (fix map f => 
      (fun l =>
	  match l with 
	  [ Nil => Nil
	  | Cons (elt, tail) => 
	      (Cons (f elt, map f tail)) ]))
in
let three =
  (S (S (S Z))) 
in
let list = 
  (Cons (three,(Cons (S three,(Cons (Z,Nil)))))) 
in
(map (fun x => x) list)
