external add_int : int -> int -> int;
external eq_int : int -> int -> bool;

type list 'a =
  [ Cons of 'a * (list 'a)
  | Nil ]
;

type nat =
  [ S of nat
  | Z ]
;

value not = fun x =>
  match x with
    [ True => False
    | False => True ];

value addf = (fix add x => fun y =>
  (match x with
  [ Z => y
  | S x => S (add x y)]));

value mulf = (fix mul x => fun y =>
    (match x with
     [ Z => Z
     | S x => addf (mul x y) y]));

value mapf = fix map f => fun l =>
  match l with
  [ Nil => Nil
  | Cons(elt, tail) => Cons(f elt, map f tail) ];

value three = S (S (S Z));

value list = Cons(three,Cons(S three, Cons(Z, Nil)));

main = mapf (fun x => mulf x three) list
