external add_int : int -> int -> int;
external sub_int : int -> int -> int;
external eq_int : int -> int -> bool;
external fail : unit -> unit;

type foo =
    [ Foo of bar | Lol ]
and bar = 
    [ Bar of foo ]
;

type list 'a =
  [ Cons of 'a * (list 'a)
  | Nil ]
;

type nat =
  [ S of nat
  | Z ]
;

type bintree =
  [ Node of bintree * nat * bintree
  | Leaf ]
;

value bound_to_fail = Foo (Bar Lol);

value natural = S (S (Z));

value map = fun f => fun l =>
    match l with
    [ Nil => Nil
    | Cons(x, tail) => Cons(f x, tail) ]
;

value list1 = (Cons (2, Nil));
value list2 = (Cons (bound_to_fail, Nil));

main = 
    (map (fun x => x) list1, map (fun x => x) list2)
