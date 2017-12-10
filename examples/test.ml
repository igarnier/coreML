builtin add_int : int -> int -> int;
builtin sub_int : int -> int -> int;
builtin eq_int : int -> int -> bool;

type list 'a =
  [ Cons : 'a * (list 'a)
  | Nil ]
;

type nat =
  [ S : nat
  | Z ]
;

type bintree =
  [ Node : bintree * nat * bintree
  | Leaf ]
;

type closure ('a, 'b, 'c) = 
    [ Closure : (((closure ('a, 'b, 'c))  * 'a) -> 'b) * 'c ]
;

value add =
 fix add x => fun y =>
  match x with
  [ Z => y
  | S x => S (add x y)]
;

value max =
 fix max x => fun y =>
   match (x, y) with
   [ (Z, _) => y
   | (_, Z) => x
   | (S x, S y) =>
       S (max x y) ]
;

value height =
 fix height tree =>
 match tree with
 [ Node(left, _, right) =>
    S (max (height left) (height right))
 | Leaf => Z ]
;

value test = fun x => add (S (S Z)) (S (S (S x)));

value sub =
 fix sub list =>
  match list with
  [ Nil => Nil
  | Cons(S (S x), tail) => Cons(S x, sub tail)
  | Cons(S x, tail) => Cons(x, sub tail)
  | Cons(Z, tail) => Cons(Z, sub tail) ]
;

value map =
 fix map f => fun list =>
    match list with
    [ Nil => Nil
    | Cons(elt, tail) => Cons(f elt, map f tail) ]
;

value pred =
 fun x =>
   match x with
   [ Z => Z
   | S x => x ]
;

main = 
    let l = sub (Cons(S (S (S Z)), (Cons(test Z, Nil)))) in
    let z = map pred l in
    let res = height (Node(Node(Leaf,Z,Node(Leaf,Z,Leaf)),Z,Leaf)) in
      (res, 3, z)

