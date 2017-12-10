type list 'a =
  [ Cons of 'a * (list 'a)
  | Nil ]
;

main =
  let x = Cons(0, Cons(1, Cons(2, Nil))) in
  match x with
  [ Nil          => 0
  | Cons(x, Nil) => x
  | _            => 1
  ]
