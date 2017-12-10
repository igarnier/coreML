# coreML
A small core ML implementation in OCaml.

The language is CBV and pure. This is a cleanup of an old compiler project of mine, dating from my master's year in Paris.

Compiler passes (in no particular order):
. parsing (using menhir)
. alpha-conversion
. polymorphic type inference
. pattern matching compilation (in the process of being cleaned up)
. lambda lifting
. a simple big-step evaluator

Being refreshed:
. monomorphisation
. data-type specialization
. closure conversion - due to the lack of
  existential types, function application
  turns into dynamic dispatch, we plan to
  alleviate this through some static analysis.

TODO:
. I'd like this small project to serve as a testbed to
  some ideas on probabilistic programming. We'll see.
. Constant folding
. (look at the no-brainer CPS conversion, maybe)
. compiling to some VM?