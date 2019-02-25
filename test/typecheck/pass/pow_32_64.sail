default Order dec

$include <prelude.sail>

$option -smt_linearize

val bar : forall 'n, 'n <= 2 ^ 64 - 1. int('n) -> unit

val foo : forall 'n, 'n in {32, 64}. bits('n) -> unit

function foo(xs) = {
  let x = unsigned(xs);
  bar(x)
}
