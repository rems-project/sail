default Order dec
$include <prelude.sail>

val f : forall 'n. int('n) -> int

function f(n) = {
  assert(constraint('n * 8 in {8, 16, 32}));
  n
}

