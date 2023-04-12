default Order dec

$include <prelude.sail>

val f : forall 'n, 'n in {8,16}. (int('n), bits('n)) -> int

function f(8, _) = 1
and f(16, _) = 2