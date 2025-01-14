default Order dec
$include <prelude.sail>

val f : forall 'n, 'n > 0. (implicit('n), vector('n, int)) -> unit
val g : forall 'n, 'n > 0. vector('n, int) -> unit

function g(bv) = f(bv)
