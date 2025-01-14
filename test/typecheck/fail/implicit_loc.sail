default Order dec
$include <prelude.sail>

struct foo('n) = {
  field : bits('n)
}

val f : forall 'n, 'n > 0. (implicit('n), foo('n)) -> unit
val g : forall 'n, 'n > 0. foo('n) -> unit

function g(x) = f(x)
