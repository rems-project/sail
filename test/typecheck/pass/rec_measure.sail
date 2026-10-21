default Order dec
$include <prelude.sail>

val f : nat -> nat
function {x => x} f(x) = if x == 0 then 0 else f(x - 1)
