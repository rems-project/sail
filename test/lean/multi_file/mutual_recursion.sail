default Order dec
$include <prelude.sail>

val f : nat -> bool
val g : nat -> bool

termination_measure f(n) = n
termination_measure g(n) = n

function f(n) = if n > 0 then g(n - 1) else true
function g(n) = if n > 0 then f(n - 1) else false
