default Order dec
$include <prelude.sail>

val f : bits(128) -> int

function f(v[2..0] @ v[3]) = unsigned(v)
and f(_) = 0
