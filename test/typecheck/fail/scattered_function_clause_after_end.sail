default Order dec

$include <prelude.sail>

val f : int -> int

scattered function f
function clause f(0) = 0
end f

function clause f(x) = x
