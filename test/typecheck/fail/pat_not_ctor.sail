default Order dec
$include <prelude.sail>

val g : int -> int
function f(x : int) -> unit = match x { g(y) => () }
