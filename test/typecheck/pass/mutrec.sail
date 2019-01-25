$include <prelude.sail>

val f : list(int) -> int
val g : list(int) -> int

function f([| |]) = 0
and f(h::t) = h + g(t)
function g([||]) = 0
and g(h::t) = f(t) - h

val test : unit -> int
function test() = f([|1,2,3|])
