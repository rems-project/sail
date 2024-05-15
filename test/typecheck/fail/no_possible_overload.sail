default Order dec

$include <prelude.sail>

val f : (int, int, int) -> unit
val g : (int, int, string) -> unit

overload h = {f, g}

val main : unit -> unit

function main() = h(1, 2)
