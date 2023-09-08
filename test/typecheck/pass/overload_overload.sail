default Order dec

$include <prelude.sail>

val a : unit -> unit

val b : unit -> unit

overload c = {a, b}

val d : unit -> unit

overload e = {d, c}
