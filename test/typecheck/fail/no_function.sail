default Order dec

$include <prelude.sail>

val foo_quux : unit -> unit

val foo_bar : unit -> unit

function test() -> unit = {
  let _ = foo_baz()
}
