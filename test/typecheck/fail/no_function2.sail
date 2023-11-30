default Order dec

$include <prelude.sail>

val foo_quux : unit -> unit

function test() -> unit = {
  let _ = foo_baz()
}
