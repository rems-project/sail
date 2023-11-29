$option -dmagic_hash

$project# A {}

default Order dec

$include <prelude.sail>

$start_module# A

register foo : bits(32)

$end_module# A

val bar : unit -> unit

function bar() = {
  let _ = foo;
  ()
}
