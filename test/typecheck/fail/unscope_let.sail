$option -dmagic_hash

$project# A {}

default Order dec

$include <prelude.sail>

$start_module# A

let foo : bits(32) = 0xFFFF_FFFF

$end_module# A

val bar : unit -> unit

function bar() = {
  let _ = foo;
  ()
}
