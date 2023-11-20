$option -dmagic_hash

default Order dec

$include <prelude.sail>

type foo = bits(32)

$unscope# type foo

val bar : unit -> unit

function bar() = {
  let _ : foo = 0xFFFF_FFFF;
  ()
}
