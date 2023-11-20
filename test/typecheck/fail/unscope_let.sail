$option -dmagic_hash

default Order dec

$include <prelude.sail>

let foo : bits(32) = 0xFFFF_FFFF

$unscope# let foo

val bar : unit -> unit

function bar() = {
  let _ = foo;
  ()
}
