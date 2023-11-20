$option -dmagic_hash

default Order dec

$include <prelude.sail>

register foo : bits(32)

$unscope# register foo

val bar : unit -> unit

function bar() = {
  let _ = foo;
  ()
}
