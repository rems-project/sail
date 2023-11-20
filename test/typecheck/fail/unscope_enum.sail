$option -dmagic_hash

default Order dec

$include <prelude.sail>

enum E = A | B | C

$unscope# enum E

val bar : unit -> unit

function bar() = {
  let _ = A;
  ()
}
