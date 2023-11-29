$option -dmagic_hash

$project# A {}

default Order dec

$include <prelude.sail>

$start_module# A

enum E = A | B | C

$end_module# A

val bar : unit -> unit

function bar() = {
  let _ = A;
  ()
}
