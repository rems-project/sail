$option -dmagic_hash

default Order dec

$include <prelude.sail>

val foo : unit -> unit

$unscope# val foo

function foo() = ()
