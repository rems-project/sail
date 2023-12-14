default Order dec

$include <prelude.sail>

val foo : int <-> unit

mapping foo : unit <-> int = { 0 <-> () }
