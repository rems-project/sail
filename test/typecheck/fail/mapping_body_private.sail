$option -dmagic_hash
default Order dec

$include <prelude.sail>

$project# A {} B { requires A }

$start_module# A

val foo : int <-> unit

private mapping foo = { 0 <-> () }

$end_module#
