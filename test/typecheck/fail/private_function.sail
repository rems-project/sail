$option -dmagic_hash
default Order dec

$include <prelude.sail>

$project# A {} B { requires A }

$start_module# A

private val foo : unit -> unit

$end_module#

$start_module# B

val bar : unit -> unit

function bar() = foo()

$end_module#
