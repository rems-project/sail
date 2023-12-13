$option -dmagic_hash
default Order dec

$include <prelude.sail>

$project# A {} B { requires A }

$start_module# A

private union Foo = {
  Bar : unit
}

$end_module#

$start_module# B

val baz : unit -> Foo

function baz() = Bar()

$end_module#
