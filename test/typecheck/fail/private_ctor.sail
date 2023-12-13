$option -dmagic_hash
default Order dec

$include <prelude.sail>

$project# A {} B { requires A }

$start_module# A

union Foo = {
  private Bar : unit
}

$end_module#

$start_module# B

val baz : unit -> Foo

function baz() = Bar()

$end_module#
