$option -dmagic_hash
default Order dec

$include <prelude.sail>

$project# A {} B { requires A }

$start_module# A

val foo : unit -> unit

private function foo() = print_endline("Hello, World!")

$end_module#

$start_module# B

function bar() -> unit = {
  foo()
}

$end_module#
