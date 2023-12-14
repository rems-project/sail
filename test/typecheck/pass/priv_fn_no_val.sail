$option -dmagic_hash
default Order dec

$include <prelude.sail>

$project# A {} B { requires A }

$start_module# A

private function foo() -> unit = print_endline("Hello, World!")

$end_module#
