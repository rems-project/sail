$option -dmagic_hash
default Order dec

$include <prelude.sail>

$project# A {} E { optional } B { requires A }

$start_module# A

private union Foo = {
  $[extension E] Bar : unit
}

$end_module#

$start_module# E

function quux() -> unit = {
  let _ = Bar();
}

$end_module#
