default Order dec

$include <prelude.sail>

union instr = {
   Foo : (bool, unit)
}

val bar : instr <-> bool

scattered mapping bar

mapping clause bar = Foo(b, ()) <-> b
