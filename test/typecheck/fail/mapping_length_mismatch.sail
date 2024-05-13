default Order dec

$include <prelude.sail>

val foo : bits(1) <-> bits(2)

scattered mapping foo

mapping clause foo = x : bits(1) <-> x : bits(2)
