default Order dec

$include <prelude.sail>

val foo : forall ('a 'b : Type). 'a <-> 'b

scattered mapping foo

mapping clause foo = x : 'a <-> x : 'b
