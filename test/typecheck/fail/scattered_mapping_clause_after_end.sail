default Order dec

$include <prelude.sail>

val m : int <-> bool

scattered mapping m
mapping clause m = 0 <-> false
end m

mapping clause m = 1 <-> true
