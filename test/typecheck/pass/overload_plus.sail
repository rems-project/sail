default Order inc

$include <prelude.sail>

val test : (bitvector(3), bitvector(3)) -> bitvector(3)

function test (x, y) = x + y
