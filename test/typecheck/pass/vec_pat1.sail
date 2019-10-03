default Order inc

$include <prelude.sail>

val test : (bitvector(3, inc), bitvector(3, inc)) -> bitvector(3, inc)

function test (x : bitvector(1, inc) @ 0b1 @ 0b0, z) = (x @ 0b11) + z
