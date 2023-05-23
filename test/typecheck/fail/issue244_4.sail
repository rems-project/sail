default Order dec
$include <prelude.sail>

let zeros_2 : bits(2) = sail_zeros(2)
let zeros_3 : bits(3) = sail_zeros(3)

val test : (bits(3), bits(3)) <-> bits(6)
scattered mapping test

mapping clause test = (0b000, 0b001) <-> zeros_3 @ 0b001
