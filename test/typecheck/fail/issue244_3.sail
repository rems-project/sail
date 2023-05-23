default Order dec
$include <prelude.sail>

let zeros_2 : bits(2) = sail_zeros(2)
let zeros_3 : bits(3) = sail_zeros(3)

val test : (bits(3), bits(3)) <-> bits(6)
scattered mapping test

mapping clause test = (zeros_3, zeros_3) <-> 0b000010
