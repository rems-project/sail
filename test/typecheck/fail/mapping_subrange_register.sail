default Order dec
$include <prelude.sail>

register R : bits(8)
mapping m : bits(8) <-> (bits(8), unit) = { R[7 .. 0] <-> (R, ()) }
