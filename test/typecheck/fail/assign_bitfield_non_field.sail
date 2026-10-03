default Order dec
$include <prelude.sail>

bitfield B : bits(8) = { F : 3 .. 0 }
register R : B
function f() -> unit = { R[1] = 0b0000 }
