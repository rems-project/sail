default Order dec

$include <vector_dec.sail>

$property
function prop((): unit) -> bool = {
  0x1000_0000_0000_0000_0 != sail_zeros(68)
}