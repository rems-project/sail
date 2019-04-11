default Order dec

$include <vector_dec.sail>

$property
function prop((): unit) -> bool = {
  0x0000_0000_0000_0000 != sail_zeros(64)
}