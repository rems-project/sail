default Order dec

$include <vector_dec.sail>

$property
function prop((): unit) -> bool = {
  0x1 != sail_zeros(4)
}
