default Order dec

$include <vector_dec.sail>

$property
function prop((): unit) -> bool = {
  0b1 != sail_zeros(1)
}