default Order dec

$include <vector_dec.sail>

$property
function prop((): unit) -> bool = {
  not_bool(0x0000_0000_0000_0000_0 == sail_zeros(68))
}