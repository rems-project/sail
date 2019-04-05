default Order dec

$include <vector_dec.sail>

function check_sat((): unit) -> bool = {
  0x0000_0000_0000_0000 == sail_zeros(64)
}