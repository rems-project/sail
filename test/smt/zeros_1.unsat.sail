default Order dec

$include <vector_dec.sail>

function check_sat((): unit) -> bool = {
  0x1 == sail_zeros(4)
}