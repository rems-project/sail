default Order dec

$include <vector_dec.sail>

function check_sat((): unit) -> bool = {
  0x00 == sail_zeros(8)
}