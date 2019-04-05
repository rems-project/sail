default Order dec

$include <vector_dec.sail>

function check_sat((): unit) -> bool = {
  0x1000_0000_0000_0000_0 == sail_zeros(68)
}