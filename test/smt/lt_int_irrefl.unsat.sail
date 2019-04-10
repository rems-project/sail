default Order dec

$include <prelude.sail>

function check_sat(x: int) -> bool = {
  x < x
}