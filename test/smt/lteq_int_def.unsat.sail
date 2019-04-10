default Order dec

$include <prelude.sail>

function check_sat(x: int, y: int) -> bool = {
  if x <= y then not_bool(x < y | x == y) else not_bool(y < x)
}