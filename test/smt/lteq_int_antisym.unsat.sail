default Order dec

$include <prelude.sail>

function check_sat(x: int, y: int) -> bool = {
  if x <= y & y <= x then not_bool(x == y) else false
}