default Order dec

$include <prelude.sail>

function check_sat(x: int, y: int, z: int) -> bool = {
  if (x <= y & y <= z) then not_bool(x <= z) else false
}