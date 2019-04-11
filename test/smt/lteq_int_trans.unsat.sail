default Order dec

$include <prelude.sail>

$property
function prop(x: int, y: int, z: int) -> bool = {
  if (x <= y & y <= z) then x <= z else true
}