default Order dec

$include <prelude.sail>

$property
function prop(x: int, y: int) -> bool = {
  if x <= y & y <= x then x == y else true
}