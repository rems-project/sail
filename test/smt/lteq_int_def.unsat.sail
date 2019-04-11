default Order dec

$include <prelude.sail>

$property
function prop(x: int, y: int) -> bool = {
  if x <= y then x < y | x == y else y < x
}