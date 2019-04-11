default Order dec

$include <prelude.sail>

$property
function prop(x: int) -> bool = {
  x <= x
}