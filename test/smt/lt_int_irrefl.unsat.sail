default Order dec

$include <prelude.sail>

$property
function prop(x: int) -> bool = {
  not_bool(x < x)
}