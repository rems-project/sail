default Order dec

$include <prelude.sail>

$property
function prop(x: int, y: int) -> bool = {
  if x >= 0  & y >= 0 then {
    x + y >= 0
  } else true
}
