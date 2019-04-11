default Order dec

$include <flow.sail>

function f((): unit) -> bool = false

$property
function prop((): unit) -> bool = {
  f()
}