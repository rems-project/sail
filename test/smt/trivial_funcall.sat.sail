default Order dec

$include <flow.sail>

function f((): unit) -> bool = true

function check_sat((): unit) -> bool = {
  f()
}