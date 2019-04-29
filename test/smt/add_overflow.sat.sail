default Order dec

$include <prelude.sail>

$option -smt_ignore_overflow

$counterexample
function prop(x: int, y: int) -> bool = {
  if x >= 0  & y >= 0 then {
    x + y >= 0
  } else true
}
