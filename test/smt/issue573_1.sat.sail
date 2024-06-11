default Order dec

$include <prelude.sail>

$counterexample
function prop(x : int) -> bool = {
  if x == 0 then return true;
  if x == 100 then return true;
  false
}
