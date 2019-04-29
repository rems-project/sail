default Order dec

$include <prelude.sail>

$counterexample
function prop(x: bits(5), y: bits(5)) -> bool = {
  assert(x == y);
  true
}
