default Order dec

$include <prelude.sail>
$include <real.sail>

$counterexample
function prop(x: real) -> bool = {
  not_bool(sqrt(x) == 2.0);
}
