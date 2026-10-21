default Order dec

$include <prelude.sail>
$include <real.sail>

// Test for the gt_real primitive
function main() -> unit = {
  assert(gt_real(2.5, 1.5));
  assert(not_bool(gt_real(2.5, 2.5)));
  assert(not_bool(gt_real(1.5, 2.5)));
}
