default Order dec

$include <prelude.sail>

// Test for the gt_int primitive
function main() -> unit = {
  assert(gt_int(5, 3));
  assert(not_bool(gt_int(5, 5)));
  assert(not_bool(gt_int(5, 6)));
  assert(gt_int(18446744073709551616, -18446744073709551616));
}
