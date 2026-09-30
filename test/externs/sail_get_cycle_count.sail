default Order dec

$include <prelude.sail>
$include <concurrency_interface.sail>

// Test for the sail_get_cycle_count primitive
function main() -> unit = {
  let c = sail_get_cycle_count();
  assert(c >= 0);
  assert(sail_get_cycle_count() == c);
  sail_end_cycle();
  assert(sail_get_cycle_count() == c + 1);
}
