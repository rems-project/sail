default Order dec

$include <prelude.sail>
$include <concurrency_interface.sail>

// Test for the sail_end_cycle primitive
function main() -> unit = {
  let c = sail_get_cycle_count();
  sail_end_cycle();
  assert(sail_get_cycle_count() == c + 1);
  sail_end_cycle();
  sail_end_cycle();
  assert(sail_get_cycle_count() == c + 3);
}
