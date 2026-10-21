default Order dec

$include <prelude.sail>
$include <real.sail>

// Test for the floor primitive
function main() -> unit = {
  assert(floor(2.5) == 2);
  assert(floor(2.0) == 2);
  assert(floor(sub_real(0.0, 2.5)) == -3);
  assert(floor(0.0) == 0);
}
