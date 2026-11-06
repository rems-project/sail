default Order dec

$include <prelude.sail>
$include <real.sail>

// Test for the to_real primitive
function main() -> unit = {
  assert(to_real(3) == 3.0);
  assert(to_real(0) == 0.0);
  assert(to_real(-3) == sub_real(0.0, 3.0));
}
