default Order dec

$include <prelude.sail>
$include <real.sail>

// Test for the mult_real primitive
function main() -> unit = {
  assert(mult_real(2.5, 4.0) == 10.0);
  assert(mult_real(0.5, 0.5) == 0.25);
  assert(mult_real(2.0, 0.0) == 0.0);
}
