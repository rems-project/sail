default Order dec

$include <prelude.sail>
$include <real.sail>

// Test for the pow_real primitive
function main() -> unit = {
  assert(pow_real(2.0, 3) == 8.0);
  assert(pow_real(2.5, 0) == 1.0);
  assert(pow_real(0.5, 2) == 0.25);
}
