default Order dec

$include <prelude.sail>
$include <real.sail>

// Test for the eq_real primitive
function main() -> unit = {
  assert(eq_real(2.5, 2.5));
  assert(not_bool(eq_real(2.5, 2.25)));
  assert(eq_real(0.5, div_real(1.0, 2.0)));
}
