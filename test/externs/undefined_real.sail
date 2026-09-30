default Order dec

$include <prelude.sail>
$include <real.sail>

// Test for the undefined_real primitive
function main() -> unit = {
  let x : real = undefined_real();
  assert(eq_real(x, x));
}
