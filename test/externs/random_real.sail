default Order dec

$include <prelude.sail>
$include <real.sail>

// Test for the random_real primitive
function main() -> unit = {
  let x : real = random_real();
  assert(eq_real(x, x));
}
