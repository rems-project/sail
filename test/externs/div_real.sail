default Order dec

$include <prelude.sail>
$include <real.sail>

// Test for the div_real primitive
function main() -> unit = {
  assert(div_real(1.0, 4.0) == 0.25);
  assert(div_real(10.0, 2.5) == 4.0);
  assert(mult_real(div_real(1.0, 3.0), 3.0) == 1.0);
}
