default Order dec

$include <prelude.sail>
$include <real.sail>

// Test for the add_real primitive
function main() -> unit = {
  assert(add_real(1.5, 2.25) == 3.75);
  assert(add_real(0.0, 0.0) == 0.0);
}
