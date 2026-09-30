default Order dec

$include <prelude.sail>
$include <real.sail>

// Test for the sqrt primitive
function main() -> unit = {
  assert(sqrt(4.0) == 2.0);
  assert(sqrt(0.25) == 0.5);
  assert(sqrt(0.0) == 0.0);
}
