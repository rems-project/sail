default Order dec

$include <prelude.sail>
$include <real.sail>

// Test for the ceil primitive
function main() -> unit = {
  assert(ceil(2.5) == 3);
  assert(ceil(2.0) == 2);
  assert(ceil(sub_real(0.0, 2.5)) == -2);
  assert(ceil(0.0) == 0);
}
