default Order dec

$include <prelude.sail>
$include <real.sail>

// Test for the neg_real primitive
function main() -> unit = {
  assert(neg_real(2.5) == sub_real(0.0, 2.5));
  assert(neg_real(neg_real(2.5)) == 2.5);
  assert(neg_real(0.0) == 0.0);
}
