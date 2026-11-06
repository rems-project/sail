default Order dec

$include <prelude.sail>
$include <real.sail>

// Test for the lteq_real primitive
function main() -> unit = {
  assert(lteq_real(1.5, 2.5));
  assert(lteq_real(2.5, 2.5));
  assert(not_bool(lteq_real(3.5, 2.5)));
}
