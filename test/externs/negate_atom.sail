default Order dec

$include <prelude.sail>

// Test for the negate_atom primitive
function main() -> unit = {
  assert(negate_atom(5) == -5);
  assert(negate_atom(-5) == 5);
  assert(negate_atom(0) == 0);
  assert(negate_atom(9223372036854775808) == -9223372036854775808);
  assert(negate_atom(-9223372036854775808) == 9223372036854775808);
}
