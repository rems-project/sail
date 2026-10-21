default Order dec

$include <prelude.sail>

// Test for the negate_int primitive
function main() -> unit = {
  let x : int = 5;
  assert(negate_int(x) == -5);
  assert(negate_int(-5) == 5);
  assert(negate_int(0) == 0);
  assert(negate_int(-9223372036854775808) == 9223372036854775808);
}
