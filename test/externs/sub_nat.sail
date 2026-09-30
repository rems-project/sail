default Order dec

$include <prelude.sail>

// Test for the sub_nat primitive
function main() -> unit = {
  assert(sub_nat(5, 3) == 2);
  assert(sub_nat(3, 3) == 0);
  // Subtraction on naturals saturates at zero
  assert(sub_nat(3, 5) == 0);
  assert(sub_nat(18446744073709551616, 1) == 18446744073709551615);
}
