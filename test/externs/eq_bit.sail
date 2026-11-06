default Order dec

$include <prelude.sail>

// Test for the eq_bit primitive
function main() -> unit = {
  assert(eq_bit(bitzero, bitzero));
  assert(eq_bit(bitone, bitone));
  assert(not_bool(eq_bit(bitzero, bitone)));
  assert(not_bool(eq_bit(bitone, bitzero)));
}
