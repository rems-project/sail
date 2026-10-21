default Order dec

$include <prelude.sail>

// Test for the eq_bits primitive
function main() -> unit = {
  assert(eq_bits(0xAB, 0xAB));
  assert(not_bool(eq_bits(0xAB, 0xAC)));
  assert(eq_bits(0b1, 0b1));
  assert(eq_bits(0xFFFF_FFFF_FFFF_FFFF_F, 0xFFFF_FFFF_FFFF_FFFF_F));
  assert(not_bool(eq_bits(0xFFFF_FFFF_FFFF_FFFF_F, 0x7FFF_FFFF_FFFF_FFFF_F)));
}
