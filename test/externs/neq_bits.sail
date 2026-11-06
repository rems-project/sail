default Order dec

$include <prelude.sail>

// Test for the neq_bits primitive
function main() -> unit = {
  assert(neq_bits(0xAB, 0xAC));
  assert(not_bool(neq_bits(0xAB, 0xAB)));
  assert(neq_bits(0xFFFF_FFFF_FFFF_FFFF_F, 0x7FFF_FFFF_FFFF_FFFF_F));
}
