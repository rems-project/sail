default Order dec

$include <prelude.sail>

// Test for the add_bits primitive
function main() -> unit = {
  assert(add_bits(0x01, 0x02) == 0x03);
  // Addition wraps around
  assert(add_bits(0xFF, 0x01) == 0x00);
  assert(add_bits(0xFFFF_FFFF_FFFF_FFFF_F, 0x0000_0000_0000_0000_1) == 0x0000_0000_0000_0000_0);
}
