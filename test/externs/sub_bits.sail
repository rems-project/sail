default Order dec

$include <prelude.sail>

// Test for the sub_bits primitive
function main() -> unit = {
  assert(sub_bits(0x03, 0x02) == 0x01);
  // Subtraction wraps around
  assert(sub_bits(0x00, 0x01) == 0xFF);
  assert(sub_bits(0x0000_0000_0000_0000_0, 0x0000_0000_0000_0000_1) == 0xFFFF_FFFF_FFFF_FFFF_F);
}
