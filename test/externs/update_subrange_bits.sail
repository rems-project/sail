default Order dec

$include <prelude.sail>

// Test for the update_subrange_bits primitive
function main() -> unit = {
  assert(update_subrange_bits(0xABCD, 11, 4, 0x00) == 0xA00D);
  assert(update_subrange_bits(0xABCD, 15, 0, 0x1234) == 0x1234);
  assert(update_subrange_bits(0xABCD, 0, 0, 0b0) == 0xABCC);
  assert(update_subrange_bits(0x0000_0000_0000_0000_0, 67, 64, 0xF) == 0xF000_0000_0000_0000_0);
}
