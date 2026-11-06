default Order inc

$include <prelude.sail>

// Test for the update_subrange_bits primitive
function main() -> unit = {
  // With increasing order, index 0 is the most significant bit
  assert(update_subrange_bits(0xABCD, 4, 11, 0x00) == 0xA00D);
  assert(update_subrange_bits(0xABCD, 0, 15, 0x1234) == 0x1234);
  assert(update_subrange_bits(0xABCD, 15, 15, 0b0) == 0xABCC);
}
