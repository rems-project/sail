default Order inc

$include <prelude.sail>

// Test for the subrange_bits primitive
function main() -> unit = {
  // With increasing order, index 0 is the most significant bit
  assert(subrange_bits(0xABCD, 4, 11) == 0xBC);
  assert(subrange_bits(0xABCD, 0, 15) == 0xABCD);
  assert(subrange_bits(0xABCD, 15, 15) == 0b1);
}
