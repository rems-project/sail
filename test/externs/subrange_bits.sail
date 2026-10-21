default Order dec

$include <prelude.sail>

// Test for the subrange_bits primitive
function main() -> unit = {
  assert(subrange_bits(0xABCD, 11, 4) == 0xBC);
  assert(subrange_bits(0xABCD, 15, 0) == 0xABCD);
  assert(subrange_bits(0xABCD, 0, 0) == 0b1);
  assert(subrange_bits(0xABCD_0000_0000_0000_0, 67, 52) == 0xABCD);
}
