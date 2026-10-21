default Order inc

$include <prelude.sail>

// Test for the slice primitive
function main() -> unit = {
  // With increasing order, index 0 is the most significant bit
  assert(slice(0xABCD, 4, 8) == 0xBC);
  assert(slice(0xABCD, 0, 16) == 0xABCD);
  assert(slice(0xABCD, 0, 1) == 0b1);
}
