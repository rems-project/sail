default Order inc

$include <prelude.sail>

// Test for the bitvector_update primitive
function main() -> unit = {
  // With increasing order, index 0 is the most significant bit
  assert(bitvector_update(0b0000, 1, bitone) == 0b0100);
  assert(bitvector_update(0b1111, 0, bitzero) == 0b0111);
  assert(bitvector_update(0x0000_0000_0000_0000_0, 67, bitone) == 0x0000_0000_0000_0000_1);
}
