default Order inc

$include <prelude.sail>

// Test for the bitvector_access primitive
function main() -> unit = {
  // With increasing order, index 0 is the most significant bit
  assert(bitvector_access(0b0010, 2) == bitone);
  assert(bitvector_access(0b0010, 1) == bitzero);
  assert(bitvector_access(0b1000, 0) == bitone);
  assert(bitvector_access(0x0000_0000_0000_0000_1, 67) == bitone);
}
