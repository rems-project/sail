default Order dec

$include <prelude.sail>

// Test for the bitvector_access primitive
function main() -> unit = {
  // With decreasing order, index 0 is the least significant bit
  assert(bitvector_access(0b0010, 1) == bitone);
  assert(bitvector_access(0b0010, 0) == bitzero);
  assert(bitvector_access(0b1000, 3) == bitone);
  assert(bitvector_access(0x8000_0000_0000_0000_0, 67) == bitone);
}
