default Order dec

$include <prelude.sail>

// Test for the bitvector_update primitive
function main() -> unit = {
  assert(bitvector_update(0b0000, 1, bitone) == 0b0010);
  assert(bitvector_update(0b1111, 3, bitzero) == 0b0111);
  assert(bitvector_update(0b1111, 0, bitone) == 0b1111);
  assert(bitvector_update(0x0000_0000_0000_0000_0, 67, bitone) == 0x8000_0000_0000_0000_0);
}
