default Order dec

$include <prelude.sail>

// Test for the bitvector_concat primitive
function main() -> unit = {
  assert(bitvector_concat(0xAB, 0xCD) == 0xABCD);
  assert(bitvector_concat(0b1, 0b0) == 0b10);
  assert(bitvector_concat(0xAB, sail_zeros(0)) == 0xAB);
  assert(bitvector_concat(0xF, 0x0000_0000_0000_0000) == 0xF_0000_0000_0000_0000);
}
