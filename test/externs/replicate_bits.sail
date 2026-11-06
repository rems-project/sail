default Order dec

$include <prelude.sail>

// Test for the replicate_bits primitive
function main() -> unit = {
  assert(replicate_bits(0b10, 3) == 0b101010);
  assert(replicate_bits(0xAB, 1) == 0xAB);
  assert(bitvector_length(replicate_bits(0xAB, 0)) == 0);
  assert(replicate_bits(0xF, 17) == 0xFFFF_FFFF_FFFF_FFFF_F);
}
