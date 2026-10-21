default Order dec

$include <prelude.sail>

// Test for the bitvector_length primitive
function main() -> unit = {
  assert(bitvector_length(0xABC) == 12);
  assert(bitvector_length(0b1) == 1);
  assert(bitvector_length(0xFFFF_FFFF_FFFF_FFFF_F) == 68);
}
