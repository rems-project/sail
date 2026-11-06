default Order dec

$include <prelude.sail>

// Test for the sail_ones primitive
function main() -> unit = {
  assert(sail_ones(4) == 0xF);
  assert(sail_ones(1) == 0b1);
  assert(bitvector_length(sail_ones(0)) == 0);
  assert(sail_ones(68) == 0xFFFF_FFFF_FFFF_FFFF_F);
}
