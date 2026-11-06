default Order dec

$include <prelude.sail>

// Test for the sail_zeros primitive
function main() -> unit = {
  assert(sail_zeros(4) == 0x0);
  assert(sail_zeros(1) == 0b0);
  assert(bitvector_length(sail_zeros(0)) == 0);
  assert(sail_zeros(68) == 0x0000_0000_0000_0000_0);
}
