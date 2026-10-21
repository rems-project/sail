default Order dec

$include <prelude.sail>

// Test for the truncate primitive
function main() -> unit = {
  assert(truncate(0xABCD, 8) == 0xCD);
  assert(truncate(0xABCD, 16) == 0xABCD);
  assert(truncate(0xABCD, 0) == sail_zeros(0));
  assert(truncate(0xFFFF_FFFF_FFFF_FFFF_A, 4) == 0xA);
}
