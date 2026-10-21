default Order dec

$include <prelude.sail>

// Test for the truncateLSB primitive
function main() -> unit = {
  assert(truncateLSB(0xABCD, 8) == 0xAB);
  assert(truncateLSB(0xABCD, 16) == 0xABCD);
  assert(truncateLSB(0xABCD, 0) == sail_zeros(0));
  assert(truncateLSB(0xAFFF_FFFF_FFFF_FFFF_F, 4) == 0xA);
}
