default Order dec

$include <prelude.sail>

// Test for the unsigned primitive
function main() -> unit = {
  assert(unsigned(0x00) == 0);
  assert(unsigned(0xFF) == 255);
  assert(unsigned(0b1) == 1);
  assert(unsigned(0xFFFF_FFFF_FFFF_FFFF_F) == 295147905179352825855);
}
