default Order dec

$include <prelude.sail>

// Test for the and_vec primitive
function main() -> unit = {
  assert(and_vec(0xF0, 0x3C) == 0x30);
  assert(and_vec(0b1, 0b0) == 0b0);
  assert(and_vec(0xFFFF_FFFF_FFFF_FFFF_0, 0x0FFF_FFFF_FFFF_FFFF_F) == 0x0FFF_FFFF_FFFF_FFFF_0);
}
