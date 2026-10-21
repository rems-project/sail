default Order dec

$include <prelude.sail>

// Test for the xor_vec primitive
function main() -> unit = {
  assert(xor_vec(0xF0, 0x3C) == 0xCC);
  assert(xor_vec(0b1, 0b1) == 0b0);
  assert(xor_vec(0xFFFF_FFFF_FFFF_FFFF_F, 0x0FFF_FFFF_FFFF_FFFF_0) == 0xF000_0000_0000_0000_F);
}
