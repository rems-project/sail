default Order dec

$include <prelude.sail>

// Test for the not_vec primitive
function main() -> unit = {
  assert(not_vec(0x0F) == 0xF0);
  assert(not_vec(0b1) == 0b0);
  assert(not_vec(0x0000_0000_0000_0000_0) == 0xFFFF_FFFF_FFFF_FFFF_F);
}
