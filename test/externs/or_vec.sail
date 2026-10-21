default Order dec

$include <prelude.sail>

// Test for the or_vec primitive
function main() -> unit = {
  assert(or_vec(0xF0, 0x3C) == 0xFC);
  assert(or_vec(0b1, 0b0) == 0b1);
  assert(or_vec(0xF000_0000_0000_0000_0, 0x0000_0000_0000_0000_F) == 0xF000_0000_0000_0000_F);
}
