default Order dec

$include <prelude.sail>

// Test for the signed primitive
function main() -> unit = {
  assert(signed(0x00) == 0);
  assert(signed(0x7F) == 127);
  assert(signed(0xFF) == -1);
  assert(signed(0x80) == -128);
  assert(signed(0b1) == -1);
  assert(signed(0x8000_0000_0000_0000_0) == -147573952589676412928);
}
