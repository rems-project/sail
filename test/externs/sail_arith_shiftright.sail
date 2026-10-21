default Order dec

$include <prelude.sail>

// Test for the sail_arith_shiftright primitive
function main() -> unit = {
  assert(sail_arith_shiftright(0x80, 1) == 0xC0);
  assert(sail_arith_shiftright(0x40, 1) == 0x20);
  assert(sail_arith_shiftright(0x81, 0) == 0x81);
  assert(sail_arith_shiftright(0x80, 8) == 0xFF);
  assert(sail_arith_shiftright(0x8000_0000_0000_0000_0, 4) == 0xF800_0000_0000_0000_0);
}
