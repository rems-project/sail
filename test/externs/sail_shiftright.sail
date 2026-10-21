default Order dec

$include <prelude.sail>

// Test for the sail_shiftright primitive
function main() -> unit = {
  assert(sail_shiftright(0x81, 1) == 0x40);
  assert(sail_shiftright(0x81, 0) == 0x81);
  assert(sail_shiftright(0x81, 8) == 0x00);
  assert(sail_shiftright(0x8000_0000_0000_0000_1, 4) == 0x0800_0000_0000_0000_0);
}
