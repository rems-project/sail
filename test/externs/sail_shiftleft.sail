default Order dec

$include <prelude.sail>

// Test for the sail_shiftleft primitive
function main() -> unit = {
  assert(sail_shiftleft(0x81, 1) == 0x02);
  assert(sail_shiftleft(0x81, 0) == 0x81);
  assert(sail_shiftleft(0x81, 8) == 0x00);
  assert(sail_shiftleft(0x8000_0000_0000_0000_1, 4) == 0x0000_0000_0000_0001_0);
}
