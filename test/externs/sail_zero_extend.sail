default Order dec

$include <prelude.sail>

// Test for the sail_zero_extend primitive
function main() -> unit = {
  assert(sail_zero_extend(0xF, 8) == 0x0F);
  assert(sail_zero_extend(0x80, 8) == 0x80);
  assert(sail_zero_extend(0x8, 68) == 0x0000_0000_0000_0000_8);
}
