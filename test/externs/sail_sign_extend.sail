default Order dec

$include <prelude.sail>

// Test for the sail_sign_extend primitive
function main() -> unit = {
  assert(sail_sign_extend(0xF, 8) == 0xFF);
  assert(sail_sign_extend(0x7, 8) == 0x07);
  assert(sail_sign_extend(0x80, 8) == 0x80);
  assert(sail_sign_extend(0x8, 68) == 0xFFFF_FFFF_FFFF_FFFF_8);
}
