default Order dec

$include <prelude.sail>

// Test for the sub_bits_int primitive
function main() -> unit = {
  assert(sub_bits_int(0x03, 2) == 0x01);
  assert(sub_bits_int(0x00, 1) == 0xFF);
  assert(sub_bits_int(0xFF, -1) == 0x00);
  assert(sub_bits_int(0x01, 257) == 0x00);
}
