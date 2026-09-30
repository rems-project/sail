default Order dec

$include <prelude.sail>

// Test for the add_bits_int primitive
function main() -> unit = {
  assert(add_bits_int(0x01, 2) == 0x03);
  assert(add_bits_int(0xFF, 1) == 0x00);
  assert(add_bits_int(0x00, -1) == 0xFF);
  assert(add_bits_int(0x00, 257) == 0x01);
}
