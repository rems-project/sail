default Order dec

$include <prelude.sail>
$include <hex_bits.sail>

// Test for the valid_hex_bits primitive
function main() -> unit = {
  assert(valid_hex_bits(8, "0x0"));
  assert(valid_hex_bits(8, "0xAB"));
  assert(valid_hex_bits(8, "0xab"));
  assert(valid_hex_bits(8, "0x00FF"));
  assert(not_bool(valid_hex_bits(8, "0x1FF")));
  assert(not_bool(valid_hex_bits(8, "AB")));
  assert(not_bool(valid_hex_bits(8, "0x")));
  assert(not_bool(valid_hex_bits(8, "0xAG")));
  assert(valid_hex_bits(72, "0xFFFFFFFFFFFFFFFFFF"));
  assert(not_bool(valid_hex_bits(72, "0x1FFFFFFFFFFFFFFFFFF")));
}
