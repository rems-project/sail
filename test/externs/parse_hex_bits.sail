default Order dec

$include <prelude.sail>
$include <hex_bits.sail>

// Test for the parse_hex_bits primitive
function main() -> unit = {
  assert(parse_hex_bits(8, "0x0") == 0x00);
  assert(parse_hex_bits(8, "0xAB") == 0xAB);
  assert(parse_hex_bits(8, "0xab") == 0xAB);
  assert(parse_hex_bits(8, "0x00AB") == 0xAB);
  assert(parse_hex_bits(4, "0xF") == 0xF);
  assert(parse_hex_bits(72, "0xFFFFFFFFFFFFFFFFFF") == 0xFF_FFFF_FFFF_FFFF_FFFF);
  // Invalid strings parse as zero
  assert(parse_hex_bits(8, "AB") == 0x00);
  assert(parse_hex_bits(8, "0x1FF") == 0x00);
  assert(parse_hex_bits(8, "0xAG") == 0x00);
}
