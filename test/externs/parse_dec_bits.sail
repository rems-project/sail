default Order dec

$include <prelude.sail>
$include <dec_bits.sail>

// Test for the parse_dec_bits primitive
function main() -> unit = {
  assert(parse_dec_bits(8, "0") == 0x00);
  assert(parse_dec_bits(8, "171") == 0xAB);
  assert(parse_dec_bits(8, "255") == 0xFF);
  assert(parse_dec_bits(16, "0043981") == 0xABCD);
  assert(parse_dec_bits(72, "4722366482869645213695") == 0xFF_FFFF_FFFF_FFFF_FFFF);
  // Invalid strings parse as zero
  assert(parse_dec_bits(8, "256") == 0x00);
  assert(parse_dec_bits(8, "12a") == 0x00);
  assert(parse_dec_bits(8, "-1") == 0x00);
}
