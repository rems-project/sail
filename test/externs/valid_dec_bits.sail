default Order dec

$include <prelude.sail>
$include <dec_bits.sail>

// Test for the valid_dec_bits primitive
function main() -> unit = {
  assert(valid_dec_bits(8, "0"));
  assert(valid_dec_bits(8, "255"));
  assert(valid_dec_bits(8, "000255"));
  assert(not_bool(valid_dec_bits(8, "256")));
  assert(not_bool(valid_dec_bits(8, "12a")));
  assert(not_bool(valid_dec_bits(8, "-1")));
  assert(not_bool(valid_dec_bits(8, "0x12")));
  assert(valid_dec_bits(72, "4722366482869645213695"));
  assert(not_bool(valid_dec_bits(72, "4722366482869645213696")));
}
