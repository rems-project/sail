default Order dec

$include <prelude.sail>
$include <mono_rewrites.sail>

// Test for the string_of_bits_subrange primitive
function main() -> unit = {
  assert(string_of_bits_subrange(0xABCD, 15, 0) == "0xABCD");
  assert(string_of_bits_subrange(0xABCD, 11, 4) == "0xBC");
  assert(string_of_bits_subrange(0xABCD, 2, 0) == "0b101");
}
