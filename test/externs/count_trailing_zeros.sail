default Order dec

$include <prelude.sail>

// Test for the count_trailing_zeros primitive
function main() -> unit = {
  assert(count_trailing_zeros(0xF0) == 4);
  assert(count_trailing_zeros(0x01) == 0);
  assert(count_trailing_zeros(0x00) == 8);
  assert(count_trailing_zeros(0b1) == 0);
  assert(count_trailing_zeros(0x8000_0000_0000_0000_0) == 67);
}
