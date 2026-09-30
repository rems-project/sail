default Order dec

$include <prelude.sail>

// Test for the count_leading_zeros primitive
function main() -> unit = {
  assert(count_leading_zeros(0x0F) == 4);
  assert(count_leading_zeros(0x80) == 0);
  assert(count_leading_zeros(0x00) == 8);
  assert(count_leading_zeros(0b1) == 0);
  assert(count_leading_zeros(0x0000_0000_0000_0000_1) == 67);
}
