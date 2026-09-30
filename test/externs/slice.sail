default Order dec

$include <prelude.sail>

// Test for the slice primitive
function main() -> unit = {
  // slice(xs, start, len) takes len bits starting at index start
  assert(slice(0xABCD, 4, 8) == 0xBC);
  assert(slice(0xABCD, 0, 16) == 0xABCD);
  assert(slice(0xABCD, 0, 1) == 0b1);
  assert(slice(0xABCD_0000_0000_0000_0, 52, 16) == 0xABCD);
}
