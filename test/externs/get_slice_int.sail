default Order dec

$include <prelude.sail>

// Test for the get_slice_int primitive
function main() -> unit = {
  assert(get_slice_int(8, 43981, 4) == 0xBC);
  assert(get_slice_int(16, 43981, 0) == 0xABCD);
  // Negative integers are treated as two's complement
  assert(get_slice_int(8, -1, 0) == 0xFF);
  assert(get_slice_int(8, -2, 0) == 0xFE);
  assert(get_slice_int(4, 18446744073709551616, 62) == 0x4);
}
