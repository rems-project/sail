default Order dec

$include <prelude.sail>

// Test for the set_slice_int primitive
function main() -> unit = {
  assert(set_slice_int(8, 0, 4, 0xFF) == 4080);
  assert(set_slice_int(4, 43981, 4, 0x0) == 43789);
  assert(set_slice_int(8, -1, 0, 0x00) == -256);
  assert(set_slice_int(4, 0, 64, 0x1) == 18446744073709551616);
}
