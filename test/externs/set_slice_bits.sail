default Order dec

$include <prelude.sail>

// Test for the set_slice_bits primitive
function main() -> unit = {
  let x : bits(16) = set_slice_bits(8, 0x0000, 4, 0xFF);
  assert(x == 0x0FF0);
  let y : bits(16) = set_slice_bits(4, 0xABCD, 12, 0x0);
  assert(y == 0x0BCD);
  let z : bits(68) = set_slice_bits(4, 0x0000_0000_0000_0000_0, 64, 0xF);
  assert(z == 0xF000_0000_0000_0000_0);
}
