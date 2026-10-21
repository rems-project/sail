default Order dec

$include <prelude.sail>

// Test for the _shl8 primitive
function main() -> unit = {
  assert(_shl8(8, 0) == 8);
  assert(_shl8(8, 1) == 16);
  assert(_shl8(8, 2) == 32);
  assert(_shl8(8, 3) == 64);
}
