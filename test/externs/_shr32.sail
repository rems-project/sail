default Order dec

$include <prelude.sail>

// Test for the _shr32 primitive
function main() -> unit = {
  assert(_shr32(0, 1) == 0);
  assert(_shr32(1, 1) == 0);
  assert(_shr32(30, 1) == 15);
  assert(_shr32(31, 1) == 15);
}
