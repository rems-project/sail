default Order dec

$include <prelude.sail>

// Test for the _shl32 primitive
function main() -> unit = {
  assert(_shl32(32, 0) == 32);
  assert(_shl32(32, 1) == 64);
}
