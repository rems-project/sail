default Order dec

$include <prelude.sail>

// Test for the _shl1 primitive
function main() -> unit = {
  assert(_shl1(1, 0) == 1);
  assert(_shl1(1, 1) == 2);
  assert(_shl1(1, 2) == 4);
  assert(_shl1(1, 3) == 8);
}
