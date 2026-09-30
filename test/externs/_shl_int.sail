default Order dec

$include <prelude.sail>

// Test for the _shl_int primitive
function main() -> unit = {
  assert(_shl_int(5, 0) == 5);
  assert(_shl_int(5, 3) == 40);
  assert(_shl_int(-1, 4) == -16);
  assert(_shl_int(1, 64) == 18446744073709551616);
}
