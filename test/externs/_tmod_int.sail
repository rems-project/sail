default Order dec

$include <prelude.sail>

// Test for the _tmod_int primitive
function main() -> unit = {
  // The remainder takes the sign of the dividend
  assert(_tmod_int(7, 2) == 1);
  assert(_tmod_int(-7, 2) == -1);
  assert(_tmod_int(7, -2) == 1);
  assert(_tmod_int(-7, -2) == -1);
  assert(_tmod_int(6, 3) == 0);
  assert(_tmod_int(18446744073709551617, 4294967296) == 1);
}
