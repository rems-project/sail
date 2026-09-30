default Order dec

$include <prelude.sail>

// Test for the _shr_int primitive
function main() -> unit = {
  assert(_shr_int(40, 0) == 40);
  assert(_shr_int(40, 3) == 5);
  assert(_shr_int(41, 3) == 5);
  // Right shift of a negative integer rounds towards negative infinity
  assert(_shr_int(-16, 2) == -4);
  assert(_shr_int(-1, 1) == -1);
  assert(_shr_int(18446744073709551616, 64) == 1);
}
