default Order dec

$include <prelude.sail>

// Test for the _tmod_int_positive primitive
function main() -> unit = {
  assert(_tmod_int_positive(7, 2) == 1);
  assert(_tmod_int_positive(6, 3) == 0);
  assert(_tmod_int_positive(18446744073709551617, 4294967296) == 1);
}
