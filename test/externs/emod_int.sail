default Order dec

$include <prelude.sail>
$include <smt.sail>

// Test for the emod_int primitive
function main() -> unit = {
  // Euclidean remainder is always non-negative
  assert(emod_int(7, 2) == 1);
  assert(emod_int(-7, 2) == 1);
  assert(emod_int(7, -2) == 1);
  assert(emod_int(-7, -2) == 1);
  assert(emod_int(6, 3) == 0);
  assert(emod_int(18446744073709551617, 4294967296) == 1);
}
