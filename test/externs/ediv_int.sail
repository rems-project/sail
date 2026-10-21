default Order dec

$include <prelude.sail>
$include <smt.sail>

// Test for the ediv_int primitive
function main() -> unit = {
  // Euclidean division: the remainder is always non-negative
  assert(ediv_int(7, 2) == 3);
  assert(ediv_int(-7, 2) == -4);
  assert(ediv_int(7, -2) == -3);
  assert(ediv_int(-7, -2) == 4);
  assert(ediv_int(6, 3) == 2);
  assert(ediv_int(18446744073709551616, 4294967296) == 4294967296);
}
