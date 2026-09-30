default Order dec

$include <prelude.sail>

// Test for the tdiv_int primitive
function main() -> unit = {
  // Division truncates towards zero
  assert(tdiv_int(7, 2) == 3);
  assert(tdiv_int(-7, 2) == -3);
  assert(tdiv_int(7, -2) == -3);
  assert(tdiv_int(-7, -2) == 3);
  assert(tdiv_int(6, 3) == 2);
  assert(tdiv_int(18446744073709551616, 4294967296) == 4294967296);
}
