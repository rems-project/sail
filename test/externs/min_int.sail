default Order dec

$include <prelude.sail>

// Test for the min_int primitive
function main() -> unit = {
  assert(min_int(3, 5) == 3);
  assert(min_int(5, 3) == 3);
  assert(min_int(-3, -5) == -5);
  assert(min_int(4, 4) == 4);
  assert(min_int(-18446744073709551616, 1) == -18446744073709551616);
}
