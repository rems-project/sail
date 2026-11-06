default Order dec

$include <prelude.sail>

// Test for the max_int primitive
function main() -> unit = {
  assert(max_int(3, 5) == 5);
  assert(max_int(5, 3) == 5);
  assert(max_int(-3, -5) == -3);
  assert(max_int(4, 4) == 4);
  assert(max_int(18446744073709551616, 1) == 18446744073709551616);
}
