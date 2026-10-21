default Order dec

$include <prelude.sail>

// Test for the add_atom primitive
function main() -> unit = {
  assert(add_atom(2, 3) == 5);
  assert(add_atom(-7, 3) == -4);
  assert(add_atom(0, 0) == 0);
  assert(add_atom(18446744073709551615, 1) == 18446744073709551616);
  assert(add_atom(-9223372036854775808, -1) == -9223372036854775809);
}
