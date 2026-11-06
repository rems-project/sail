default Order dec

$include <prelude.sail>

// Test for the sub_atom primitive
function main() -> unit = {
  assert(sub_atom(5, 3) == 2);
  assert(sub_atom(3, 5) == -2);
  assert(sub_atom(18446744073709551616, 1) == 18446744073709551615);
  assert(sub_atom(-9223372036854775808, 1) == -9223372036854775809);
}
