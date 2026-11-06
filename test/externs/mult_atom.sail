default Order dec

$include <prelude.sail>

// Test for the mult_atom primitive
function main() -> unit = {
  assert(mult_atom(6, 7) == 42);
  assert(mult_atom(-6, 7) == -42);
  assert(mult_atom(-6, -7) == 42);
  assert(mult_atom(0, 7) == 0);
  assert(mult_atom(4294967296, 4294967296) == 18446744073709551616);
}
