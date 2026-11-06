default Order dec

$include <prelude.sail>
$include <smt.sail>

// Test for the abs_int_atom primitive
function main() -> unit = {
  assert(abs_int_atom(-5) == 5);
  assert(abs_int_atom(5) == 5);
  assert(abs_int_atom(0) == 0);
  assert(abs_int_atom(-18446744073709551616) == 18446744073709551616);
}
