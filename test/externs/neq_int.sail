default Order dec

$include <prelude.sail>

// Test for the neq_int primitive
function main() -> unit = {
  assert(neq_int(5, 6));
  assert(not_bool(neq_int(5, 5)));
  assert(neq_int(18446744073709551616, 18446744073709551617));
}
