default Order dec

$include <prelude.sail>

// Test for the eq_int primitive
function main() -> unit = {
  assert(eq_int(5, 5));
  assert(not_bool(eq_int(5, 6)));
  assert(eq_int(-5, -5));
  assert(eq_int(18446744073709551616, 18446744073709551616));
  assert(not_bool(eq_int(18446744073709551616, 18446744073709551617)));
}
