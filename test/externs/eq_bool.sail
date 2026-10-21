default Order dec

$include <prelude.sail>

// Test for the eq_bool primitive
function main() -> unit = {
  assert(eq_bool(true, true));
  assert(eq_bool(false, false));
  assert(not_bool(eq_bool(true, false)));
  assert(not_bool(eq_bool(false, true)));
}
