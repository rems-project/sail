default Order dec

$include <prelude.sail>

// Test for the eq_unit primitive
function main() -> unit = {
  assert(eq_unit((), ()));
}
