default Order dec

$include <prelude.sail>

// Test for the eq_string primitive
function main() -> unit = {
  assert(eq_string("abc", "abc"));
  assert(eq_string("", ""));
  assert(not_bool(eq_string("abc", "abd")));
  assert(not_bool(eq_string("abc", "ab")));
}
