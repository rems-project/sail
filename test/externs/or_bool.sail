default Order dec

$include <prelude.sail>

// Test for the or_bool primitive
function main() -> unit = {
  assert(or_bool(true, true));
  assert(or_bool(true, false));
  assert(or_bool(false, true));
  assert(not_bool(or_bool(false, false)));
}
