default Order dec

$include <prelude.sail>

// Test for the and_bool primitive
function main() -> unit = {
  assert(and_bool(true, true));
  assert(not_bool(and_bool(true, false)));
  assert(not_bool(and_bool(false, true)));
  assert(not_bool(and_bool(false, false)));
}
