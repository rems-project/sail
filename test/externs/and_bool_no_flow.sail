default Order dec

$include <prelude.sail>

// Test for the and_bool_no_flow primitive
function main() -> unit = {
  let t : bool = true;
  let f : bool = false;
  assert(and_bool_no_flow(t, t));
  assert(not_bool(and_bool_no_flow(t, f)));
  assert(not_bool(and_bool_no_flow(f, t)));
  assert(not_bool(and_bool_no_flow(f, f)));
}
