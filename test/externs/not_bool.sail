default Order dec

$include <prelude.sail>

// Test for the not_bool primitive
function main() -> unit = {
  assert(not_bool(false));
  assert(not_bool(not_bool(true)));
  let b : bool = true;
  assert(not_bool(b) == false);
}
