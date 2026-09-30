default Order dec

$include <prelude.sail>

// Test for the undefined_bool primitive
function main() -> unit = {
  let b : bool = undefined_bool();
  assert(b | not_bool(b));
}
