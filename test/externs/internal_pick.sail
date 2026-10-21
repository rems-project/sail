default Order dec

$include <prelude.sail>

// Test for the internal_pick primitive
function main() -> unit = {
  let x : int = internal_pick([|1, 2, 3|]);
  assert(x == 1 | x == 2 | x == 3);
  let y : int = internal_pick([|7|]);
  assert(y == 7);
}
