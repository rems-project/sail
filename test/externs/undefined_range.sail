default Order dec

$include <prelude.sail>

// Test for the undefined_range primitive
function main() -> unit = {
  let x : range(3, 7) = undefined_range(3, 7);
  assert(3 <= x & x <= 7);
  let y : range(-5, -5) = undefined_range(-5, -5);
  assert(y == -5);
}
