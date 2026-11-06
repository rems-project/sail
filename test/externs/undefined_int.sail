default Order dec

$include <prelude.sail>

// Test for the undefined_int primitive
function main() -> unit = {
  let x : int = undefined_int();
  assert(x == x);
}
