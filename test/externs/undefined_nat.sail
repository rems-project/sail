default Order dec

$include <prelude.sail>

// Test for the undefined_nat primitive
function main() -> unit = {
  let x : nat = undefined_nat();
  assert(x >= 0);
}
