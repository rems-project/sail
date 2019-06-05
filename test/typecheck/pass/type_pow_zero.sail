default Order dec

$include <flow.sail>

/* Run this test with CVC4, as we want to test that 1 - 1 gets
simplified, and 2 ^ 0 evaluates directly to 1. CVC4 doesn't deal with
power unlike z3, so by using it we ensure we check this. */
$option -smt_solver cvc4

function test() -> unit = {
  _prove(constraint(2 ^ (1 - 1) == 1))
}
