default Order dec
$include <prelude.sail>

// Recent Lean versions with the legacy do-elaborator forbid certain syntactic
// forms which we used to generate.

register R1 : int = 123

function f(x : int) -> int = x

function g(x : int, b : bool) -> int = {
  let y : int = f (if b then R1 else 456);
  x + y
}
