default Order dec
$include <prelude.sail>

/* Tests for a bug where Sail would complain that a lone declaring
assignment in a block had unclear scope.  While this isn't terribly
useful, it has appeared in an Arm model (possibly due to some
preprocessing?). */

val g : unit -> int

function g() = {
  print_endline("g called");
  5
}

val f : int -> int

function f(x) = {
  {
    y : int = g()
  };
  x
}
