default Order dec

$include <prelude.sail>
$include <option.sail>

val f : unit -> unit

function f() = {
  var x : int = 3;
  x = 4;
}

val g : unit -> unit

function g() = {
  var x : int = 2;
  f();
  print_int("x (in g) = ", x);
}

val main : unit -> unit

function main() = g()
