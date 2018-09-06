default Order dec

$include <prelude.sail>

val main : unit -> unit

function main() = {
  let x : int = 3;
  print_int("x = ", x);
  let x = x + 2;
  print_int("x = ", x);
  let x = x + 2;
  print_int("x = ", x)
}