default Order dec

$include <prelude.sail>

let x : int = {
  assert(true);
  3
}

val main : unit -> unit

function main() = {
  print_int("x = ", x)
}
