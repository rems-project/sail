default Order dec

$include <prelude.sail>

enum E = {A, B, C}

val main : unit -> unit

function main() = {
  let x : vector(3, dec, int) = [1, 2, 3];
  print_int("x = ", x[num_of_E(B)])
}
