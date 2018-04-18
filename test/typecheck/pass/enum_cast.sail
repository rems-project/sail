default Order dec

$include <prelude.sail>

enum E = {A, B, C}

val cast E_cast : E -> {'e, 0 <= 'e <= 2. atom('e)}
function E_cast(e) = num_of_E(e)

val main : unit -> unit

function main() = {
  let x : vector(3, dec, int) = [1, 2, 3];
  print_int("x = ", x[B])
}
