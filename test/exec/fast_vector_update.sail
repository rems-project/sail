default Order dec

$include <prelude.sail>

let my_vec : vector(3, range(1, 100)) = [3, 2, 1]

val main : unit -> unit

$[test_no_gmp]
function main() = {
  let x : range(0, 2) = 2;
  print_int("", my_vec[x]);
}
