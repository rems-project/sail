
default Order dec

$include <vector_dec.sail>

val main : unit -> unit

function main() = {
  let x : vector(2, dec, bits(8)) = [0xAB, 0xCD];
  print_bits("x[0] = ", x[0]);
  print_bits("x[1] = ", x[1]);
}