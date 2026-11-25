default Order dec

$include <prelude.sail>

val main : unit -> unit

function main() = {
  let v : vector(4, bits(1)) = [0b1, 0b0, 0b1, 0b1];
  print_bits("v[0] = ", v[0])
}
