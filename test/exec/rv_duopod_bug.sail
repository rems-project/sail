default Order dec

$include <prelude.sail>

val rX : int -> bits(64)

function rX 0 = sail_zeros(64)
and rX (r if r > 0) = sail_ones(64)

function main() -> unit = {
  print_bits("0 ", rX(0));
  print_bits("1 ", rX(1))
}
