default Order dec

$include <prelude.sail>

bitfield B : bits(32) = {
  high : 32 >.. 16,
  low : 16 >.. 0,
  zero_width : 16 >.. 16,
}

val main : unit -> unit

function main() = {
  var x : B = struct { bits = 0xAAAA_BBBB };
  print_bits("", x[high]);
  print_bits("", x[low]);
  assert(x[zero_width] == sail_zeros(0));
  print_bits("", [x with low = 0xCCCC].bits);
  x[low] = 0xDDDD;
  x[zero_width] = sail_zeros(0);
  print_bits("", x[low]);
}
