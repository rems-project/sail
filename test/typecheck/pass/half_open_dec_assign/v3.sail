default Order dec
$include <prelude.sail>

val main : unit -> unit

function main() = {
  var x = 0xFFFF_FFFF;
  x[0 ..< 0] = sail_zeros(0);
  x[32 >.. 15] = 0xAAAA;
  print_bits("x = ", x);
}
