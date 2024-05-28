default Order dec
$include <prelude.sail>

val main : unit -> unit

function main() = {
  var x = 0xFFFF_FFFF;
  x[32 >.. 16] = 0xAAAA;
  x[16 >.. 0] = 0xBBBB;
  x[0 >.. 0] = sail_zeros(0);
  print_bits("x = ", x);
}
