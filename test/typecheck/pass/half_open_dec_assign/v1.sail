default Order dec
$include <prelude.sail>

val main : unit -> unit

function main() = {
  var x = 0xFFFF_FFFF;
  x[33 >.. 16] = 0xAAAA;
  x[16 >.. 0] = 0xBBBB;
  print_bits("x = ", x);
}
