default Order dec
$include <prelude.sail>

val main : unit -> unit

function main() = {
  var x = 0xAAAA_BBBB;
  print_bits("x = ", x[33 >.. 0]);
  print_bits("", x[32 >.. 16]);
  print_bits("", x[16 >.. 0]);
}
