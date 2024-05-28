default Order dec
$include <prelude.sail>

val main : unit -> unit

function main() = {
  var x = 0xAAAA_BBBB;
  print_bits("x = ", x[32 >.. 0]);
  print_bits("", x[32 >.. 16]);
  print_bits("", x[16 >.. 0]);
  print_bits("", [x with 32 >.. 16 = 0xCCCC]);
  print_bits("", [x with 32 >.. 16 = 0xCCCC, 7 .. 0 = 0xDD]);
}
