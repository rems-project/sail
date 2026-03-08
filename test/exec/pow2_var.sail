default Order dec

$include <arith.sail>

register R : int

register T : range(0, 5)

val main : unit -> unit

$[jib_debug]
function main() = {
  let x = 2 ^ 0;
  let y = 2 ^ 1;
  R = 3;
  let z = 2 ^ R;
  T = 4;
  let w = 2 ^ T;
  print_int("x = ", x);
  print_int("y = ", y);
  print_int("z = ", z);
  print_int("w = ", w);
}
