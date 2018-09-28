default Order dec
$include <vector_dec.sail>
$include <string.sail>

val main : unit -> unit
function main () = {
  let x1 = 0xffffffffffffffff;
  let x2 : int = unsigned(x1);
  let x3 : int = if false then signed(x1) else unsigned(x1);
  print_int("x2:", x2);
  print_int("x3:", x3);
}