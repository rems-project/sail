default Order dec

$include <prelude.sail>

val main : unit -> unit

function main() = {
  var v1 : int = 0;
  var v2 : int = 0;
  var v3 : int = 0;
  var v4 : int = 0;
  (v1, ((v2, v3), v4)) = (1, ((2, 3), 4));
  print_int("v1 = ", v1);
  print_int("v2 = ", v2);
  print_int("v3 = ", v3);
  print_int("v4 = ", v4);
}
