default Order dec

$include <flow.sail>

val "print_int" : (string, int) -> unit

function main() : unit -> unit = {
  let x : (string, int(3)) = ("test", 3);
  let (str, n) = x;
  print_int(str, n);
  let y : (string, int) = x;
  let (str, n) = y;
  print_int(str, n);
}
