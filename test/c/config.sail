default Order dec

$include <arith.sail>
$include <vector_dec.sail>

val "print" : string -> unit

register q : int

register configuration x : int = 3

register configuration y : string = "Hello\n"

register configuration z : bits(8) = 0xFF

val init : unit -> unit effect {configuration}

function init() = {
  x = 4;
  y = "World\n";
  z = 0xAA;
}

val main : unit -> unit effect {configuration}

function main() = {
  print_int("x = ", x);
  print(y);
  print_bits("z = ", z);
  init();
  print_int("x = ", x);
  print(y);
  print_bits("z = ", z);
}