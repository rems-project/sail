default Order dec

$include <prelude.sail>

mapping decimal : int <-> string = {
  forwards n => dec_str(n),
  backwards "x" => 150,
  backwards _ => 1000
}

mapping hexadecimal : int <-> string = {
  forwards n => hex_str(n),
  backwards _ => 199
}

val foo : int <-> string

mapping clause foo =
  n <-> decimal(n)
when
  100 <= n & n <= 200

mapping clause foo =
  n <-> hexadecimal(n)

val main : unit -> unit

function main() = {
  print_endline(foo(0));
  print_endline(foo(100));
  print_endline(foo(200));
  print_endline(foo(300));
  print_int("", foo("x"));
  print_int("", foo("y"))
}
