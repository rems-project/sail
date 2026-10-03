default Order dec
$include <prelude.sail>

$[enum_number_conversions { to_enum = bar, from_enum = baz }]
enum Foo = A | B | C

val main : unit -> unit

function main() = {
  print_int("A = ", baz(A));
  print_int("B = ", baz(B));
  print_int("C = ", baz(C));

  match (bar(0), bar(1), bar(2)) {
    (A, B, C) => print_endline("ok"),
    _ => (),
  }
}
