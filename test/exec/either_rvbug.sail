default Order dec

$include <prelude.sail>
$include <string.sail>

union E = {
  E_A : unit,
  E_B : unit,
}

// Testing that things work as expected when the type parameter order differs to usage within typedef
union either('b: Type, 'a: Type) = {
  Left: 'a,
  Right: 'b,
}

val foo : unit -> either(E, bits(32))

function foo() = {
  Right(E_A())
}

val main : unit -> unit

function main() = {
  let x = foo();
  match x {
    Right(E_B()) => print_endline("E_B"),
    Right(E_A()) => print_endline("E_A"),
    Left(b) => print_bits("b = ", b),
  };
  print_endline("ok");
  ()
}
