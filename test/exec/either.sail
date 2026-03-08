default Order dec

$include <prelude.sail>

union either('a: Type, 'b: Type) = {
  Left: 'a,
  Right: 'b,
}

val foo : forall ('a: Type) ('b: Type). 'a -> either('a, 'b)

function foo(x) = Left(x)

val main : unit -> unit

function main() = {
    let x: int(5) = 5;
    let y: either(int(5), int) = foo(x);
    match y {
      Left(a) => print_int("left = ", a),
      Right(b) => print_int("right = ", b),
    }
}

