default Order dec

$include <prelude.sail>
$include <string.sail>

enum test_enum = A | B | C | D | E | F

function foo (a : bool, b : bool, c : bool) -> option(test_enum) =
  match (a, b, c) {
    (false, false, false) => Some(A),
    (true, false, false)  => Some(B),
    (true, true, false)   => Some(C),
    (false, false, true)  => Some(D),
    (true, false, true)   => Some(E),
    (true, true, true)    => Some(F),
    (false, true, false)  => None(),
    (false, true, true)   => None()
  }

val main : unit -> unit

function main() = {
  let x = foo(false, false, false);
  match x {
    Some(A) => print_endline("ok"),
    _ => (),
  }
}
