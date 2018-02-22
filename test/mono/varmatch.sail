val operator & = "and_bool" : (bool, bool) -> bool
val operator == = {ocaml: "(fun (x, y) -> x = y)", lem: "eq"} : forall ('a : Type). ('a, 'a) -> bool

/* Check that when we case split on a variable that the constant propagation
   handles the default case correctly. */

enum AnEnum = One | Two | Three

val foo : AnEnum -> AnEnum

function foo(x) = {
  match (x) {
  One => Two,
  y => y
  }
}

val run : unit -> bool

function run () = {
  foo(One) == Two &
  foo(Two) == Two &
  foo(Three) == Three
}
