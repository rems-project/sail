$include <flow.sail>

val eq_all = {ocaml: "(fun (x, y) -> x = y)", lem: "eq"} : forall ('a : Type). ('a, 'a) -> bool
overload operator == = {eq_all}


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

val run : unit -> unit

function run () = {
  assert(foo(One) == Two);
  assert(foo(Two) == Two);
  assert(foo(Three) == Three);
}
