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

val run : unit -> unit effect {escape}

function run () = {
  assert(foo(One) == Two);
  assert(foo(Two) == Two);
  assert(foo(Three) == Three);
}
