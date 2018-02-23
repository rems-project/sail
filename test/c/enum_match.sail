
val "eq_anything" : forall ('a : Type). ('a, 'a) -> bool

overload operator == = {eq_anything}

val print = "print_endline" : string -> unit

enum test = A | B

function main (() : unit) -> unit = {
  let x = A;
  match x {
    B => print("B"),
    A => print("A")
  }
}