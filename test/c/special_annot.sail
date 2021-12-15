$sail_internal

union option ('a : Type) = {
  None : unit,
  Some : 'a
}

val test : forall ('a : Type). 'a -> option('a)

function test(x) =
  let y : 'a = x in Some(y)

val "print_endline" : string -> unit

val main : unit -> unit

function main() = {
  let Some(y) = test("string");
  print_endline(y)
}