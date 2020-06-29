default Order dec

$include <prelude.sail>

val "print_endline" : string -> unit

enum foo = {
  Bar,
  Baz
}

val test : (foo, foo) -> bool

function test(x, y) =
  match (x, y) {
    (Baz, Baz) => false,
    (Bar, Bar) => true,
    (_, _)     => false
  }

function main() : unit -> unit = {
  assert(test(Bar, Bar));
  print_endline("ok")
}
