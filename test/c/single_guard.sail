default Order dec

$include <prelude.sail>

val "print_endline" : string -> unit

val test : unit -> unit

function test(_ if true) = {
  print_endline("In test")
}

function main() -> unit = {
  print_endline("In main");
  test()
}