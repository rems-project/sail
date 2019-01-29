default Order dec

$include <prelude.sail>

$not_a_valid_pragma test

val "print_endline" : string -> unit

function main((): unit) -> unit = {
  print_endline("test")
}

