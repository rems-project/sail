default Order dec

$include <string.sail>

val multi_line : unit -> unit

function multi_line() = {
  print_endline("Hello, \
                 World!");
  // Is equivalent to
  print_endline("Hello, World!")
}

val test : unit -> unit

function test() = {
  print_endline("\'");
  print_endline("'")
}
