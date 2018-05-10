/* This is a regression test for a bug where an option type in a
struct would cause the ocaml backend to generate a bad string_of
function for the struct */

struct test = {
  test1 : int,
  test2 : option(int)
}

val main : unit -> unit

function main () = ()