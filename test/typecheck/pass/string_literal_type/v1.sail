default Order dec

$include <prelude.sail>

$option -string_literal_type

val test : string_literal -> unit

function test(s) = print_endline(s)

val main : unit -> unit

function main() = {
  let x : string_literal = "foo";
  let z = "baz";
  test(concat_str(x, z))
}
