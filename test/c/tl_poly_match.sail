default Order dec

$include <prelude.sail>

val "print" : string -> unit

val f : option(int) -> string

function f(Some(_)) = "1\n"
and f(None()) = "2\n"

val main : unit -> unit

function main() = {
  print(f(Some(3)));
  print(f(None()));
}