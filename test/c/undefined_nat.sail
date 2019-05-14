default Order dec

$include <prelude.sail>

val "print_endline" : string -> unit

register R : nat

register T : int

function main() -> unit = {
  print_endline("ok");
}