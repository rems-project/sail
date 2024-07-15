default Order dec

$include <prelude.sail>

$[sv_module]
val "print_endline" : string -> unit

register R : nat = 0

register T : int

function main() -> unit = {
  print_endline("ok");
}
