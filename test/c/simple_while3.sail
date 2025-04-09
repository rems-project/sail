default Order dec

$include <prelude.sail>

register i : int = 0

val main : unit -> unit

function main() = {
  while i < 10 do {
    print_int("i = ", i);
    i = i + 1
  }
}
