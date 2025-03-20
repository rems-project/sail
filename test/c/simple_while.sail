default Order dec

$include <prelude.sail>

val main : unit -> unit

function main() = {
  var i : int = 0;
  while i < 10 do {
    print_int("i = ", i);
    i = i + 1
  }
}
