default Order dec

$include <prelude.sail>

val f : (int, int) -> int

function f(x) = {
  match x {
    (y, z) => y + z
  }
}

function main() : unit -> unit = {
  print_int("", f(2, 3));
}