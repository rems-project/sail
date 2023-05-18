default Order dec

$include <prelude.sail>

val int_fst : ((int, int)) -> int

function int_fst((x, _)) = x

val test : unit -> unit

function test() = {
  let pair: (int, int) = (1, 3);
  print_int("", int_fst(pair))
}
