default Order dec

$include <flow.sail>
$include <arith.sail>

val m : unit <-> int(1)

mapping m = {
  () <-> 1
}

val main : unit -> unit

function main() = {
  print_int("m() = ", m());
  m(1)
}