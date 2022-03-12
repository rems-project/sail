default Order dec

$include <vector_dec.sail>

enum E = A | B | C | D | E | F

val foo : E -> bits(3)

val testm : E <-> bits(3)

mapping clause testm = A <-> 0b000
mapping clause testm = B <-> 0b001
mapping clause testm = C <-> 0b010
mapping clause testm = D <-> 0b011
mapping clause testm = E <-> 0b100
mapping clause testm = F <-> 0b111

val main : unit -> unit

function main() = {
  let _ = testm_forwards(A);
  ()
}

function foo(e) = testm(e)
