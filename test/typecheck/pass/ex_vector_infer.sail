default Order dec

$include <prelude.sail>

register R : bool

register X : bits(32)

val test : unit -> {'n 'm, 'n > 1 & 'n == 'm. vector('n, bits('m))}

function test() = {
  if R then {
    [0b00, 0b11]
  } else {
    [match X { _ => 0b000 }, 0b001, 0b100]
  }
}
