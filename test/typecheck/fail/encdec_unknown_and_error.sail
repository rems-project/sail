default Order dec

$include <prelude.sail>

scattered union instr

val encdec : instr <-> bits(32)

scattered mapping encdec

union clause instr = X : bits(21)

mapping clause encdec = X(y @ x @ Z() : bits(1))
  <-> 0xF @ x @ 0x00 @ y
