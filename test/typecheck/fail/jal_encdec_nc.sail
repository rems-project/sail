default Order dec

$include <prelude.sail>

scattered union instruction

val encdec : instruction <-> bits(32)

scattered mapping encdec

union clause instruction = JAL : (bits(21), bits(5))

mapping clause encdec = JAL(imm : bits(20) @ 0b0, rd)
  <-> imm[20] @ imm[9..0] @ imm[11] @ imm[19..12] @ rd @ 0b1101111
