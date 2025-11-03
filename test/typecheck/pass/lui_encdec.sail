default Order dec

$include <vector.sail>

union instruction = {
  LUI : bitvector(6)
}

val encdec : instruction <-> bitvector(11)
scattered mapping encdec

mapping clause encdec = LUI(imm)
  <-> 0b011 @ imm[5] : bitvector(1) @ imm[4..0] : bitvector(5) @ 0b01
  when imm != 0b000000

end encdec
