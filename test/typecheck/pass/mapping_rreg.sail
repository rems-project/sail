default Order dec

$include <prelude.sail>

register enabled : bits(1)

union ast = {
  I: bits(1)
}

val encdec : ast <-> bits(2) effect {rreg}

scattered mapping encdec

mapping clause encdec = I(imm) if enabled == 0b0 <-> 0b0 @ imm if enabled == 0b0

end encdec
