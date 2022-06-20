default Order dec

$include <prelude.sail>

type xlen       : Int  = 32
type xlen_bytes : Int  = 4
type xlenbits   : Type = bits(xlen)

type regno ('n : Int), 0 <= 'n < 32 = atom('n)
type regbits = bits(5)

val regbits_to_regno : bits(5) -> {'n, 0 <= 'n < 32. regno('n)}
function regbits_to_regno b = unsigned(b)

enum iop = {RISCV_ADDI, RISCV_SLTI, RISCV_SLTIU, RISCV_XORI, RISCV_ORI, RISCV_ANDI}

/* Architectural state */
register R1 : xlenbits
register R2 : xlenbits
register R3 : xlenbits
register R4 : xlenbits
register R5 : xlenbits
register R6 : xlenbits
register R7 : xlenbits
register R8 : xlenbits
register R9 : xlenbits
register R10 : xlenbits
register R11 : xlenbits
register R12 : xlenbits
register R13 : xlenbits
register R14 : xlenbits
register R15 : xlenbits
register R16 : xlenbits
register R17 : xlenbits
register R18 : xlenbits
register R19 : xlenbits
register R20 : xlenbits
register R21 : xlenbits
register R22 : xlenbits
register R23 : xlenbits
register R24 : xlenbits
register R25 : xlenbits
register R26 : xlenbits
register R27 : xlenbits
register R28 : xlenbits
register R29 : xlenbits
register R30 : xlenbits
register R31 : xlenbits

/* Getters and setters for X registers (special case for zeros register, x0) */
val rX : forall 'n, 0 <= 'n < 32. regno('n) -> xlenbits effect {rreg}

function rX(r) = {
  if r == 0 then sail_zero_extend(0x0, sizeof(xlen))
  else if r == 1 then R1
  else if r == 2 then R2
  else if r == 3 then R3
  else if r == 4 then R4
  else if r == 5 then R5
  else if r == 6 then R6
  else if r == 7 then R7
  else if r == 8 then R8
  else if r == 9 then R9
  else if r == 10 then R10
  else if r == 11 then R11
  else if r == 12 then R12
  else if r == 13 then R13
  else if r == 14 then R14
  else if r == 15 then R15
  else if r == 16 then R16
  else if r == 17 then R17
  else if r == 18 then R18
  else if r == 19 then R19
  else if r == 20 then R20
  else if r == 21 then R21
  else if r == 22 then R22
  else if r == 23 then R23
  else if r == 24 then R24
  else if r == 25 then R25
  else if r == 26 then R26
  else if r == 27 then R27
  else if r == 28 then R28
  else if r == 29 then R29
  else if r == 30 then R30
  else R31
}

val wX : forall 'n, 0 <= 'n < 32. (regno('n), xlenbits) -> unit effect {wreg}

function wX(r, v) = {
  if r == 0 then ()
  else if r == 1 then R1 = v
  else if r == 2 then R2 = v
  else if r == 3 then R3 = v
  else if r == 4 then R4 = v
  else if r == 5 then R5 = v
  else if r == 6 then R6 = v
  else if r == 7 then R7 = v
  else if r == 8 then R8 = v
  else if r == 9 then R9 = v
  else if r == 10 then R10 = v
  else if r == 11 then R11 = v
  else if r == 12 then R12 = v
  else if r == 13 then R13 = v
  else if r == 14 then R14 = v
  else if r == 15 then R15 = v
  else if r == 16 then R16 = v
  else if r == 17 then R17 = v
  else if r == 18 then R18 = v
  else if r == 19 then R19 = v
  else if r == 20 then R20 = v
  else if r == 21 then R21 = v
  else if r == 22 then R22 = v
  else if r == 23 then R23 = v
  else if r == 24 then R24 = v
  else if r == 25 then R25 = v
  else if r == 26 then R26 = v
  else if r == 27 then R27 = v
  else if r == 28 then R28 = v
  else if r == 29 then R29 = v
  else if r == 30 then R30 = v
  else R31 = v
}

val rX_bits : bits(5) -> xlenbits effect {rreg}
function rX_bits(r) = rX(regbits_to_regno(r))
val wX_bits : (bits(5), xlenbits) -> unit effect {wreg}
function wX_bits(r,v) = wX(regbits_to_regno(r), v)

overload X = {rX, wX, rX_bits, wX_bits}

scattered union ast

union clause ast = ITYPE : (bits(12), regbits, regbits, iop)

$property
function prop(r: regbits, v: xlenbits) -> bool = {
  X(r) = v;
  X(r) == v | r == 0b00000
}
