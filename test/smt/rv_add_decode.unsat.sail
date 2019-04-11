default Order dec

$include <prelude.sail>

type regbits = bits(5)

enum iop = {RISCV_ADDI, RISCV_SLTI, RISCV_SLTIU, RISCV_XORI, RISCV_ORI, RISCV_ANDI}

scattered union ast

union clause ast = ITYPE : (bits(12), regbits, regbits, iop)

val decode : bits(32) -> option(ast) effect pure

function clause decode imm : bits(12) @ rs1 : regbits @ 0b000 @ rd : regbits @ 0b0010011
  = Some(ITYPE(imm, rs1, rd, RISCV_ADDI))

function clause decode _ = None()

$property
function prop(imm:  bits(12), rs1: regbits, rd: regbits) -> bool = {
  match decode(imm @ rs1 @ 0b000 @ rd @ 0b0010011) {
    Some(ITYPE(_)) => true,
    _ => false
  }
}