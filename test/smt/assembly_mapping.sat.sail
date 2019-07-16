default Order dec

$include <prelude.sail>
$include <string.sail>
$include <mapping.sail>

type regbits  = bits(5)

val reg_name : bits(5) <-> string
mapping reg_name = {
  0b00000 <-> "zero",
  0b00001 <-> "ra",
  0b00010 <-> "sp",
  0b00011 <-> "gp",
  0b00100 <-> "tp",
  0b00101 <-> "t0",
  0b00110 <-> "t1",
  0b00111 <-> "t2",
  0b01000 <-> "fp",
  0b01001 <-> "s1",
  0b01010 <-> "a0",
  0b01011 <-> "a1",
  0b01100 <-> "a2",
  0b01101 <-> "a3",
  0b01110 <-> "a4",
  0b01111 <-> "a5",
  0b10000 <-> "a6",
  0b10001 <-> "a7",
  0b10010 <-> "s2",
  0b10011 <-> "s3",
  0b10100 <-> "s4",
  0b10101 <-> "s5",
  0b10110 <-> "s6",
  0b10111 <-> "s7",
  0b11000 <-> "s8",
  0b11001 <-> "s9",
  0b11010 <-> "s10",
  0b11011 <-> "s11",
  0b11100 <-> "t3",
  0b11101 <-> "t4",
  0b11110 <-> "t5",
  0b11111 <-> "t6"
}

enum uop = RISCV_LUI | RISCV_AUIPC

mapping utype_mnemonic : uop <-> string = {
  RISCV_LUI   <-> "lui",
  RISCV_AUIPC <-> "auipc"
}

scattered union ast

val assembly : ast <-> string

union clause ast = UTYPE : (bits(20), regbits, uop)

mapping clause assembly = UTYPE(imm, rd, op)
  <-> utype_mnemonic(op) ^ spc() ^ reg_name(rd) ^ sep() ^ hex_bits_20(imm)

$counterexample
function prop(x: string) -> bool = {
  not_bool(assembly(UTYPE(0x00000, 0b00000, RISCV_LUI)) == x)
}
