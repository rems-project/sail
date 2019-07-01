$include <mapping.sail>

mapping wreg_name : regex("w[0-9]+") <-> reg_index = {
  "w0" <-> 0,
  "w1" <-> 1,
  "w2" <-> 2,
  "w3" <-> 3,
  "w4" <-> 4,
  "w5" <-> 5,
  "w6" <-> 6,
  "w7" <-> 7,
  "w8" <-> 8,
  "w9" <-> 9,
  "w10" <-> 10,
  "w11" <-> 11,
  "w12" <-> 12,
  "w13" <-> 13,
  "w14" <-> 14,
  "w15" <-> 15,
  "w16" <-> 16,
  "w17" <-> 17,
  "w18" <-> 18,
  "w19" <-> 19,
  "w20" <-> 20,
  "w21" <-> 21,
  "w22" <-> 22,
  "w23" <-> 23,
  "w24" <-> 24,
  "w25" <-> 25,
  "w26" <-> 26,
  "w27" <-> 27,
  "w28" <-> 28,
  "w29" <-> 29,
  "w30" <-> 30,
  "w31" <-> 31
}

mapping xreg_name : regex("x[0-9]+") <-> reg_index = {
  "x0" <-> 0,
  "x1" <-> 1,
  "x2" <-> 2,
  "x3" <-> 3,
  "x4" <-> 4,
  "x5" <-> 5,
  "x6" <-> 6,
  "x7" <-> 7,
  "x8" <-> 8,
  "x9" <-> 9,
  "x10" <-> 10,
  "x11" <-> 11,
  "x12" <-> 12,
  "x13" <-> 13,
  "x14" <-> 14,
  "x15" <-> 15,
  "x16" <-> 16,
  "x17" <-> 17,
  "x18" <-> 18,
  "x19" <-> 19,
  "x20" <-> 20,
  "x21" <-> 21,
  "x22" <-> 22,
  "x23" <-> 23,
  "x24" <-> 24,
  "x25" <-> 25,
  "x26" <-> 26,
  "x27" <-> 27,
  "x28" <-> 28,
  "x29" <-> 29,
  "x30" <-> 30,
  "x31" <-> 31
}

type labels = list((string, int))

val assoc : (list((string, int)), string) -> option(int)

function assoc(map, key) = {
  match map {
    (key', value) :: map if key == key' => Some(value),
    _ :: map => assoc(map, key),
    [||] => None()
  }
}

val label : (int, labels) -> string <-> bits(26)

mapping label(n: int, labels: labels) -> string <-> bits(26) = {
  x <- bits(26) <-> x,
  forwards l => match assoc(labels, l) {
    Some(offset) => get_slice_int(26, offset - n, 0),
    None() => sail_zeros(26)
  }
}

val assembly : (int, labels) -> string <-> ast

mapping assembly(offset, labels) = {
  "str" ^ spc() ^ t <- wreg_name() ^ sep() ^ "[" ^ n <- xreg_name() ^ "]"
    <->
  LoadRegister(n, t, 31, AccType_NORMAL, MemOp_STORE, bitzero, bitzero, bitzero, ExtendType_UXTB, 0, 32, 32),

  "ldr" ^ spc() ^ t <- wreg_name() ^ sep() ^ "[" ^ n <- xreg_name() ^ "]"
    <->
  LoadRegister(n, t, 31, AccType_NORMAL, MemOp_LOAD, bitzero, bitzero, bitzero, ExtendType_UXTB, 0, 32, 32),

  "mov" ^ spc() ^ d <- wreg_name() ^ sep() ^ hash() ^ imm <- bits(32)
    <->
  LogicalImmediate(d, 31, 32, bitzero, LogicalOp_ORR, imm),

  "mov" ^ spc() ^ d <- xreg_name() ^ sep() ^ hash() ^ imm <- bits(64)
    <->
  LogicalImmediate(d, 31, 64, bitzero, LogicalOp_ORR, imm),

  "isb"
    <->
  Barrier(MemBarrierOp_ISB, MBReqDomain_FullSystem, MBReqTypes_All),

  forwards "b" ^ spc() ^ imm26 <- label(offset, labels) => BranchImmediate(BranchType_JMP, SignExtend(imm26 @ 0b00)),
  backwards BranchImmediate(BranchType_JMP, offset) => concat_str("b ", hex_string(offset[27 .. 2])) 
}

function litmus_start(_: unit) -> unit = {
  R0 = 0x0000_0000_0000_0000;
  R1 = 0x0000_0000_0000_0000;
  R2 = 0x0000_0000_0000_0000;
  R3 = 0x0000_0000_0000_0000;
  R4 = 0x0000_0000_0000_0000;
  R5 = 0x0000_0000_0000_0000;
  R6 = 0x0000_0000_0000_0000;
  R7 = 0x0000_0000_0000_0000;
  R8 = 0x0000_0000_0000_0000;
  R9 = 0x0000_0000_0000_0000;
  R10 = 0x0000_0000_0000_0000;
  R11 = 0x0000_0000_0000_0000;
  R12 = 0x0000_0000_0000_0000;
  R13 = 0x0000_0000_0000_0000;
  R14 = 0x0000_0000_0000_0000;
  R15 = 0x0000_0000_0000_0000;
  R16 = 0x0000_0000_0000_0000;
  R17 = 0x0000_0000_0000_0000;
  R18 = 0x0000_0000_0000_0000;
  R19 = 0x0000_0000_0000_0000;
  R20 = 0x0000_0000_0000_0000;
  R21 = 0x0000_0000_0000_0000;
  R22 = 0x0000_0000_0000_0000;
  R23 = 0x0000_0000_0000_0000;
  R24 = 0x0000_0000_0000_0000;
  R25 = 0x0000_0000_0000_0000;
  R26 = 0x0000_0000_0000_0000;
  R27 = 0x0000_0000_0000_0000;
  R28 = 0x0000_0000_0000_0000;
  R29 = 0x0000_0000_0000_0000;
  R30 = 0x0000_0000_0000_0000
}