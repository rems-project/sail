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

type labels = list((string, bits(64)))

val assembly : (bits(64), labels) -> string <-> ast

mapping assembly(offset, labels) = {
  "str" ^ spc() ^ t <- wreg_name() ^ sep() ^ "[" ^ n <- xreg_name() ^ "]"
    <->
  LoadRegister(n, t, 0, AccType_NORMAL, MemOp_STORE, bitzero, bitzero, bitzero, ExtendType_UXTB, 0, 32, 64),

  "ldr" ^ spc() ^ t <- wreg_name() ^ sep() ^ "[" ^ n <- xreg_name() ^ "]"
    <->
  LoadRegister(n, t, 0, AccType_NORMAL, MemOp_LOAD, bitzero, bitzero, bitzero, ExtendType_UXTB, 0, 32, 64),

  "mov" ^ spc() ^ d <- wreg_name() ^ sep() ^ hash() ^ imm <- bits(64)
    <->
  LogicalImmediate(d, 0, 64, bitzero, LogicalOp_ORR, imm)
}
