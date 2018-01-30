$include <flow.sail>

val extz : forall ('n : Int) ('m : Int) ('ord : Order).
  vector('n, 'ord, bit) -> vector('m, 'ord, bit)

val exts : forall ('n : Int) ('m : Int) ('ord : Order).
  vector('n, 'ord, bit) -> vector('m, 'ord, bit)

overload EXTZ = {extz}

overload EXTS = {exts}

val add_vec : forall ('n : Int) ('ord : Order).
  (vector('n, 'ord, bit), vector('n, 'ord, bit)) -> vector('n, 'ord, bit)

overload operator + = {add_vec}

val bool_not : bool -> bool

overload ~ = {bool_not}

default Order dec

register CP0LLBit : vector(1, dec, bit)

register CP0LLAddr : vector(64, dec, bit)

enum MemAccessType = {Instruction, LoadData, StoreData}

type regno = vector(5, dec, bit)

type imm16 = vector(16, dec, bit)

enum Exception = {
  EInt,
  TLBMod,
  TLBL,
  TLBS,
  AdEL,
  AdES,
  Sys,
  Bp,
  ResI,
  CpU,
  Ov,
  Tr,
  C2E,
  C2Trap,
  XTLBRefillL,
  XTLBRefillS,
  XTLBInvL,
  XTLBInvS,
  MCheck
}

enum WordType = {B, H, W, D}

val rGPR : vector(5, dec, bit) -> vector(64, dec, bit) effect {rreg}

val isAddressAligned : (vector(64, dec, bit), WordType) -> bool

val SignalExceptionBadAddr : forall ('o : Type).
  (Exception, vector(64, dec, bit)) -> 'o

val wordWidthBytes : WordType -> {|1, 2, 4, 8|}

function wordWidthBytes w = match w {
  B => 1,
  H => 2,
  W => 4,
  D => 8
}

val MEMr_reserve_wrapper : forall ('n : Int).
  (vector(64, dec, bit), atom('n)) -> vector(8 * 'n, dec, bit) effect {rmem}

val MEMr_wrapper : forall ('n : Int).
  (vector(64, dec, bit), atom('n)) -> vector(8 * 'n, dec, bit) effect {rmem}

val wGPR : (vector(5, dec, bit), vector(64, dec, bit)) -> unit effect {wreg}

val addrWrapper : (vector(64, dec, bit), MemAccessType, WordType) -> vector(64, dec, bit)

function addrWrapper (addr : vector(64, dec, bit), accessType : MemAccessType, width : WordType) = addr

val TLBTranslate : (vector(64, dec, bit), MemAccessType) -> vector(64, dec, bit)

function TLBTranslate (vAddr : vector(64, dec, bit), accessType : MemAccessType) = vAddr

union ast = {Load : (WordType, bool, bool, regno, regno, imm16)}

val execute : ast -> unit effect {rmem, rreg, wreg}

function execute Load(width, signed, linked, base, rt, offset) = {
  vAddr : vector(64, dec, bit) = addrWrapper(EXTS(offset) + rGPR(base), LoadData, width);
  if ~(isAddressAligned(vAddr, width)) then SignalExceptionBadAddr(AdEL, vAddr) else let pAddr = TLBTranslate(vAddr, LoadData) in {
    memResult : {'t, 't in {1, 2, 4, 8}. vector(8 * 't, dec, bit)} = if linked then {
      CP0LLBit = 0b1;
      CP0LLAddr = pAddr;
      MEMr_reserve_wrapper(pAddr, wordWidthBytes(width))
    } else MEMr_wrapper(pAddr, wordWidthBytes(width));
    if signed then wGPR(rt) = EXTS(memResult)
    else wGPR(rt) = EXTZ(memResult)
  }
}
