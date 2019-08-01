$include <flow.sail>

val extz : forall ('n : Int) ('m : Int) ('ord : Order).
  bitvector('n, 'ord) -> bitvector('m, 'ord)

val exts : forall ('n : Int) ('m : Int) ('ord : Order).
  bitvector('n, 'ord) -> bitvector('m, 'ord)

overload EXTZ = {extz}

overload EXTS = {exts}

val add_vec : forall ('n : Int) ('ord : Order).
  (bitvector('n, 'ord), bitvector('n, 'ord)) -> bitvector('n, 'ord)

overload operator + = {add_vec}

val bool_not : bool -> bool

overload ~ = {bool_not}

default Order dec

register CP0LLBit : bitvector(1, dec)

register CP0LLAddr : bitvector(64, dec)

enum MemAccessType = {Instruction, LoadData, StoreData}

type regno = bitvector(5, dec)

type imm16 = bitvector(16, dec)

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

val rGPR : bitvector(5, dec) -> bitvector(64, dec) effect {rreg}

val isAddressAligned : (bitvector(64, dec), WordType) -> bool

val SignalExceptionBadAddr : forall ('o : Type).
  (Exception, bitvector(64, dec)) -> 'o

val wordWidthBytes : WordType -> {|1, 2, 4, 8|}

function wordWidthBytes w = match w {
  B => 1,
  H => 2,
  W => 4,
  D => 8
}

val MEMr_reserve_wrapper : forall ('n : Int).
  (bitvector(64, dec), atom('n)) -> bitvector(8 * 'n, dec) effect {rmem}

val MEMr_wrapper : forall ('n : Int).
  (bitvector(64, dec), atom('n)) -> bitvector(8 * 'n, dec) effect {rmem}

val wGPR : (bitvector(5, dec), bitvector(64, dec)) -> unit effect {wreg}

val addrWrapper : (bitvector(64, dec), MemAccessType, WordType) -> bitvector(64, dec)

function addrWrapper (addr : bitvector(64, dec), accessType : MemAccessType, width : WordType) = addr

val TLBTranslate : (bitvector(64, dec), MemAccessType) -> bitvector(64, dec)

function TLBTranslate (vAddr : bitvector(64, dec), accessType : MemAccessType) = vAddr

union ast = {Load : (WordType, bool, bool, regno, regno, imm16)}

val execute : ast -> unit effect {rmem, rreg, wreg}

function execute Load(width, signed, linked, base, rt, offset) = {
  vAddr : bitvector(64, dec) = addrWrapper(EXTS(offset) + rGPR(base), LoadData, width);
  if ~(isAddressAligned(vAddr, width)) then SignalExceptionBadAddr(AdEL, vAddr) else let pAddr = TLBTranslate(vAddr, LoadData) in {
    memResult : {'t, 't in {1, 2, 4, 8}. bitvector(8 * 't, dec)} = if linked then {
      CP0LLBit = 0b1;
      CP0LLAddr = pAddr;
      MEMr_reserve_wrapper(pAddr, wordWidthBytes(width))
    } else MEMr_wrapper(pAddr, wordWidthBytes(width));
    if signed then wGPR(rt) = EXTS(memResult)
    else wGPR(rt) = EXTZ(memResult)
  }
}
