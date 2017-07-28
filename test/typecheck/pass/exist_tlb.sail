
(* Minimal prelude *)

val forall Num 'n, Num 'm, Num 'o, Num 'p, Order 'ord.
    vector<'o, 'n, 'ord, bit> -> vector<'p, 'm, 'ord, bit> effect pure extz

val forall Num 'n, Num 'm, Num 'o, Num 'p, Order 'ord.
    vector<'o, 'n, 'ord, bit> -> vector<'p, 'm, 'ord, bit> effect pure exts

overload EXTZ [extz]
overload EXTS [exts]

val forall Num 'n, Num 'o, Order 'ord.
    (vector<'o, 'n, 'ord, bit>, vector<'o, 'n, 'ord, bit>) -> vector<'o, 'n, 'ord, bit> effect pure add_vec

overload (deinfix +) [add_vec]

val bool -> bool effect pure bool_not
overload ~ [bool_not]

(* MIPS spec subset *)

default Order dec

register (bit[1])   CP0LLBit
register (bit[64])  CP0LLAddr

typedef MemAccessType = enumerate {Instruction; LoadData; StoreData}

typedef regno = bit[5]                      (* a register number *)
typedef imm16 = bit[16]                     (* 16-bit immediate *)

typedef Exception = enumerate
{
   Int; TLBMod; TLBL; TLBS; AdEL; AdES; Sys; Bp; ResI; CpU; Ov; Tr; C2E; C2Trap;
   XTLBRefillL; XTLBRefillS; XTLBInvL; XTLBInvS; MCheck
}

typedef WordType = enumerate {B; H; W; D}

val bit[5] -> bit[64] effect {rreg} rGPR
val (bit[64], WordType) -> bool effect pure isAddressAligned
val forall Type 'o. (Exception, bit[64]) -> 'o effect pure SignalExceptionBadAddr

val WordType -> exist 'r, 'r in {1,2,4,8}. [:'r:] effect pure wordWidthBytes

function wordWidthBytes w = switch w {
  case B -> 1
  case H -> 2
  case W -> 4
  case D -> 8
}

val forall Nat 'n. (bit[64], [:'n:]) -> bit[8 * 'n] effect {rmem} MEMr_reserve_wrapper
val forall Nat 'n. (bit[64], [:'n:]) -> bit[8 * 'n] effect {rmem} MEMr_wrapper
val (bit[5], bit[64]) -> unit effect {wreg} wGPR

function bit[64] addrWrapper((bit[64]) addr, (MemAccessType) accessType, (WordType) width) = addr

function (bit[64]) TLBTranslate ((bit[64]) vAddr, (MemAccessType) accessType) = vAddr

scattered typedef ast = const union

val ast -> unit effect {rmem, rreg, wreg} execute

scattered function unit execute

union ast member (WordType, bool, bool, regno, regno, imm16) Load

function clause execute (Load(width, signed, linked, base, rt, offset)) =
  {
    (bit[64]) vAddr := addrWrapper(EXTS(offset) + rGPR(base), LoadData, width);
    if ~ (isAddressAligned(vAddr, width)) then
      (SignalExceptionBadAddr(AdEL, vAddr)) (* unaligned access *)
    else
      let pAddr = (TLBTranslate(vAddr, LoadData)) in
          {
	    (exist 't, 't in {1,2,4,8}. bit[8 * 't]) memResult := if linked then
                {
                  CP0LLBit  := 0b1;
                  CP0LLAddr := pAddr;
                  MEMr_reserve_wrapper(pAddr, wordWidthBytes(width));
                }
              else
                MEMr_wrapper(pAddr, wordWidthBytes(width));
            if (signed) then
              wGPR(rt) := EXTS(memResult)
            else
              wGPR(rt) := EXTZ(memResult)
          }
  }

end ast
end execute
