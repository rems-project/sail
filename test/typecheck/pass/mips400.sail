(* New typechecker prelude *)

val cast forall Nat 'n, Nat 'm, Order 'ord. vector<'n,'m,'ord,bit> -> [|0:2**'m - 1|] effect pure unsigned

(* Vector access can't actually be properly polymorphic on vector
   direction because of the ranges being different for each type, so
   we overload it instead *)
val forall Nat 'n, Nat 'l, Type 'a, 'l >= 0. (vector<'n,'l,dec,'a>, [|'n - 'l + 1:'n|]) -> 'a effect pure vector_access_dec
val forall Nat 'n, Nat 'l, Type 'a, 'l >= 0. (vector<'n,'l,inc,'a>, [|'n:'n + 'l - 1|]) -> 'a effect pure vector_access_inc

(* Type safe vector subrange *)
val forall Nat 'n, Nat 'l, Nat 'm, Nat 'o, Type 'a, 'l >= 0, 'm <= 'o, 'o <= 'l.
  (vector<'n,'l,inc,'a>, [:'m:], [:'o:]) -> vector<'m,'o - 'm,inc,'a> effect pure vector_subrange_inc

val forall Nat 'n, Nat 'l, Nat 'm, Nat 'o, Type 'a, 'n >= 'm, 'm >= 'o, 'o >= 'n - 'l + 1.
  (vector<'n,'l,dec,'a>, [:'m:], [:'o:]) -> vector<'m,'m - 'o - 1,dec,'a> effect pure vector_subrange_dec

overload vector_subrange [vector_subrange_inc; vector_subrange_dec]

(* Type safe vector append *)
val forall Nat 'n1, Nat 'l1, Nat 'n2, Nat 'l2, Order 'o, Type 'a, 'l1 >= 0, 'l2 >= 0.
  (vector<'n1,'l1,'o,'a>, vector<'n2,'l2,'o,'a>) -> vector<'n1,'l1 + 'l2,'o,'a> effect pure vector_append

(* Implicit register dereferencing *)
val cast forall Type 'a. register<'a> -> 'a effect pure reg_deref

overload vector_access [vector_access_inc; vector_access_dec]

(* Bitvector duplication *)
val forall Nat 'n. (bit, [:'n:]) -> vector<'n - 1,'n,dec,bit> effect pure duplicate

val forall Nat 'n, Nat 'm, Nat 'o, Order 'ord.
  (vector<'o,'n,'ord,bit>, [:'m:]) -> vector<'o,'m*'n,'ord,bit> effect pure duplicate_bits

overload (deinfix ^^) [duplicate; duplicate_bits]

(* Bitvector extension *)
val forall Nat 'n, Nat 'm, Nat 'o, Nat 'p, Order 'ord.
    vector<'o, 'n, 'ord, bit> -> vector<'p, 'm, 'ord, bit> effect pure extz

val forall Nat 'n, Nat 'm, Nat 'o, Nat 'p, Order 'ord.
    vector<'o, 'n, 'ord, bit> -> vector<'p, 'm, 'ord, bit> effect pure exts

overload EXTZ [extz]
overload EXTS [exts]

val forall Type 'a, Nat 'n, Nat 'm, Nat 'o, Nat 'p, Order 'ord, 'm >= 'o.
    vector<'n, 'm, 'ord, 'a> -> vector<'p, 'o, 'ord, 'a> effect pure mask

(* Adjust the start index of a decreasing bitvector *)
val cast forall Nat 'n, Nat 'm, Nat 'o, 'n >= 'm - 1, 'o >= 'm - 1.
  vector<'n,'m,dec,bit> -> vector<'o,'m,dec,bit>
  effect pure adjust_dec

(* Various casts from 0 and 1 to bitvectors *)
val cast forall Nat 'n, Nat 'l, Order 'ord. [:0:] -> vector<'n,'l,'ord,bit> effect pure cast_0_vec
val cast forall Nat 'n, Nat 'l, Order 'ord. [:1:] -> vector<'n,'l,'ord,bit> effect pure cast_1_vec
val cast forall Nat 'n, Nat 'l, Order 'ord. [|0:1|] -> vector<'n,'l,'ord,bit> effect pure cast_01_vec

val cast forall Nat 'n, Order 'ord. vector<'n,1,'ord,bit> -> bool effect pure cast_vec_bool
val cast bit -> bool effect pure cast_bit_bool

(* MSB *)
val forall Nat 'n, Nat 'm, Order 'ord. vector<'n, 'm, 'ord, bit> -> bit effect pure most_significant

(* Arithmetic *)

val forall Nat 'n, Nat 'm.
    (atom<'n>, atom<'m>) -> atom<'n+'m> effect pure add

val forall Nat 'n, Nat 'o, Nat 'p, Order 'ord.
    (vector<'o, 'n, 'ord, bit>, vector<'p, 'n, 'ord, bit>) -> vector<'o, 'n, 'ord, bit> effect pure add_vec

val forall Nat 'n, Nat 'o, Nat 'p, Nat 'q, Order 'ord.
    (vector<'o, 'n, 'ord, bit>, vector<'p, 'n, 'ord, bit>) -> range<'q, 2**'n> effect pure add_vec_vec_range

(* FIXME: the parser is broken for 2**... it's just been hacked to work for this common case *)
val forall Nat 'n, Nat 'm, Nat 'o, Order 'ord, 'o <= 2** 'm - 1.
    (vector<'n, 'm, 'ord, bit>, atom<'o>) -> vector<'n, 'm, 'ord, bit> effect pure add_vec_range

val forall Nat 'n, Nat 'o, Nat 'p, Order 'ord.
    (vector<'o, 'n, 'ord, bit>, vector<'p, 'n, 'ord, bit>) -> (vector<'o, 'n, 'ord, bit>, bit, bit) effect pure add_overflow_vec

(* but it doesn't parse this
val forall Nat 'n, Nat 'm, Nat 'o, Order 'ord, 'o <= 2** 'm - 1.
    (vector<'n, 'm, 'ord, bit>, atom<'o>) -> range<'o, 'o+2** 'm> effect pure add_vec_range_range
    *)

val forall Nat 'n, Nat 'm, Nat 'o, Order 'ord, 'o <= 2** 'm - 1.
    (atom<'o>, vector<'n, 'm, 'ord, bit>) -> vector<'n, 'm, 'ord, bit> effect pure add_range_vec

(* or this
val forall Nat 'n, Nat 'm, Nat 'o, Order 'ord, 'o <= 2** 'm - 1.
    (atom<'o>, vector<'n, 'm, 'ord, bit>) -> range<'o, 'o+2**'m-1> effect pure add_range_vec_range
*)

val forall Nat 'o, Nat 'p, Order 'ord.
    (vector<'o, 'p, 'ord, bit>, bit) -> vector<'o, 'p, 'ord, bit> effect pure add_vec_bit

val forall Nat 'o, Nat 'p, Order 'ord.
    (bit, vector<'o, 'p, 'ord, bit>) -> vector<'o, 'p, 'ord, bit> effect pure add_bit_vec

val forall Nat 'n, Nat 'm. ([:'n:], [:'m:]) -> [:'n - 'm:] effect pure sub_exact
val forall Nat 'n, Nat 'm, Nat 'o, 'o <= 'm - 'n. ([|'n:'m|], [:'o:]) -> [|'n:'m - 'o|] effect pure sub_range
val forall Nat 'n, Nat 'm, Order 'ord. (vector<'n,'m,'ord,bit>, int) -> vector<'n,'m,'ord,bit> effect pure sub_bv

overload (deinfix +) [
  add;
  add_vec;
  add_vec_vec_range;
  add_vec_range;
  add_overflow_vec;
  add_vec_range_range;
  add_range_vec;
  add_range_vec_range;
  add_vec_bit;
  add_bit_vec;
]

overload (deinfix -) [
  sub_exact;
  sub_bv;
  sub_range;
]

(* Equality *)

(* Sail gives a bunch of overloads for equality, but apparantly also
gives an equality and inequality for any type 'a, so why bother
overloading? *)

val forall Type 'a. ('a, 'a) -> bool effect pure eq
val forall Type 'a. ('a, 'a) -> bool effect pure neq

overload (deinfix ==) [eq]
overload (deinfix !=) [neq]

(* Boolean operators *)
val bool -> bool effect pure bool_not
val (bool, bool) -> bool effect pure bool_or
val (bool, bool) -> bool effect pure bool_and

overload ~ [bool_not]
overload (deinfix &) [bool_and]
overload (deinfix |) [bool_or]

(* Mips spec starts here *)

(*========================================================================*)
(*                                                                        *)
(*  Copyright (c) 2015-2017 Robert M. Norton                              *)
(*  Copyright (c) 2015-2017 Kathyrn Gray                                  *)
(*  All rights reserved.                                                  *)
(*                                                                        *)
(*  This software was developed by the University of Cambridge Computer   *)
(*  Laboratory as part of the Rigorous Engineering of Mainstream Systems  *)
(*  (REMS) project, funded by EPSRC grant EP/K008528/1.                   *)
(*                                                                        *)
(*  Redistribution and use in source and binary forms, with or without    *)
(*  modification, are permitted provided that the following conditions    *)
(*  are met:                                                              *)
(*  1. Redistributions of source code must retain the above copyright     *)
(*     notice, this list of conditions and the following disclaimer.      *)
(*  2. Redistributions in binary form must reproduce the above copyright  *)
(*     notice, this list of conditions and the following disclaimer in    *)
(*     the documentation and/or other materials provided with the         *)
(*     distribution.                                                      *)
(*                                                                        *)
(*  THIS SOFTWARE IS PROVIDED BY THE AUTHOR AND CONTRIBUTORS ``AS IS''    *)
(*  AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED     *)
(*  TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A       *)
(*  PARTICULAR PURPOSE ARE DISCLAIMED.  IN NO EVENT SHALL THE AUTHOR OR   *)
(*  CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,          *)
(*  SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT      *)
(*  LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF      *)
(*  USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND   *)
(*  ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,    *)
(*  OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT    *)
(*  OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF    *)
(*  SUCH DAMAGE.                                                          *)
(*========================================================================*)

(* mips_prelude.sail: declarations of mips registers, and functions common 
   to mips instructions (e.g. address translation) *)

(* bit vectors have indices decreasing from left i.e. msb is highest index *)
default Order dec

register (bit[64]) PC
register (bit[64]) nextPC

(* CP0 Registers *)

typedef CauseReg = register bits [ 31 : 0 ] {
  31       : BD; (* branch delay *)
  (*30       : Z0;*)
  29 .. 28 : CE; (* for coprocessor enable exception *)
  (*27 .. 24 : Z1;*)
  23       : IV; (* special interrupt vector not supported *)
  22       : WP; (* watchpoint exception occurred *)
  (*21 .. 16 : Z2; *)
  15 .. 8  : IP; (* interrupt pending bits *)
  (*7        : Z3;*)
  6 .. 2   : ExcCode; (* code of last exception *)
  (*1 .. 0   : Z4;*)
}

typedef TLBEntryLoReg = register bits [63 : 0] {
  63      : CapS;
  62      : CapL;
  29 .. 6 : PFN;
  5  .. 3 : C;
  2       : D;
  1       : V;
  0       : G;
}

typedef TLBEntryHiReg = register bits [63 : 0] {
  63 .. 62 : R;
  39 .. 13 : VPN2;
  7  ..  0 : ASID;
}

typedef ContextReg = register bits [63 : 0] {
  63 .. 23 : PTEBase;
  22 .. 4  : BadVPN2;
  (*3  .. 0  : ZR;*)
}

typedef XContextReg = register bits [63 : 0] {
  63 .. 33: PTEBase;
  32 .. 31: R;
  30 ..  4: BadVPN2;
}

let ([:64:]) TLBNumEntries = 64
typedef TLBIndexT = (bit[6])
let (TLBIndexT) TLBIndexMax = 0b111111

let MAX_U64 = unsigned(0xffffffffffffffff)
let MAX_VA  = unsigned(0xffffffffff)
let MAX_PA  = unsigned(0xfffffffff)

typedef TLBEntry = register bits [116 : 0] {
  116 ..  101: pagemask;
  100 ..  99 : r       ;
  98  ..  72 : vpn2    ;
  71  ..  64 : asid    ;
  63         : g       ;
  62         : valid   ;
  61         : caps1   ;
  60         : capl1   ;
  59  ..  36 : pfn1    ;
  35  ..  33 : c1      ;
  32         : d1      ;
  31         : v1      ;
  30         : caps0   ;
  29         : capl0   ;
  28  ..  5  : pfn0    ;
  4   ..  2  : c0      ;
  1          : d0      ;
  0          : v0      ;
}

register (bit[1])        TLBProbe
register (TLBIndexT)     TLBIndex
register (TLBIndexT)     TLBRandom
register (TLBEntryLoReg) TLBEntryLo0
register (TLBEntryLoReg) TLBEntryLo1
register (ContextReg)    TLBContext
register (bit[16])       TLBPageMask
register (TLBIndexT)     TLBWired
register (TLBEntryHiReg) TLBEntryHi
register (XContextReg)   TLBXContext

register (TLBEntry) TLBEntry00
register (TLBEntry) TLBEntry01
register (TLBEntry) TLBEntry02
register (TLBEntry) TLBEntry03
register (TLBEntry) TLBEntry04
register (TLBEntry) TLBEntry05
register (TLBEntry) TLBEntry06
register (TLBEntry) TLBEntry07
register (TLBEntry) TLBEntry08
register (TLBEntry) TLBEntry09
register (TLBEntry) TLBEntry10
register (TLBEntry) TLBEntry11
register (TLBEntry) TLBEntry12
register (TLBEntry) TLBEntry13
register (TLBEntry) TLBEntry14
register (TLBEntry) TLBEntry15
register (TLBEntry) TLBEntry16
register (TLBEntry) TLBEntry17
register (TLBEntry) TLBEntry18
register (TLBEntry) TLBEntry19
register (TLBEntry) TLBEntry20
register (TLBEntry) TLBEntry21
register (TLBEntry) TLBEntry22
register (TLBEntry) TLBEntry23
register (TLBEntry) TLBEntry24
register (TLBEntry) TLBEntry25
register (TLBEntry) TLBEntry26
register (TLBEntry) TLBEntry27
register (TLBEntry) TLBEntry28
register (TLBEntry) TLBEntry29
register (TLBEntry) TLBEntry30
register (TLBEntry) TLBEntry31
register (TLBEntry) TLBEntry32
register (TLBEntry) TLBEntry33
register (TLBEntry) TLBEntry34
register (TLBEntry) TLBEntry35
register (TLBEntry) TLBEntry36
register (TLBEntry) TLBEntry37
register (TLBEntry) TLBEntry38
register (TLBEntry) TLBEntry39
register (TLBEntry) TLBEntry40
register (TLBEntry) TLBEntry41
register (TLBEntry) TLBEntry42
register (TLBEntry) TLBEntry43
register (TLBEntry) TLBEntry44
register (TLBEntry) TLBEntry45
register (TLBEntry) TLBEntry46
register (TLBEntry) TLBEntry47
register (TLBEntry) TLBEntry48
register (TLBEntry) TLBEntry49
register (TLBEntry) TLBEntry50
register (TLBEntry) TLBEntry51
register (TLBEntry) TLBEntry52
register (TLBEntry) TLBEntry53
register (TLBEntry) TLBEntry54
register (TLBEntry) TLBEntry55
register (TLBEntry) TLBEntry56
register (TLBEntry) TLBEntry57
register (TLBEntry) TLBEntry58
register (TLBEntry) TLBEntry59
register (TLBEntry) TLBEntry60
register (TLBEntry) TLBEntry61
register (TLBEntry) TLBEntry62
register (TLBEntry) TLBEntry63

let (vector <0, 64, inc, (TLBEntry)>) TLBEntries = [
TLBEntry00,
TLBEntry01,
TLBEntry02,
TLBEntry03,
TLBEntry04,
TLBEntry05,
TLBEntry06,
TLBEntry07,
TLBEntry08,
TLBEntry09,
TLBEntry10,
TLBEntry11,
TLBEntry12,
TLBEntry13,
TLBEntry14,
TLBEntry15,
TLBEntry16,
TLBEntry17,
TLBEntry18,
TLBEntry19,
TLBEntry20,
TLBEntry21,
TLBEntry22,
TLBEntry23,
TLBEntry24,
TLBEntry25,
TLBEntry26,
TLBEntry27,
TLBEntry28,
TLBEntry29,
TLBEntry30,
TLBEntry31,
TLBEntry32,
TLBEntry33,
TLBEntry34,
TLBEntry35,
TLBEntry36,
TLBEntry37,
TLBEntry38,
TLBEntry39,
TLBEntry40,
TLBEntry41,
TLBEntry42,
TLBEntry43,
TLBEntry44,
TLBEntry45,
TLBEntry46,
TLBEntry47,
TLBEntry48,
TLBEntry49,
TLBEntry50,
TLBEntry51,
TLBEntry52,
TLBEntry53,
TLBEntry54,
TLBEntry55,
TLBEntry56,
TLBEntry57,
TLBEntry58,
TLBEntry59,
TLBEntry60,
TLBEntry61,
TLBEntry62,
TLBEntry63
]

register (bit[32])  CP0Compare
register (CauseReg) CP0Cause
register (bit[64])  CP0EPC
register (bit[64])  CP0ErrorEPC
register (bit[1])   CP0LLBit
register (bit[64])  CP0LLAddr
register (bit[64])  CP0BadVAddr
register (bit[32])  CP0Count
register (bit[32])  CP0HWREna
register (bit[64])  CP0UserLocal

typedef StatusReg = register bits [31:0] {
  31 .. 28        : CU;  (* co-processor enable bits *)
  (* RP/FR/RE/MX/PX not implemented *)
  22              : BEV; (* use boot exception vectors (initialised to one) *)
  (* TS/SR/NMI not implemented *)
  15 .. 8         : IM;  (* Interrupt mask *)
  7               : KX;  (* kernel 64-bit enable *)
  6               : SX;  (* supervisor 64-bit enable *)
  5               : UX;  (* user 64-bit enable *)
  4 .. 3          : KSU; (* Processor mode *)
  2               : ERL; (* error level (should be initialised to one, but BERI is different) *)
  1               : EXL; (* exception level *)
  0               : IE;  (* interrupt enable *)
}
register (StatusReg) CP0Status

(* Implementation registers -- not ISA defined *)
register (bit[1])  branchPending      (* Set by branch instructions to implement branch delay *)
register (bit[1])  inBranchDelay      (* Needs to be set by outside world when in branch delay slot *)
register (bit[64]) delayedPC          (* Set by branch instructions to implement branch delay *)

(* General purpose registers *)

register (bit[64]) GPR00 (* should never be read or written *)
register (bit[64]) GPR01
register (bit[64]) GPR02
register (bit[64]) GPR03
register (bit[64]) GPR04
register (bit[64]) GPR05
register (bit[64]) GPR06
register (bit[64]) GPR07
register (bit[64]) GPR08
register (bit[64]) GPR09
register (bit[64]) GPR10
register (bit[64]) GPR11
register (bit[64]) GPR12
register (bit[64]) GPR13
register (bit[64]) GPR14
register (bit[64]) GPR15
register (bit[64]) GPR16
register (bit[64]) GPR17
register (bit[64]) GPR18
register (bit[64]) GPR19
register (bit[64]) GPR20
register (bit[64]) GPR21
register (bit[64]) GPR22
register (bit[64]) GPR23
register (bit[64]) GPR24
register (bit[64]) GPR25
register (bit[64]) GPR26
register (bit[64]) GPR27
register (bit[64]) GPR28
register (bit[64]) GPR29
register (bit[64]) GPR30
register (bit[64]) GPR31

(* Special registers For MUL/DIV *)
register (bit[64]) HI
register (bit[64]) LO

let (vector <0, 32, inc, (register<(bit[64])>) >) GPR =
  [ GPR00, GPR01, GPR02, GPR03, GPR04, GPR05, GPR06, GPR07, GPR08, GPR09, GPR10,
  GPR11, GPR12, GPR13, GPR14, GPR15, GPR16, GPR17, GPR18, GPR19, GPR20,
  GPR21, GPR22, GPR23, GPR24, GPR25, GPR26, GPR27, GPR28, GPR29, GPR30, GPR31
  ]

(* JTAG Uart registers *)

register (bit[8]) UART_WDATA
register (bit[1]) UART_WRITTEN
register (bit[8]) UART_RDATA
register (bit[1]) UART_RVALID

(* Check whether a given 64-bit vector is a properly sign extended 32-bit word *)
val bit[64] -> bool effect pure NotWordVal
function bool NotWordVal (word) = 
    (word[31] ^^ 32) != word[63..32]

(* Read numbered GP reg. (r0 is always zero) *)
val bit[5] -> bit[64] effect {rreg} rGPR
function bit[64] rGPR idx = {
         if idx == 0 then 0 else GPR[idx]
}

(* Write numbered GP reg. (writes to r0 ignored) *)
val (bit[5], bit[64]) -> unit effect {wreg} wGPR
function unit wGPR (idx, v) = {
         if idx == 0 then () else GPR[idx] := v
}

val extern forall Nat 'n. ( bit[64] , [|'n|] ) -> (bit[8 * 'n]) effect { rmem } MEMr
val extern forall Nat 'n. ( bit[64] , [|'n|] ) -> (bit[8 * 'n]) effect { rmem } MEMr_reserve
val extern unit -> unit effect { barr } MEM_sync

val extern forall Nat 'n. ( bit[64] , [|'n|]) -> unit effect { eamem } MEMea
val extern forall Nat 'n. ( bit[64] , [|'n|]) -> unit effect { eamem } MEMea_conditional
val extern forall Nat 'n. ( bit[64] , [|'n|] , bit[8*'n]) -> unit effect { wmv } MEMval
val extern forall Nat 'n. ( bit[64] , [|'n|] , bit[8*'n]) -> bool effect { wmv } MEMval_conditional

typedef Exception = enumerate
{
   Int; TLBMod; TLBL; TLBS; AdEL; AdES; Sys; Bp; ResI; CpU; Ov; Tr; C2E; C2Trap;
   XTLBRefillL; XTLBRefillS; XTLBInvL; XTLBInvS; MCheck
}

(* Return the ISA defined code for an exception condition *)
function (bit[5]) ExceptionCode ((Exception) ex) =
   switch (ex)
   {
      case Int         -> mask(0x00) (* Interrupt *)
      case TLBMod      -> mask(0x01) (* TLB modification exception *)
      case TLBL        -> mask(0x02) (* TLB exception (load or fetch) *)
      case TLBS        -> mask(0x03) (* TLB exception (store) *)
      case AdEL        -> mask(0x04) (* Address error (load or fetch) *)
      case AdES        -> mask(0x05) (* Address error (store) *)
      case Sys         -> mask(0x08) (* Syscall *)
      case Bp          -> mask(0x09) (* Breakpoint *)
      case ResI        -> mask(0x0a) (* Reserved instruction *)
      case CpU         -> mask(0x0b) (* Coprocessor Unusable *)
      case Ov          -> mask(0x0c) (* Arithmetic overflow *)
      case Tr          -> mask(0x0d) (* Trap *)
      case C2E         -> mask(0x12) (* C2E coprocessor 2 exception *)
      case C2Trap      -> mask(0x12) (* C2Trap maps to same exception code, different vector *)
      case XTLBRefillL -> mask(0x02)
      case XTLBRefillS -> mask(0x03)
      case XTLBInvL    -> mask(0x02)
      case XTLBInvS    -> mask(0x03)
      case MCheck      -> mask(0x18)
   }



function forall Type 'o. 'o SignalExceptionMIPS ((Exception) ex, (bit[64]) kccBase) = 
  {
    (* Only update EPC and BD if not already in EXL mode *)
    if (~ (CP0Status.EXL)) then 
      {
        if (inBranchDelay[0]) then
          {
            CP0EPC := PC - 4;
            CP0Cause.BD := 1;
          }
        else
          {
            CP0EPC := PC;
            CP0Cause.BD := 0;
          }
      };

      (* choose an exception vector to branch to. Some are not supported 
         e.g. Reset *)
      vectorOffset := 
        if (CP0Status.EXL) then
          0x180 (* Always use common vector if in exception mode already *)
        else if ((ex == XTLBRefillL) | (ex == XTLBRefillS)) then 
          0x080
        else if (ex == C2Trap) then
          0x280 (* Special vector for CHERI traps *)
        else
          0x180; (* Common vector *)
      (bit[64]) vectorBase  := if CP0Status.BEV then
                   0xFFFFFFFFBFC00200
                else
                   0xFFFFFFFF80000000;
      (* On CHERI we have to subtract KCC.base so that we end up at the 
         right absolute vector address after indirecting via new PCC *)
      nextPC := ((bit[64])(vectorBase + (bit[64])(EXTS(vectorOffset)))) - kccBase;
      CP0Cause.ExcCode      := ExceptionCode(ex);
      CP0Status.EXL         := 1;
      exit ();
  }

val forall Type 'o . Exception -> 'o effect {escape, rreg, wreg} SignalException

function forall Type 'o. 'o SignalExceptionBadAddr((Exception) ex, (bit[64]) badAddr) =
  {
    CP0BadVAddr := badAddr;
    SignalException(ex);
  }

function forall Type 'o. 'o  SignalExceptionTLB((Exception) ex, (bit[64]) badAddr) = {
  CP0BadVAddr := badAddr;
  (TLBContext.BadVPN2) := (badAddr[31..13]);
  (TLBXContext.BadVPN2):= (badAddr[39..13]);
  (TLBXContext.R)      := (badAddr[63..62]);
  (TLBEntryHi.R)       := (badAddr[63..62]);
  (TLBEntryHi.VPN2)    := (badAddr[39..13]);
  SignalException(ex);
}

typedef MemAccessType = enumerate {Instruction; LoadData; StoreData}
typedef AccessLevel   = enumerate {User; Supervisor; Kernel} 

function AccessLevel getAccessLevel() =
  if ((CP0Status.EXL) | (CP0Status.ERL)) then
    Kernel
  else switch (bit[2]) (CP0Status.KSU)
    {
      case 0b00 -> Kernel
      case 0b01 -> Supervisor
      case 0b10 -> User
      case _    -> User (* behaviour undefined, assume user *)
    }

function unit checkCP0Access () =
  {
    let accessLevel = getAccessLevel() in
    if ((accessLevel != Kernel) & (~(CP0Status[28] (*CU0*)))) then
      {
        (CP0Cause.CE) := 0b00;
        SignalException(CpU);
      }
  }
