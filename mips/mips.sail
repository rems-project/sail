(* bit vectors have indices decreasing from left i.e. msb is highest index *)
default Order dec

(*(* external functions *)
val extern forall Nat 'm, Nat 'n. (implicit<'m>,bit['n]) -> bit['m] effect pure EXTS (* Sign extend *)
val extern forall Nat 'n, Nat 'm. (implicit<'m>,bit['n]) -> bit['m] effect pure EXTZ (* Zero extend *)
*)
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
register (CauseReg) CP0Cause
register (bit[64]) CP0EPC

typedef StatusReg = register bits [31:0] {
  31 .. 28        : CU;  (* co-processor enable bits *)
  (* RP/FR/RE/MX/PX not implemented *)
  22              : BEV; (* use boot exception vectors XXX initialise to one *)
  (* TS/SR/NMI not implemented *)
  15 .. 8         : IM;  (* Interrupt mask *)
  (* KX/SX/UX not implemented (XXX initialise to one) *)
  4 .. 3          : KSU; (* Processor mode *)
  2               : ERL; (* error level XXX initialise to one *)
  1               : EXL; (* exception level *)
  0               : IE;  (* interrupt enable *)
}
register (StatusReg) CP0Status

(* Implementation registers -- not ISA defined *)
register (bit[1])  branchPending
register (bit[1])  exceptionSignalled
register (bit[64]) delayedPC

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

(* Check whether a given 64-bit vector is a properly sign extended 32-bit word *)
val bit[64] -> bool effect pure isWordVal
function bool NotWordVal (word) = 
    (word[31] ^^ 32) != word[63..32]

val bit[5] -> bit[64] effect {rreg} rGPR
function bit[64] rGPR idx = {
         if idx == 0 then 0 else GPR[idx]
}

val (bit[5], bit[64]) -> unit effect {wreg} wGPR
function unit wGPR (idx, v) = {
         if idx == 0 then () else GPR[idx] := v
}

val extern forall Nat 'n. ( bit[64] , [|'n|] , bit[8*'n]) -> unit effect { wmem } MEMw
val extern forall Nat 'n. ( bit[64] , [|'n|] ) -> (bit[8 * 'n]) effect { rmem } MEMr
val extern forall Nat 'n. ( bit[64] , [|'n|] ) -> (bit[8 * 'n]) effect { rmem } MEMr_reserve
val extern forall Nat 'n. ( bit[64] , [|'n|] , bit[8*'n]) -> bool effect { wmem } MEMw_conditional
val extern unit -> unit effect { barr } MEM_sync

typedef Exception = enumerate
{
   Int; Mod; TLBL; TLBS; AdEL; AdES; Sys; Bp; ResI; CpU; Ov; Tr; C2E;
   XTLBRefillL; XTLBRefillS
}

(* Return the ISA defined code for an exception condition *)
function (bit[5]) ExceptionCode ((Exception) ex) =
   switch (ex)
   {
      case Int         -> mask(0x00) (* Interrupt *)
      case Mod         -> mask(0x01) (* TLB modification exception *)
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
      case XTLBRefillL -> mask(0x02)
      case XTLBRefillS -> mask(0x03)
   }


function unit SignalException ((Exception) ex) = 
  {
    CP0Cause.ExcCode := ExceptionCode(ex);
    CP0Status.EXL         := 1;
    exceptionSignalled    := 1;
    (* Only update EPC and BD if not already in EXL mode *)
    if (~ (CP0Status.EXL)) then 
      {
        if (branchPending) then
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

      (* choose an exception vector to branch to *)
      vectorOffset := if ((ex == XTLBRefillL) | (ex == XTLBRefillS)) & ~ (CP0Status.EXL) then
                     0x080
                  else
                     0x180;
      (bit[64]) vectorBase  := if CP0Status.BEV then
                   0xFFFFFFFFBFC00200
                else
                   0xFFFFFFFF80000000;
      nextPC := vectorBase + EXTS(vectorOffset);
  }

typedef MemAccessType = enumerate {Instruction; LoadData; StoreData}
function (bool, bit[64]) TranslateAddress ((bit[64]) vAddr, (MemAccessType) accessType) = 
  {
    (false, vAddr)
  }

typedef regno = bit[5]                      (* a register number *)
typedef imm16 = bit[16]                     (* 16-bit immediate *)
typedef regregreg   = (regno, regno, regno) (* a commonly used instruction format with three register operands *)
typedef regregimm16 = (regno, regno, imm16) (* a commonly used instruction format with two register operands and 16-bit immediate *)
typedef decode_failure = enumerate { no_matching_pattern; unsupported_instruction; illegal_instruction; internal_error }
(* Used by branch and trap instructions *)
typedef Comparison = enumerate { 
  EQ; (* equal *)
  NE; (* not equal *)
  GE; (* signed greater than or equal *)
  GEU;(* unsigned greater than or equal *) 
  GT; (* signed strictly greater than *) 
  LE; (* signed less than or equal *) 
  LT; (* signed strictly less than *) 
  LTU;(* unsigned less than or qual *) 
}
function bool compare ((Comparison)cmp, (bit[64]) valA, (bit[64]) valB) =
  switch(cmp) {
    case EQ  -> valA ==   valB
    case NE  -> valA !=   valB
    case GE  -> valA >=_s valB
    case GEU -> valA >=   valB
    case GT  -> valA >    valB
    case LE  -> valA <=_s valB
    case LT  -> valA <_s  valB
    case LTU -> valA <    valB
  }
typedef WordType = enumerate { B; H; W; D}

function forall Nat 'r, 'r IN {1,2,4,8}.[:'r:] wordWidthBytes((WordType) w) =
  switch(w) {
    case B -> 1
    case H -> 2
    case W -> 4
    case D -> 8
  }

function bool isAddressAligned(addr, (WordType) wordType) =
  switch (wordType) {
    case B -> true
    case H -> (addr[0]    == 0b0)
    case W -> (addr[1..0] == 0b00)
    case D -> (addr[2..0] == 0b000)
  }

scattered function unit execute
scattered typedef ast = const union

val bit[32] -> option<ast> effect pure decode
scattered function option<ast> decode

(**************************************************************************************)
(* [D]ADD[I][U] various forms of ADD                                                  *)
(**************************************************************************************)

(* DADDIU Doubleword Add Immediate Unsigned -- 
   the simplest possible instruction, no undefined behaviour or exceptions 
   reg, reg, immediate *)

union ast member regregimm16 DADDIU

function clause decode (0b011001 : (regno) rs : (regno) rt : (imm16) imm) = 
  Some(DADDIU(rs, rt, imm))

function clause execute (DADDIU (rs, rt, imm)) =
  {
    wGPR(rt) := rGPR(rs) + EXTS(imm)
  }

(* DADDU Doubleword Add Unsigned -- another very simple instruction,
   reg, reg, reg *)

union ast member regregreg DADDU

function clause decode (0b000000 : (regno) rs : (regno) rt : (regno) rd : 0b00000 : 0b101101) = 
  Some(DADDU(rs, rt, rd))

function clause execute (DADDU (rs, rt, rd)) =
  {
    wGPR(rd) := rGPR(rs) + rGPR(rt)
  }

(* DADDI Doubleword Add Immediate
   reg, reg, imm with possible exception *)

union ast member regregimm16 DADDI

function clause decode (0b011000 : (regno) rs : (regno) rt : (imm16) imm) = 
  Some(DADDI(rs, rt, imm))

function clause execute (DADDI (rs, rt, imm)) =
  {
    let (bit[65]) sum65 = (EXTS(rGPR(rs)) + EXTS(imm)) in
    {
      if (sum65[64] != sum65[63]) then
        SignalException(Ov)
      else
        wGPR(rt) := sum65[63..0]
    }
  }

(* DADD Doubleword Add
   reg, reg, reg with possible exception *)

union ast member regregreg DADD

function clause decode (0b000000 : (regno) rs : (regno) rt : (regno) rd : 0b00000 : 0b101100) = 
  Some(DADD(rs, rt, rd))

function clause execute (DADD (rs, rt, rd)) =
  {
    let (bit[65]) sum65 = (EXTS(rGPR(rs)) + EXTS(rGPR(rt))) in
    {
      if sum65[64] != sum65[63] then
        SignalException(Ov)
      else
        wGPR(rd) := sum65[63..0]
    }
  }

(* ADD   32-bit add           -- reg, reg, reg with possible undefined behaviour or exception *)

union ast member regregreg ADD

function clause decode (0b000000 : (regno) rs : (regno) rt : (regno) rd : 0b00000 : 0b100000) =
  Some(ADD(rs, rt, rd))

function clause execute (ADD(rs, rt, rd)) = 
  {
    (bit[64]) opA := rGPR(rs);
    (bit[64]) opB := rGPR(rt);
    if NotWordVal(opA) | NotWordVal(opB) then
      wGPR(rd) := undefined (* XXX could exit instead *)
    else
      let (bit[33]) sum33 = (EXTS(opA[31 .. 0]) + EXTS(opB[31 .. 0])) in
        if sum33[32] != sum33[31] then
          SignalException(Ov)
        else
          wGPR(rd) := EXTS(sum33[31..0])
  }

(* ADDI  32-bit add immediate -- reg, reg, imm with possible undefined behaviour or exception *)

union ast member regregimm16 ADDI

function clause decode (0b001000 : (regno) rs : (regno) rt : (imm16) imm) =
  Some(ADDI(rs, rt, imm))

function clause execute (ADDI(rs, rt, imm)) = 
  {
    (bit[64]) opA := rGPR(rs);
    if NotWordVal(opA) then
      wGPR(rt) := undefined (* XXX could exit instead *)
    else
      let (bit[33]) sum33 = (EXTS(opA[31 .. 0]) + EXTS(imm)) in
        if sum33[32] != sum33[31] then
          SignalException(Ov)
        else
          wGPR(rt) := EXTS(sum33[31..0])
  }

(* ADDU  32-bit add immediate -- reg, reg, reg with possible undefined behaviour *)

union ast member regregreg ADDU

function clause decode (0b000000 : (regno) rs : (regno) rt : (regno) rd : 0b00000 : 0b100001) =
  Some(ADDU(rs, rt, rd))

function clause execute (ADDU(rs, rt, rd)) = 
  {
    (bit[64]) opA := rGPR(rs);
    (bit[64]) opB := rGPR(rt);
    if NotWordVal(opA) | NotWordVal(opB) then
      wGPR(rd) := undefined
    else
      wGPR(rd) := EXTS(opA[31..0] + opB[31..0])
  }


(* ADDIU 32-bit add immediate -- reg, reg, imm with possible undefined behaviour *)

union ast member regregimm16 ADDIU

function clause decode (0b001001 : (regno) rs : (regno) rt : (imm16) imm) =
  Some(ADDIU(rs, rt, imm))

function clause execute (ADDIU(rs, rt, imm)) = 
  {
    (bit[64]) opA := rGPR(rs);
    if NotWordVal(opA) then
      wGPR(rt) := undefined (* XXX could exit instead *)
    else
      wGPR(rt) := EXTS((opA[31 .. 0]) + EXTS(imm))
  }

(**************************************************************************************)
(* [D]SUB[U] various forms of SUB                                                     *)
(**************************************************************************************)

(* DSUBU doubleword subtract 'unsigned' reg, reg, reg *)

union ast member regregreg DSUBU

function clause decode (0b000000 : (regno) rs : (regno) rt : (regno) rd : 0b00000 : 0b101111) = 
  Some(DSUBU(rs, rt, rd))

function clause execute (DSUBU (rs, rt, rd)) =
  {
    wGPR(rd) := rGPR(rs) - rGPR(rt)
  }

(* DSUB reg, reg, reg with possible exception *)

union ast member regregreg DSUB

function clause decode (0b000000 : (regno) rs : (regno) rt : (regno) rd : 0b00000 : 0b101110) = 
  Some(DSUB(rs, rt, rd))

function clause execute (DSUB (rs, rt, rd)) =
  {
    let (bit[65]) temp65 = (EXTS(rGPR(rs)) - EXTS(rGPR(rt))) in
    {
      if temp65[64] != temp65[63] then
        SignalException(Ov)
      else
        wGPR(rd) := temp65[63..0]
    }
  }

(* SUB   32-bit sub           -- reg, reg, reg with possible undefined behaviour or exception *)

union ast member regregreg SUB

function clause decode (0b000000 : (regno) rs : (regno) rt : (regno) rd : 0b00000 : 0b100010) =
  Some(SUB(rs, rt, rd))

function clause execute (SUB(rs, rt, rd)) = 
  {
    (bit[64]) opA := rGPR(rs);
    (bit[64]) opB := rGPR(rt);
    if NotWordVal(opA) | NotWordVal(opB) then
      wGPR(rd) := undefined (* XXX could exit instead *)
    else
      let (bit[33]) temp33 = (EXTS(opA[31..0]) - EXTS(opB[31..0])) in
      if temp33[32] != temp33[31] then
        SignalException(Ov)
      else
        wGPR(rd) := EXTS(temp33[31..0])
  }

(* SUBU  32-bit 'unsigned' sub -- reg, reg, reg with possible undefined behaviour *)

union ast member regregreg SUBU
function clause decode (0b000000 : (regno) rs : (regno) rt : (regno) rd : 0b00000 : 0b100011) =
    Some(SUBU(rs, rt, rd))

function clause execute (SUBU(rs, rt, rd)) = 
  {
    (bit[64]) opA := rGPR(rs);
    (bit[64]) opB := rGPR(rt);
    if NotWordVal(opA) | NotWordVal(opB) then
      wGPR(rd) := undefined
    else
      wGPR(rd) := EXTS(opA[31..0] - opB[31..0])
  }

(**************************************************************************************)
(* Logical bitwise operations                                                         *)
(**************************************************************************************)

(* AND reg, reg, reg *)

union ast member regregreg AND
function clause decode (0b000000 : (regno) rs : (regno) rt : (regno) rd : 0b00000 : 0b100100) = 
    Some(AND(rs, rt, rd))

function clause execute (AND (rs, rt, rd)) =
  {
    wGPR(rd) := (rGPR(rs) & rGPR(rt))
  }

(* ANDI reg, reg, imm *)

union ast member regregimm16 ANDI
function clause decode (0b001100 : (regno) rs : (regno) rt : (imm16) imm) = 
  Some(ANDI(rs, rt, imm))
function clause execute (ANDI (rs, rt, imm)) =
  {
    wGPR(rt) := (rGPR(rs) & EXTZ(imm))
  }

(* OR reg, reg, reg *)

union ast member regregreg OR
function clause decode (0b000000 : (regno) rs : (regno) rt : (regno) rd : 0b00000 : 0b100101) = 
  Some(OR(rs, rt, rd))
function clause execute (OR (rs, rt, rd)) =
  {
    wGPR(rd) := (rGPR(rs) | rGPR(rt))
  }

(* ORI reg, reg, imm *)

union ast member regregimm16 ORI
function clause decode (0b001101 : (regno) rs : (regno) rt : (imm16) imm) = 
  Some(ORI(rs, rt, imm))
function clause execute (ORI (rs, rt, imm)) =
  {
    wGPR(rt) := (rGPR(rs) | EXTZ(imm))
  }

(* NOR reg, reg, reg *)

union ast member regregreg NOR
function clause decode (0b000000 : (regno) rs : (regno) rt : (regno) rd : 0b00000 : 0b100111) = 
  Some(NOR(rs, rt, rd))
function clause execute (NOR (rs, rt, rd)) =
  {
    wGPR(rd) := ~(rGPR(rs) | rGPR(rt))
  }

(* XOR reg, reg, reg *)

union ast member regregreg XOR
function clause decode (0b000000 : (regno) rs : (regno) rt : (regno) rd : 0b00000 : 0b100110) = 
  Some(XOR(rs, rt, rd))
function clause execute (XOR (rs, rt, rd)) =
  {
    wGPR(rd) := (rGPR(rs) ^ rGPR(rt))
  }

(* XORI reg, reg, imm *)
union ast member regregimm16 XORI
function clause decode (0b001110 : (regno) rs : (regno) rt : (imm16) imm) = 
  Some(XORI(rs, rt, imm))
function clause execute (XORI (rs, rt, imm)) =
  {
    wGPR(rt) := (rGPR(rs) ^ EXTZ(imm))
  }

(* LUI reg, imm 32-bit load immediate into upper 16 bits *)
union ast member (regno, imm16) LUI 
function clause decode (0b001111 : 0b00000 : (regno) rt : (imm16) imm) = 
  Some(LUI(rt, imm))
function clause execute (LUI (rt, imm)) =
  {
    wGPR(rt) := EXTS(imm : 0x0000)
  }

(**************************************************************************************)
(* 64-bit  shift operations                                                           *)
(**************************************************************************************)

(* DSLL reg, reg, imm5 *)

union ast member regregreg DSLL
function clause decode (0b000000 : 0b00000 : (regno) rt : (regno) rd : (bit[5]) sa : 0b111000) = 
  Some(DSLL(rt, rd, sa))
function clause execute (DSLL (rt, rd, sa)) =
  {
    
    wGPR(rd) := (rGPR(rt) << sa) (* make tuareg mode less blue >> *)
  }

(* DSLL32 reg, reg, imm5 *)

union ast member regregreg DSLL32
function clause decode (0b000000 : 0b00000 : (regno) rt : (regno) rd : (bit[5]) sa : 0b111100) = 
  Some(DSLL32(rt, rd, sa))
function clause execute (DSLL32 (rt, rd, sa)) =
  {
    wGPR(rd) := (rGPR(rt) << (0b1 : sa)) (* make tuareg mode less blue >> *)
  }

(* DSLLV reg, reg, reg *)

union ast member regregreg DSLLV
function clause decode (0b000000 : (regno) rs : (regno) rt : (regno) rd : 0b00000 : 0b101100) = 
  Some(DSLLV(rs, rt, rd))
function clause execute (DSLLV (rs, rt, rd)) =
  {
    wGPR(rd) := (rGPR(rs) << ((rGPR(rt))[5 .. 0])) (* make tuareg mode less blue >> *)
    (* alternative slicing based version of above 
    sa       := (rGPR(rt))[5 .. 0];
    v        := rGPR(rs);
    wGPR(rd) := v[(63-sa) .. 0] : (0b0 ^^ sa)  *)
  }

(* DSRA arithmetic shift duplicating sign bit - reg, reg, imm5 *)

union ast member regregreg DSRA
function clause decode (0b000000 : 0b00000 : (regno) rt : (regno) rd : (bit[5]) sa : 0b111011) = 
  Some(DSRA(rt, rd, sa))
function clause execute (DSRA (rt, rd, sa)) =
  {
    temp     := rGPR(rt);
    wGPR(rd) := ((temp[63] ^^ sa) : (temp[63 .. sa]))
  }

(* DSRA32 reg, reg, imm5 *)

union ast member regregreg DSRA32
function clause decode (0b000000 : 0b00000 : (regno) rt : (regno) rd : (bit[5]) sa : 0b111111) = 
  Some(DSRA32(rt, rd, sa))
function clause execute (DSRA32 (rt, rd, sa)) =
  {
    temp     := rGPR(rt);
    sa32     := (0b1 : sa); (* sa+32 *)
    wGPR(rd) := ((temp[63] ^^ sa32) : (temp[63 .. sa32]))
  }

(* DSRAV reg, reg, reg *)
union ast member regregreg DSRAV
function clause decode (0b000000 : (regno) rs : (regno) rt : (regno) rd : 0b00000 : 0b010111) =
  Some(DSRAV(rs, rt, rd))
function clause execute (DSRAV (rs, rt, rd)) =
  {
    temp     := rGPR(rt);
    sa       := (rGPR(rs)) [5..0];
    wGPR(rd) := ((temp[63] ^^ sa) : temp[63 .. sa])
  }

(* DSRL shift right logical - reg, reg, imm5 *)

union ast member regregreg DSRL
function clause decode (0b000000 : 0b00000 : (regno) rt : (regno) rd : (bit[5]) sa : 0b111010) = 
  Some(DSRL(rt, rd, sa))
function clause execute (DSRL (rt, rd, sa)) =
  {
    temp     := rGPR(rt);
    wGPR(rd) := ((bitzero ^^ sa) : (temp[63 .. sa]))
  }

(* DSRL32 reg, reg, imm5 *)

union ast member regregreg DSRL32
function clause decode (0b000000 : 0b00000 : (regno) rt : (regno) rd : (bit[5]) sa : 0b111110) = 
  Some(DSRA32(rt, rd, sa))
function clause execute (DSRL32 (rt, rd, sa)) =
  {
    temp     := rGPR(rt);
    sa32     := (0b1 : sa); (* sa+32 *)
    wGPR(rd) := ((bitzero ^^ sa32) : (temp[63 .. sa32]))
  }

(* DSRLV reg, reg, reg *)

union ast member regregreg DSRLV
function clause decode (0b000000 : (regno) rs : (regno) rt : (regno) rd : 0b00000 : 0b010110) = 
  Some(DSRLV(rs, rt, rd))
function clause execute (DSRLV (rs, rt, rd)) =
  {
    temp     := rGPR(rt);
    sa       := (rGPR(rs)) [5..0];
    wGPR(rd) := ((bitone ^^ sa) : temp[63 .. sa])
  }

(**************************************************************************************)
(* 32-bit  shift operations                                                           *)
(**************************************************************************************)

(* SLL 32-bit shift left *)

union ast member regregreg SLL
function clause decode (0b000000 : 0b00000 : (regno) rt : (regno) rd : (regno) sa : 0b000000) = 
  Some(SLL(rt, rd, sa))
function clause execute (SLL(rt, rd, sa)) =
  {
    wGPR(rd) := EXTS((rGPR(rt)) [(31-sa)..0] : (bitzero ^^ sa))
  }

(* SLLV 32-bit shift left variable *)

union ast member regregreg SLLV
function clause decode (0b000000 : (regno) rs : (regno) rt : (regno) rd : 0b00000 : 0b000100) = 
  Some(SLLV(rs, rt, rd))
function clause execute (SLLV(rs, rt, rd)) =
  {
    sa       := (rGPR(rs))[4..0];
    wGPR(rd) := EXTS((rGPR(rt)) [(31-sa)..0] : (bitzero ^^ sa))
  }

(* SRA 32-bit arithmetic shift right *)

union ast member regregreg SRA
function clause decode (0b000000 : 0b00000 : (regno) rt : (regno) rd : (regno) sa : 0b000011) = 
  Some(SRA(rt, rd, sa))
function clause execute (SRA(rt, rd, sa)) =
  {
    temp := rGPR(rt);
    if (NotWordVal(temp)) then
      wGPR(rd) := undefined
    else
      wGPR(rd) := (temp[31] ^^ (sa+32)) : temp [31..sa]
  }

(* SRAV 32-bit arithmetic shift right variable *)

union ast member regregreg SRAV
function clause decode (0b000000 : (regno) rs : (regno) rt : (regno) rd : 0b00000 : 0b000111) = 
  Some(SRAV(rs, rt, rd))
function clause execute (SRAV(rs, rt, rd)) =
  {
    temp := rGPR(rt);
    sa   := (rGPR(rs))[4..0];
    if (NotWordVal(temp)) then
      wGPR(rd) := undefined
    else
      wGPR(rd) := (temp[31] ^^ (sa+32)) : temp [31..sa]
  }

(* SRL 32-bit shift right *)

union ast member regregreg SRL
function clause decode (0b000000 : 0b00000 : (regno) rt : (regno) rd : (regno) sa : 0b000010) = 
  Some(SRL(rt, rd, sa))
function clause execute (SRL(rt, rd, sa)) =
  {
    temp := rGPR(rt);
    if (NotWordVal(temp)) then
      wGPR(rd) := undefined
    else
      wGPR(rd) := EXTS((bitzero ^^ sa) : (temp [31..sa]))
  }

(* SRLV 32-bit shift right variable *)

union ast member regregreg SRLV
function clause decode (0b000000 : (regno) rs : (regno) rt : (regno) rd : 0b00000 : 0b000110) = 
  Some(SRLV(rs, rt, rd))
function clause execute (SRLV(rs, rt, rd)) =
  {
    temp := rGPR(rt);
    sa   := (rGPR(rs))[4..0];
    if (NotWordVal(temp)) then
      wGPR(rd) := undefined
    else
      wGPR(rd) := EXTS((bitzero ^^ sa) : (temp [31..sa]))
  }

(**************************************************************************************)
(* set less than / conditional move                                                    *)
(**************************************************************************************)

(* SLT set if less than (signed) *)

union ast member regregreg SLT
function clause decode (0b000000 : (regno) rs : (regno) rt : (regno) rd : 0b00000 : 0b101010) = 
  Some(SLT(rs, rt, rd))
function clause execute (SLT(rs, rt, rd)) =
  {
    wGPR(rd) := if (rGPR(rs) <_s rGPR(rt)) then 1 else 0
  }

(* SLT set if less than immediate (signed) *)

union ast member regregimm16 SLTI
function clause decode (0b001010 : (regno) rs : (regno) rt : (imm16) imm) = 
  Some(SLTI(rs, rt, imm))
function clause execute (SLTI(rs, rt, imm)) =
  {
    wGPR(rt) := if (rGPR(rs) <_s EXTS(imm)) then 1 else 0
  }

(* SLTU set if less than unsigned *)

union ast member regregreg SLTU
function clause decode (0b000000 : (regno) rs : (regno) rt : (regno) rd : 0b00000 : 0b101011) = 
  Some(SLT(rs, rt, rd))
function clause execute (SLTU(rs, rt, rd)) =
  {
    wGPR(rd) := if (rGPR(rs) < rGPR(rt)) then 1 else 0
  }

(* SLTIU set if less than immediate unsigned *)

union ast member regregimm16 SLTIU
function clause decode (0b001011 : (regno) rs : (regno) rt : (imm16) imm) = 
  Some(SLTIU(rs, rt, imm))
function clause execute (SLTIU(rs, rt, imm)) =
  {
    wGPR(rt) := if (rGPR(rs) < EXTS(imm)) then 1 else 0
  }

(* MOVN move if non-zero *)

union ast member regregreg MOVN
function clause decode (0b000000 : (regno) rs : (regno) rt : (regno) rd : 0b00000 : 0b001011) = 
  Some(MOVN(rs, rt, rd))
function clause execute (MOVN(rs, rt, rd)) =
  {
    if (rGPR(rt) != 0) then 
      wGPR(rd) := rGPR(rs)
  }

(* MOVZ move if zero *)

union ast member regregreg MOVZ
function clause decode (0b000000 : (regno) rs : (regno) rt : (regno) rd : 0b00000 : 0b001010) = 
  Some(MOVZ(rs, rt, rd))
function clause execute (MOVZ(rs, rt, rd)) =
  {
    if (rGPR(rt) == 0) then 
      wGPR(rd) := rGPR(rs)
  }

(******************************************************************************)
(* MUL/DIV instructions                                                       *)
(******************************************************************************)

(* MFHI move from HI register *)
union ast member regno MFHI
function clause decode (0b000000 : 0b0000000000 : (regno) rd : 0b00000 : 0b010000) = 
  Some(MFHI(rd))
function clause execute (MFHI(rd)) =
  {
    wGPR(rd) := HI
  }

(* MFLO move from LO register *)
union ast member regno MFLO
function clause decode (0b000000 : 0b0000000000 : (regno) rd : 0b00000 : 0b010010) = 
  Some(MFLO(rd))
function clause execute (MFLO(rd)) =
  {
    wGPR(rd) := LO
  }

(* MTHI move to HI register *)
union ast member regno MTHI
function clause decode (0b000000 : (regno) rs : 0b000000000000000 : 0b010001) = 
  Some(MTHI(rs))
function clause execute (MTHI(rs)) =
  {
    HI := rGPR(rs)
  }

(* MTLO move to LO register *)
union ast member regno MTLO
function clause decode (0b000000 : (regno) rs : 0b000000000000000 : 0b010011) = 
  Some(MTLO(rs))
function clause execute (MTLO(rs)) =
  {
    LO := rGPR(rs)
  }

(* MUL 32-bit multiply into GPR *)
union ast member regregreg MUL
function clause decode (0b011100 : (regno) rs : (regno) rt : (regno) rd : 0b00000 : 0b000010) =
  Some(MUL(rs, rt, rd))
function clause execute (MUL(rs, rt, rd)) =
  {
    rsVal := rGPR(rs);
    rtVal := rGPR(rt);
    (bit[64]) result := (rsVal[31..0]) *_s (rtVal[31..0]);
    wGPR(rd) := if (NotWordVal(rsVal) | NotWordVal(rtVal)) then
        undefined
      else
        EXTS(result[31..0]);
    (* HI and LO are always undefined after MUL *)
    HI := undefined;
    LO := undefined;
  }

(* MULT 32-bit multiply into HI/LO *)
union ast member (regno, regno) MULT
function clause decode (0b000000 : (regno) rs : (regno) rt : 0b00000 : 0b00000 : 0b011000) =
  Some(MULT(rs, rt))
function clause execute (MULT(rs, rt)) =
  {
    rsVal := rGPR(rs);
    rtVal := rGPR(rt);
    (bit[64]) result := if (NotWordVal(rsVal) | NotWordVal(rtVal)) then
        undefined
      else
        (rsVal[31..0]) *_s (rtVal[31..0]);
    HI := EXTS(result[63..32]);
    LO := EXTS(result[31..0]);
  }

(* MULTU 32-bit unsignedm rultiply into HI/LO *)
union ast member (regno, regno) MULTU
function clause decode (0b000000 : (regno) rs : (regno) rt : 0b00000 : 0b00000 : 0b011001) =
  Some(MULTU(rs, rt))
function clause execute (MULTU(rs, rt)) =
  {
    rsVal := rGPR(rs);
    rtVal := rGPR(rt);
    (bit[64]) result := if (NotWordVal(rsVal) | NotWordVal(rtVal)) then
        undefined
      else
        (rsVal[31..0]) * (rtVal[31..0]);
    HI := EXTS(result[63..32]);
    LO := EXTS(result[31..0]);
  }

(* DMULT 64-bit multiply into HI/LO *)
union ast member (regno, regno) DMULT
function clause decode (0b000000 : (regno) rs : (regno) rt : 0b00000 : 0b00000 : 0b011100) =
  Some(DMULT(rs, rt))
function clause execute (DMULT(rs, rt)) =
  {
    (bit[128]) result := (rGPR(rs)) *_s (rGPR(rt));
    HI := (result[127..64]);
    LO := (result[63..0]);
  }

(* DMULTU 64-bit unsigned multiply into HI/LO *)
union ast member (regno, regno) DMULTU
function clause decode (0b000000 : (regno) rs : (regno) rt : 0b00000 : 0b00000 : 0b011101) =
  Some(DMULTU(rs, rt))
function clause execute (DMULTU(rs, rt)) =
  {
    (bit[128]) result := (rGPR(rs)) * (rGPR(rt));
    HI := (result[127..64]);
    LO := (result[63..0]);
  }

(* MADD 32-bit signed multiply and add into HI/LO *)
union ast member (regno, regno) MADD
function clause decode (0b011100 : (regno) rs : (regno) rt : 0b00000 : 0b00000 : 0b000000) =
  Some(MADD(rs, rt))
function clause execute (MADD(rs, rt)) =
  {
    rsVal := rGPR(rs);
    rtVal := rGPR(rt);
    (bit[64]) mul_result := if (NotWordVal(rsVal) | NotWordVal(rtVal)) then
        undefined
      else
        ((rsVal[31..0]) *_s (rtVal[31..0]));
    (bit[64]) result := mul_result + (HI[31..0] : LO[31..0]);
    HI := EXTS(result[63..32]);
    LO := EXTS(result[31..0]);
  }

(* MADDU 32-bit unsigned multiply and add into HI/LO *)
union ast member (regno, regno) MADDU
function clause decode (0b011100 : (regno) rs : (regno) rt : 0b00000 : 0b00000 : 0b000001) =
  Some(MADDU(rs, rt))
function clause execute (MADDU(rs, rt)) =
  {
    rsVal := rGPR(rs);
    rtVal := rGPR(rt);
    (bit[64]) mul_result := if (NotWordVal(rsVal) | NotWordVal(rtVal)) then
        undefined
      else
        ((rsVal[31..0]) * (rtVal[31..0]));
    (bit[64]) result := mul_result + (HI[31..0] : LO[31..0]);
    HI := EXTS(result[63..32]);
    LO := EXTS(result[31..0]);
  }

(* MSUB 32-bit signed multiply and sub from HI/LO *)
union ast member (regno, regno) MSUB
function clause decode (0b011100 : (regno) rs : (regno) rt : 0b00000 : 0b00000 : 0b000100) =
  Some(MSUB(rs, rt))
function clause execute (MSUB(rs, rt)) =
  {
    rsVal := rGPR(rs);
    rtVal := rGPR(rt);
    (bit[64]) mul_result := if (NotWordVal(rsVal) | NotWordVal(rtVal)) then
        undefined
      else
        ((rsVal[31..0]) *_s (rtVal[31..0]));
    (bit[64]) result := (HI[31..0] : LO[31..0]) - mul_result;
    HI := EXTS(result[63..32]);
    LO := EXTS(result[31..0]);
  }

(* MSUBU 32-bit unsigned multiply and sub from HI/LO *)
union ast member (regno, regno) MSUBU
function clause decode (0b011100 : (regno) rs : (regno) rt : 0b00000 : 0b00000 : 0b000101) =
  Some(MSUBU(rs, rt))
function clause execute (MSUBU(rs, rt)) =
  {
    rsVal := rGPR(rs);
    rtVal := rGPR(rt);
    (bit[64]) mul_result := if (NotWordVal(rsVal) | NotWordVal(rtVal)) then
        undefined
      else
        ((rsVal[31..0]) * (rtVal[31..0]));
    (bit[64]) result := (HI[31..0] : LO[31..0]) - mul_result;
    HI := EXTS(result[63..32]);
    LO := EXTS(result[31..0]);
  }

(* DIV 32-bit divide into HI/LO *)
union ast member (regno, regno) DIV
function clause decode (0b000000 : (regno) rs : (regno) rt : 0b00000 : 0b00000 : 0b011010) =
  Some(DIV(rs, rt))
function clause execute (DIV(rs, rt)) =
  {
    rsVal := rGPR(rs);
    rtVal := rGPR(rt);
    let ((bit[32]) q, (bit[32])r) = (if (NotWordVal(rsVal) | NotWordVal(rtVal)) then
        (undefined, undefined)
      else
        ((rsVal[31..0]) quot_s (rtVal[31..0]), (rsVal[31..0]) mod (rtVal[31..0])))
    in
    {
      HI := EXTS(r);
      LO := EXTS(q);
    }
  }

(* DIVU 32-bit unsigned divide into HI/LO *)
union ast member (regno, regno) DIVU
function clause decode (0b000000 : (regno) rs : (regno) rt : 0b00000 : 0b00000 : 0b011011) =
  Some(DIVU(rs, rt))
function clause execute (DIVU(rs, rt)) =
  {
    rsVal := rGPR(rs);
    rtVal := rGPR(rt);
    let ((bit[32]) q, (bit[32])r) = (if (NotWordVal(rsVal) | NotWordVal(rtVal)) then
        (undefined, undefined)
      else
        ((rsVal[31..0]) quot (rtVal[31..0]), (rsVal[31..0]) mod (rtVal[31..0])))
    in
    {
      HI := EXTS(r);
      LO := EXTS(q);
    }
  }

(* DDIV 64-bit divide into HI/LO *)
union ast member (regno, regno) DDIV
function clause decode (0b000000 : (regno) rs : (regno) rt : 0b00000 : 0b00000 : 0b011110) =
  Some(DDIV(rs, rt))
function clause execute (DDIV(rs, rt)) =
  {
    rsVal := rGPR(rs);
    rtVal := rGPR(rt);
    LO    := rsVal quot_s rtVal;
    HI    := rsVal mod rtVal; (* signed? *)
  }

(* DDIV 64-bit divide into HI/LO *)
union ast member (regno, regno) DDIVU
function clause decode (0b000000 : (regno) rs : (regno) rt : 0b00000 : 0b00000 : 0b011111) =
  Some(DDIVU(rs, rt))
function clause execute (DDIVU(rs, rt)) =
  {
    rsVal := rGPR(rs);
    rtVal := rGPR(rt);
    LO    := rsVal quot rtVal;
    HI    := rsVal mod rtVal;
  }

(**************************************************************************************)
(* Jump instructions -- unconditional branches                                        *)
(**************************************************************************************)

(* J    - jump, the simplest control flow instruction, with branch delay slot *)
union ast member (bit[26]) J
function clause decode (0b000010 : (bit[26]) offset) =
  Some(J(offset))
function clause execute (J(offset)) = 
  {
    delayedPC     := PC[63..28] : offset : 0b00;
    branchPending := 1
  }

(* JAL    - jump and link *)
union ast member (bit[26]) JAL
function clause decode (0b000011 : (bit[26]) offset) =
  Some(JAL(offset))
function clause execute (JAL(offset)) = 
  {
    delayedPC     := PC[63..28] : offset : 0b00;
    branchPending := 1;
    wGPR(31)      := PC + 8;
  }

(* JR -- jump via register *)
union ast member regno JR
function clause decode (0b000000 : (regno) rs : 0b00000 : 0b00000 : (regno) hint : 0b001000) =
  Some(JR(rs)) (* hint is ignored *)
function clause execute (JR(rs)) =
  {
    delayedPC     := rGPR(rs);
    branchPending := 1;
  }

(* JALR -- jump via register with link *)
union ast member (regno, regno) JALR
function clause decode (0b000000 : (regno) rs : 0b00000 : (regno) rd : (regno) hint : 0b001001) =
  Some(JALR(rs, rd)) (* hint is ignored *)
function clause execute (JALR(rs, rd)) =
  {
    delayedPC     := rGPR(rs);
    branchPending := 1;
    wGPR(rd)      := PC + 8;
  }

(**************************************************************************************)
(* B[N]EQ[L]  - branch on (not) equal (likely)                                        *)
(* Conditional branch instructions with two register operands                         *)
(**************************************************************************************)

union ast member (regno, regno, imm16, bool, bool) BEQ
function clause decode (0b000100 : (regno) rs : (regno) rt : (imm16) imm) =  Some(BEQ(rs, rt, imm, false, false))  (* BEQ  *)
function clause decode (0b000100 : (regno) rs : (regno) rt : (imm16) imm) =  Some(BEQ(rs, rt, imm, false, true))   (* BEQL *)
function clause decode (0b000101 : (regno) rs : (regno) rt : (imm16) imm) =  Some(BEQ(rs, rt, imm, true , false))  (* BNE  *)
function clause decode (0b010101 : (regno) rs : (regno) rt : (imm16) imm) =  Some(BEQ(rs, rt, imm, true , true))   (* BNEL *)
function clause execute (BEQ(rs, rd, imm, ne, likely)) =
  {
    if ((rGPR(rs) == rGPR(rd)) ^ ne) then
      {
        delayedPC     := PC + EXTS(imm : 0b00);
        branchPending := 1;
      }
    else
      {
        if (likely) then
          nextPC := PC + 8; (* skip branch delay *)
      }
  }

(* 
   
   Branches comparing with zero (single register operand, possible link in r31)
*)

(**************************************************************************************)
(* BGEZ[AL][L] - branch on comparison with zero (possibly  link, likely)              *)
(* Conditional branch instructions with single register operand                       *)
(**************************************************************************************)

union ast member (regno, imm16, Comparison, bool, bool) BCMPZ
function clause decode (0b000001 : (regno) rs : 0b00000 : (imm16) imm) = Some(BCMPZ(rs, imm, LT, false, false)) (* BLTZ *)
function clause decode (0b000001 : (regno) rs : 0b10000 : (imm16) imm) = Some(BCMPZ(rs, imm, LT, true, false))  (* BLTZAL *)
function clause decode (0b000001 : (regno) rs : 0b00010 : (imm16) imm) = Some(BCMPZ(rs, imm, LT, false, true))  (* BLTZL *)
function clause decode (0b000001 : (regno) rs : 0b10010 : (imm16) imm) = Some(BCMPZ(rs, imm, LT, true, true))   (* BLTZALL *)

function clause decode (0b000001 : (regno) rs : 0b00001 : (imm16) imm) = Some(BCMPZ(rs, imm, GE, false, false)) (* BGEZ *)
function clause decode (0b000001 : (regno) rs : 0b10001 : (imm16) imm) = Some(BCMPZ(rs, imm, GE, true, false))  (* BGEZAL *)
function clause decode (0b000001 : (regno) rs : 0b00011 : (imm16) imm) = Some(BCMPZ(rs, imm, GE, false, true))  (* BGEZL *)
function clause decode (0b000001 : (regno) rs : 0b10011 : (imm16) imm) = Some(BCMPZ(rs, imm, GE, true, true))   (* BGEZALL *)

function clause decode (0b000111 : (regno) rs : 0b00000 : (imm16) imm) = Some(BCMPZ(rs, imm, GT, false, false)) (* BGTZ *)
function clause decode (0b010111 : (regno) rs : 0b00000 : (imm16) imm) = Some(BCMPZ(rs, imm, GT, false, true))  (* BGTZL *)

function clause decode (0b000110 : (regno) rs : 0b00000 : (imm16) imm) = Some(BCMPZ(rs, imm, LE, false, false)) (* BLEZ *)
function clause decode (0b010110 : (regno) rs : 0b00000 : (imm16) imm) = Some(BCMPZ(rs, imm, LE, false, true))  (* BLEZL *)

function clause execute (BCMPZ(rs, imm, cmp, link, likely)) =
  {
    (bit[64]) linkVal := PC + 8;
    regVal := rGPR(rs);
    condition := compare(cmp, regVal, 0);
    if (condition) then
      {
        delayedPC := PC + EXTS(imm : 0b00);
        branchPending := 1;
      }
    else if (likely) then
      {
        nextPC := PC + 8  (* skip branch delay *)
      };
    if (link) then
      wGPR(31) := linkVal
  }

(**************************************************************************************)
(* SYSCALL/BREAK/WAIT/Trap                                                            *)
(**************************************************************************************)

union ast member unit SYSCALL
function clause decode (0b000000 : (bit[20]) code : 0b001100) =
  Some(SYSCALL) (* code is ignored *)
function clause execute (SYSCALL) =
  {
    SignalException(Sys)
  }

(* BREAK is identical to SYSCALL exception for the exception raised *)
union ast member unit BREAK
function clause decode (0b000000 : (bit[20]) code : 0b001101) =
  Some(BREAK) (* code is ignored *)
function clause execute (BREAK) =
  {
    SignalException(Bp)
  }

(* Accept WAIT as a NOP *)
union ast member unit WAIT
function clause decode (0b010000 : 0x80000 : 0b100000) =
  Some(WAIT) (* we only accept code == 0 *)
function clause execute (WAIT) = ()

(* Trap instructions with two register operands *)
union ast member (regno, regno, Comparison) TRAPREG
function clause decode (0b000000 : (regno) rs : (regno) rt : (bit[10]) code : 0b110000) = Some(TRAPREG(rs, rt, GE)) (* TGE *)
function clause decode (0b000000 : (regno) rs : (regno) rt : (bit[10]) code : 0b110001) = Some(TRAPREG(rs, rt, GEU)) (* TGEU *)
function clause decode (0b000000 : (regno) rs : (regno) rt : (bit[10]) code : 0b110010) = Some(TRAPREG(rs, rt, LT)) (* TLT *)
function clause decode (0b000000 : (regno) rs : (regno) rt : (bit[10]) code : 0b110011) = Some(TRAPREG(rs, rt, LTU)) (* TLTU *)
function clause decode (0b000000 : (regno) rs : (regno) rt : (bit[10]) code : 0b110100) = Some(TRAPREG(rs, rt, EQ)) (* TEQ *)
function clause decode (0b000000 : (regno) rs : (regno) rt : (bit[10]) code : 0b110110) = Some(TRAPREG(rs, rt, NE)) (* TNE *)
function clause execute (TRAPREG(rs, rt, cmp)) =
  {
    rs_val := rGPR(rs);
    rt_val := rGPR(rt);
    condition := compare(cmp, rs_val, rt_val);
    if (condition) then
      SignalException(Tr)
  }


(* Trap instructions with one register and one immediate operand *)
union ast member (regno, imm16, Comparison) TRAPIMM
function clause decode (0b000001 : (regno) rs : 0b01100 : (imm16) imm) = Some(TRAPIMM(rs, imm, EQ)) (* TEQI *)
function clause decode (0b000001 : (regno) rs : 0b01110 : (imm16) imm) = Some(TRAPIMM(rs, imm, NE)) (* TNEI *)
function clause decode (0b000001 : (regno) rs : 0b10000 : (imm16) imm) = Some(TRAPIMM(rs, imm, GE)) (* TGEI *)
function clause decode (0b000001 : (regno) rs : 0b10001 : (imm16) imm) = Some(TRAPIMM(rs, imm, GEU)) (* TGEIU *)
function clause decode (0b000001 : (regno) rs : 0b01010 : (imm16) imm) = Some(TRAPIMM(rs, imm, LT))  (* TLTI *)
function clause decode (0b000001 : (regno) rs : 0b01011 : (imm16) imm) = Some(TRAPIMM(rs, imm, LTU))  (* TLTIU *)
function clause execute (TRAPIMM(rs, imm, cmp)) =
  {
    rs_val := rGPR(rs);
    imm_val := EXTS(imm);
    condition := compare(cmp, rs_val, imm_val);
    if (condition) then
      SignalException(Tr)
  }

(**************************************************************************************)
(* Load instructions -- various width/signs                                           *)
(**************************************************************************************)

union ast member (WordType, bool, bool, regno, regno, imm16) Load
function clause decode (0b100000 : (regno) base : (regno) rt : (imm16) offset) = Some(Load(B, true,  false, base, rt, offset)) (* LB *)
function clause decode (0b100100 : (regno) base : (regno) rt : (imm16) offset) = Some(Load(B, false, false, base, rt, offset)) (* LBU *)
function clause decode (0b100001 : (regno) base : (regno) rt : (imm16) offset) = Some(Load(H, true,  false, base, rt, offset)) (* LH *)
function clause decode (0b100101 : (regno) base : (regno) rt : (imm16) offset) = Some(Load(H, false, false, base, rt, offset)) (* LHU *)
function clause decode (0b100011 : (regno) base : (regno) rt : (imm16) offset) = Some(Load(W, true,  false, base, rt, offset)) (* LW *)
function clause decode (0b100111 : (regno) base : (regno) rt : (imm16) offset) = Some(Load(W, false, false, base, rt, offset)) (* LWU *)
function clause decode (0b110111 : (regno) base : (regno) rt : (imm16) offset) = Some(Load(D, false, false, base, rt, offset)) (* LD *)
function clause decode (0b110000 : (regno) base : (regno) rt : (imm16) offset) = Some(Load(W, false, true, base, rt, offset))  (* LL *)
function clause decode (0b110100 : (regno) base : (regno) rt : (imm16) offset) = Some(Load(D, false, true, base, rt, offset))  (* LLD *)
function clause execute (Load(width, signed, linked, base, rt, offset)) =
  {
    (bit[64]) vAddr := EXTS(offset) + rGPR(base);
    if ~ (isAddressAligned(vAddr, width)) then
      SignalException(AdEL) (* unaligned access *)
    else
      let (ex, pAddr) = (TranslateAddress(vAddr, LoadData)) in
      {
        if ~ (ex) then
          {
            memResult := if (linked) then
                MEMr_reserve(pAddr, wordWidthBytes(width))
              else
                MEMr(pAddr, wordWidthBytes(width));
            if (signed) then
              wGPR(rt) := EXTS(memResult)
            else
              wGPR(rt) := EXTZ(memResult)
          }
      }
  }

(**************************************************************************************)
(* Store instructions -- various widths                                               *)
(**************************************************************************************)

union ast member (WordType, bool, regno, regno, imm16) Store
function clause decode (0b101000 : (regno) base : (regno) rt : (imm16) offset) = Some(Store(B, false, base, rt, offset)) (* SB *)
function clause decode (0b101001 : (regno) base : (regno) rt : (imm16) offset) = Some(Store(H, false, base, rt, offset)) (* SH *)
function clause decode (0b101011 : (regno) base : (regno) rt : (imm16) offset) = Some(Store(W, false, base, rt, offset)) (* SW *)
function clause decode (0b111111 : (regno) base : (regno) rt : (imm16) offset) = Some(Store(D, false, base, rt, offset)) (* SD *)
function clause decode (0b111000 : (regno) base : (regno) rt : (imm16) offset) = Some(Store(W, true, base, rt, offset))  (* SC *)
function clause decode (0b111100 : (regno) base : (regno) rt : (imm16) offset) = Some(Store(D, true, base, rt, offset))  (* SCD *)
function clause execute (Store(width, conditional, base, rt, offset)) =
      {
        (bit[64]) vAddr := EXTS(offset) + rGPR(base);
        if ~ (isAddressAligned(vAddr, width)) then
          SignalException(AdES) (* unaligned access *)
        else
          let (ex, pAddr) = (TranslateAddress(vAddr, StoreData)) in
          {
            if ~ (ex) then
              {
                if (conditional) then
                  {
                    success  := (MEMw_conditional(vAddr, wordWidthBytes(width), rGPR(rt)));
                    wGPR(rt) := EXTZ([success])
                  }
                else
                  MEMw(vAddr, wordWidthBytes(width)) := rGPR(rt)
              }
          }
      }

(* LWL   - Load word left (big-endian only) *)

union ast member regregimm16 LWL
function clause decode(0b100010 : (regno) base : (regno) rt : (imm16) offset) =
      Some(LWL(base, rt, offset))
function clause execute(LWL(base, rt, offset)) = 
      {
        (bit[64]) vAddr := EXTS(offset) + rGPR(base);
        let (ex, pAddr) = (TranslateAddress(vAddr, LoadData)) in
        if ~ (ex) then
          {
            mem_val   := MEMr (pAddr[63..2] : 0b00, 4); (* read word of interest *)
            reg_val   := rGPR(rt);
            wGPR(rt)  := EXTS(switch(vAddr[1..0])
              {
                case 0b00 -> mem_val
                case 0b01 -> mem_val[23..0] : reg_val[07..0]
                case 0b10 -> mem_val[15..0] : reg_val[15..0]
                case 0b11 -> mem_val[07..0] : reg_val[23..0]
              });
          }
      }
union ast member regregimm16 LWR
function clause decode(0b100110 : (regno) base : (regno) rt : (imm16) offset) =
      Some(LWR(base, rt, offset))
function clause execute(LWR(base, rt, offset)) = 
      {
        (bit[64]) vAddr := EXTS(offset) + rGPR(base);
        let (ex, pAddr) = (TranslateAddress(vAddr, LoadData)) in
        if ~ (ex) then
          {
            mem_val   := MEMr (pAddr[63..2] : 0b00, 4); (* read word of interest *)
            reg_val   := rGPR(rt);
            wGPR(rt)  := EXTS(switch(vAddr[1..0]) (* it is acceptable to sign extend in all cases *)
              {
                case 0b00 -> reg_val[31..8]  : mem_val[7..0]
                case 0b01 -> reg_val[31..16] : mem_val[15..0]
                case 0b10 -> reg_val[31..24] : mem_val[23..0]
                case 0b11 -> mem_val
              });
          }
      }

(* SWL   - Store word left *)
union ast member regregimm16 SWL
function clause decode(0b101010 : (regno) base : (regno) rt : (imm16) offset) =
      Some(SWL(base, rt, offset))
function clause execute(SWL(base, rt, offset)) = 
      {
        (bit[64]) vAddr := EXTS(offset) + rGPR(base);
        let (ex, pAddr) = (TranslateAddress(vAddr, StoreData)) in
        if ~ (ex) then
          {
            reg_val   := rGPR(rt);
            switch (vAddr[1..0])
            {
              case 0b00 -> (MEMw(pAddr, 4) := reg_val[31..0])
              case 0b01 -> (MEMw(pAddr, 3) := reg_val[31..8])
              case 0b10 -> (MEMw(pAddr, 2) := reg_val[31..16])
              case 0b11 -> (MEMw(pAddr, 1) := reg_val[31..24])
            }
          }
      }

union ast member regregimm16 SWR
function clause decode(0b101110 : (regno) base : (regno) rt : (imm16) offset) =
      Some(SWR(base, rt, offset))
function clause execute(SWR(base, rt, offset)) = 
      {
        (bit[64]) vAddr := EXTS(offset) + rGPR(base);
        let (ex, pAddr) = (TranslateAddress(vAddr, StoreData)) in
        if ~ (ex) then
          {
            wordAddr := pAddr[63..2] : 0b00;
            reg_val   := rGPR(rt);
            switch (vAddr[1..0])
              {
                case 0b00 -> (MEMw(wordAddr, 1) := reg_val[7..0])
                case 0b01 -> (MEMw(wordAddr, 2) := reg_val[15..0])
                case 0b10 -> (MEMw(wordAddr, 3) := reg_val[23..0])
                case 0b11 -> (MEMw(wordAddr, 4) := reg_val[31..0])
              }
          }
      }

(* Load double-word left *)
union ast member regregimm16 LDL
function clause decode(0b011010 : (regno) base : (regno) rt : (imm16) offset) =
  Some(LDL(base, rt, offset))
function clause execute(LDL(base, rt, offset)) = 
  {
    (bit[64]) vAddr := EXTS(offset) + rGPR(base);
    let (ex, pAddr) = (TranslateAddress(vAddr, StoreData)) in
    if ~ (ex) then
      {
        mem_val   := MEMr (pAddr[63..3] : 0b000, 8); (* read double of interest *)
        reg_val   := rGPR(rt);
        wGPR(rt)  := switch(vAddr[2..0])
              {
                case 0b000 -> mem_val
                case 0b001 -> mem_val[55..0] : reg_val[7..0]
                case 0b010 -> mem_val[47..0] : reg_val[15..0]
                case 0b011 -> mem_val[39..0] : reg_val[23..0]
                case 0b100 -> mem_val[31..0] : reg_val[31..0]
                case 0b101 -> mem_val[23..0] : reg_val[39..0]
                case 0b110 -> mem_val[15..0] : reg_val[47..0]
                case 0b111 -> mem_val[07..0] : reg_val[55..0]
              };
      }
  }

(* Load double-word right *)
union ast member regregimm16 LDR
function clause decode(0b011011 : (regno) base : (regno) rt : (imm16) offset) =
  Some(LDR(base, rt, offset))
function clause execute(LDR(base, rt, offset)) = 
  {
    (bit[64]) vAddr := EXTS(offset) + rGPR(base);
    let (ex, pAddr) = (TranslateAddress(vAddr, StoreData)) in
    if ~ (ex) then
      {
        mem_val   := MEMr (pAddr[63..3] : 0b000, 8); (* read double of interest *)
        reg_val   := rGPR(rt);
        wGPR(rt)  := switch(vAddr[2..0])
              {
                case 0b000 -> reg_val[55..0] : mem_val[07..0]
                case 0b001 -> reg_val[47..0] : mem_val[15..0]
                case 0b010 -> reg_val[39..0] : mem_val[23..0]
                case 0b011 -> reg_val[31..0] : mem_val[31..0]
                case 0b100 -> reg_val[23..0] : mem_val[39..0]
                case 0b101 -> reg_val[15..0] : mem_val[47..0]
                case 0b110 -> reg_val[07..0] : mem_val[55..0]
                case 0b111 -> mem_val
              };
      }
  }

(* SDL   - Store double-word left *)
union ast member regregimm16 SDL
function clause decode(0b101100 : (regno) base : (regno) rt : (imm16) offset) =
      Some(SDL(base, rt, offset))
function clause execute(SDL(base, rt, offset)) = 
      {
        (bit[64]) vAddr := EXTS(offset) + rGPR(base);
        let (ex, pAddr) = (TranslateAddress(vAddr, StoreData)) in
        if ~ (ex) then
          {
            reg_val := rGPR(rt);
            switch (vAddr[2..0])
            {
              case 0b000 -> (MEMw(pAddr, 8) := reg_val[63..00])
              case 0b001 -> (MEMw(pAddr, 7) := reg_val[63..08])
              case 0b010 -> (MEMw(pAddr, 6) := reg_val[63..16])
              case 0b011 -> (MEMw(pAddr, 5) := reg_val[63..24])
              case 0b100 -> (MEMw(pAddr, 4) := reg_val[63..32])
              case 0b101 -> (MEMw(pAddr, 3) := reg_val[63..40])
              case 0b110 -> (MEMw(pAddr, 2) := reg_val[63..48])
              case 0b111 -> (MEMw(pAddr, 1) := reg_val[63..56])
            }
          }
      }


(* SDR   - Store double-word right *)
union ast member regregimm16 SDR
function clause decode(0b101101 : (regno) base : (regno) rt : (imm16) offset) =
      Some(SDR(base, rt, offset))
function clause execute(SDR(base, rt, offset)) = 
      {
        (bit[64]) vAddr := EXTS(offset) + rGPR(base);
        let (ex, pAddr) = (TranslateAddress(vAddr, StoreData)) in
        if ~ (ex) then
          {
            reg_val := rGPR(rt);
            wordAddr := pAddr[63..3] : 0b000;
            switch (vAddr[2..0])
            {
              case 0b000 -> (MEMw(wordAddr, 1) := reg_val[07..0])
              case 0b001 -> (MEMw(wordAddr, 2) := reg_val[15..0])
              case 0b010 -> (MEMw(wordAddr, 3) := reg_val[23..0])
              case 0b011 -> (MEMw(wordAddr, 4) := reg_val[31..0])
              case 0b100 -> (MEMw(wordAddr, 5) := reg_val[39..0])
              case 0b101 -> (MEMw(wordAddr, 6) := reg_val[47..0])
              case 0b110 -> (MEMw(wordAddr, 7) := reg_val[55..0])
              case 0b111 -> (MEMw(wordAddr, 8) := reg_val[63..0])
            }
          }
      }

(* CACHE - manipulate (non-existent) caches *)

union ast member regregimm16 CACHE
function clause decode (0b101111 : (regno) base : (regno) op : (imm16) imm) =
  Some(CACHE(base, op, imm))
function clause execute (CACHE(base, op, imm)) =
  () (* XXX NOP *)

(* PREF - prefetching into (non-existent) caches *)

union ast member regregimm16 PREF
function clause decode (0b110011 : (regno) base : (regno) op : (imm16) imm) =
  Some(PREF(base, op, imm))
function clause execute (PREF(base, op, imm)) =
  () (* XXX NOP *)


(* SYNC  - Memory barrier *)
union ast member unit SYNC
function clause decode (0b000000 : 0b00000 : 0b00000 : 0b00000 : (regno) stype : 0b001111) = 
  Some(SYNC()) (* stype is currently ignored *)
function clause execute(SYNC) =
  MEM_sync()

union ast member unit HCF
function clause decode (0b010000 : 0b00100 : (regno) rt : 0b10111 : 0b00000000000) =
  Some(HCF()) (* simulator halt instruction "MTC0 rt, $23" (cheri specific behaviour) *)

function clause decode (0b010000 : 0b00100 : (regno) rt : 0b11010 : 0b00000000000) =
  Some(HCF()) (* simulator halt instruction "MTC0 rt, $26" (cheri specific behaviour) *)

function clause execute (HCF) =
  () (* halt instruction actually executed by interpreter framework *)

function clause decode _ = None

end decode
end execute
end ast

function option<ast> supported_instructions (instr) = Some(instr)
