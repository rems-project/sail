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
register (bit[32])  CP0Compare
register (CauseReg) CP0Cause
register (bit[64])  CP0EPC
register (bit[64])  CP0ErrorEPC
register (bit[1])   CP0LLBit
register (bit[64])  CP0LLAddr
register (bit[64])  CP0BadVAddr

typedef StatusReg = register bits [31:0] {
  31 .. 28        : CU;  (* co-processor enable bits *)
  (* RP/FR/RE/MX/PX not implemented *)
  22              : BEV; (* use boot exception vectors XXX initialise to one *)
  (* TS/SR/NMI not implemented *)
  15 .. 8         : IM;  (* Interrupt mask *)
  7               : KX;  (* kernel 64-bit enable *)
  6               : SX;  (* supervisor 64-bit enable *)
  5               : UX;  (* user 64-bit enable *)
  4 .. 3          : KSU; (* Processor mode *)
  2               : ERL; (* error level XXX initialise to one *)
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

(* Check whether a given 64-bit vector is a properly sign extended 32-bit word *)
val bit[64] -> bool effect pure NotWordVal
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


val Exception -> unit effect {rreg, wreg} SignalException

function unit SignalExceptionMIPS ((Exception) ex) = 
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
      CP0Cause.ExcCode      := ExceptionCode(ex);
      CP0Status.EXL         := 1;
  }

function unit SignalExceptionBadAddr((Exception) ex, (bit[64]) badAddr) =
  {
    CP0BadVAddr := badAddr;
    SignalException(ex);
  }

typedef MemAccessType = enumerate {Instruction; LoadData; StoreData}
typedef AccessLevel   = enumerate {Kernel; Supervisor; User}
function (option<Exception>, option<bit[64]>) TLBTranslate ((bit[64]) vAddr, (MemAccessType) accessType) = 
  {
    err := (if (accessType == StoreData) then Some(AdES) else Some(AdEL));
    switch(vAddr[63..62]) {
      case 0b11 -> switch(vAddr[61..31], vAddr[30..29]) { (* xkseg *)
        case (0b1111111111111111111111111111111, 0b11) -> (err, None)  (* kseg3 mapped 32-bit compat TODO *)
        case (0b1111111111111111111111111111111, 0b10) -> (err, None)  (* sseg  mapped 32-bit compat TODO *)
        case (0b1111111111111111111111111111111, 0b01) -> (None, Some(EXTZ(vAddr[28..0]))) (* kseg1 unmapped uncached 32-bit compat *)
        case (0b1111111111111111111111111111111, 0b00) -> (None, Some(EXTZ(vAddr[28..0]))) (* kseg0 unmapped cached 32-bit compat *)
        case (_, _) -> (err, None)  (* xkseg mapped TODO *)
      }
      case 0b10 -> (None, Some(EXTZ(vAddr[58..0]))) (* xkphys bits 61-59 are cache mode which we ignore *)
      case 0b01 -> (err, None) (* xsseg - supervisor mapped TODO *)
      case 0b00 -> (err, None) (* xuseg - user mapped TODO *)
    }
  }

function bit[64] TranslateOrExit((bit[64]) vAddr, (MemAccessType) accessType) =
  switch (TLBTranslate(vAddr, accessType)) {
    case ((Some(ex)), _)    -> (exit (SignalExceptionBadAddr (ex, vAddr)))
    case (_, (Some(pAddr))) -> pAddr
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
  let valA65 = (0b0 : valA) in (* sail comparisons are signed so extend to 65 bits for unsigned comparisons *)
  let valB65 = (0b0 : valB) in
  switch(cmp) {
    case EQ  -> valA ==   valB
    case NE  -> valA !=   valB
    case GE  -> valA >=   valB
    case GEU -> valA65 >= valB65
    case GT  -> valA >    valB
    case LE  -> valA <=   valB
    case LT  -> valA <    valB
    case LTU -> valA65 <  valB65
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
    case H -> (addr[0]    == 0)
    case W -> (addr[1..0] == 0b00)
    case D -> (addr[2..0] == 0b000)
  }

