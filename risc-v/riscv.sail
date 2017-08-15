default Order dec

typedef regval = bit[64]
typedef regno = bit[5]

register (regval) x0
register (regval) x1
register (regval) x2
register (regval) x3
register (regval) x4
register (regval) x5
register (regval) x6
register (regval) x7
register (regval) x8
register (regval) x9
register (regval) x10
register (regval) x11
register (regval) x12
register (regval) x13
register (regval) x14
register (regval) x15
register (regval) x16
register (regval) x17
register (regval) x18
register (regval) x19
register (regval) x20
register (regval) x21
register (regval) x22
register (regval) x23
register (regval) x24
register (regval) x25
register (regval) x26
register (regval) x27
register (regval) x28
register (regval) x29
register (regval) x30
register (regval) x31

register (bit[64]) PC
register (bit[64]) nextPC

let (vector <0, 32, inc, (register<(regval)>)>) GPRs =
  [x0, x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,x17,x18,x19,x20,x21,x22,x23,x24,x25,x26,x27,x28,x29,x30,x31]

function (regval) rGPR ((regno) r) = 
    if (r == 0) then 
        0
    else 
        GPRs[r]

function unit wGPR((regno) r, (regval) v) =
    if (r != 0) then
        GPRs[r] := v

val extern forall Nat 'n. ( bit[64] , [|'n|] ) -> (bit[8 * 'n]) effect { rmem } MEMr
val extern forall Nat 'n. ( bit[64] , [|'n|]) -> unit effect { eamem } MEMea
val extern forall Nat 'n. ( bit[64] , [|'n|] , bit[8*'n]) -> unit effect { wmv } MEMval
val extern unit -> unit effect { barr } MEM_sync

(* Ideally these would be sail builtin *)
function (bit[64]) shift_right_arith64 ((bit[64]) v, (bit[6]) shift) =
    let (bit[128]) v128 = EXTS(v) in
    (v128 >> shift)[63..0]

function (bit[32]) shift_right_arith32 ((bit[32]) v, (bit[5]) shift) =
    let (bit[64]) v64 = EXTS(v) in
    (v64 >> shift)[31..0]

typedef uop = enumerate {LUI; AUIPC} (* upper immediate ops *)
typedef bop = enumerate {BEQ; BNE; BLT; BGE; BLTU; BGEU} (* branch ops *)
typedef iop = enumerate {ADDI; SLTI; SLTIU; XORI; ORI; ANDI} (* immediate ops *)
typedef sop = enumerate {SLLI; SRLI; SRAI} (* shift ops *)
typedef rop = enumerate {ADD; SUB; SLL; SLT; SLTU; XOR; SRL; SRA; OR; AND} (* reg-reg ops *)
typedef ropw = enumerate {ADDW; SUBW; SLLW; SRLW; SRAW} (* reg-reg 32-bit ops *)

typedef word_width = enumerate {BYTE; HALF; WORD; DOUBLE}

scattered function unit execute
scattered typedef ast = const union

val bit[32] -> option<ast> effect pure decode

scattered function option<ast> decode

union ast member ((bit[20]), regno, uop) UTYPE

function clause decode ((bit[20]) imm : (regno) rd : 0b0110111) = Some(UTYPE(imm, rd, LUI))
function clause decode ((bit[20]) imm : (regno) rd : 0b0010111) = Some(UTYPE(imm, rd, AUIPC))

function clause execute (UTYPE(imm, rd, op)) =
    let (bit[64]) off = EXTS(imm : 0x000) in
    let ret = switch (op) {
      case LUI   -> off
      case AUIPC -> PC + off
    } in
    wGPR(rd, ret)

union ast member ((bit[20]), regno) JAL
function clause decode ((bit[20]) imm : (regno) rd : 0b1101111) = Some (JAL(imm, rd))
function clause execute (JAL(imm, rd)) =
    let (bit[64]) offset = EXTS(imm[19] : imm[7..0] : imm[8] : imm[18..13] : imm[12..9] : 0b0) in {
      nextPC :=  PC + offset;
      wGPR(rd, PC + 4);
    }

union ast member((bit[12]), regno, regno) JALR
function clause decode ((bit[12]) imm : (regno) rs1 : 0b000 : (regno) rd : 0b1100111) =
    Some(JALR(imm, rs1, rd))
function clause execute (JALR(imm, rs1, rd)) =
    let (bit[64]) newPC = rGPR(rs1) + EXTS(imm) in {
      nextPC := newPC[63..1] : 0b0;
      wGPR(rd, PC + 4);
    }

union ast member ((bit[12]), regno, regno, bop) BTYPE
function clause decode ((bit[7]) imm7 : (regno) rs2 : (regno) rs1 : 0b000 : (bit[5]) imm5 : 0b1100011) = Some(BTYPE(imm7[6] : imm5[0] : imm7[5..0] : imm5[4..1], rs2, rs1, BEQ))
function clause decode ((bit[7]) imm7 : (regno) rs2 : (regno) rs1 : 0b001 : (bit[5]) imm5 : 0b1100011) = Some(BTYPE(imm7[6] : imm5[0] : imm7[5..0] : imm5[4..1], rs2, rs1, BNE))
function clause decode ((bit[7]) imm7 : (regno) rs2 : (regno) rs1 : 0b100 : (bit[5]) imm5 : 0b1100011) = Some(BTYPE(imm7[6] : imm5[0] : imm7[5..0] : imm5[4..1], rs2, rs1, BLT))
function clause decode ((bit[7]) imm7 : (regno) rs2 : (regno) rs1 : 0b101 : (bit[5]) imm5 : 0b1100011) = Some(BTYPE(imm7[6] : imm5[0] : imm7[5..0] : imm5[4..1], rs2, rs1, BGE))
function clause decode ((bit[7]) imm7 : (regno) rs2 : (regno) rs1 : 0b110 : (bit[5]) imm5 : 0b1100011) = Some(BTYPE(imm7[6] : imm5[0] : imm7[5..0] : imm5[4..1], rs2, rs1, BLTU))
function clause decode ((bit[7]) imm7 : (regno) rs2 : (regno) rs1 : 0b111 : (bit[5]) imm5 : 0b1100011) = Some(BTYPE(imm7[6] : imm5[0] : imm7[5..0] : imm5[4..1], rs2, rs1, BGEU))

function clause execute (BTYPE(imm, rs2, rs1, op)) =
  let rs1_val = rGPR(rs1) in
  let rs2_val = rGPR(rs2) in
  let taken   = switch(op) {
    case BEQ  -> rs1_val == rs2_val
    case BNE  -> rs1_val != rs2_val
    case BLT  -> rs1_val <_s rs2_val
    case BGE  -> rs1_val >=_s rs2_val
    case BLTU -> rs1_val <_u rs2_val
    case BGEU -> unsigned(rs1_val) >= unsigned(rs2_val) (* XXX sail missing >=_u *)
  } in
  if (taken) then
      nextPC := PC + EXTS(imm : 0b0)

union ast member ((bit[12]), regno, regno, iop) ITYPE
function clause decode ((bit[12]) imm : (regno) rs1 : 0b000 : (regno) rd : 0b0010011) = Some(ITYPE(imm, rs1, rd, ADDI))
function clause decode ((bit[12]) imm : (regno) rs1 : 0b010 : (regno) rd : 0b0010011) = Some(ITYPE(imm, rs1, rd, SLTI))
function clause decode ((bit[12]) imm : (regno) rs1 : 0b011 : (regno) rd : 0b0010011) = Some(ITYPE(imm, rs1, rd, SLTIU))
function clause decode ((bit[12]) imm : (regno) rs1 : 0b100 : (regno) rd : 0b0010011) = Some(ITYPE(imm, rs1, rd, XORI))
function clause decode ((bit[12]) imm : (regno) rs1 : 0b110 : (regno) rd : 0b0010011) = Some(ITYPE(imm, rs1, rd, ORI))
function clause decode ((bit[12]) imm : (regno) rs1 : 0b111 : (regno) rd : 0b0010011) = Some(ITYPE(imm, rs1, rd, ANDI))
function clause execute (ITYPE (imm, rs1, rd, op)) =
  let rs1_val = rGPR(rs1) in
  let imm64 = (bit[64]) (EXTS(imm)) in
  let (bit[64]) result = switch(op) {
    case ADDI  -> rs1_val + imm64
    case SLTI  -> EXTZ(rs1_val <_s imm64)
    case SLTIU -> EXTZ(rs1_val <_u imm64)
    case XORI  -> rs1_val ^ imm64
    case ORI   -> rs1_val | imm64
    case ANDI  -> rs1_val & imm64
  } in
  wGPR(rd, result)

union ast member ((bit[6]), regno, regno, sop) SHIFTIOP
function clause decode (0b000000 : (bit[6]) shamt : (regno) rs1 : 0b001 : (regno) rd : 0b0010011) = Some(SHIFTIOP(shamt, rs1, rd, SLLI))
function clause decode (0b000000 : (bit[6]) shamt : (regno) rs1 : 0b101 : (regno) rd : 0b0010011) = Some(SHIFTIOP(shamt, rs1, rd, SRLI))
function clause decode (0b010000 : (bit[6]) shamt : (regno) rs1 : 0b101 : (regno) rd : 0b0010011) = Some(SHIFTIOP(shamt, rs1, rd, SRAI))
function clause execute (SHIFTIOP(shamt, rs1, rd, op)) = 
    let rs1_val = rGPR(rs1) in
    let result = switch(op) {
      case SLLI -> rs1_val >> shamt
      case SRLI -> rs1_val << shamt
      case SRAI -> shift_right_arith64(rs1_val, shamt)
    } in
    wGPR(rd, result)

union ast member (regno, regno, regno, rop) RTYPE
function clause decode (0b0000000 : (regno) rs2 : (regno) rs1 : 0b000 : (regno) rd : 0b0110011) = Some(RTYPE(rs2, rs1, rd, ADD))
function clause decode (0b0100000 : (regno) rs2 : (regno) rs1 : 0b000 : (regno) rd : 0b0110011) = Some(RTYPE(rs2, rs1, rd, SUB))
function clause decode (0b0000000 : (regno) rs2 : (regno) rs1 : 0b001 : (regno) rd : 0b0110011) = Some(RTYPE(rs2, rs1, rd, SLL))
function clause decode (0b0000000 : (regno) rs2 : (regno) rs1 : 0b010 : (regno) rd : 0b0110011) = Some(RTYPE(rs2, rs1, rd, SLT))
function clause decode (0b0000000 : (regno) rs2 : (regno) rs1 : 0b011 : (regno) rd : 0b0110011) = Some(RTYPE(rs2, rs1, rd, SLTU))
function clause decode (0b0000000 : (regno) rs2 : (regno) rs1 : 0b100 : (regno) rd : 0b0110011) = Some(RTYPE(rs2, rs1, rd, XOR))
function clause decode (0b0000000 : (regno) rs2 : (regno) rs1 : 0b101 : (regno) rd : 0b0110011) = Some(RTYPE(rs2, rs1, rd, SRL))
function clause decode (0b0100000 : (regno) rs2 : (regno) rs1 : 0b101 : (regno) rd : 0b0110011) = Some(RTYPE(rs2, rs1, rd, SRA))
function clause decode (0b0000000 : (regno) rs2 : (regno) rs1 : 0b110 : (regno) rd : 0b0110011) = Some(RTYPE(rs2, rs1, rd, OR))
function clause decode (0b0000000 : (regno) rs2 : (regno) rs1 : 0b111 : (regno) rd : 0b0110011) = Some(RTYPE(rs2, rs1, rd, AND))
function clause execute (RTYPE(rs2, rs1, rd, op)) =
  let rs1_val = rGPR(rs1) in
  let rs2_val = rGPR(rs2) in
  let (bit[64]) result = switch(op) {
    case ADD  -> rs1_val + rs2_val
    case SUB  -> rs1_val - rs2_val
    case SLL  -> rs1_val << (rs2_val[5..0])
    case SLT  -> EXTZ(rs1_val <_s rs2_val)
    case SLTU -> EXTZ(rs1_val <_u rs2_val)
    case XOR  -> rs1_val ^ rs2_val
    case SRL  -> rs1_val >> (rs2_val[5..0])
    case SRA  -> shift_right_arith64(rs1_val, rs2_val[5..0])
    case OR   -> rs1_val | rs2_val
    case AND  -> rs1_val & rs2_val
  } in
  wGPR(rd, result)

union ast member ((bit[12]), regno, regno, bool, word_width) LOAD
function clause decode ((bit[12]) imm : (regno) rs1 : 0b000 : (regno) rd : 0b0000011) = Some(LOAD(imm, rs1, rd, false, BYTE))
function clause decode ((bit[12]) imm : (regno) rs1 : 0b001 : (regno) rd : 0b0000011) = Some(LOAD(imm, rs1, rd, false, HALF))
function clause decode ((bit[12]) imm : (regno) rs1 : 0b010 : (regno) rd : 0b0000011) = Some(LOAD(imm, rs1, rd, false, WORD))
function clause decode ((bit[12]) imm : (regno) rs1 : 0b011 : (regno) rd : 0b0000011) = Some(LOAD(imm, rs1, rd, false, DOUBLE))
function clause decode ((bit[12]) imm : (regno) rs1 : 0b100 : (regno) rd : 0b0000011) = Some(LOAD(imm, rs1, rd, true,  BYTE))
function clause decode ((bit[12]) imm : (regno) rs1 : 0b101 : (regno) rd : 0b0000011) = Some(LOAD(imm, rs1, rd, true,  HALF))
function clause decode ((bit[12]) imm : (regno) rs1 : 0b110 : (regno) rd : 0b0000011) = Some(LOAD(imm, rs1, rd, true,  WORD))
function clause execute(LOAD(imm, rs1, rd, unsigned, width)) =
    let (bit[64]) addr = rGPR(rs1) + EXTS(imm) in
    let (bit[64]) result = if unsigned then 
        switch (width) {
          case BYTE   -> EXTZ(MEMr(addr, 1))
          case HALF   -> EXTZ(MEMr(addr, 2))
          case WORD   -> EXTZ(MEMr(addr, 4))
          case DOUBLE -> MEMr(addr, 8)
        }
      else
        switch (width) {
          case BYTE   -> EXTS(MEMr(addr, 1))
          case HALF   -> EXTS(MEMr(addr, 2))
          case WORD   -> EXTS(MEMr(addr, 4))
          case DOUBLE -> MEMr(addr, 8)
        } in
    wGPR(rd, result)

union ast member ((bit[12]), regno, regno, word_width) STORE
function clause decode ((bit[7]) imm7 : (regno) rs2 : (regno) rs1 : 0b000 : (bit[5]) imm5 : 0b0100011) = Some(STORE(imm7 : imm5, rs2, rs1, BYTE))
function clause decode ((bit[7]) imm7 : (regno) rs2 : (regno) rs1 : 0b001 : (bit[5]) imm5 : 0b0100011) = Some(STORE(imm7 : imm5, rs2, rs1, HALF))
function clause decode ((bit[7]) imm7 : (regno) rs2 : (regno) rs1 : 0b010 : (bit[5]) imm5 : 0b0100011) = Some(STORE(imm7 : imm5, rs2, rs1, WORD))
function clause decode ((bit[7]) imm7 : (regno) rs2 : (regno) rs1 : 0b011 : (bit[5]) imm5 : 0b0100011) = Some(STORE(imm7 : imm5, rs2, rs1, DOUBLE))
function clause execute (STORE(imm, rs2, rs1, width)) =
    let (bit[64]) addr = rGPR(rs1) + EXTS(imm) in {
      switch (width) {
        case BYTE   -> MEMea(addr, 1)
        case HALF   -> MEMea(addr, 2)
        case WORD   -> MEMea(addr, 4)
        case DOUBLE -> MEMea(addr, 8)
      };
      let rs2_val = rGPR(rs2) in
      switch (width) {
        case BYTE   -> MEMval(addr, 1, rs2_val[7..0])
        case HALF   -> MEMval(addr, 2, rs2_val[15..0])
        case WORD   -> MEMval(addr, 4, rs2_val[31..0])
        case DOUBLE -> MEMval(addr, 8, rs2_val)
      }
    }

union ast member ((bit[12]), regno, regno) ADDIW
function clause decode ((bit[12]) imm : (regno) rs1 : 0b000 : (regno) rd : 0b0011011) = Some(ADDIW(imm, rs1, rd))
function clause execute (ADDIW(imm, rs1, rd)) =
  let (bit[64]) imm64 = EXTS(imm) in
  let (bit[64]) result64 = imm64 + rGPR(rs1) in
  let (bit[64]) result32 = EXTS(result64[31..0]) in
  wGPR(rd, result32)

union ast member ((bit[5]), regno, regno, sop) SHIFTW
function clause decode (0b0000000 : (bit[5]) shamt : (regno) rs1 : 0b001 : (regno) rd : 0b0011011) = Some(SHIFTW(shamt, rs1, rd, SLLI))
function clause decode (0b0000000 : (bit[5]) shamt : (regno) rs1 : 0b101 : (regno) rd : 0b0011011) = Some(SHIFTW(shamt, rs1, rd, SRLI))
function clause decode (0b0100000 : (bit[5]) shamt : (regno) rs1 : 0b101 : (regno) rd : 0b0011011) = Some(SHIFTW(shamt, rs1, rd, SRAI))
function clause execute (SHIFTW(shamt, rs1, rd, op)) = 
    let rs1_val = (rGPR(rs1))[31..0] in
    let result = switch(op) {
      case SLLI -> rs1_val >> shamt
      case SRLI -> rs1_val << shamt
      case SRAI -> shift_right_arith32(rs1_val, shamt)
    } in
    wGPR(rd, EXTS(result))

union ast member (regno, regno, regno, ropw) RTYPEW
function clause decode (0b0000000 : (regno) rs2 : (regno) rs1 : 0b000 : (regno) rd : 0b0111011) = Some(RTYPEW(rs2, rs1, rd, ADDW))
function clause decode (0b0100000 : (regno) rs2 : (regno) rs1 : 0b000 : (regno) rd : 0b0111011) = Some(RTYPEW(rs2, rs1, rd, SUBW))
function clause decode (0b0000000 : (regno) rs2 : (regno) rs1 : 0b001 : (regno) rd : 0b0111011) = Some(RTYPEW(rs2, rs1, rd, SLLW))
function clause decode (0b0000000 : (regno) rs2 : (regno) rs1 : 0b101 : (regno) rd : 0b0111011) = Some(RTYPEW(rs2, rs1, rd, SRLW))
function clause decode (0b0100000 : (regno) rs2 : (regno) rs1 : 0b101 : (regno) rd : 0b0111011) = Some(RTYPEW(rs2, rs1, rd, SRAW))
function clause execute (RTYPEW(rs2, rs1, rd, op)) =
  let rs1_val = (rGPR(rs1))[31..0] in
  let rs2_val = (rGPR(rs2))[31..0] in
  let (bit[32]) result = switch(op) {
    case ADDW -> rs1_val + rs2_val
    case SUBW -> rs1_val - rs2_val
    case SLLW -> rs1_val << (rs2_val[4..0])
    case SRLW -> rs1_val >> (rs2_val[4..0])
    case SRAW -> shift_right_arith32(rs1_val, rs2_val[4..0])
  } in
  wGPR(rd, EXTS(result))

union ast member (bit[4], bit[4]) FENCE
function clause decode (0b0000 : (bit[4]) pred : (bit[4]) succ : 0b00000 : 0b000 : 0b00000 : 0b0001111) = Some(FENCE (pred, succ))
function clause execute (FENCE(pred, succ)) = {
 MEM_sync(); (* XXX use pred and succ *)
}

union ast member unit FENCEI
function clause decode (0b0000 : 0b0000 : 0b0000 : 0b00000 : 0b001 : 0b00000 : 0b0001111) = Some(FENCEI)
function clause execute FENCEI = () (* XXX TODO *)

union ast member unit ECALL
function clause decode (0b000000000000 : 0b00000 : 0b000 : 0b00000 : 0b1110011) = Some(ECALL ())
function clause execute ECALL = ()

union ast member unit EBREAK
function clause decode (0b000000000001 : 0b00000 : 0b000 : 0b00000 : 0b1110011) = Some(EBREAK ())
function clause execute EBREAK = { exit () }


function clause decode _ = None

end ast
end decode
end execute
