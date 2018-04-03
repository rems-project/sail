scattered typedef ast = const union

val bit[32] -> option<ast> effect pure decode
scattered function option<ast> decode

scattered function unit execute

(********************************************************************)
union ast member ((bit[20]), regno, uop) UTYPE

function clause decode ((bit[20]) imm : (regno) rd : 0b0110111) = Some(UTYPE(imm, rd, RISCV_LUI))
function clause decode ((bit[20]) imm : (regno) rd : 0b0010111) = Some(UTYPE(imm, rd, RISCV_AUIPC))

function clause execute (UTYPE(imm, rd, op)) =
    let (bit[64]) off = EXTS(imm : 0x000) in
    let ret = switch (op) {
      case RISCV_LUI   -> off
      case RISCV_AUIPC -> PC + off
    } in
    wGPR(rd, ret)

(********************************************************************)
union ast member ((bit[21]), regno) RISCV_JAL

function clause decode ((bit[20]) imm : (regno) rd : 0b1101111) = Some (RISCV_JAL(imm[19] : imm[7..0] : imm[8] : imm[18..13] : imm[12..9] : 0b0, rd))

function clause execute (RISCV_JAL(imm, rd)) = {
    (bit[64]) pc := PC;
    wGPR(rd, pc + 4);
    (bit[64]) offset := EXTS(imm);
    nextPC :=  pc + offset;
}

(********************************************************************)
union ast member((bit[12]), regno, regno) RISCV_JALR

function clause decode ((bit[12]) imm : (regno) rs1 : 0b000 : (regno) rd : 0b1100111) =
    Some(RISCV_JALR(imm, rs1, rd))

function clause execute (RISCV_JALR(imm, rs1, rd)) = {
    (* write rd before anything else to prevent unintended strength *)
    wGPR(rd, PC + 4);
    (bit[64]) newPC := rGPR(rs1) + EXTS(imm);
    nextPC := newPC[63..1] : 0b0;
}

(********************************************************************)
union ast member ((bit[13]), regno, regno, bop) BTYPE

function clause decode ((bit[7]) imm7 : (regno) rs2 : (regno) rs1 : 0b000 : (bit[5]) imm5 : 0b1100011) =
  Some(BTYPE(imm7[6] : imm5[0] : imm7[5..0] : imm5[4..1] : 0b0, rs2, rs1, RISCV_BEQ))
function clause decode ((bit[7]) imm7 : (regno) rs2 : (regno) rs1 : 0b001 : (bit[5]) imm5 : 0b1100011) =
  Some(BTYPE(imm7[6] : imm5[0] : imm7[5..0] : imm5[4..1] : 0b0, rs2, rs1, RISCV_BNE))
function clause decode ((bit[7]) imm7 : (regno) rs2 : (regno) rs1 : 0b100 : (bit[5]) imm5 : 0b1100011) =
  Some(BTYPE(imm7[6] : imm5[0] : imm7[5..0] : imm5[4..1] : 0b0, rs2, rs1, RISCV_BLT))
function clause decode ((bit[7]) imm7 : (regno) rs2 : (regno) rs1 : 0b101 : (bit[5]) imm5 : 0b1100011) =
  Some(BTYPE(imm7[6] : imm5[0] : imm7[5..0] : imm5[4..1] : 0b0, rs2, rs1, RISCV_BGE))
function clause decode ((bit[7]) imm7 : (regno) rs2 : (regno) rs1 : 0b110 : (bit[5]) imm5 : 0b1100011) =
  Some(BTYPE(imm7[6] : imm5[0] : imm7[5..0] : imm5[4..1] : 0b0, rs2, rs1, RISCV_BLTU))
function clause decode ((bit[7]) imm7 : (regno) rs2 : (regno) rs1 : 0b111 : (bit[5]) imm5 : 0b1100011) =
  Some(BTYPE(imm7[6] : imm5[0] : imm7[5..0] : imm5[4..1] : 0b0, rs2, rs1, RISCV_BGEU))

function clause execute (BTYPE(imm, rs2, rs1, op)) =
  let rs1_val = rGPR(rs1) in
  let rs2_val = rGPR(rs2) in
  let taken   = switch(op) {
    case RISCV_BEQ  -> rs1_val == rs2_val
    case RISCV_BNE  -> rs1_val != rs2_val
    case RISCV_BLT  -> rs1_val <_s rs2_val
    case RISCV_BGE  -> rs1_val >=_s rs2_val
    case RISCV_BLTU -> rs1_val <_u rs2_val
    case RISCV_BGEU -> unsigned(rs1_val) >= unsigned(rs2_val) (* XXX sail missing >=_u *)
  } in
  if (taken) then
      nextPC := PC + EXTS(imm)

(********************************************************************)
union ast member ((bit[12]), regno, regno, iop) ITYPE

function clause decode ((bit[12]) imm : (regno) rs1 : 0b000 : (regno) rd : 0b0010011) = Some(ITYPE(imm, rs1, rd, RISCV_ADDI))
function clause decode ((bit[12]) imm : (regno) rs1 : 0b010 : (regno) rd : 0b0010011) = Some(ITYPE(imm, rs1, rd, RISCV_SLTI))
function clause decode ((bit[12]) imm : (regno) rs1 : 0b011 : (regno) rd : 0b0010011) = Some(ITYPE(imm, rs1, rd, RISCV_SLTIU))
function clause decode ((bit[12]) imm : (regno) rs1 : 0b100 : (regno) rd : 0b0010011) = Some(ITYPE(imm, rs1, rd, RISCV_XORI))
function clause decode ((bit[12]) imm : (regno) rs1 : 0b110 : (regno) rd : 0b0010011) = Some(ITYPE(imm, rs1, rd, RISCV_ORI))
function clause decode ((bit[12]) imm : (regno) rs1 : 0b111 : (regno) rd : 0b0010011) = Some(ITYPE(imm, rs1, rd, RISCV_ANDI))

function clause execute (ITYPE (imm, rs1, rd, op)) =
  let rs1_val = rGPR(rs1) in
  let imm64 = (bit[64]) (EXTS(imm)) in
  let (bit[64]) result = switch(op) {
    case RISCV_ADDI  -> rs1_val + imm64
    case RISCV_SLTI  -> EXTZ(rs1_val <_s imm64)
    case RISCV_SLTIU -> EXTZ(rs1_val <_u imm64)
    case RISCV_XORI  -> rs1_val ^ imm64
    case RISCV_ORI   -> rs1_val | imm64
    case RISCV_ANDI  -> rs1_val & imm64
  } in
  wGPR(rd, result)

(********************************************************************)
union ast member ((bit[6]), regno, regno, sop) SHIFTIOP

function clause decode (0b000000 : (bit[6]) shamt : (regno) rs1 : 0b001 : (regno) rd : 0b0010011) = Some(SHIFTIOP(shamt, rs1, rd, RISCV_SLLI))
function clause decode (0b000000 : (bit[6]) shamt : (regno) rs1 : 0b101 : (regno) rd : 0b0010011) = Some(SHIFTIOP(shamt, rs1, rd, RISCV_SRLI))
function clause decode (0b010000 : (bit[6]) shamt : (regno) rs1 : 0b101 : (regno) rd : 0b0010011) = Some(SHIFTIOP(shamt, rs1, rd, RISCV_SRAI))

function clause execute (SHIFTIOP(shamt, rs1, rd, op)) = 
    let rs1_val = rGPR(rs1) in
    let result = switch(op) {
      case RISCV_SLLI -> rs1_val >> shamt
      case RISCV_SRLI -> rs1_val << shamt
      case RISCV_SRAI -> shift_right_arith64(rs1_val, shamt)
    } in
    wGPR(rd, result)

(********************************************************************)
union ast member (regno, regno, regno, rop) RTYPE

function clause decode (0b0000000 : (regno) rs2 : (regno) rs1 : 0b000 : (regno) rd : 0b0110011) = Some(RTYPE(rs2, rs1, rd, RISCV_ADD))
function clause decode (0b0100000 : (regno) rs2 : (regno) rs1 : 0b000 : (regno) rd : 0b0110011) = Some(RTYPE(rs2, rs1, rd, RISCV_SUB))
function clause decode (0b0000000 : (regno) rs2 : (regno) rs1 : 0b001 : (regno) rd : 0b0110011) = Some(RTYPE(rs2, rs1, rd, RISCV_SLL))
function clause decode (0b0000000 : (regno) rs2 : (regno) rs1 : 0b010 : (regno) rd : 0b0110011) = Some(RTYPE(rs2, rs1, rd, RISCV_SLT))
function clause decode (0b0000000 : (regno) rs2 : (regno) rs1 : 0b011 : (regno) rd : 0b0110011) = Some(RTYPE(rs2, rs1, rd, RISCV_SLTU))
function clause decode (0b0000000 : (regno) rs2 : (regno) rs1 : 0b100 : (regno) rd : 0b0110011) = Some(RTYPE(rs2, rs1, rd, RISCV_XOR))
function clause decode (0b0000000 : (regno) rs2 : (regno) rs1 : 0b101 : (regno) rd : 0b0110011) = Some(RTYPE(rs2, rs1, rd, RISCV_SRL))
function clause decode (0b0100000 : (regno) rs2 : (regno) rs1 : 0b101 : (regno) rd : 0b0110011) = Some(RTYPE(rs2, rs1, rd, RISCV_SRA))
function clause decode (0b0000000 : (regno) rs2 : (regno) rs1 : 0b110 : (regno) rd : 0b0110011) = Some(RTYPE(rs2, rs1, rd, RISCV_OR))
function clause decode (0b0000000 : (regno) rs2 : (regno) rs1 : 0b111 : (regno) rd : 0b0110011) = Some(RTYPE(rs2, rs1, rd, RISCV_AND))

function clause execute (RTYPE(rs2, rs1, rd, op)) =
  let rs1_val = rGPR(rs1) in
  let rs2_val = rGPR(rs2) in
  let (bit[64]) result = switch(op) {
    case RISCV_ADD  -> rs1_val + rs2_val
    case RISCV_SUB  -> rs1_val - rs2_val
    case RISCV_SLL  -> rs1_val << (rs2_val[5..0])
    case RISCV_SLT  -> EXTZ(rs1_val <_s rs2_val)
    case RISCV_SLTU -> EXTZ(rs1_val <_u rs2_val)
    case RISCV_XOR  -> rs1_val ^ rs2_val
    case RISCV_SRL  -> rs1_val >> (rs2_val[5..0])
    case RISCV_SRA  -> shift_right_arith64(rs1_val, rs2_val[5..0])
    case RISCV_OR   -> rs1_val | rs2_val
    case RISCV_AND  -> rs1_val & rs2_val
  } in
  wGPR(rd, result)

(********************************************************************)
union ast member ((bit[12]), regno, regno, bool, word_width, bool, bool) LOAD

function clause decode ((bit[12]) imm : (regno) rs1 : 0b000 : (regno) rd : 0b0000011) = Some(LOAD(imm, rs1, rd, false, BYTE,   false, false))
function clause decode ((bit[12]) imm : (regno) rs1 : 0b001 : (regno) rd : 0b0000011) = Some(LOAD(imm, rs1, rd, false, HALF,   false, false))
function clause decode ((bit[12]) imm : (regno) rs1 : 0b010 : (regno) rd : 0b0000011) = Some(LOAD(imm, rs1, rd, false, WORD,   false, false))
function clause decode ((bit[12]) imm : (regno) rs1 : 0b011 : (regno) rd : 0b0000011) = Some(LOAD(imm, rs1, rd, false, DOUBLE, false, false))
function clause decode ((bit[12]) imm : (regno) rs1 : 0b100 : (regno) rd : 0b0000011) = Some(LOAD(imm, rs1, rd, true,  BYTE,   false, false))
function clause decode ((bit[12]) imm : (regno) rs1 : 0b101 : (regno) rd : 0b0000011) = Some(LOAD(imm, rs1, rd, true,  HALF,   false, false))
function clause decode ((bit[12]) imm : (regno) rs1 : 0b110 : (regno) rd : 0b0000011) = Some(LOAD(imm, rs1, rd, true,  WORD,   false, false))

function clause execute(LOAD(imm, rs1, rd, unsigned, width, aq, rl)) =
    let (bit[64]) addr = rGPR(rs1) + EXTS(imm) in
    let (bit[64]) result = if unsigned then 
        switch (width) {
          case BYTE   -> EXTZ(mem_read(addr, 1, aq, rl, false))
          case HALF   -> EXTZ(mem_read(addr, 2, aq, rl, false))
          case WORD   -> EXTZ(mem_read(addr, 4, aq, rl, false))
          case DOUBLE -> mem_read(addr, 8, aq, rl, false)
        }
      else
        switch (width) {
          case BYTE   -> EXTS(mem_read(addr, 1, aq, rl, false))
          case HALF   -> EXTS(mem_read(addr, 2, aq, rl, false))
          case WORD   -> EXTS(mem_read(addr, 4, aq, rl, false))
          case DOUBLE -> mem_read(addr, 8, aq, rl, false)
        } in
    wGPR(rd, result)

(********************************************************************)
union ast member ((bit[12]), regno, regno, word_width, bool, bool) STORE

function clause decode ((bit[7]) imm7 : (regno) rs2 : (regno) rs1 : 0b000 : (bit[5]) imm5 : 0b0100011) =
  Some(STORE(imm7 : imm5, rs2, rs1, BYTE, false, false))
function clause decode ((bit[7]) imm7 : (regno) rs2 : (regno) rs1 : 0b001 : (bit[5]) imm5 : 0b0100011) =
  Some(STORE(imm7 : imm5, rs2, rs1, HALF, false, false))
function clause decode ((bit[7]) imm7 : (regno) rs2 : (regno) rs1 : 0b010 : (bit[5]) imm5 : 0b0100011) =
  Some(STORE(imm7 : imm5, rs2, rs1, WORD, false, false))
function clause decode ((bit[7]) imm7 : (regno) rs2 : (regno) rs1 : 0b011 : (bit[5]) imm5 : 0b0100011) =
  Some(STORE(imm7 : imm5, rs2, rs1, DOUBLE, false, false))

function clause execute (STORE(imm, rs2, rs1, width, aq, rl)) =
    let (bit[64]) addr = rGPR(rs1) + EXTS(imm) in {
      switch (width) {
        case BYTE   -> mem_write_ea(addr, 1, aq, rl, false)
        case HALF   -> mem_write_ea(addr, 2, aq, rl, false)
        case WORD   -> mem_write_ea(addr, 4, aq, rl, false)
        case DOUBLE -> mem_write_ea(addr, 8, aq, rl, false)
      };
      let rs2_val = rGPR(rs2) in
      switch (width) {
        case BYTE   -> mem_write_value(addr, 1, rs2_val[7..0],  aq, rl)
        case HALF   -> mem_write_value(addr, 2, rs2_val[15..0], aq, rl)
        case WORD   -> mem_write_value(addr, 4, rs2_val[31..0], aq, rl)
        case DOUBLE -> mem_write_value(addr, 8, rs2_val,        aq, rl)
      }
    }

(********************************************************************)
union ast member ((bit[12]), regno, regno) ADDIW

function clause decode ((bit[12]) imm : (regno) rs1 : 0b000 : (regno) rd : 0b0011011) =
  Some(ADDIW(imm, rs1, rd))

function clause execute (ADDIW(imm, rs1, rd)) =
  let (bit[64]) imm64 = EXTS(imm) in
  let (bit[64]) result64 = imm64 + rGPR(rs1) in
  let (bit[64]) result32 = EXTS(result64[31..0]) in
  wGPR(rd, result32)

(********************************************************************)
union ast member ((bit[5]), regno, regno, sop) SHIFTW

function clause decode (0b0000000 : (bit[5]) shamt : (regno) rs1 : 0b001 : (regno) rd : 0b0011011) = Some(SHIFTW(shamt, rs1, rd, RISCV_SLLI))
function clause decode (0b0000000 : (bit[5]) shamt : (regno) rs1 : 0b101 : (regno) rd : 0b0011011) = Some(SHIFTW(shamt, rs1, rd, RISCV_SRLI))
function clause decode (0b0100000 : (bit[5]) shamt : (regno) rs1 : 0b101 : (regno) rd : 0b0011011) = Some(SHIFTW(shamt, rs1, rd, RISCV_SRAI))

function clause execute (SHIFTW(shamt, rs1, rd, op)) = 
    let rs1_val = (rGPR(rs1))[31..0] in
    let result = switch(op) {
      case RISCV_SLLI -> rs1_val >> shamt
      case RISCV_SRLI -> rs1_val << shamt
      case RISCV_SRAI -> shift_right_arith32(rs1_val, shamt)
    } in
    wGPR(rd, EXTS(result))

(********************************************************************)
union ast member (regno, regno, regno, ropw) RTYPEW

function clause decode (0b0000000 : (regno) rs2 : (regno) rs1 : 0b000 : (regno) rd : 0b0111011) = Some(RTYPEW(rs2, rs1, rd, RISCV_ADDW))
function clause decode (0b0100000 : (regno) rs2 : (regno) rs1 : 0b000 : (regno) rd : 0b0111011) = Some(RTYPEW(rs2, rs1, rd, RISCV_SUBW))
function clause decode (0b0000000 : (regno) rs2 : (regno) rs1 : 0b001 : (regno) rd : 0b0111011) = Some(RTYPEW(rs2, rs1, rd, RISCV_SLLW))
function clause decode (0b0000000 : (regno) rs2 : (regno) rs1 : 0b101 : (regno) rd : 0b0111011) = Some(RTYPEW(rs2, rs1, rd, RISCV_SRLW))
function clause decode (0b0100000 : (regno) rs2 : (regno) rs1 : 0b101 : (regno) rd : 0b0111011) = Some(RTYPEW(rs2, rs1, rd, RISCV_SRAW))

function clause execute (RTYPEW(rs2, rs1, rd, op)) =
  let rs1_val = (rGPR(rs1))[31..0] in
  let rs2_val = (rGPR(rs2))[31..0] in
  let (bit[32]) result = switch(op) {
    case RISCV_ADDW -> rs1_val + rs2_val
    case RISCV_SUBW -> rs1_val - rs2_val
    case RISCV_SLLW -> rs1_val << (rs2_val[4..0])
    case RISCV_SRLW -> rs1_val >> (rs2_val[4..0])
    case RISCV_SRAW -> shift_right_arith32(rs1_val, rs2_val[4..0])
  } in
  wGPR(rd, EXTS(result))

(********************************************************************)
union ast member (bit[4], bit[4]) FENCE

function clause decode (0b0000 : (bit[4]) pred : (bit[4]) succ : 0b00000 : 0b000 : 0b00000 : 0b0001111) = Some(FENCE (pred, succ))

function clause execute (FENCE(pred, succ)) = {
  switch(pred, succ) {
    case (0b0011, 0b0011) -> MEM_fence_rw_rw()
    case (0b0010, 0b0011) -> MEM_fence_r_rw()
    case (0b0001, 0b0011) -> MEM_fence_w_rw()

    case (0b0011, 0b0010) -> MEM_fence_rw_r()
    case (0b0010, 0b0010) -> MEM_fence_r_r()
    case (0b0001, 0b0010) -> MEM_fence_w_r()

    case (0b0011, 0b0001) -> MEM_fence_rw_w()
    case (0b0010, 0b0001) -> MEM_fence_r_w()
    case (0b0001, 0b0001) -> MEM_fence_w_w()

    case _ -> not_implemented("unsupported fence")
  }
}

(********************************************************************)
union ast member unit FENCEI
function clause decode (0b000000000000 : 0b00000 : 0b001 : 0b00000 : 0b0001111) = Some(FENCEI)
function clause execute FENCEI = ()
  (* the memory model group decided fence.i is a NOP for all memory model purposes *)
  (* MEM_fence_i() *)

(********************************************************************)
union ast member unit ECALL
function clause decode (0b000000000000 : 0b00000 : 0b000 : 0b00000 : 0b1110011) = Some(ECALL ())
function clause execute ECALL = not_implemented("ECALL is not implemented")

(********************************************************************)
union ast member unit EBREAK
function clause decode (0b000000000001 : 0b00000 : 0b000 : 0b00000 : 0b1110011) = Some(EBREAK ())
function clause execute EBREAK = { exit () }

(********************************************************************)
union ast member (bool, bool, regno, word_width, regno) LOADRES

function clause decode (0b00010 : [aq] : [rl] : 0b00000 : (regno) rs1 : 0b010 : (regno) rd : 0b0101111) = Some(LOADRES(aq, rl, rs1, WORD, rd))
function clause decode (0b00010 : [aq] : [rl] : 0b00000 : (regno) rs1 : 0b011 : (regno) rd : 0b0101111) = Some(LOADRES(aq, rl, rs1, DOUBLE, rd))
function clause execute(LOADRES(aq, rl, rs1, width, rd)) =
  let (bit[64]) addr = rGPR(rs1) in
  let (bit[64]) result =
      switch width {
        case WORD   -> EXTS(mem_read(addr, 4, aq, rl, true))
        case DOUBLE -> mem_read(addr, 8, aq, rl, true)
      } in
  wGPR(rd, result)

(********************************************************************)
union ast member (bool, bool, regno, regno, word_width, regno) STORECON

function clause decode (0b00011 : [aq] : [rl] : (regno) rs2 : (regno) rs1 : 0b010 : (regno) rd : 0b0101111) =
  Some(STORECON(aq, rl, rs2, rs1, WORD, rd))
function clause decode (0b00011 : [aq] : [rl] : (regno) rs2 : (regno) rs1 : 0b011 : (regno) rd : 0b0101111) =
  Some(STORECON(aq, rl, rs2, rs1, DOUBLE, rd))

function clause execute (STORECON(aq, rl, rs2, rs1, width, rd)) = {
  if speculate_conditional_success() then {
    (bit[64]) addr := rGPR(rs1);
    switch width {
      case WORD   -> mem_write_ea(addr, 4, aq, rl, true)
      case DOUBLE -> mem_write_ea(addr, 8, aq, rl, true)
    };

    rs2_val := rGPR(rs2);
    if
      switch width {
        case WORD   -> mem_cond_write_value(addr, 4, rs2_val[31..0], aq, rl)
        case DOUBLE -> mem_cond_write_value(addr, 8, rs2_val,        aq, rl)
      }
    then wGPR(rd) := 0x0000000000000000
    else wGPR(rd) := 0x0000000000000001
  } else {
    wGPR(rd) := 0x0000000000000001
  }
}

(********************************************************************)
union ast member (amoop, bool, bool, regno, regno, word_width, regno) AMO

function clause decode (0b00001 : [aq] : [rl] : (regno) rs2 : (regno) rs1 : 0b010 : (regno) rd : 0b0101111) =
  Some(AMO(AMOSWAP, aq, rl, rs2, rs1, WORD,   rd))
function clause decode (0b00001 : [aq] : [rl] : (regno) rs2 : (regno) rs1 : 0b011 : (regno) rd : 0b0101111) =
  Some(AMO(AMOSWAP, aq, rl, rs2, rs1, DOUBLE, rd))
function clause decode (0b00000 : [aq] : [rl] : (regno) rs2 : (regno) rs1 : 0b010 : (regno) rd : 0b0101111) =
  Some(AMO(AMOADD , aq, rl, rs2, rs1, WORD,   rd))
function clause decode (0b00000 : [aq] : [rl] : (regno) rs2 : (regno) rs1 : 0b011 : (regno) rd : 0b0101111) =
  Some(AMO(AMOADD , aq, rl, rs2, rs1, DOUBLE, rd))
function clause decode (0b00100 : [aq] : [rl] : (regno) rs2 : (regno) rs1 : 0b010 : (regno) rd : 0b0101111) =
  Some(AMO(AMOXOR , aq, rl, rs2, rs1, WORD,   rd))
function clause decode (0b00100 : [aq] : [rl] : (regno) rs2 : (regno) rs1 : 0b011 : (regno) rd : 0b0101111) =
  Some(AMO(AMOXOR , aq, rl, rs2, rs1, DOUBLE, rd))
function clause decode (0b01100 : [aq] : [rl] : (regno) rs2 : (regno) rs1 : 0b010 : (regno) rd : 0b0101111) =
  Some(AMO(AMOAND , aq, rl, rs2, rs1, WORD,   rd))
function clause decode (0b01100 : [aq] : [rl] : (regno) rs2 : (regno) rs1 : 0b011 : (regno) rd : 0b0101111) =
  Some(AMO(AMOAND , aq, rl, rs2, rs1, DOUBLE, rd))
function clause decode (0b01000 : [aq] : [rl] : (regno) rs2 : (regno) rs1 : 0b010 : (regno) rd : 0b0101111) =
  Some(AMO(AMOOR  , aq, rl, rs2, rs1, WORD,   rd))
function clause decode (0b01000 : [aq] : [rl] : (regno) rs2 : (regno) rs1 : 0b011 : (regno) rd : 0b0101111) =
  Some(AMO(AMOOR  , aq, rl, rs2, rs1, DOUBLE, rd))
function clause decode (0b10000 : [aq] : [rl] : (regno) rs2 : (regno) rs1 : 0b010 : (regno) rd : 0b0101111) =
  Some(AMO(AMOMIN , aq, rl, rs2, rs1, WORD,   rd))
function clause decode (0b10000 : [aq] : [rl] : (regno) rs2 : (regno) rs1 : 0b011 : (regno) rd : 0b0101111) =
  Some(AMO(AMOMIN , aq, rl, rs2, rs1, DOUBLE, rd))
function clause decode (0b10100 : [aq] : [rl] : (regno) rs2 : (regno) rs1 : 0b010 : (regno) rd : 0b0101111) =
  Some(AMO(AMOMAX , aq, rl, rs2, rs1, WORD,   rd))
function clause decode (0b10100 : [aq] : [rl] : (regno) rs2 : (regno) rs1 : 0b011 : (regno) rd : 0b0101111) =
  Some(AMO(AMOMAX , aq, rl, rs2, rs1, DOUBLE, rd))
function clause decode (0b11000 : [aq] : [rl] : (regno) rs2 : (regno) rs1 : 0b010 : (regno) rd : 0b0101111) =
  Some(AMO(AMOMINU, aq, rl, rs2, rs1, WORD,   rd))
function clause decode (0b11000 : [aq] : [rl] : (regno) rs2 : (regno) rs1 : 0b011 : (regno) rd : 0b0101111) =
  Some(AMO(AMOMINU, aq, rl, rs2, rs1, DOUBLE, rd))
function clause decode (0b11100 : [aq] : [rl] : (regno) rs2 : (regno) rs1 : 0b010 : (regno) rd : 0b0101111) =
  Some(AMO(AMOMAXU, aq, rl, rs2, rs1, WORD,   rd))
function clause decode (0b11100 : [aq] : [rl] : (regno) rs2 : (regno) rs1 : 0b011 : (regno) rd : 0b0101111) =
  Some(AMO(AMOMAXU, aq, rl, rs2, rs1, DOUBLE, rd))

function clause execute (AMO(op, aq, rl, rs2, rs1, width, rd)) = {
  (bit[64]) addr := rGPR(rs1);
  switch (width) {
    case WORD   -> mem_write_ea(addr, 4, aq & rl, rl, true)
    case DOUBLE -> mem_write_ea(addr, 8, aq & rl, rl, true)
  };

  (bit[64]) rs2_val := rGPR(rs2);

  (*atomic_memory_access_begin();*)
  (** this code should have a memoryload, followed by a memory store,
  and have no other effects **)

  (bit[64]) loaded := switch (width) {
    case WORD   -> EXTS(mem_read(addr, 4, aq, aq & rl, true))
    case DOUBLE ->      mem_read(addr, 8, aq, aq & rl, true)
  };

  (bit[64]) result := switch(op) {
    case AMOSWAP -> rs2_val
    case AMOADD  -> rs2_val + loaded
    case AMOXOR  -> rs2_val ^ loaded
    case AMOAND  -> rs2_val & loaded
    case AMOOR   -> rs2_val | loaded

    case AMOMIN  -> (bit[64]) (min(signed(rs2_val),   signed(loaded)))
    case AMOMAX  -> (bit[64]) (max(signed(rs2_val),   signed(loaded)))
    case AMOMINU -> (bit[64]) (min(unsigned(rs2_val), unsigned(loaded)))
    case AMOMAXU -> (bit[64]) (max(unsigned(rs2_val), unsigned(loaded)))
  };

  let success =
    switch (width) {
      case WORD   -> mem_cond_write_value(addr, 4, result[31..0], aq & rl, rl)
      case DOUBLE -> mem_cond_write_value(addr, 8, result,        aq & rl, rl)
    }
  in
  assert(success, Some("an AMO store has failed"));

  (*atomic_memory_access_end();*)

  wGPR(rd, loaded);
}

(********************************************************************)

function clause decode _ = None

end ast
end decode
end execute
