scattered union ast

val decode : bits(32) -> option(ast) effect pure
scattered function decode

val decodeCompressed : bits(16) -> option(ast) effect pure
scattered function decodeCompressed


val execute : ast -> unit effect {escape, wreg, rreg, wmv, eamem, rmem, barr, exmem}
scattered function execute

/* ****************************************************************** */

union clause ast = UTYPE : (bits(20), regbits, uop)

function clause decode imm : bits(20) @ rd : regbits @ 0b0110111 = Some(UTYPE(imm, rd, RISCV_LUI))
function clause decode imm : bits(20) @ rd : regbits @ 0b0010111 = Some(UTYPE(imm, rd, RISCV_AUIPC))

function clause execute UTYPE(imm, rd, op) =
    let off : bits(64) = EXTS(imm @ 0x000) in
    let ret : regval   = match op {
      RISCV_LUI   => off,
      RISCV_AUIPC => PC + off
    } in
    wGPR(rd, ret)

/* ****************************************************************** */

union clause ast = RISCV_JAL : (bits(21), regbits)

function clause decode imm : bits(20) @ rd : regbits @ 0b1101111 = Some (RISCV_JAL(imm[19] @ imm[7..0] @ imm[8] @ imm[18..13] @ imm[12..9] @ 0b0, rd))

function clause execute (RISCV_JAL(imm, rd)) = {
    let pc : bits(64) = PC;
    wGPR(rd, nextPC);  /* compatible with JAL and C.JAL */
    let offset : bits(64) = EXTS(imm);
    nextPC = pc + offset;
}

/* ****************************************************************** */
union clause ast = RISCV_JALR : (bits(12), regbits, regbits)

function clause decode imm : bits(12) @ rs1 : regbits @ 0b000 @ rd : regbits @ 0b1100111 =
    Some(RISCV_JALR(imm, rs1, rd))

function clause execute (RISCV_JALR(imm, rs1, rd)) = {
    /* write rd before anything else to prevent unintended strength */
    wGPR(rd, PC + 4);
    let newPC : bits(64) = rGPR(rs1) + EXTS(imm);
    nextPC = newPC[63..1] @ 0b0;
}

/* ****************************************************************** */
union clause ast = BTYPE : (bits(13), regbits, regbits, bop)

function clause decode imm7 : bits(7) @ rs2 : regbits @ rs1 : regbits @ 0b000 @ imm5 : bits(5) @ 0b1100011 = Some(BTYPE(imm7[6] @ imm5[0] @ imm7[5..0] @ imm5[4..1] @ 0b0, rs2, rs1, RISCV_BEQ))
function clause decode imm7 : bits(7) @ rs2 : regbits @ rs1 : regbits @ 0b001 @ imm5 : bits(5) @ 0b1100011 = Some(BTYPE(imm7[6] @ imm5[0] @ imm7[5..0] @ imm5[4..1] @ 0b0, rs2, rs1, RISCV_BNE))
function clause decode imm7 : bits(7) @ rs2 : regbits @ rs1 : regbits @ 0b100 @ imm5 : bits(5) @ 0b1100011 = Some(BTYPE(imm7[6] @ imm5[0] @ imm7[5..0] @ imm5[4..1] @ 0b0, rs2, rs1, RISCV_BLT))
function clause decode imm7 : bits(7) @ rs2 : regbits @ rs1 : regbits @ 0b101 @ imm5 : bits(5) @ 0b1100011 = Some(BTYPE(imm7[6] @ imm5[0] @ imm7[5..0] @ imm5[4..1] @ 0b0, rs2, rs1, RISCV_BGE))
function clause decode imm7 : bits(7) @ rs2 : regbits @ rs1 : regbits @ 0b110 @ imm5 : bits(5) @ 0b1100011 = Some(BTYPE(imm7[6] @ imm5[0] @ imm7[5..0] @ imm5[4..1] @ 0b0, rs2, rs1, RISCV_BLTU))
function clause decode imm7 : bits(7) @ rs2 : regbits @ rs1 : regbits @ 0b111 @ imm5 : bits(5) @ 0b1100011 = Some(BTYPE(imm7[6] @ imm5[0] @ imm7[5..0] @ imm5[4..1] @ 0b0, rs2, rs1, RISCV_BGEU))

function clause execute (BTYPE(imm, rs2, rs1, op)) =
  let rs1_val = rGPR(rs1) in
  let rs2_val = rGPR(rs2) in
  let taken : bool = match op {
    RISCV_BEQ  => rs1_val == rs2_val,
    RISCV_BNE  => rs1_val != rs2_val,
    RISCV_BLT  => rs1_val <_s rs2_val,
    RISCV_BGE  => rs1_val >=_s rs2_val,
    RISCV_BLTU => rs1_val <_u rs2_val,
    RISCV_BGEU => rs1_val >=_u rs2_val
  } in
  if taken then
    nextPC = PC + EXTS(imm)

/* ****************************************************************** */
union clause ast = ITYPE : (bits(12), regbits, regbits, iop)

function clause decode imm : bits(12) @ rs1 : regbits @ 0b000 @ rd : regbits @ 0b0010011 = Some(ITYPE(imm, rs1, rd, RISCV_ADDI))
function clause decode imm : bits(12) @ rs1 : regbits @ 0b010 @ rd : regbits @ 0b0010011 = Some(ITYPE(imm, rs1, rd, RISCV_SLTI))
function clause decode imm : bits(12) @ rs1 : regbits @ 0b011 @ rd : regbits @ 0b0010011 = Some(ITYPE(imm, rs1, rd, RISCV_SLTIU))
function clause decode imm : bits(12) @ rs1 : regbits @ 0b100 @ rd : regbits @ 0b0010011 = Some(ITYPE(imm, rs1, rd, RISCV_XORI))
function clause decode imm : bits(12) @ rs1 : regbits @ 0b110 @ rd : regbits @ 0b0010011 = Some(ITYPE(imm, rs1, rd, RISCV_ORI))
function clause decode imm : bits(12) @ rs1 : regbits @ 0b111 @ rd : regbits @ 0b0010011 = Some(ITYPE(imm, rs1, rd, RISCV_ANDI))

function clause execute (ITYPE (imm, rs1, rd, op)) =
  let rs1_val = rGPR(rs1) in
  let imm64 : bits(64) = EXTS(imm) in
  let result : bits(64) = match op {
    RISCV_ADDI  => rs1_val + imm64,
    RISCV_SLTI  => EXTZ(rs1_val <_s imm64),
    RISCV_SLTIU => EXTZ(rs1_val <_u imm64),
    RISCV_XORI  => rs1_val ^ imm64,
    RISCV_ORI   => rs1_val | imm64,
    RISCV_ANDI  => rs1_val & imm64
  } in
  wGPR(rd, result)

/* ****************************************************************** */
union clause ast = SHIFTIOP : (bits(6), regbits, regbits, sop)

function clause decode 0b000000 @ shamt : bits(6) @ rs1 : regbits @ 0b001 @ rd : regbits @ 0b0010011 = Some(SHIFTIOP(shamt, rs1, rd, RISCV_SLLI))
function clause decode 0b000000 @ shamt : bits(6) @ rs1 : regbits @ 0b101 @ rd : regbits @ 0b0010011 = Some(SHIFTIOP(shamt, rs1, rd, RISCV_SRLI))
function clause decode 0b010000 @ shamt : bits(6) @ rs1 : regbits @ 0b101 @ rd : regbits @ 0b0010011 = Some(SHIFTIOP(shamt, rs1, rd, RISCV_SRAI))

function clause execute (SHIFTIOP(shamt, rs1, rd, op)) = 
    let rs1_val = rGPR(rs1) in
    let result : bits(64) = match op {
      RISCV_SLLI => rs1_val << shamt,
      RISCV_SRLI => rs1_val >> shamt,
      RISCV_SRAI => shift_right_arith64(rs1_val, shamt)
    } in
    wGPR(rd, result)


/* ****************************************************************** */
union clause ast = RTYPE : (regbits, regbits, regbits, rop)

function clause decode 0b0000000 @ rs2 : regbits @ rs1 : regbits @ 0b000 @ rd : regbits @ 0b0110011 = Some(RTYPE(rs2, rs1, rd, RISCV_ADD))
function clause decode 0b0100000 @ rs2 : regbits @ rs1 : regbits @ 0b000 @ rd : regbits @ 0b0110011 = Some(RTYPE(rs2, rs1, rd, RISCV_SUB))
function clause decode 0b0000000 @ rs2 : regbits @ rs1 : regbits @ 0b001 @ rd : regbits @ 0b0110011 = Some(RTYPE(rs2, rs1, rd, RISCV_SLL))
function clause decode 0b0000000 @ rs2 : regbits @ rs1 : regbits @ 0b010 @ rd : regbits @ 0b0110011 = Some(RTYPE(rs2, rs1, rd, RISCV_SLT))
function clause decode 0b0000000 @ rs2 : regbits @ rs1 : regbits @ 0b011 @ rd : regbits @ 0b0110011 = Some(RTYPE(rs2, rs1, rd, RISCV_SLTU))
function clause decode 0b0000000 @ rs2 : regbits @ rs1 : regbits @ 0b100 @ rd : regbits @ 0b0110011 = Some(RTYPE(rs2, rs1, rd, RISCV_XOR))
function clause decode 0b0000000 @ rs2 : regbits @ rs1 : regbits @ 0b101 @ rd : regbits @ 0b0110011 = Some(RTYPE(rs2, rs1, rd, RISCV_SRL))
function clause decode 0b0100000 @ rs2 : regbits @ rs1 : regbits @ 0b101 @ rd : regbits @ 0b0110011 = Some(RTYPE(rs2, rs1, rd, RISCV_SRA))
function clause decode 0b0000000 @ rs2 : regbits @ rs1 : regbits @ 0b110 @ rd : regbits @ 0b0110011 = Some(RTYPE(rs2, rs1, rd, RISCV_OR))
function clause decode 0b0000000 @ rs2 : regbits @ rs1 : regbits @ 0b111 @ rd : regbits @ 0b0110011 = Some(RTYPE(rs2, rs1, rd, RISCV_AND))


function clause execute (RTYPE(rs2, rs1, rd, op)) =
  let rs1_val = rGPR(rs1) in
  let rs2_val = rGPR(rs2) in
  let result : bits(64) = match op {
    RISCV_ADD  => rs1_val + rs2_val,
    RISCV_SUB  => rs1_val - rs2_val,
    RISCV_SLL  => rs1_val << (rs2_val[5..0]),
    RISCV_SLT  => EXTZ(rs1_val <_s rs2_val),
    RISCV_SLTU => EXTZ(rs1_val <_u rs2_val),
    RISCV_XOR  => rs1_val ^ rs2_val,
    RISCV_SRL  => rs1_val >> (rs2_val[5..0]),
    RISCV_SRA  => shift_right_arith64(rs1_val, rs2_val[5..0]),
    RISCV_OR   => rs1_val | rs2_val,
    RISCV_AND  => rs1_val & rs2_val
  } in
  wGPR(rd, result)

/* ****************************************************************** */
union clause ast = LOAD : (bits(12), regbits, regbits, bool, word_width, bool, bool)

function clause decode imm : bits(12) @ rs1 : regbits @ 0b000 @ rd : regbits @ 0b0000011 = Some(LOAD(imm, rs1, rd, false, BYTE,   false, false))
function clause decode imm : bits(12) @ rs1 : regbits @ 0b001 @ rd : regbits @ 0b0000011 = Some(LOAD(imm, rs1, rd, false, HALF,   false, false))
function clause decode imm : bits(12) @ rs1 : regbits @ 0b010 @ rd : regbits @ 0b0000011 = Some(LOAD(imm, rs1, rd, false, WORD,   false, false))
function clause decode imm : bits(12) @ rs1 : regbits @ 0b011 @ rd : regbits @ 0b0000011 = Some(LOAD(imm, rs1, rd, false, DOUBLE, false, false))
function clause decode imm : bits(12) @ rs1 : regbits @ 0b100 @ rd : regbits @ 0b0000011 = Some(LOAD(imm, rs1, rd, true,  BYTE,   false, false))
function clause decode imm : bits(12) @ rs1 : regbits @ 0b101 @ rd : regbits @ 0b0000011 = Some(LOAD(imm, rs1, rd, true,  HALF,   false, false))
function clause decode imm : bits(12) @ rs1 : regbits @ 0b110 @ rd : regbits @ 0b0000011 = Some(LOAD(imm, rs1, rd, true,  WORD,   false, false))


function clause execute(LOAD(imm, rs1, rd, is_unsigned, width, aq, rl)) =
    let addr : bits(64) = rGPR(rs1) + EXTS(imm) in
    let result : bits(64) = if is_unsigned then
        match width {
	  BYTE   => EXTZ(mem_read(addr, 1, aq, rl, false)),
	  HALF   => EXTZ(mem_read(addr, 2, aq, rl, false)),
	  WORD   => EXTZ(mem_read(addr, 4, aq, rl, false)),
	  DOUBLE => mem_read(addr, 8, aq, rl, false)
        }
      else
        match width {
	  BYTE   => EXTS(mem_read(addr, 1, aq, rl, false)),
	  HALF   => EXTS(mem_read(addr, 2, aq, rl, false)),
	  WORD   => EXTS(mem_read(addr, 4, aq, rl, false)),
	  DOUBLE => mem_read(addr, 8, aq, rl, false)
        } in
    wGPR(rd, result)

/* ****************************************************************** */
union clause ast = STORE : (bits(12), regbits, regbits, word_width, bool, bool)

function clause decode imm7 : bits(7) @ rs2 : regbits @ rs1 : regbits @ 0b000 @ imm5 : bits(5) @ 0b0100011 = Some(STORE(imm7 @ imm5, rs2, rs1, BYTE, false, false))
function clause decode imm7 : bits(7) @ rs2 : regbits @ rs1 : regbits @ 0b001 @ imm5 : bits(5) @ 0b0100011 = Some(STORE(imm7 @ imm5, rs2, rs1, HALF, false, false))
function clause decode imm7 : bits(7) @ rs2 : regbits @ rs1 : regbits @ 0b010 @ imm5 : bits(5) @ 0b0100011 = Some(STORE(imm7 @ imm5, rs2, rs1, WORD, false, false))
function clause decode imm7 : bits(7) @ rs2 : regbits @ rs1 : regbits @ 0b011 @ imm5 : bits(5) @ 0b0100011 = Some(STORE(imm7 @ imm5, rs2, rs1, DOUBLE, false, false))

function clause execute (STORE(imm, rs2, rs1, width, aq, rl)) =
    let addr : bits(64) = rGPR(rs1) + EXTS(imm) in {
      match width {
	BYTE   => mem_write_ea(addr, 1, aq, rl, false),
	HALF   => mem_write_ea(addr, 2, aq, rl, false),
	WORD   => mem_write_ea(addr, 4, aq, rl, false),
	DOUBLE => mem_write_ea(addr, 8, aq, rl, false)
      };
      let rs2_val = rGPR(rs2) in
      match width {
	BYTE   => mem_write_value(addr, 1, rs2_val[7..0],  aq, rl, false),
	HALF   => mem_write_value(addr, 2, rs2_val[15..0], aq, rl, false),
	WORD   => mem_write_value(addr, 4, rs2_val[31..0], aq, rl, false),
	DOUBLE => mem_write_value(addr, 8, rs2_val,        aq, rl, false)
      }
    }


/* ****************************************************************** */
union clause ast = ADDIW : (bits(12), regbits, regbits)

function clause decode imm : bits(12) @ rs1 : regbits @ 0b000 @ rd : regbits @ 0b0011011 = Some(ADDIW(imm, rs1, rd))

function clause execute (ADDIW(imm, rs1, rd)) =
  let imm64 : bits(64) = EXTS(imm) in
  let result64 : bits(64) = imm64 + rGPR(rs1) in
  let result32 : bits(64) = EXTS(result64[31..0]) in
  wGPR(rd, result32)

/* ****************************************************************** */
union clause ast = SHIFTW : (bits(5), regbits, regbits, sop)

function clause decode 0b0000000 @ shamt : bits(5) @ rs1 : regbits @ 0b001 @ rd : regbits @ 0b0011011 = Some(SHIFTW(shamt, rs1, rd, RISCV_SLLI))
function clause decode 0b0000000 @ shamt : bits(5) @ rs1 : regbits @ 0b101 @ rd : regbits @ 0b0011011 = Some(SHIFTW(shamt, rs1, rd, RISCV_SRLI))
function clause decode 0b0100000 @ shamt : bits(5) @ rs1 : regbits @ 0b101 @ rd : regbits @ 0b0011011 = Some(SHIFTW(shamt, rs1, rd, RISCV_SRAI))

function clause execute (SHIFTW(shamt, rs1, rd, op)) =
    let rs1_val = (rGPR(rs1))[31..0] in
    let result : bits(32) = match op {
      RISCV_SLLI => rs1_val << shamt,
      RISCV_SRLI => rs1_val >> shamt,
      RISCV_SRAI => shift_right_arith32(rs1_val, shamt)
    } in
    wGPR(rd, EXTS(result))

/* ****************************************************************** */
union clause ast = RTYPEW : (regbits, regbits, regbits, ropw)

function clause decode 0b0000000 @ rs2 : regbits @ rs1 : regbits @ 0b000 @ rd : regbits @ 0b0111011 = Some(RTYPEW(rs2, rs1, rd, RISCV_ADDW))
function clause decode 0b0100000 @ rs2 : regbits @ rs1 : regbits @ 0b000 @ rd : regbits @ 0b0111011 = Some(RTYPEW(rs2, rs1, rd, RISCV_SUBW))
function clause decode 0b0000000 @ rs2 : regbits @ rs1 : regbits @ 0b001 @ rd : regbits @ 0b0111011 = Some(RTYPEW(rs2, rs1, rd, RISCV_SLLW))
function clause decode 0b0000000 @ rs2 : regbits @ rs1 : regbits @ 0b101 @ rd : regbits @ 0b0111011 = Some(RTYPEW(rs2, rs1, rd, RISCV_SRLW))
function clause decode 0b0100000 @ rs2 : regbits @ rs1 : regbits @ 0b101 @ rd : regbits @ 0b0111011 = Some(RTYPEW(rs2, rs1, rd, RISCV_SRAW))

function clause execute (RTYPEW(rs2, rs1, rd, op)) =
  let rs1_val = (rGPR(rs1))[31..0] in
  let rs2_val = (rGPR(rs2))[31..0] in
  let result : bits(32) = match op {
    RISCV_ADDW => rs1_val + rs2_val,
    RISCV_SUBW => rs1_val - rs2_val,
    RISCV_SLLW => rs1_val << (rs2_val[4..0]),
    RISCV_SRLW => rs1_val >> (rs2_val[4..0]),
    RISCV_SRAW => shift_right_arith32(rs1_val, rs2_val[4..0])
  } in
  wGPR(rd, EXTS(result))

/* ****************************************************************** */

union clause ast = MUL : (regbits, regbits, regbits, bool, bool, bool)

function clause decode 0b0000001 @ rs2 : regbits @ rs1 : regbits @ 0b000 @ rd : regbits @ 0b0110011 = Some(MUL(rs2, rs1, rd, false,  true, true))  /* MUL */
function clause decode 0b0000001 @ rs2 : regbits @ rs1 : regbits @ 0b001 @ rd : regbits @ 0b0110011 = Some(MUL(rs2, rs1, rd,  true,  true, true))  /* MULH */
function clause decode 0b0000001 @ rs2 : regbits @ rs1 : regbits @ 0b010 @ rd : regbits @ 0b0110011 = Some(MUL(rs2, rs1, rd,  true,  true, false)) /* MULHSU */
function clause decode 0b0000001 @ rs2 : regbits @ rs1 : regbits @ 0b011 @ rd : regbits @ 0b0110011 = Some(MUL(rs2, rs1, rd,  true, false, false)) /* MULHU */
function clause execute (MUL(rs2, rs1, rd, high, signed1, signed2)) =
  let rs1_val = rGPR(rs1) in
  let rs2_val = rGPR(rs2) in
  let rs1_int : int = if signed1 then signed(rs1_val) else unsigned(rs1_val) in
  let rs2_int : int = if signed2 then signed(rs2_val) else unsigned(rs2_val) in
  let result128 = to_bits(128, rs1_int * rs2_int) in
  let result = if high then result128[127..64] else result128[63..0] in
  wGPR(rd, result)

/* ****************************************************************** */

union clause ast = DIV : (regbits, regbits, regbits, bool)
function clause decode 0b0000001 @ rs2 : regbits @ rs1 : regbits @ 0b100 @ rd : regbits @ 0b0110011 = Some(DIV(rs2, rs1, rd,  true))  /* DIV */
function clause decode 0b0000001 @ rs2 : regbits @ rs1 : regbits @ 0b101 @ rd : regbits @ 0b0110011 = Some(DIV(rs2, rs1, rd, false))  /* DIVU */
function clause execute (DIV(rs2, rs1, rd, s)) =
  let rs1_val = rGPR(rs1) in
  let rs2_val = rGPR(rs2) in
  let rs1_int : int = if s then signed(rs1_val) else unsigned(rs1_val) in
  let rs2_int : int = if s then signed(rs2_val) else unsigned(rs2_val) in
  let q : int = if rs2_int == 0 then -1 else quot_round_zero(rs1_int, rs2_int) in
  let q': int = if s & q > (2 ^ 63 - 1) then  (0 - 2^63) else q in /* check for signed overflow */
  wGPR(rd, to_bits(64, q'))

/* ****************************************************************** */

union clause ast = REM : (regbits, regbits, regbits, bool)
function clause decode 0b0000001 @ rs2 : regbits @ rs1 : regbits @ 0b110 @ rd : regbits @ 0b0110011 = Some(REM(rs2, rs1, rd,  true))  /* REM */
function clause decode 0b0000001 @ rs2 : regbits @ rs1 : regbits @ 0b111 @ rd : regbits @ 0b0110011 = Some(REM(rs2, rs1, rd, false))  /* REMU */
function clause execute (REM(rs2, rs1, rd, s)) =
  let rs1_val = rGPR(rs1) in
  let rs2_val = rGPR(rs2) in
  let rs1_int : int = if s then signed(rs1_val) else unsigned(rs1_val) in
  let rs2_int : int = if s then signed(rs2_val) else unsigned(rs2_val) in
  let r : int = if rs2_int == 0 then rs1_int else rem_round_zero(rs1_int, rs2_int) in
  /* signed overflow case returns zero naturally as required due to -1 divisor */
  wGPR(rd, to_bits(64, r))

/* ****************************************************************** */

union clause ast = MULW : (regbits, regbits, regbits)
function clause decode 0b0000001 @ rs2 : regbits @ rs1 : regbits @ 0b000 @ rd : regbits @ 0b0111011 = Some(MULW(rs2, rs1, rd)) /* MULW */
function clause execute (MULW(rs2, rs1, rd)) =
  let rs1_val = rGPR(rs1)[31..0] in
  let rs2_val = rGPR(rs2)[31..0] in
  let rs1_int : int = signed(rs1_val) in
  let rs2_int : int = signed(rs2_val) in
  let result32 = to_bits(64, rs1_int * rs2_int)[31..0] in /* XXX surprising behaviour of to_bits requires exapnsion to 64 bits followed by truncation... */
  let result64 : regval = EXTS(result32) in
  wGPR(rd, result64)

/* ****************************************************************** */

union clause ast = DIVW : (regbits, regbits, regbits, bool)
function clause decode 0b0000001 @ rs2 : regbits @ rs1 : regbits @ 0b100 @ rd : regbits @ 0b0111011 = Some(DIVW(rs2, rs1, rd,  true))  /* DIVW */
function clause decode 0b0000001 @ rs2 : regbits @ rs1 : regbits @ 0b101 @ rd : regbits @ 0b0111011 = Some(DIVW(rs2, rs1, rd, false))  /* DIVUW */
function clause execute (DIVW(rs2, rs1, rd, s)) =
  let rs1_val = rGPR(rs1)[31..0] in
  let rs2_val = rGPR(rs2)[31..0] in
  let rs1_int : int = if s then signed(rs1_val) else unsigned(rs1_val) in
  let rs2_int : int = if s then signed(rs2_val) else unsigned(rs2_val) in
  let q : int = if rs2_int == 0 then -1 else quot_round_zero(rs1_int, rs2_int) in
  let q': int = if s & q > (2 ^ 31 - 1) then  (0 - 2^31) else q in /* check for signed overflow */
  wGPR(rd, EXTS(to_bits(32, q')))

/* ****************************************************************** */

union clause ast = REMW : (regbits, regbits, regbits, bool)
function clause decode 0b0000001 @ rs2 : regbits @ rs1 : regbits @ 0b110 @ rd : regbits @ 0b0111011 = Some(REMW(rs2, rs1, rd,  true))  /* REMW */
function clause decode 0b0000001 @ rs2 : regbits @ rs1 : regbits @ 0b111 @ rd : regbits @ 0b0111011 = Some(REMW(rs2, rs1, rd, false))  /* REMUW */
function clause execute (REMW(rs2, rs1, rd, s)) =
  let rs1_val = rGPR(rs1)[31..0] in
  let rs2_val = rGPR(rs2)[31..0] in
  let rs1_int : int = if s then signed(rs1_val) else unsigned(rs1_val) in
  let rs2_int : int = if s then signed(rs2_val) else unsigned(rs2_val) in
  let r : int = if rs2_int == 0 then rs1_int else rem_round_zero(rs1_int, rs2_int) in
  /* signed overflow case returns zero naturally as required due to -1 divisor */
  wGPR(rd, EXTS(to_bits(32, r)))

/* ****************************************************************** */

union clause ast = FENCE : (bits(4), bits(4))

function clause decode 0b0000 @ pred : bits(4) @ succ : bits(4) @ 0b00000 @ 0b000 @ 0b00000 @ 0b0001111 = Some(FENCE(pred, succ))

function clause execute (FENCE(pred, succ)) = {
  match (pred, succ) {
    (0b0011, 0b0011) => MEM_fence_rw_rw(),
    (0b0010, 0b0011) => MEM_fence_r_rw(),
    (0b0010, 0b0010) => MEM_fence_r_r(),
    (0b0011, 0b0001) => MEM_fence_rw_w(),
    (0b0001, 0b0001) => MEM_fence_w_w(),
    _ => { print("FIXME: unsupported fence");
           () }
  }
}

/* ****************************************************************** */
union clause ast = FENCEI

function clause decode 0b000000000000 @ 0b00000 @ 0b001 @ 0b00000 @ 0b0001111 = Some(FENCEI)

function clause execute FENCEI = MEM_fence_i()

/* ****************************************************************** */
union clause ast = ECALL

function clause decode 0b000000000000 @ 0b00000 @ 0b000 @ 0b00000 @ 0b1110011 = Some(ECALL)

function clause execute ECALL =
  let t : sync_exception =
    struct { trap = match (cur_privilege) {
                      USER => User_ECall,
		      MACHINE => Machine_ECall
		    },
             excinfo = (None : option(regval)) } in
  nextPC = handle_exception_ctl(cur_privilege, CTL_TRAP(t), PC)

/* ****************************************************************** */
union clause ast = MRET

function clause decode 0b0011000 @ 0b00010 @ 0b00000 @ 0b000 @ 0b00000 @ 0b1110011 = Some(MRET)

function clause execute MRET =
  nextPC = handle_exception_ctl(cur_privilege, CTL_MRET, PC)

/* ****************************************************************** */
union clause ast = EBREAK

function clause decode 0b000000000001 @ 0b00000 @ 0b000 @ 0b00000 @ 0b1110011 = Some(EBREAK)

function clause execute EBREAK = { throw(Error_EBREAK) }

/* ****************************************************************** */
union clause ast = LOADRES : (bool, bool, regbits, word_width, regbits)

function clause decode 0b00010 @ [aq] @ [rl] @ 0b00000 @ rs1 : regbits @ 0b010 @ rd : regbits @ 0b0101111 = Some(LOADRES(aq, rl, rs1, WORD, rd))
function clause decode 0b00010 @ [aq] @ [rl] @ 0b00000 @ rs1 : regbits @ 0b011 @ rd : regbits @ 0b0101111 = Some(LOADRES(aq, rl, rs1, DOUBLE, rd))

function clause execute(LOADRES(aq, rl, rs1, width, rd)) =
  let addr : bits(64) = rGPR(rs1) in
  let result : bits(64) =
      match width {
	WORD   => EXTS(mem_read(addr, 4, aq, rl, true)),
	DOUBLE => mem_read(addr, 8, aq, rl, true),
	_      => internal_error("LOADRES expected WORD or DOUBLE")
      } in
  wGPR(rd, result)

/* ****************************************************************** */
union clause ast = STORECON : (bool, bool, regbits, regbits, word_width, regbits)

function clause decode 0b00011 @ [aq] @ [rl] @ rs2 : regbits @ rs1 : regbits @ 0b010 @ rd : regbits @ 0b0101111 = Some(STORECON(aq, rl, rs2, rs1, WORD, rd))
function clause decode 0b00011 @ [aq] @ [rl] @ rs2 : regbits @ rs1 : regbits @ 0b011 @ rd : regbits @ 0b0101111 = Some(STORECON(aq, rl, rs2, rs1, DOUBLE, rd))

function clause execute (STORECON(aq, rl, rs2, rs1, width, rd)) = {
  status : bits(1) = if speculate_conditional_success() then 0b0 else 0b1;
  wGPR(rd) = EXTZ(status);

  if status == 0b1 then () else {
    addr : bits(64) = rGPR(rs1);
    match width {
      WORD   => mem_write_ea(addr, 4, aq, rl, true),
      DOUBLE => mem_write_ea(addr, 8, aq, rl, true),
      _      => internal_error("STORECON expected word or double")
    };
    rs2_val = rGPR(rs2);
    match width {
      WORD   => mem_write_value(addr, 4, rs2_val[31..0], aq, rl, true),
      DOUBLE => mem_write_value(addr, 8, rs2_val,        aq, rl, true),
      _      => internal_error("STORECON expected word or double")
    };
  };
}

/* ****************************************************************** */
union clause ast = AMO : (amoop, bool, bool, regbits, regbits, word_width, regbits)

function clause decode 0b00001 @ [aq] @ [rl] @ rs2 : regbits @ rs1 : regbits @ 0b010 @ rd : regbits @ 0b0101111 = Some(AMO(AMOSWAP, aq, rl, rs2, rs1, WORD,   rd))
function clause decode 0b00001 @ [aq] @ [rl] @ rs2 : regbits @ rs1 : regbits @ 0b011 @ rd : regbits @ 0b0101111 = Some(AMO(AMOSWAP, aq, rl, rs2, rs1, DOUBLE, rd))
function clause decode 0b00000 @ [aq] @ [rl] @ rs2 : regbits @ rs1 : regbits @ 0b010 @ rd : regbits @ 0b0101111 = Some(AMO(AMOADD , aq, rl, rs2, rs1, WORD,   rd))
function clause decode 0b00000 @ [aq] @ [rl] @ rs2 : regbits @ rs1 : regbits @ 0b011 @ rd : regbits @ 0b0101111 = Some(AMO(AMOADD , aq, rl, rs2, rs1, DOUBLE, rd))
function clause decode 0b00100 @ [aq] @ [rl] @ rs2 : regbits @ rs1 : regbits @ 0b010 @ rd : regbits @ 0b0101111 = Some(AMO(AMOXOR , aq, rl, rs2, rs1, WORD,   rd))
function clause decode 0b00100 @ [aq] @ [rl] @ rs2 : regbits @ rs1 : regbits @ 0b011 @ rd : regbits @ 0b0101111 = Some(AMO(AMOXOR , aq, rl, rs2, rs1, DOUBLE, rd))
function clause decode 0b01100 @ [aq] @ [rl] @ rs2 : regbits @ rs1 : regbits @ 0b010 @ rd : regbits @ 0b0101111 = Some(AMO(AMOAND , aq, rl, rs2, rs1, WORD,   rd))
function clause decode 0b01100 @ [aq] @ [rl] @ rs2 : regbits @ rs1 : regbits @ 0b011 @ rd : regbits @ 0b0101111 = Some(AMO(AMOAND , aq, rl, rs2, rs1, DOUBLE, rd))
function clause decode 0b01000 @ [aq] @ [rl] @ rs2 : regbits @ rs1 : regbits @ 0b010 @ rd : regbits @ 0b0101111 = Some(AMO(AMOOR  , aq, rl, rs2, rs1, WORD,   rd))
function clause decode 0b01000 @ [aq] @ [rl] @ rs2 : regbits @ rs1 : regbits @ 0b011 @ rd : regbits @ 0b0101111 = Some(AMO(AMOOR  , aq, rl, rs2, rs1, DOUBLE, rd))
function clause decode 0b10000 @ [aq] @ [rl] @ rs2 : regbits @ rs1 : regbits @ 0b010 @ rd : regbits @ 0b0101111 = Some(AMO(AMOMIN , aq, rl, rs2, rs1, WORD,   rd))
function clause decode 0b10000 @ [aq] @ [rl] @ rs2 : regbits @ rs1 : regbits @ 0b011 @ rd : regbits @ 0b0101111 = Some(AMO(AMOMIN , aq, rl, rs2, rs1, DOUBLE, rd))
function clause decode 0b10100 @ [aq] @ [rl] @ rs2 : regbits @ rs1 : regbits @ 0b010 @ rd : regbits @ 0b0101111 = Some(AMO(AMOMAX , aq, rl, rs2, rs1, WORD,   rd))
function clause decode 0b10100 @ [aq] @ [rl] @ rs2 : regbits @ rs1 : regbits @ 0b011 @ rd : regbits @ 0b0101111 = Some(AMO(AMOMAX , aq, rl, rs2, rs1, DOUBLE, rd))
function clause decode 0b11000 @ [aq] @ [rl] @ rs2 : regbits @ rs1 : regbits @ 0b010 @ rd : regbits @ 0b0101111 = Some(AMO(AMOMINU, aq, rl, rs2, rs1, WORD,   rd))
function clause decode 0b11000 @ [aq] @ [rl] @ rs2 : regbits @ rs1 : regbits @ 0b011 @ rd : regbits @ 0b0101111 = Some(AMO(AMOMINU, aq, rl, rs2, rs1, DOUBLE, rd))
function clause decode 0b11100 @ [aq] @ [rl] @ rs2 : regbits @ rs1 : regbits @ 0b010 @ rd : regbits @ 0b0101111 = Some(AMO(AMOMAXU, aq, rl, rs2, rs1, WORD,   rd))
function clause decode 0b11100 @ [aq] @ [rl] @ rs2 : regbits @ rs1 : regbits @ 0b011 @ rd : regbits @ 0b0101111 = Some(AMO(AMOMAXU, aq, rl, rs2, rs1, DOUBLE, rd))

function clause execute (AMO(op, aq, rl, rs2, rs1, width, rd)) = {
  addr : bits(64) = rGPR(rs1);

  match width {
    WORD   => mem_write_ea(addr, 4, aq & rl, rl, true),
    DOUBLE => mem_write_ea(addr, 8, aq & rl, rl, true),
    _      => internal_error ("AMO expected WORD or DOUBLE")
  };

  loaded : bits(64) =
    match width {
      WORD   => EXTS(mem_read(addr, 4, aq, aq & rl, true)),
      DOUBLE => mem_read(addr, 8, aq, aq & rl, true),
      _      => internal_error ("AMO expected WORD or DOUBLE")
    };
  wGPR(rd) = loaded;

  rs2_val : bits(64) = rGPR(rs2);
  result : bits(64) =
    match op {
      AMOSWAP => rs2_val,
      AMOADD  => rs2_val + loaded,
      AMOXOR  => rs2_val ^ loaded,
      AMOAND  => rs2_val & loaded,
      AMOOR   => rs2_val | loaded,

      /* Have to convert number to vector here. Check this */
      AMOMIN  => vector64(min(signed(rs2_val),   signed(loaded))),
      AMOMAX  => vector64(max(signed(rs2_val),   signed(loaded))),
      AMOMINU => vector64(min(unsigned(rs2_val), unsigned(loaded))),
      AMOMAXU => vector64(max(unsigned(rs2_val), unsigned(loaded)))
    };

  match width {
    WORD   => mem_write_value(addr, 4, result[31..0], aq & rl, rl, true),
    DOUBLE => mem_write_value(addr, 8, result,        aq & rl, rl, true),
    _      => internal_error("AMO expected WORD or DOUBLE")
  };
}

union clause ast = CSR  : (bits(12), regbits, regbits, bool, csrop)

function clause decode csr : bits(12) @ rs1 : regbits @ 0b001 @ rd : regbits @ 0b1110011 = Some(CSR (csr, rs1, rd, false, CSRRW))
function clause decode csr : bits(12) @ rs1 : regbits @ 0b010 @ rd : regbits @ 0b1110011 = Some(CSR (csr, rs1, rd, false, CSRRS))
function clause decode csr : bits(12) @ rs1 : regbits @ 0b011 @ rd : regbits @ 0b1110011 = Some(CSR (csr, rs1, rd, false, CSRRC))
function clause decode csr : bits(12) @ rs1 : regbits @ 0b101 @ rd : regbits @ 0b1110011 = Some(CSR (csr, rs1, rd, true,  CSRRW))
function clause decode csr : bits(12) @ rs1 : regbits @ 0b110 @ rd : regbits @ 0b1110011 = Some(CSR (csr, rs1, rd, true,  CSRRS))
function clause decode csr : bits(12) @ rs1 : regbits @ 0b111 @ rd : regbits @ 0b1110011 = Some(CSR (csr, rs1, rd, true,  CSRRC))

val isCSRImplemented : bits(12) -> bool
function isCSRImplemented csr : bits(12) -> bool =
  match csr {
    0xf11 => true, // mvendorid
    0xf12 => true, // marchdid
    0xf13 => true, // mimpid
    0xf14 => true, // mhartid
    0x300 => true, // mstatus
    0x301 => true, // misa
    0x302 => true, // medeleg
    0x303 => true, // mideleg
    0x304 => true, // mie
    0x305 => true, // mtvec
    0x306 => true, // mcounteren
    0x340 => true, // mscratch
    0x341 => true, // mepc
    0x342 => true, // mcause
    0x343 => true, // mtval
    0x344 => true, // mip

    // for riscv-tests
    0x180 => true, // satp
    _     => false
  }

function readCSR csr: bits(12) -> regval =
  match csr {
    0x300 => mstatus.bits(),
    0x302 => medeleg.bits(),
    0x303 => mideleg.bits(),
    0x304 => mie.bits(),
    0x305 => mtvec,
    0x340 => mscratch,
    0x341 => mepc,
    0x342 => mcause,
    0x343 => mtval,
    0x344 => mip.bits(),
    _     => { print_bits("unhandled read to CSR ", csr);
               0x0000_0000_0000_0000 }
  }

function writeCSR (csr : bits(12), value : bits(64)) -> unit =
  match csr {
    0x300 => mstatus->bits() = value,
    0x302 => medeleg->bits() = value,
    0x303 => mideleg->bits() = value,
    0x304 => mie->bits() = value,
    0x305 => mtvec = value,
    0x340 => mscratch = value,
    0x341 => mepc = value,
    0x342 => mcause = value,
    0x343 => mtval = value,
    0x344 => mip->bits() = value,
    _     => print_bits("unhandled write to CSR ", csr)
  }

function haveCSRPriv (csr : bits(12), isWrite : bool) -> bool =
  let isRO = csr[11..10] == 0b11 in
  ~ (isRO & isWrite) /* XXX TODO check priv */

val signalIllegalInstruction : unit -> unit effect {escape}
function signalIllegalInstruction () = not_implemented ("illegal instruction")

function clause execute CSR(csr, rs1, rd, is_imm, op) =
  let rs1_val : bits(64) = if is_imm then EXTZ(rs1) else rGPR(rs1) in
  let isWrite : bool = match op {
    CSRRW  => true,
    _      => if is_imm then unsigned(rs1_val) != 0 else unsigned(rs1) != 0
  } in
  if ~ (isCSRImplemented(csr) & haveCSRPriv(csr, isWrite)) then {
    let instr : regval = EXTZ(__RISCV_read(PC, 4));
    let t : sync_exception =
    struct { trap = Illegal_Instr,
             excinfo = Some (instr) } in
    nextPC = handle_exception_ctl(cur_privilege, CTL_TRAP(t), PC)
  } else {
    let csr_val = readCSR(csr); /* could have side-effects, so technically shouldn't perform for CSRW[I] with rd == 0 */
    if isWrite then {
      let new_val : bits(64) = match op {
        CSRRW => rs1_val,
        CSRRS => csr_val | rs1_val,
        CSRRC => csr_val & ~(rs1_val)
      } in
      writeCSR(csr, new_val)
    };
    wGPR(rd, csr_val)
  }

/* ****************************************************************** */

union clause ast = NOP

function clause decodeCompressed (0b000 @ nzi1 : bits(1) @ 0b00000 @ (nzi0 : bits(5)) @ 0b01) : bits(16) = {
  if (nzi1 == 0b0) & (nzi0 == 0b00000) then None
  else Some(NOP)
}

function clause execute (NOP) = ()

/* ****************************************************************** */

union clause ast = ILLEGAL

function clause decodeCompressed (0b0000 @ 0b00000 @ 0b00000 @ 0b00) : bits(16) = Some(ILLEGAL)

function clause execute (ILLEGAL) = {
  let t : sync_exception =
  struct { trap = Illegal_Instr,
           excinfo = Some (EXTZ(0b0)) } in
  nextPC = handle_exception_ctl(cur_privilege, CTL_TRAP(t), PC)
}

/* ****************************************************************** */

union clause ast = C_ADDI4SPN : (cregbits, bits(8))

function clause decodeCompressed (0b000 @ nz54 : bits(2) @ nz96 : bits(4) @ nz2 : bits(1) @ nz3 : bits(1) @ rd : cregbits @ 0b00) : bits(16) = {
  let nzimm = (nz96 @ nz54 @ nz3 @ nz2) : bits(8) in
  if nzimm == 0b00000000 then None
  else Some(C_ADDI4SPN(rd, nzimm))
}

function clause execute (C_ADDI4SPN(rdc, nzimm)) = {
  let imm : bits(12) = (0b00 @ nzimm @ 0b00) in
  let rd = creg2reg_bits(rdc) in
  execute(ITYPE(imm, sp, rd, RISCV_ADDI))
}

/* ****************************************************************** */

union clause ast = C_LW : (bits(5), cregbits, cregbits)

function clause decodeCompressed (0b010 @ ui53 : bits(3) @ rs1 : cregbits @ ui2 : bits(1) @ ui6 : bits(1) @ rd : cregbits @ 0b00) : bits(16) = {
  let uimm = (ui6 @ ui53 @ ui2) : bits(5) in
  Some(C_LW(uimm, rs1, rd))
}

function clause execute (C_LW(uimm, rsc, rdc)) = {
  let imm : bits(12) = EXTZ(uimm @ 0b00) in
  let rd = creg2reg_bits(rdc) in
  let rs = creg2reg_bits(rsc) in
  execute(LOAD(imm, rs, rd, true, WORD, false, false))
}

/* ****************************************************************** */

union clause ast = C_SW : (bits(5), cregbits, cregbits)

function clause decodeCompressed (0b110 @ ui53 : bits(3) @ rs1 : cregbits @ ui2 : bits(1) @ ui6 : bits(1) @ rs2 : cregbits @ 0b00) : bits(16) = {
  let uimm = (ui6 @ ui53 @ ui2) : bits(5) in
  Some(C_SW(uimm, rs1, rs2))
}

function clause execute (C_SW(uimm, rsc1, rsc2)) = {
  let imm : bits(12) = EXTZ(uimm @ 0b00) in
  let rs1 = creg2reg_bits(rsc1) in
  let rs2 = creg2reg_bits(rsc2) in
  execute(STORE(imm, rs2, rs1, WORD, false, false))
}

/* ****************************************************************** */

union clause ast = C_SD : (bits(5), cregbits, cregbits)

function clause decodeCompressed (0b111 @ ui53 : bits(3) @ rs1 : bits(3) @ ui76 : bits(2) @ rs2 : bits(3) @ 0b00): bits(16) = {
  let uimm = (ui76 @ ui53) : bits(5) in
  Some(C_SD(uimm, rs1, rs2))
}

function clause execute (C_SD(uimm, rsc1, rsc2)) = {
  let imm : bits(12) = EXTZ(uimm @ 0b000) in
  let rs1 = creg2reg_bits(rsc1) in
  let rs2 = creg2reg_bits(rsc2) in
  execute(STORE(imm, rs2, rs1, DOUBLE, false, false))
}

/* ****************************************************************** */

union clause ast = C_ADDI : (bits(6), regbits)

function clause decodeCompressed (0b000 @ nzi5 : bits(1) @ rsd : regbits @ nzi40 : bits(5) @ 0b01) : bits(16) = {
  let nzi = (nzi5 @ nzi40) : bits(6) in
  if (nzi == 0b000000) | (rsd == zreg) then None
  else Some(C_ADDI(nzi, rsd))
}

function clause execute (C_ADDI(nzi, rsd)) = {
  let imm : bits(12) = EXTS(nzi) in
  execute(ITYPE(imm, rsd, rsd, RISCV_ADDI))
}

/* ****************************************************************** */

union clause ast = C_JAL : (bits(11))
union clause ast = C_ADDIW : (bits(6), regbits)

/* FIXME: decoding differs for RVC32/RVC64.  Below, we are assuming
 * RV64, and C_JAL is RV32 only. */

function clause decodeCompressed (0b001 @ imm5 : bits(1) @ rsd : regbits @ imm40 : bits(5) @ 0b01) =
  Some (C_ADDIW((imm5 @ imm40), rsd))

function clause execute (C_JAL(imm)) = {
  execute(RISCV_JAL(EXTS(imm @ 0b0), ra))
}

function clause execute (C_ADDIW(imm, rsd)) = {
  let imm : bits(32) = EXTS(imm) in
  let rs_val = rGPR(rsd) in
  let res : bits(32) = rs_val[31..0] + imm in
  wGPR(rsd, EXTS(res))
}

/* ****************************************************************** */

union clause ast = C_LI : (bits(6), regbits)

function clause decodeCompressed (0b010 @ imm5 : bits(1) @ rd : regbits @ imm40 : bits(5) @ 0b01) = {
  if (rd == zreg) then None
  else Some(C_LI(imm5 @ imm40, rd))
}

function clause execute (C_LI(imm, rd)) = {
  let imm : bits(12) = EXTS(imm) in
  execute(ITYPE(imm, zreg, rd, RISCV_ADDI))
}

/* ****************************************************************** */

union clause ast = C_ADDI16SP : (bits(6))

function clause decodeCompressed (0b011 @ nzi9 : bits(1) @ /* x2 */ 0b00010 @ nzi4 : bits(1) @ nzi6 : bits(1) @ nzi87 : bits(2) @ nzi5 : bits(1) @ 0b01) = {
  let nzimm = nzi9 @ nzi87 @ nzi6 @ nzi5 @ nzi4 in
  if (nzimm == 0b000000) then None
  else Some(C_ADDI16SP(nzimm))
}

function clause execute (C_ADDI16SP(imm)) = {
  let imm : bits(12) = EXTS(imm @ 0x0) in
  execute(ITYPE(imm, sp, sp, RISCV_ADDI))
}

/* ****************************************************************** */

union clause ast = C_LUI : (bits(6), regbits)

function clause decodeCompressed (0b011 @ imm17 : bits(1) @ rd : regbits @ imm1612 : bits(5) @ 0b01) = {
  if (rd == zreg) | (rd == sp) then None
  else Some(C_LUI(imm17 @ imm1612, rd))
}

function clause execute (C_LUI(imm, rd)) = {
  let res : bits(20) = EXTS(imm) in
  execute(UTYPE(res, rd, RISCV_LUI))
}

/* ****************************************************************** */

union clause ast = C_SRLI : (bits(6), cregbits)

function clause decodeCompressed (0b100 @ nzui5 : bits(1) @ 0b00 @ rsd : cregbits @ nzui40 : bits(5) @ 0b01) = {
  let shamt : bits(6) = nzui5 @ nzui40 in
  if shamt == 0b000000 /* TODO: On RV32, also need shamt[5] == 0 */
  then None
  else Some(C_SRLI(shamt, rsd))
}

function clause execute (C_SRLI(shamt, rsd)) = {
  let rsd = creg2reg_bits(rsd)  in
  execute(SHIFTIOP(shamt, rsd, rsd, RISCV_SRLI))
}

/* ****************************************************************** */

union clause ast = C_SRAI : (bits(6), cregbits)

function clause decodeCompressed (0b100 @ nzui5 : bits(1) @ 0b01 @ rsd : cregbits @ nzui40 : bits(5) @ 0b01) = {
  let shamt : bits(6) = nzui5 @ nzui40 in
  if shamt == 0b000000 /* TODO: On RV32, also need shamt[5] == 0 */
  then None
  else Some(C_SRAI(shamt, rsd))
}

function clause execute (C_SRAI(shamt, rsd)) = {
  let rsd = creg2reg_bits(rsd)  in
  execute(SHIFTIOP(shamt, rsd, rsd, RISCV_SRAI))
}

/* ****************************************************************** */

union clause ast = C_ANDI : (bits(6), cregbits)

function clause decodeCompressed (0b100 @ i5 : bits(1) @ 0b10 @ rsd : cregbits @ i40 : bits(5) @ 0b01) = Some(C_ANDI(i5 @ i40, rsd))

function clause execute (C_ANDI(imm, rsd)) = {
  let rsd = creg2reg_bits(rsd) in
  execute(ITYPE(EXTS(imm), rsd, rsd, RISCV_ANDI))
}

/* ****************************************************************** */

union clause ast = C_SUB : (cregbits, cregbits)

function clause decodeCompressed (0b100 @ 0b0 @ 0b11 @ rsd : cregbits @ 0b00 @ rs2 : cregbits @ 0b01) = Some(C_SUB(rsd, rs2))

function clause execute (C_SUB(rsd, rs2)) = {
  let rsd = creg2reg_bits(rsd) in
  let rs2 = creg2reg_bits(rs2) in
  execute(RTYPE(rs2, rsd, rsd, RISCV_SUB))
}

/* ****************************************************************** */

union clause ast = C_XOR : (cregbits, cregbits)

function clause decodeCompressed (0b100 @ 0b0 @ 0b11 @ rsd : cregbits @ 0b01 @ rs2 : cregbits @ 0b01) = Some(C_XOR(rsd, rs2))

function clause execute (C_SUB(rsd, rs2)) = {
  let rsd = creg2reg_bits(rsd) in
  let rs2 = creg2reg_bits(rs2) in
  execute(RTYPE(rs2, rsd, rsd, RISCV_XOR))
}

/* ****************************************************************** */

union clause ast = C_OR : (cregbits, cregbits)

function clause decodeCompressed (0b100 @ 0b0 @ 0b11 @ rsd : cregbits @ 0b10 @ rs2 : cregbits @ 0b01) = Some(C_OR(rsd, rs2))

function clause execute (C_OR(rsd, rs2)) = {
  let rsd = creg2reg_bits(rsd) in
  let rs2 = creg2reg_bits(rs2) in
  execute(RTYPE(rs2, rsd, rsd, RISCV_OR))
}

/* ****************************************************************** */

union clause ast = C_AND : (cregbits, cregbits)

function clause decodeCompressed (0b100 @ 0b0 @ 0b11 @ rsd : cregbits @ 0b11 @ rs2 : cregbits @ 0b01) = Some(C_AND(rsd, rs2))

function clause execute (C_OR(rsd, rs2)) = {
  let rsd = creg2reg_bits(rsd) in
  let rs2 = creg2reg_bits(rs2) in
  execute(RTYPE(rs2, rsd, rsd, RISCV_OR))
}

/* ****************************************************************** */

union clause ast = C_SUBW : (cregbits, cregbits)

/* TODO: invalid on RV32 */
function clause decodeCompressed (0b100 @ 0b1 @ 0b11 @ rsd : cregbits @ 0b00 @ rs2 : cregbits @ 0b01) = Some(C_SUBW(rsd, rs2))

function clause execute (C_SUBW(rsd, rs2)) = {
  let rsd = creg2reg_bits(rsd) in
  let rs2 = creg2reg_bits(rs2) in
  execute(RTYPE(rs2, rsd, rsd, RISCV_SUB))
}

/* ****************************************************************** */

union clause ast = C_ADDW : (cregbits, cregbits)

/* TODO: invalid on RV32 */
function clause decodeCompressed (0b100 @ 0b1 @ 0b11 @ rsd : cregbits @ 0b01 @ rs2 : cregbits @ 0b01) = Some(C_ADDW(rsd, rs2))

function clause execute (C_ADDW(rsd, rs2)) = {
  let rsd = creg2reg_bits(rsd) in
  let rs2 = creg2reg_bits(rs2) in
  execute(RTYPE(rs2, rsd, rsd, RISCV_ADD))
}

/* ****************************************************************** */

union clause ast = C_J : (bits(11))

function clause decodeCompressed (0b101 @ i11 : bits(1) @ i4 : bits(1) @ i98 : bits(2) @ i10 : bits(1) @ i6 : bits(1) @ i7 : bits(1) @ i31 : bits(3) @ i5 : bits(1) @ 0b01) =
  Some(C_J(i11 @ i10 @ i98 @ i7 @ i6 @ i5 @ i4 @ i31))

function clause execute (C_J(imm)) =
  execute(RISCV_JAL(EXTS(imm @ 0b0), zreg))

/* ****************************************************************** */

union clause ast = C_BEQZ : (bits(8), cregbits)

function clause decodeCompressed (0b110 @ i8 : bits(1) @ i43 : bits(2) @ rs : cregbits @ i76 : bits(2) @ i21 : bits(2) @ i5 : bits(1) @ 0b01) =
  Some(C_BEQZ(i8 @ i76 @ i5 @ i43 @ i21, rs))

function clause execute (C_BEQZ(imm, rs)) =
  execute(BTYPE(EXTS(imm @ 0b0), zreg, creg2reg_bits(rs), RISCV_BEQ))

/* ****************************************************************** */

union clause ast = C_BNEZ : (bits(8), cregbits)

function clause decodeCompressed (0b111 @ i8 : bits(1) @ i43 : bits(2) @ rs : cregbits @ i76 : bits(2) @ i21 : bits(2) @ i5 : bits(1) @ 0b01) =
  Some(C_BNEZ(i8 @ i76 @ i5 @ i43 @ i21, rs))

function clause execute (C_BNEZ(imm, rs)) =
  execute(BTYPE(EXTS(imm @ 0b0), zreg, creg2reg_bits(rs), RISCV_BNE))

/* ****************************************************************** */

function clause decode _ = None
function clause decodeCompressed _ = None

end ast
end decode
end decodeCompressed
end execute
