/* ****************************************************************** */
union clause ast = UTYPE : (bits(20), regbits, uop)

mapping encdec_uop : uop <-> bits(7) = {
  RISCV_LUI   <-> 0b0110111,
  RISCV_AUIPC <-> 0b0010111
}

mapping clause encdec = UTYPE(imm, rd, op) <-> imm @ rd @ encdec_uop(op)

function clause execute UTYPE(imm, rd, op) = {
  let off : xlenbits = EXTS(imm @ 0x000);
  let ret : xlenbits = match op {
    RISCV_LUI   => off,
    RISCV_AUIPC => PC + off
  };
  X(rd) = ret;
  true
}

mapping utype_mnemonic : uop <-> string = {
  RISCV_LUI   <-> "lui",
  RISCV_AUIPC <-> "auipc"
}

mapping clause assembly = UTYPE(imm, rd, op)
                      <-> utype_mnemonic(op) ^ spc() ^ reg_name(rd) ^ sep() ^ hex_bits_20(imm)

/* ****************************************************************** */
union clause ast = RISCV_JAL : (bits(21), regbits)

mapping clause encdec = RISCV_JAL(imm_19 @ imm_7_0 @ imm_8 @ imm_18_13 @ imm_12_9 @ 0b0, rd)
                    <-> imm_19 : bits(1) @ imm_18_13 : bits(6) @ imm_12_9 : bits(4) @ imm_8 : bits(1) @ imm_7_0 : bits(8) @ rd @ 0b1101111

/*
ideally we want some syntax like

mapping clause encdec = RISCV_JAL(imm @ 0b0, rd) <-> imm[19] @ imm[9..0] @ imm[10] @ imm[18..11] @ rd @ 0b1101111

match bv {
  imm[19] @ imm[9..0] @ imm[10] @ imm[18..11] -> imm @ 0b0
}

but this is difficult
*/

function clause execute (RISCV_JAL(imm, rd)) = {
  let pc : xlenbits = PC;
  let newPC : xlenbits = pc + EXTS(imm);
  if newPC[1] & (~ (haveRVC())) then {
    handle_mem_exception(newPC, E_Fetch_Addr_Align);
    false
  } else {
    X(rd) = nextPC;  /* compatible with JAL and C.JAL */
    nextPC = newPC;
    true
  }
}
/* TODO: handle 2-byte-alignment in mappings */

mapping clause assembly = RISCV_JAL(imm, rd) <-> "jal" ^ spc() ^ reg_name(rd) ^ sep() ^ hex_bits_21(imm)

/* ****************************************************************** */
union clause ast = RISCV_JALR : (bits(12), regbits, regbits)

mapping clause encdec = RISCV_JALR(imm, rs1, rd) <-> imm @ rs1 @ 0b000 @ rd @ 0b1100111

mapping clause assembly = RISCV_JALR(imm, rs1, rd)
                      <-> "jalr" ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ hex_bits_12(imm)

/* see riscv_jalr_seq.sail or riscv_jalr_rmem.sail for the execute clause. */

/* ****************************************************************** */
union clause ast = BTYPE : (bits(13), regbits, regbits, bop)

mapping encdec_bop : bop <-> bits(3) = {
  RISCV_BEQ  <-> 0b000,
  RISCV_BNE  <-> 0b001,
  RISCV_BLT  <-> 0b100,
  RISCV_BGE  <-> 0b101,
  RISCV_BLTU <-> 0b110,
  RISCV_BGEU <-> 0b111
}

mapping clause encdec = BTYPE(imm7_6 @ imm5_0 @ imm7_5_0 @ imm5_4_1 @ 0b0, rs2, rs1, op)
                    <-> imm7_6 : bits(1) @ imm7_5_0 : bits(6) @ rs2 @ rs1 @ encdec_bop(op) @ imm5_4_1 : bits(4) @ imm5_0 : bits(1) @ 0b1100011

function clause execute (BTYPE(imm, rs2, rs1, op)) = {
  let rs1_val = X(rs1);
  let rs2_val = X(rs2);
  let taken : bool = match op {
    RISCV_BEQ  => rs1_val == rs2_val,
    RISCV_BNE  => rs1_val != rs2_val,
    RISCV_BLT  => rs1_val <_s rs2_val,
    RISCV_BGE  => rs1_val >=_s rs2_val,
    RISCV_BLTU => rs1_val <_u rs2_val,
    RISCV_BGEU => rs1_val >=_u rs2_val
  };
  let newPC = PC + EXTS(imm);
  if taken then {
    if newPC[1] & (~ (haveRVC())) then {
      handle_mem_exception(newPC, E_Fetch_Addr_Align);
      false;
    } else {
      nextPC = newPC;
      true
    }
  } else true
}

mapping btype_mnemonic : bop <-> string = {
  RISCV_BEQ  <-> "beq",
  RISCV_BNE  <-> "bne",
  RISCV_BLT  <-> "blt",
  RISCV_BGE  <-> "bge",
  RISCV_BLTU <-> "bltu",
  RISCV_BGEU <-> "bgeu"
}

mapping clause assembly = BTYPE(imm, rs2, rs1, op)
                      <-> btype_mnemonic(op) ^ spc() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2) ^ sep() ^ hex_bits_13(imm)

/* ****************************************************************** */
union clause ast = ITYPE : (bits(12), regbits, regbits, iop)

mapping encdec_iop : iop <-> bits(3) = {
  RISCV_ADDI  <-> 0b000,
  RISCV_SLTI  <-> 0b010,
  RISCV_SLTIU <-> 0b011,
  RISCV_XORI  <-> 0b100,
  RISCV_ORI   <-> 0b110,
  RISCV_ANDI  <-> 0b111
}

mapping clause encdec = ITYPE(imm, rs1, rd, op) <-> imm @ rs1 @ encdec_iop(op) @ rd @ 0b0010011

function clause execute (ITYPE (imm, rs1, rd, op)) = {
  let rs1_val = X(rs1);
  let immext : xlenbits = EXTS(imm);
  let result : xlenbits = match op {
    RISCV_ADDI  => rs1_val + immext,
    RISCV_SLTI  => EXTZ(rs1_val <_s immext),
    RISCV_SLTIU => EXTZ(rs1_val <_u immext),
    RISCV_XORI  => rs1_val ^ immext,
    RISCV_ORI   => rs1_val | immext,
    RISCV_ANDI  => rs1_val & immext
  };
  X(rd) = result;
  true
}

mapping itype_mnemonic : iop <-> string = {
  RISCV_ADDI  <-> "addi",
  RISCV_SLTI  <-> "slti",
  RISCV_SLTIU <-> "sltiu",
  RISCV_XORI  <-> "xori",
  RISCV_ORI   <-> "ori",
  RISCV_ANDI  <-> "andi"
}

mapping clause assembly = ITYPE(imm, rs1, rd, op)
                      <-> itype_mnemonic(op) ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ hex_bits_12(imm)

/* ****************************************************************** */
union clause ast = SHIFTIOP : (bits(6), regbits, regbits, sop)

mapping encdec_sop : sop <-> bits(3) = {
  RISCV_SLLI <-> 0b001,
  RISCV_SRLI <-> 0b101,
  RISCV_SRAI <-> 0b101
}

mapping clause encdec = SHIFTIOP(shamt, rs1, rd, RISCV_SLLI) <-> 0b000000 @ shamt @ rs1 @ 0b001 @ rd @ 0b0010011
mapping clause encdec = SHIFTIOP(shamt, rs1, rd, RISCV_SRLI) <-> 0b000000 @ shamt @ rs1 @ 0b101 @ rd @ 0b0010011
mapping clause encdec = SHIFTIOP(shamt, rs1, rd, RISCV_SRAI) <-> 0b010000 @ shamt @ rs1 @ 0b101 @ rd @ 0b0010011

function clause execute (SHIFTIOP(shamt, rs1, rd, op)) = {
  let rs1_val = X(rs1);
  let result : xlenbits = match op {
    RISCV_SLLI => rs1_val << shamt,
    RISCV_SRLI => rs1_val >> shamt,
    RISCV_SRAI => shift_right_arith64(rs1_val, shamt)
  };
  X(rd) = result;
  true
}

mapping shiftiop_mnemonic : sop <-> string = {
  RISCV_SLLI <-> "slli",
  RISCV_SRLI <-> "srli",
  RISCV_SRAI <-> "srai"
}

mapping clause assembly = SHIFTIOP(shamt, rs1, rd, op)
                      <-> shiftiop_mnemonic(op) ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ hex_bits_6(shamt)

/* ****************************************************************** */
union clause ast = RTYPE : (regbits, regbits, regbits, rop)

mapping clause encdec = RTYPE(rs2, rs1, rd, RISCV_ADD)  <-> 0b0000000 @ rs2 @ rs1 @ 0b000 @ rd @ 0b0110011
mapping clause encdec = RTYPE(rs2, rs1, rd, RISCV_SUB)  <-> 0b0100000 @ rs2 @ rs1 @ 0b000 @ rd @ 0b0110011
mapping clause encdec = RTYPE(rs2, rs1, rd, RISCV_SLL)  <-> 0b0000000 @ rs2 @ rs1 @ 0b001 @ rd @ 0b0110011
mapping clause encdec = RTYPE(rs2, rs1, rd, RISCV_SLT)  <-> 0b0000000 @ rs2 @ rs1 @ 0b010 @ rd @ 0b0110011
mapping clause encdec = RTYPE(rs2, rs1, rd, RISCV_SLTU) <-> 0b0000000 @ rs2 @ rs1 @ 0b011 @ rd @ 0b0110011
mapping clause encdec = RTYPE(rs2, rs1, rd, RISCV_XOR)  <-> 0b0000000 @ rs2 @ rs1 @ 0b100 @ rd @ 0b0110011
mapping clause encdec = RTYPE(rs2, rs1, rd, RISCV_SRL)  <-> 0b0000000 @ rs2 @ rs1 @ 0b101 @ rd @ 0b0110011
mapping clause encdec = RTYPE(rs2, rs1, rd, RISCV_SRA)  <-> 0b0100000 @ rs2 @ rs1 @ 0b101 @ rd @ 0b0110011
mapping clause encdec = RTYPE(rs2, rs1, rd, RISCV_OR)   <-> 0b0000000 @ rs2 @ rs1 @ 0b110 @ rd @ 0b0110011
mapping clause encdec = RTYPE(rs2, rs1, rd, RISCV_AND)  <-> 0b0000000 @ rs2 @ rs1 @ 0b111 @ rd @ 0b0110011

function clause execute (RTYPE(rs2, rs1, rd, op)) = {
  let rs1_val = X(rs1);
  let rs2_val = X(rs2);
  let result : xlenbits = match op {
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
  };
  X(rd) = result;
  true
}

mapping rtype_mnemonic : rop <-> string = {
  RISCV_ADD  <-> "add",
  RISCV_SUB  <-> "sub",
  RISCV_SLL  <-> "sll",
  RISCV_SLT  <-> "slt",
  RISCV_SLTU <-> "sltu",
  RISCV_XOR  <-> "xor",
  RISCV_SRL  <-> "srl",
  RISCV_SRA  <-> "sra",
  RISCV_OR   <-> "or",
  RISCV_AND  <-> "and"
}

mapping clause assembly = RTYPE(rs2, rs1, rd, op)
                      <-> rtype_mnemonic(op) ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2)

/* ****************************************************************** */
union clause ast = LOAD : (bits(12), regbits, regbits, bool, word_width, bool, bool)

/* Load unsigned double is only present in RV128I, not RV64I */
/* TODO: aq/rl */
mapping clause encdec = LOAD(imm, rs1, rd, is_unsigned, size, false, false) if size_bits(size) != 0b11 | not_bool(is_unsigned)
                    <-> imm @ rs1 @ bool_bits(is_unsigned) @ size_bits(size) @ rd @ 0b0000011 if size_bits(size) != 0b11 | not_bool(is_unsigned)

val extend_value : forall 'n, 0 < 'n <= 8. (bool, MemoryOpResult(bits(8 * 'n))) -> MemoryOpResult(xlenbits)
function extend_value(is_unsigned, value) = match (value) {
  MemValue(v)     => MemValue(if is_unsigned then EXTZ(v) else EXTS(v) : xlenbits),
  MemException(e) => MemException(e)
}

val process_load : forall 'n, 0 < 'n <= 8. (regbits, xlenbits, MemoryOpResult(bits(8 * 'n)), bool) -> bool effect {escape, rreg, wreg}
function process_load(rd, addr, value, is_unsigned) =
  match extend_value(is_unsigned, value) {
    MemValue(result) => { X(rd) = result; true },
    MemException(e)  => { handle_mem_exception(addr, e); false }
  }

function check_misaligned(vaddr : xlenbits, width : word_width) -> bool =
  if   plat_enable_misaligned_access() then false
  else match width {
         BYTE   => false,
         HALF   => vaddr[0] == true,
         WORD   => vaddr[0] == true | vaddr[1] == true,
         DOUBLE => vaddr[0] == true | vaddr[1] == true | vaddr[2] == true
       }

function clause execute(LOAD(imm, rs1, rd, is_unsigned, width, aq, rl)) =
  let vaddr : xlenbits = X(rs1) + EXTS(imm) in
  if   check_misaligned(vaddr, width)
  then { handle_mem_exception(vaddr, E_Load_Addr_Align); false }
  else match translateAddr(vaddr, Read, Data) {
    TR_Failure(e) => { handle_mem_exception(vaddr, e); false },
    TR_Address(addr) =>
      match width {
        BYTE   => process_load(rd, vaddr, mem_read(addr, 1, aq, rl, false), is_unsigned),
        HALF   => process_load(rd, vaddr, mem_read(addr, 2, aq, rl, false), is_unsigned),
        WORD   => process_load(rd, vaddr, mem_read(addr, 4, aq, rl, false), is_unsigned),
        DOUBLE => process_load(rd, vaddr, mem_read(addr, 8, aq, rl, false), is_unsigned)
      }
  }

/* TODO FIXME: is this the actual aq/rl syntax? */
val maybe_aq : bool <-> string
mapping maybe_aq = {
  true  <-> ".aq",
  false <-> ""
}

val maybe_rl : bool <-> string
mapping maybe_rl = {
  true  <-> ".rl",
  false <-> ""
}

val maybe_u : bool <-> string
mapping maybe_u = {
  true  <-> "u",
  false <-> ""
}


mapping clause assembly = LOAD(imm, rs1, rd, is_unsigned, size, aq, rl)
                      <-> "l" ^ size_mnemonic(size) ^ maybe_u(is_unsigned) ^ maybe_aq(aq) ^ maybe_rl(rl) ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ hex_bits_12(imm)

/* ****************************************************************** */
union clause ast = STORE : (bits(12), regbits, regbits, word_width, bool, bool)

/* TODO: aq/rl */
mapping clause encdec = STORE(imm7 @ imm5, rs2, rs1, size, false, false)
                    <-> imm7 : bits(7) @ rs2 @ rs1 @ 0b0 @ size_bits(size) @ imm5 : bits(5) @ 0b0100011

/* NOTE: Currently, we only EA if address translation is successful.
   This may need revisiting. */
function clause execute (STORE(imm, rs2, rs1, width, aq, rl)) =
  let vaddr : xlenbits = X(rs1) + EXTS(imm) in
  if   check_misaligned(vaddr, width)
  then { handle_mem_exception(vaddr, E_SAMO_Addr_Align); false }
  else match translateAddr(vaddr, Write, Data) {
    TR_Failure(e) => { handle_mem_exception(vaddr, e); false },
    TR_Address(addr) => {
      let eares : MemoryOpResult(unit) = match width {
        BYTE   => mem_write_ea(addr, 1, aq, rl, false),
        HALF   => mem_write_ea(addr, 2, aq, rl, false),
        WORD   => mem_write_ea(addr, 4, aq, rl, false),
        DOUBLE => mem_write_ea(addr, 8, aq, rl, false)
      };
      match (eares) {
        MemException(e) => { handle_mem_exception(addr, e); false },
        MemValue(_) => {
          let rs2_val = X(rs2);
          let res : MemoryOpResult(bool) = match width {
            BYTE   => mem_write_value(addr, 1, rs2_val[7..0],  aq, rl, false),
            HALF   => mem_write_value(addr, 2, rs2_val[15..0], aq, rl, false),
            WORD   => mem_write_value(addr, 4, rs2_val[31..0], aq, rl, false),
            DOUBLE => mem_write_value(addr, 8, rs2_val,        aq, rl, false)
          };
          match (res) {
            MemValue(true)     => true,
            MemValue(false)    => internal_error("store got false from mem_write_value"),
            MemException(e) => { handle_mem_exception(addr, e); false }
          }
        }
      }
    }
  }

mapping clause assembly = STORE(imm, rs1, rd, size, aq, rl)
                      <-> "s" ^ size_mnemonic(size) ^ maybe_aq(aq) ^ maybe_rl(rl) ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ hex_bits_12(imm)


/* ****************************************************************** */
union clause ast = ADDIW : (bits(12), regbits, regbits)

mapping clause encdec = ADDIW(imm, rs1, rd) <-> imm @ rs1 @ 0b000 @ rd @ 0b0011011

function clause execute (ADDIW(imm, rs1, rd)) = {
  let result : xlenbits = EXTS(imm) + X(rs1);
  X(rd) = EXTS(result[31..0]);
  true
}


mapping clause assembly = ADDIW(imm, rs1, rd) <-> "addiw" ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ hex_bits_12(imm)

/* ****************************************************************** */
union clause ast = SHIFTW : (bits(5), regbits, regbits, sop)

mapping clause encdec = SHIFTW(shamt, rs1, rd, RISCV_SLLI) <-> 0b0000000 @ shamt @ rs1 @ 0b001 @ rd @ 0b0011011
mapping clause encdec = SHIFTW(shamt, rs1, rd, RISCV_SRLI) <-> 0b0000000 @ shamt @ rs1 @ 0b101 @ rd @ 0b0011011
mapping clause encdec = SHIFTW(shamt, rs1, rd, RISCV_SRAI) <-> 0b0100000 @ shamt @ rs1 @ 0b101 @ rd @ 0b0011011

function clause execute (SHIFTW(shamt, rs1, rd, op)) = {
  let rs1_val = (X(rs1))[31..0];
  let result : bits(32) = match op {
    RISCV_SLLI => rs1_val << shamt,
    RISCV_SRLI => rs1_val >> shamt,
    RISCV_SRAI => shift_right_arith32(rs1_val, shamt)
  };
  X(rd) = EXTS(result);
  true
}

mapping shiftw_mnemonic : sop <-> string = {
  RISCV_SLLI <-> "slli",
  RISCV_SRLI <-> "srli",
  RISCV_SRAI <-> "srai"
}

mapping clause assembly = SHIFTW(shamt, rs1, rd, op)
                      <-> shiftw_mnemonic(op) ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ hex_bits_5(shamt)

/* ****************************************************************** */
union clause ast = RTYPEW : (regbits, regbits, regbits, ropw)

mapping clause encdec = RTYPEW(rs2, rs1, rd, RISCV_ADDW) <-> 0b0000000 @ rs2 @ rs1 @ 0b000 @ rd @ 0b0111011
mapping clause encdec = RTYPEW(rs2, rs1, rd, RISCV_SUBW) <-> 0b0100000 @ rs2 @ rs1 @ 0b000 @ rd @ 0b0111011
mapping clause encdec = RTYPEW(rs2, rs1, rd, RISCV_SLLW) <-> 0b0000000 @ rs2 @ rs1 @ 0b001 @ rd @ 0b0111011
mapping clause encdec = RTYPEW(rs2, rs1, rd, RISCV_SRLW) <-> 0b0000000 @ rs2 @ rs1 @ 0b101 @ rd @ 0b0111011
mapping clause encdec = RTYPEW(rs2, rs1, rd, RISCV_SRAW) <-> 0b0100000 @ rs2 @ rs1 @ 0b101 @ rd @ 0b0111011

function clause execute (RTYPEW(rs2, rs1, rd, op)) = {
  let rs1_val = (X(rs1))[31..0];
  let rs2_val = (X(rs2))[31..0];
  let result : bits(32) = match op {
    RISCV_ADDW => rs1_val + rs2_val,
    RISCV_SUBW => rs1_val - rs2_val,
    RISCV_SLLW => rs1_val << (rs2_val[4..0]),
    RISCV_SRLW => rs1_val >> (rs2_val[4..0]),
    RISCV_SRAW => shift_right_arith32(rs1_val, rs2_val[4..0])
  };
  X(rd) = EXTS(result);
  true
}

mapping rtypew_mnemonic : ropw <-> string = {
  RISCV_ADDW <-> "addw",
  RISCV_SUBW <-> "subw",
  RISCV_SLLW <-> "sllw",
  RISCV_SRLW <-> "srlw",
  RISCV_SRAW <-> "sraw"
}

mapping clause assembly = RTYPEW(rs2, rs1, rd, op)
                      <-> rtypew_mnemonic(op) ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2)

/* ****************************************************************** */
union clause ast = SHIFTIWOP : (bits(5), regbits, regbits, sopw)

mapping clause encdec = SHIFTIWOP(shamt, rs1, rd, RISCV_SLLIW) <-> 0b0000000 @ shamt @ rs1 @ 0b001 @ rd @ 0b0011011
mapping clause encdec = SHIFTIWOP(shamt, rs1, rd, RISCV_SRLIW) <-> 0b0000000 @ shamt @ rs1 @ 0b101 @ rd @ 0b0011011
mapping clause encdec = SHIFTIWOP(shamt, rs1, rd, RISCV_SRAIW) <-> 0b0100000 @ shamt @ rs1 @ 0b101 @ rd @ 0b0011011

function clause execute (SHIFTIWOP(shamt, rs1, rd, op)) = {
  let rs1_val = X(rs1);
  let result : xlenbits = match op {
    RISCV_SLLIW => EXTS(rs1_val[31..0] << shamt),
    RISCV_SRLIW => EXTS(rs1_val[31..0] >> shamt),
    RISCV_SRAIW => EXTS(shift_right_arith32(rs1_val[31..0], shamt))
  };
  X(rd) = result;
  true
}

mapping shiftiwop_mnemonic : sopw <-> string = {
  RISCV_SLLIW <-> "slliw",
  RISCV_SRLIW <-> "srliw",
  RISCV_SRAIW <-> "sraiw"
}

mapping clause assembly = SHIFTIWOP(shamt, rs1, rd, op)
                      <-> shiftiwop_mnemonic(op) ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ hex_bits_5(shamt)

/* ****************************************************************** */
/* FIXME: separate these out into separate ast variants */
union clause ast = MUL : (regbits, regbits, regbits, bool, bool, bool)

mapping encdec_mul_op : (bool, bool, bool) <-> bits(3) = {
  (false, true, true)  <-> 0b000,
  (true, true, true)   <-> 0b001,
  (true, true, false)  <-> 0b010,
  (true, false, false) <-> 0b011
}

/* for some reason the : bits(3) here is still necessary - BUG */
mapping clause encdec = MUL(rs2, rs1, rd, high, signed1, signed2)
                    <-> 0b0000001 @ rs2 @ rs1 @ encdec_mul_op(high, signed1, signed2) : bits(3) @ rd @ 0b0110011

function clause execute (MUL(rs2, rs1, rd, high, signed1, signed2)) = {
  let rs1_val = X(rs1);
  let rs2_val = X(rs2);
  let rs1_int : int = if signed1 then signed(rs1_val) else unsigned(rs1_val);
  let rs2_int : int = if signed2 then signed(rs2_val) else unsigned(rs2_val);
  let result128 = to_bits(128, rs1_int * rs2_int);
  let result = if high then result128[127..64] else result128[63..0];
  X(rd) = result;
  true
}

mapping mul_mnemonic : (bool, bool, bool) <-> string = {
  (false, true, true)  <-> "mul",
  (true, true, true)   <-> "mulh",
  (true, true, false)  <-> "mulhsu",
  (true, false, false) <-> "mulhu"
}

mapping clause assembly = MUL(rs2, rs1, rd, high, signed1, signed2) <-> mul_mnemonic(high, signed1, signed2) ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2)

/* ****************************************************************** */
union clause ast = DIV : (regbits, regbits, regbits, bool)

mapping clause encdec = DIV(rs2, rs1, rd, s) <-> 0b0000001 @ rs2 @ rs1 @ 0b10 @ bool_not_bits(s) @ rd @ 0b0110011

function clause execute (DIV(rs2, rs1, rd, s)) = {
  let rs1_val = X(rs1);
  let rs2_val = X(rs2);
  let rs1_int : int = if s then signed(rs1_val) else unsigned(rs1_val);
  let rs2_int : int = if s then signed(rs2_val) else unsigned(rs2_val);
  let q : int = if rs2_int == 0 then -1 else quot_round_zero(rs1_int, rs2_int);
  let q': int = if s & q > xlen_max_signed then xlen_min_signed else q; /* check for signed overflow */
  X(rd) = to_bits(xlen, q');
  true
}

mapping maybe_not_u : bool <-> string = {
  false <-> "u",
  true  <-> ""
}

mapping clause assembly = DIV(rs2, rs1, rd, s)
                      <-> "div" ^ maybe_not_u(s) ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2)

/* ****************************************************************** */
union clause ast = REM : (regbits, regbits, regbits, bool)

mapping clause encdec = REM(rs2, rs1, rd, s) <-> 0b0000001 @ rs2 @ rs1 @ 0b11 @ bool_not_bits(s) @ rd @ 0b0110011

function clause execute (REM(rs2, rs1, rd, s)) = {
  let rs1_val = X(rs1);
  let rs2_val = X(rs2);
  let rs1_int : int = if s then signed(rs1_val) else unsigned(rs1_val);
  let rs2_int : int = if s then signed(rs2_val) else unsigned(rs2_val);
  let r : int = if rs2_int == 0 then rs1_int else rem_round_zero(rs1_int, rs2_int);
  /* signed overflow case returns zero naturally as required due to -1 divisor */
  X(rd) = to_bits(xlen, r);
  true
}

mapping clause assembly = REM(rs2, rs1, rd, s) <-> "rem" ^ maybe_not_u(s) ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2)

/* ****************************************************************** */
union clause ast = MULW : (regbits, regbits, regbits)

mapping clause encdec = MULW(rs2, rs1, rd) <-> 0b0000001 @ rs2 @ rs1 @ 0b000 @ rd @ 0b0111011

function clause execute (MULW(rs2, rs1, rd)) = {
  let rs1_val = X(rs1)[31..0];
  let rs2_val = X(rs2)[31..0];
  let rs1_int : int = signed(rs1_val);
  let rs2_int : int = signed(rs2_val);
  let result32 = to_bits(64, rs1_int * rs2_int)[31..0]; /* XXX surprising behaviour of to_bits requires expansion to 64 bits followed by truncation... */
  let result : xlenbits = EXTS(result32);
  X(rd) = result;
  true
}

mapping clause assembly = MULW(rs2, rs1, rd)
                      <-> "mulw" ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2)

/* ****************************************************************** */
union clause ast = DIVW : (regbits, regbits, regbits, bool)

mapping clause encdec = DIVW(rs2, rs1, rd, s) <-> 0b0000001 @ rs2 @ rs1 @ 0b10 @ bool_not_bits(s) @ rd @ 0b0111011

function clause execute (DIVW(rs2, rs1, rd, s)) = {
  let rs1_val = X(rs1)[31..0];
  let rs2_val = X(rs2)[31..0];
  let rs1_int : int = if s then signed(rs1_val) else unsigned(rs1_val);
  let rs2_int : int = if s then signed(rs2_val) else unsigned(rs2_val);
  let q : int = if rs2_int == 0 then -1 else quot_round_zero(rs1_int, rs2_int);
  let q': int = if s & q > (2 ^ 31 - 1) then  (0 - 2^31) else q; /* check for signed overflow */
  X(rd) = EXTS(to_bits(32, q'));
  true
}

mapping clause assembly = DIVW(rs2, rs1, rd, s)
                      <-> "div" ^ maybe_not_u(s) ^ "w" ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2)

/* ****************************************************************** */
union clause ast = REMW : (regbits, regbits, regbits, bool)

mapping clause encdec = REMW(rs2, rs1, rd, s) <-> 0b0000001 @ rs2 @ rs1 @ 0b11 @ bool_not_bits(s) @ rd @ 0b0111011

function clause execute (REMW(rs2, rs1, rd, s)) = {
  let rs1_val = X(rs1)[31..0];
  let rs2_val = X(rs2)[31..0];
  let rs1_int : int = if s then signed(rs1_val) else unsigned(rs1_val);
  let rs2_int : int = if s then signed(rs2_val) else unsigned(rs2_val);
  let r : int = if rs2_int == 0 then rs1_int else rem_round_zero(rs1_int, rs2_int);
  /* signed overflow case returns zero naturally as required due to -1 divisor */
  X(rd) = EXTS(to_bits(32, r));
  true
}

mapping clause assembly = REMW(rs2, rs1, rd, s) <-> "rem" ^ maybe_not_u(s) ^ "w" ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2)

/* ****************************************************************** */
union clause ast = FENCE : (bits(4), bits(4))

mapping clause encdec = FENCE(pred, succ) <-> 0b0000 @ pred @ succ @ 0b00000 @ 0b000 @ 0b00000 @ 0b0001111

function clause execute (FENCE(pred, succ)) = {
  match (pred, succ) {
    (_ : bits(2) @ 0b11, _ : bits(2) @ 0b11) => MEM_fence_rw_rw(),
    (_ : bits(2) @ 0b10, _ : bits(2) @ 0b11) => MEM_fence_r_rw(),
    (_ : bits(2) @ 0b10, _ : bits(2) @ 0b10) => MEM_fence_r_r(),
    (_ : bits(2) @ 0b11, _ : bits(2) @ 0b01) => MEM_fence_rw_w(),
    (_ : bits(2) @ 0b01, _ : bits(2) @ 0b01) => MEM_fence_w_w(),
    (_ : bits(2) @ 0b01, _ : bits(2) @ 0b11) => MEM_fence_w_rw(),
    (_ : bits(2) @ 0b11, _ : bits(2) @ 0b10) => MEM_fence_rw_r(),
    (_ : bits(2) @ 0b10, _ : bits(2) @ 0b01) => MEM_fence_r_w(),
    (_ : bits(2) @ 0b01, _ : bits(2) @ 0b10) => MEM_fence_w_r(),

    (_ : bits(2) @ 0b00, _ : bits(2) @ 0b00) => (),

    _ => { print("FIXME: unsupported fence");
           () }
  };
  true
}

mapping bit_maybe_r : bits(1) <-> string = {
  0b1 <-> "r",
  0b0 <-> ""
}

mapping bit_maybe_w : bits(1) <-> string = {
  0b1 <-> "w",
  0b0 <-> ""
}

mapping bit_maybe_i : bits(1) <-> string = {
  0b1 <-> "i",
  0b0 <-> ""
}

mapping bit_maybe_o : bits(1) <-> string = {
  0b1 <-> "o",
  0b0 <-> ""
}

mapping fence_bits : bits(4) <-> string = {
  i : bits(1) @ o : bits(1) @ r : bits(1) @ w : bits(1) <-> bit_maybe_i(i) ^ bit_maybe_o(o) ^ bit_maybe_r(r) ^ bit_maybe_w(w)
}

mapping clause assembly = FENCE(pred, succ) <-> "fence" ^ spc() ^ fence_bits(pred) ^ sep() ^ fence_bits(succ)

/* ****************************************************************** */
union clause ast = FENCEI : unit

mapping clause encdec = FENCEI() <-> 0b000000000000 @ 0b00000 @ 0b001 @ 0b00000 @ 0b0001111

/* fence.i is a nop for the memory model */
function clause execute FENCEI() = { /* MEM_fence_i(); */ true }


mapping clause assembly = FENCEI() <-> "fence.i"

/* ****************************************************************** */
union clause ast = ECALL : unit

mapping clause encdec = ECALL() <-> 0b000000000000 @ 0b00000 @ 0b000 @ 0b00000 @ 0b1110011

function clause execute ECALL() = {
  let t : sync_exception =
    struct { trap = match (cur_privilege) {
                      User       => E_U_EnvCall,
                      Supervisor => E_S_EnvCall,
                      Machine    => E_M_EnvCall
                    },
             excinfo = (None() : option(xlenbits)) };
  nextPC = handle_exception(cur_privilege, CTL_TRAP(t), PC);
  false
}

mapping clause assembly = ECALL() <-> "ecall"

/* ****************************************************************** */
union clause ast = MRET : unit

mapping clause encdec = MRET() <-> 0b0011000 @ 0b00010 @ 0b00000 @ 0b000 @ 0b00000 @ 0b1110011

function clause execute MRET() = {
  if   cur_privilege == Machine
  then nextPC = handle_exception(cur_privilege, CTL_MRET(), PC)
  else handle_illegal();
  false
}

mapping clause assembly = MRET() <-> "mret"

/* ****************************************************************** */
union clause ast = SRET : unit

mapping clause encdec = SRET() <-> 0b0001000 @ 0b00010 @ 0b00000 @ 0b000 @ 0b00000 @ 0b1110011

function clause execute SRET() = {
  match cur_privilege {
    User       => handle_illegal(),
    Supervisor => if   mstatus.TSR() == true
                  then handle_illegal()
                  else nextPC = handle_exception(cur_privilege, CTL_SRET(), PC),
    Machine    => nextPC = handle_exception(cur_privilege, CTL_SRET(), PC)
  };
  false
}

mapping clause assembly = SRET() <-> "sret"

/* ****************************************************************** */
union clause ast = EBREAK : unit

mapping clause encdec = EBREAK() <-> 0b000000000001 @ 0b00000 @ 0b000 @ 0b00000 @ 0b1110011

function clause execute EBREAK() = {
  handle_mem_exception(PC, E_Breakpoint);
  false
}

mapping clause assembly = EBREAK() <-> "ebreak"

/* ****************************************************************** */
union clause ast = WFI : unit

mapping clause encdec = WFI() <-> 0b000100000101 @ 0b00000 @ 0b000 @ 0b00000 @ 0b1110011

function clause execute WFI() =
  match cur_privilege {
    Machine    => { platform_wfi(); true },
    Supervisor => if   mstatus.TW() == true
                  then { handle_illegal(); false }
                  else { platform_wfi(); true },
    User       => { handle_illegal(); false }
  }

mapping clause assembly = WFI() <-> "wfi"

/* ****************************************************************** */
union clause ast = SFENCE_VMA : (regbits, regbits)

mapping clause encdec = SFENCE_VMA(rs1, rs2) <-> 0b0001001 @ rs2 @ rs1 @ 0b000 @ 0b00000 @ 0b1110011

function clause execute SFENCE_VMA(rs1, rs2) = {
  /* TODO: handle PMP/TLB synchronization when executed in M-mode. */
  if   cur_privilege == User
  then { handle_illegal(); false }
  else match (architecture(mstatus.SXL()), mstatus.TVM()) {
    (Some(RV64), true)  => { handle_illegal(); false },
    (Some(RV64), false) => {
      let addr : option(vaddr39) = if rs1 == 0 then None() else Some(X(rs1)[38 .. 0]);
      let asid : option(asid64)  = if rs2 == 0 then None() else Some(X(rs2)[15 .. 0]);
      flushTLB(asid, addr);
      true
    },
    (_, _) => internal_error("unimplemented sfence architecture")
  }
}

mapping clause assembly = SFENCE_VMA(rs1, rs2)
                      <-> "sfence.vma" ^ spc() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2)

/* ****************************************************************** */
// Some print utils for lr/sc.

function aqrl_str(aq : bool, rl : bool) -> string =
  match (aq, rl) {
    (false, false) => "",
    (false, true)  => ".rl",
    (true, false)  => ".aq",
    (true, true)   => ".aqrl"
  }

function lrsc_width_str(width : word_width) -> string =
  match (width) {
    BYTE   => ".b",
    HALF   => ".h",
    WORD   => ".w",
    DOUBLE => ".d"
  }

/* ****************************************************************** */
union clause ast = LOADRES : (bool, bool, regbits, word_width, regbits)

mapping clause encdec = LOADRES(aq, rl, rs1, size, rd) <-> 0b00010 @ bool_bits(aq) @ bool_bits(rl) @ 0b00000 @ rs1 @ 0b0 @ size_bits(size) @ rd @ 0b0101111

/* We could set load-reservations on physical or virtual addresses.
 * For now we set them on virtual addresses, since it makes the
 * sequential model of SC a bit simpler, at the cost of an explicit
 * call to load_reservation in LR and cancel_reservation in SC.
 */

val process_loadres : forall 'n, 0 < 'n <= 8. (regbits, xlenbits, MemoryOpResult(bits(8 * 'n)), bool) -> bool effect {escape, rreg, wreg}
function process_loadres(rd, addr, value, is_unsigned) =
  match extend_value(is_unsigned, value) {
    MemValue(result) => { load_reservation(addr); X(rd) = result; true },
    MemException(e)  => { handle_mem_exception(addr, e); false }
  }

function clause execute(LOADRES(aq, rl, rs1, width, rd)) =
  let vaddr : xlenbits = X(rs1) in
  let aligned : bool =
    /* BYTE and HALF would only occur due to invalid decodes, but it doesn't hurt
     * to treat them as valid here; otherwise we'd need to throw an internal_error.
     * May need to revisit for latex output.
     */
    match width {
      BYTE   => true,
      HALF   => vaddr[0]    == 0b0,
      WORD   => vaddr[1..0] == 0b00,
      DOUBLE => vaddr[2..0] == 0b000
    } in
    /* "LR faults like a normal load, even though it's in the AMO major opcode space."
       - Andrew Waterman, isa-dev, 10 Jul 2018.
     */
  if (~ (aligned))
  then { handle_mem_exception(vaddr, E_Load_Addr_Align); false }
  else match translateAddr(vaddr, Read, Data) {
         TR_Failure(e) => { handle_mem_exception(vaddr, e); false },
         TR_Address(addr) =>
           match width {
             WORD   => process_loadres(rd, vaddr, mem_read(addr, 4, aq, rl, true), false),
             DOUBLE => process_loadres(rd, vaddr, mem_read(addr, 8, aq, rl, true), false),
             _      => internal_error("LOADRES expected WORD or DOUBLE")
           }
       }

mapping clause assembly = LOADRES(aq, rl, rs1, size, rd)
                      <-> "lr." ^ size_mnemonic(size) ^ maybe_aq(aq) ^ maybe_rl(rl) ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1)

/* ****************************************************************** */
union clause ast = STORECON : (bool, bool, regbits, regbits, word_width, regbits)

mapping clause encdec = STORECON(aq, rl, rs2, rs1, size, rd)
                    <-> 0b00011 @ bool_bits(aq) @ bool_bits(rl) @ rs2 @ rs1 @ 0b0 @ size_bits(size) @ rd @ 0b0101111

/* NOTE: Currently, we only EA if address translation is successful.
   This may need revisiting. */
function clause execute (STORECON(aq, rl, rs2, rs1, width, rd)) = {
  /* RMEM FIXME:  This definition differs from the Sail1 version:
   * rs1 is read *before* speculate_conditional_success
   * (called via match_reservation), partly due to the current api of
   * match_reservation.  Reverting back to the weaker Sail1 version
   * will require changes to the API for the ghost reservation state.
   */
  vaddr : xlenbits = X(rs1);
  let aligned : bool =
    /* BYTE and HALF would only occur due to invalid decodes, but it doesn't hurt
     * to treat them as valid here; otherwise we'd need to throw an internal_error.
     * May need to revisit for latex output.
     */
    match width {
      BYTE   => true,
      HALF   => vaddr[0]    == 0b0,
      WORD   => vaddr[1..0] == 0b00,
      DOUBLE => vaddr[2..0] == 0b000
    } in
  if (~ (aligned))
  then { handle_mem_exception(vaddr, E_SAMO_Addr_Align); false }
  else {
    if   match_reservation(vaddr) == false
    then { X(rd) = EXTZ(0b1); true }
    else {
      match translateAddr(vaddr, Write, Data) {
        TR_Failure(e) => { handle_mem_exception(vaddr, e); false },
        TR_Address(addr) => {
          let eares : MemoryOpResult(unit) = match width {
            WORD   => mem_write_ea(addr, 4, aq, rl, true),
            DOUBLE => mem_write_ea(addr, 8, aq, rl, true),
            _      => internal_error("STORECON expected word or double")
          };
          match (eares) {
            MemException(e)  => { handle_mem_exception(addr, e); false },
            MemValue(_) => {
              rs2_val = X(rs2);
              let res : MemoryOpResult(bool) = match width {
                WORD   => mem_write_value(addr, 4, rs2_val[31..0], aq, rl, true),
                DOUBLE => mem_write_value(addr, 8, rs2_val,        aq, rl, true),
                _      => internal_error("STORECON expected word or double")
              };
              match (res) {
                MemValue(true)     => { X(rd) = EXTZ(0b0); cancel_reservation(); true },
                MemValue(false)    => { X(rd) = EXTZ(0b1); cancel_reservation(); true },
                MemException(e)    => { handle_mem_exception(addr, e); false }
              }
            }
          }
        }
      }
    }
  }
}

mapping clause assembly = STORECON(aq, rl, rs2, rs1, size, rd) <-> "sc." ^ size_mnemonic(size) ^ maybe_aq(aq) ^ maybe_rl(rl) ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2)

/* ****************************************************************** */
union clause ast = AMO : (amoop, bool, bool, regbits, regbits, word_width, regbits)

mapping encdec_amoop : amoop <-> bits(5) = {
  AMOSWAP <-> 0b00001,
  AMOADD  <-> 0b00000,
  AMOXOR  <-> 0b00100,
  AMOAND  <-> 0b01100,
  AMOOR   <-> 0b01000,
  AMOMIN  <-> 0b10000,
  AMOMAX  <-> 0b10100,
  AMOMINU <-> 0b11000,
  AMOMAXU <-> 0b11100
}

mapping clause encdec = AMO(op, aq, rl, rs2, rs1, size, rd) <-> encdec_amoop(op) @ bool_bits(aq) @ bool_bits(rl) @ rs2 @ rs1 @ 0b0 @ size_bits(size) @ rd @ 0b0101111

/* NOTE: Currently, we only EA if address translation is successful.
   This may need revisiting. */
function clause execute (AMO(op, aq, rl, rs2, rs1, width, rd)) = {
  vaddr : xlenbits = X(rs1);
  match translateAddr(vaddr, ReadWrite, Data) {
    TR_Failure(e) => { handle_mem_exception(vaddr, e); false },
    TR_Address(addr) => {
      let eares : MemoryOpResult(unit) = match width {
        WORD   => mem_write_ea(addr, 4, aq & rl, rl, true),
        DOUBLE => mem_write_ea(addr, 8, aq & rl, rl, true),
        _      => internal_error ("AMO expected WORD or DOUBLE")
      };
      match (eares) {
        MemException(e) => { handle_mem_exception(addr, e); false },
        MemValue(_) => {
          let rval : MemoryOpResult(xlenbits) = match width {
            WORD   => extend_value(false, mem_read(addr, 4, aq, aq & rl, true)),
            DOUBLE => extend_value(false, mem_read(addr, 8, aq, aq & rl, true)),
          _        => internal_error ("AMO expected WORD or DOUBLE")
          };
          match (rval) {
            MemException(e)  => { handle_mem_exception(addr, e); false },
            MemValue(loaded) => {
              rs2_val : xlenbits = X(rs2);
              result  : xlenbits =
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

              let wval : MemoryOpResult(bool) = match width {
                WORD   => mem_write_value(addr, 4, result[31..0], aq & rl, rl, true),
                DOUBLE => mem_write_value(addr, 8, result,        aq & rl, rl, true),
                _      => internal_error("AMO expected WORD or DOUBLE")
              };
              match (wval) {
                MemValue(true)  => { X(rd) = loaded; true },
                MemValue(false) => { internal_error("AMO got false from mem_write_value") },
                MemException(e) => { handle_mem_exception(addr, e); false }
              }
            }
          }
        }
      }
    }
  }
}


mapping amo_mnemonic : amoop <-> string = {
  AMOSWAP <-> "amoswap",
  AMOADD  <-> "amoadd",
  AMOXOR  <-> "amoxor",
  AMOAND  <-> "amoand",
  AMOOR   <-> "amoor",
  AMOMIN  <-> "amomin",
  AMOMAX  <-> "amomax",
  AMOMINU <-> "amominu",
  AMOMAXU <-> "amomaxu"
}

mapping clause assembly = AMO(op, aq, rl, rs2, rs1, width, rd)
                      <-> amo_mnemonic(op) ^ "." ^ size_mnemonic(width) ^ maybe_aq(aq) ^ maybe_rl(rl) ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2)

/* ****************************************************************** */
union clause ast = CSR  : (bits(12), regbits, regbits, bool, csrop)

mapping encdec_csrop : csrop <-> bits(2) = {
  CSRRW <-> 0b01,
  CSRRS <-> 0b10,
  CSRRC <-> 0b11
}

mapping clause encdec = CSR(csr, rs1, rd, is_imm, op) <-> csr @ rs1 @ bool_bits(is_imm) @ encdec_csrop(op) @ rd @ 0b1110011

function readCSR csr : csreg -> xlenbits =
  let res : xlenbits =
  match csr {
    /* machine mode */
    0xF11 => mvendorid,
    0xF12 => marchid,
    0xF13 => mimpid,
    0xF14 => mhartid,
    0x300 => mstatus.bits(),
    0x301 => misa.bits(),
    0x302 => medeleg.bits(),
    0x303 => mideleg.bits(),
    0x304 => mie.bits(),
    0x305 => mtvec.bits(),
    0x306 => EXTZ(mcounteren.bits()),
    0x340 => mscratch,
    0x341 => mepc & pc_alignment_mask(),
    0x342 => mcause.bits(),
    0x343 => mtval,
    0x344 => mip.bits(),

    0x3A0 => pmpcfg0,
    0x3B0 => pmpaddr0,

    /* supervisor mode */
    0x100 => lower_mstatus(mstatus).bits(),
    0x102 => sedeleg.bits(),
    0x103 => sideleg.bits(),
    0x104 => lower_mie(mie, mideleg).bits(),
    0x105 => stvec.bits(),
    0x106 => EXTZ(scounteren.bits()),
    0x140 => sscratch,
    0x141 => sepc & pc_alignment_mask(),
    0x142 => scause.bits(),
    0x143 => stval,
    0x144 => lower_mip(mip, mideleg).bits(),
    0x180 => satp,

    /* others */
    0xC00 => mcycle,
    0xC01 => mtime,
    0xC02 => minstret,

    /* trigger/debug */
    0x7a0 => ~(tselect),    /* this indicates we don't have any trigger support */

    _     => { print_bits("unhandled read to CSR ", csr);
               0x0000_0000_0000_0000 }
  } in {
    print_reg("CSR " ^ csr ^ " -> " ^ BitStr(res));
    res
  }

function writeCSR (csr : csreg, value : xlenbits) -> unit =
  let res : option(xlenbits) =
  match csr {
    /* machine mode */
    0x300 => { mstatus = legalize_mstatus(mstatus, value); Some(mstatus.bits()) },
    0x301 => { misa = legalize_misa(misa, value); Some(misa.bits()) },
    0x302 => { medeleg = legalize_medeleg(medeleg, value); Some(medeleg.bits()) },
    0x303 => { mideleg = legalize_mideleg(mideleg, value); Some(mideleg.bits()) },
    0x304 => { mie = legalize_mie(mie, value); Some(mie.bits()) },
    0x305 => { mtvec = legalize_tvec(mtvec, value); Some(mtvec.bits()) },
    0x306 => { mcounteren = legalize_mcounteren(mcounteren, value); Some(EXTZ(mcounteren.bits())) },
    0x340 => { mscratch = value; Some(mscratch) },
    0x341 => { mepc = legalize_xepc(value); Some(mepc) },
    0x342 => { mcause->bits() = value; Some(mcause.bits()) },
    0x343 => { mtval = value; Some(mtval) },
    0x344 => { mip = legalize_mip(mip, value); Some(mip.bits()) },

    0x3A0 => { pmpcfg0 = value; Some(pmpcfg0) }, /* FIXME: legalize */
    0x3B0 => { pmpaddr0 = value; Some(pmpaddr0) }, /* FIXME: legalize */

    /* supervisor mode */
    0x100 => { mstatus = legalize_sstatus(mstatus, value); Some(mstatus.bits()) },
    0x102 => { sedeleg = legalize_sedeleg(sedeleg, value); Some(sedeleg.bits()) },
    0x103 => { sideleg->bits() = value; Some(sideleg.bits()) }, /* TODO: does this need legalization? */
    0x104 => { mie = legalize_sie(mie, mideleg, value); Some(mie.bits()) },
    0x105 => { stvec = legalize_tvec(stvec, value); Some(stvec.bits()) },
    0x106 => { scounteren = legalize_scounteren(scounteren, value); Some(EXTZ(scounteren.bits())) },
    0x140 => { sscratch = value; Some(sscratch) },
    0x141 => { sepc = legalize_xepc(value); Some(sepc) },
    0x142 => { scause->bits() = value; Some(scause.bits()) },
    0x143 => { stval = value; Some(stval) },
    0x144 => { mip = legalize_sip(mip, mideleg, value); Some(mip.bits()) },
    0x180 => { satp = legalize_satp(cur_Architecture(), satp, value); Some(satp) },

    /* trigger/debug */
    0x7a0 => { tselect = value; Some(tselect) },

    /* counters */
    0xC00 => { mcycle = value; Some(mcycle) },
    /* FIXME: it is not clear whether writable mtime is platform-dependent. */
    0xC02 => { minstret = value; minstret_written = true; Some(minstret) },

    _     => None()
  } in
  match res {
    Some(v) => print_reg("CSR " ^ csr ^ " <- " ^ BitStr(v) ^ " (input: " ^ BitStr(value) ^ ")"),
    None()  => print_bits("unhandled write to CSR ", csr)
  }

function clause execute CSR(csr, rs1, rd, is_imm, op) =
  let rs1_val : xlenbits = if is_imm then EXTZ(rs1) else X(rs1) in
  let isWrite : bool = match op {
    CSRRW  => true,
    _      => if is_imm then unsigned(rs1_val) != 0 else unsigned(rs1) != 0
  } in
  if ~ (check_CSR(csr, cur_privilege, isWrite))
  then { handle_illegal(); false }
  else {
    let csr_val = readCSR(csr); /* could have side-effects, so technically shouldn't perform for CSRW[I] with rd == 0 */
    if isWrite then {
      let new_val : xlenbits = match op {
        CSRRW => rs1_val,
        CSRRS => csr_val | rs1_val,
        CSRRC => csr_val & ~(rs1_val)
      } in
      writeCSR(csr, new_val)
    };
    X(rd) = csr_val;
    true
  }


mapping maybe_i : bool <-> string = {
  true  <-> "i",
  false <-> ""
}

mapping csr_mnemonic : csrop <-> string = {
  CSRRW <-> "csrrw",
  CSRRS <-> "csrrs",
  CSRRC <-> "csrrc"
}

mapping clause assembly = CSR(csr, rs1, rd, true, op) <-> csr_mnemonic(op) ^ "i" ^ spc() ^ reg_name(rd) ^ sep() ^ hex_bits_5(rs1) ^ sep() ^ csr_name_map(csr)
mapping clause assembly = CSR(csr, rs1, rd, false, op) <-> csr_mnemonic(op) ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ csr_name_map(csr)

/* ****************************************************************** */
union clause ast = C_NOP : unit

mapping clause encdec_compressed = C_NOP() <-> 0b000 @ 0b0 @ 0b00000 @ 0b00000 @ 0b01

function clause execute C_NOP() = true

mapping clause assembly = C_NOP() <-> "c.nop"

/* ****************************************************************** */

union clause ast = C_ADDI4SPN : (cregbits, bits(8))

mapping clause encdec_compressed = C_ADDI4SPN(rd, nz96 @ nz54 @ nz3 @ nz2)
                                     if nz96 @ nz54 @ nz3 @ nz2 != 0b00000000 <->
                                   0b000 @ nz54 : bits(2) @ nz96 : bits(4) @ nz2 : bits(1) @ nz3 : bits(1) @ rd : cregbits @ 0b00
                                     if nz96 @ nz54 @ nz3 @ nz2 != 0b00000000

function clause execute (C_ADDI4SPN(rdc, nzimm)) =
  let imm : bits(12) = (0b00 @ nzimm @ 0b00) in
  let rd = creg2reg_bits(rdc) in
  execute(ITYPE(imm, sp, rd, RISCV_ADDI))

mapping clause assembly = C_ADDI4SPN(rdc, nzimm) if nzimm != 0b00000000 <-> "c.addi4spn" ^ spc() ^ creg_name(rdc) ^ sep() ^ hex_bits_10(nzimm @ 0b00) if nzimm != 0b00000000

/* ****************************************************************** */
union clause ast = C_LW : (bits(5), cregbits, cregbits)

mapping clause encdec_compressed = C_LW(ui6 @ ui53 @ ui2, rs1, rd) <-> 0b010 @ ui53 : bits(3) @ rs1 : cregbits @ ui2 : bits(1) @ ui6 : bits(1) @ rd : cregbits @ 0b00

function clause execute (C_LW(uimm, rsc, rdc)) =
  let imm : bits(12) = EXTZ(uimm @ 0b00) in
  let rd = creg2reg_bits(rdc) in
  let rs = creg2reg_bits(rsc) in
  execute(LOAD(imm, rs, rd, false, WORD, false, false))

mapping clause assembly = C_LW(uimm, rsc, rdc) <-> "c.lw" ^ spc() ^ creg_name(rdc) ^ sep() ^ creg_name(rsc) ^ sep() ^ hex_bits_7(uimm @ 0b00)

/* ****************************************************************** */
union clause ast = C_LD : (bits(5), cregbits, cregbits)

mapping clause encdec_compressed = C_LD(ui76 @ ui53, rs1, rd) <-> 0b011 @ ui53 : bits(3) @ rs1 : cregbits @ ui76 : bits(2) @ rd : cregbits @ 0b00

function clause execute (C_LD(uimm, rsc, rdc)) =
  let imm : bits(12) = EXTZ(uimm @ 0b000) in
  let rd = creg2reg_bits(rdc) in
  let rs = creg2reg_bits(rsc) in
  execute(LOAD(imm, rs, rd, false, DOUBLE, false, false))

mapping clause assembly = C_LD(uimm, rsc, rdc) <-> "c.ld" ^ spc() ^ creg_name(rdc) ^ sep() ^ creg_name(rsc) ^ sep() ^ hex_bits_8(uimm @ 0b000)

/* ****************************************************************** */
union clause ast = C_SW : (bits(5), cregbits, cregbits)

mapping clause encdec_compressed = C_SW(ui6 @ ui53 @ ui2, rs1, rs2) <-> 0b110 @ ui53 : bits(3) @ rs1 : cregbits @ ui2 : bits(1) @ ui6 : bits(1) @ rs2 : cregbits @ 0b00

function clause execute (C_SW(uimm, rsc1, rsc2)) =
  let imm : bits(12) = EXTZ(uimm @ 0b00) in
  let rs1 = creg2reg_bits(rsc1) in
  let rs2 = creg2reg_bits(rsc2) in
  execute(STORE(imm, rs2, rs1, WORD, false, false))

mapping clause assembly = C_SW(uimm, rsc1, rsc2) <-> "c.sw" ^ spc() ^ creg_name(rsc1) ^ sep() ^ creg_name(rsc2) ^ sep() ^ hex_bits_7(uimm @ 0b00)

/* ****************************************************************** */
union clause ast = C_SD : (bits(5), cregbits, cregbits)

mapping clause encdec_compressed = C_SD(ui76 @ ui53, rs1, rs2) <-> 0b111 @ ui53 : bits(3) @ rs1 : bits(3) @ ui76 : bits(2) @ rs2 : bits(3) @ 0b00

function clause execute (C_SD(uimm, rsc1, rsc2)) =
  let imm : bits(12) = EXTZ(uimm @ 0b000) in
  let rs1 = creg2reg_bits(rsc1) in
  let rs2 = creg2reg_bits(rsc2) in
  execute(STORE(imm, rs2, rs1, DOUBLE, false, false))

mapping clause assembly = C_SD(uimm, rsc1, rsc2) <-> "c.sd" ^ spc() ^ creg_name(rsc1) ^ sep() ^ creg_name(rsc2) ^ sep() ^ hex_bits_8(uimm @ 0b000)

/* ****************************************************************** */
union clause ast = C_ADDI : (bits(6), regbits)

mapping clause encdec_compressed = C_ADDI(nzi5 @ nzi40, rsd) if nzi5 @ nzi40 != 0b000000 & rsd != zreg <-> 0b000 @ nzi5 : bits(1) @ rsd : regbits @ nzi40 : bits(5) @ 0b01 if nzi5 @ nzi40 != 0b000000 & rsd != zreg

function clause execute (C_ADDI(nzi, rsd)) =
  let imm : bits(12) = EXTS(nzi) in
  execute(ITYPE(imm, rsd, rsd, RISCV_ADDI))

mapping clause assembly = C_ADDI(nzi, rsd) if nzi != 0b000000 & rsd != zreg <-> "c.addi" ^ spc() ^ reg_name(rsd) ^ sep() ^ hex_bits_6(nzi) if nzi != 0b000000 & rsd != zreg

/* ****************************************************************** */
union clause ast = C_JAL : (bits(11))
union clause ast = C_ADDIW : (bits(6), regbits)

/* FIXME: decoding differs for RVC32/RVC64.  Below, we are assuming
 * RV64, and C_JAL is RV32 only. */

mapping clause encdec_compressed = C_ADDIW(imm5 @ imm40, rsd) if rsd != zreg <-> 0b001 @ imm5 : bits(1) @ rsd : regbits @ imm40 : bits(5) @ 0b01 if rsd != zreg

function clause execute (C_JAL(imm)) =
  execute(RISCV_JAL(EXTS(imm @ 0b0), ra))

function clause execute (C_ADDIW(imm, rsd)) = {
  let imm : bits(32) = EXTS(imm);
  let rs_val = X(rsd);
  let res : bits(32) = rs_val[31..0] + imm;
  X(rsd) = EXTS(res);
  true
}

mapping clause assembly = C_JAL(imm) <-> "c.jal" ^ spc() ^ hex_bits_12(imm @ 0b0)

mapping clause assembly = C_ADDIW(imm, rsd) <-> "c.addiw" ^ spc() ^ reg_name(rsd) ^ sep() ^ hex_bits_6(imm)

/* ****************************************************************** */
union clause ast = C_LI : (bits(6), regbits)

mapping clause encdec_compressed = C_LI(imm5 @ imm40, rd) if rd != zreg <-> 0b010 @ imm5 : bits(1) @ rd : regbits @ imm40 : bits(5) @ 0b01 if rd != zreg

function clause execute (C_LI(imm, rd)) =
  let imm : bits(12) = EXTS(imm) in
  execute(ITYPE(imm, zreg, rd, RISCV_ADDI))

mapping clause assembly = C_LI(imm, rd) if rd != zreg <-> "c.li" ^ spc() ^ reg_name(rd) ^ sep() ^ hex_bits_6(imm) if rd != zreg

/* ****************************************************************** */
union clause ast = C_ADDI16SP : (bits(6))

mapping clause encdec_compressed = C_ADDI16SP(nzi9 @ nzi87 @ nzi6 @ nzi5 @ nzi4)
                                       if nzi9 @ nzi87 @ nzi6 @ nzi5 @ nzi4 != 0b000000
                                 <-> 0b011 @ nzi9 : bits(1) @ /* x2 */ 0b00010 @ nzi4 : bits(1) @ nzi6 : bits(1) @ nzi87 : bits(2) @ nzi5 : bits(1) @ 0b01
                                       if nzi9 @ nzi87 @ nzi6 @ nzi5 @ nzi4 != 0b000000

function clause execute (C_ADDI16SP(imm)) =
  let imm : bits(12) = EXTS(imm @ 0x0) in
  execute(ITYPE(imm, sp, sp, RISCV_ADDI))

mapping clause assembly = C_ADDI16SP(imm) if imm != 0b000000 <-> "c.addi16sp" ^ spc() ^ hex_bits_6(imm) if imm != 0b000000

/* ****************************************************************** */
union clause ast = C_LUI : (bits(6), regbits)

mapping clause encdec_compressed = C_LUI(imm17 @ imm1612, rd) if rd != zreg & rd != sp & imm17 @ imm1612 != 0b000000 <-> 0b011 @ imm17 : bits(1) @ rd : regbits @ imm1612 : bits(5) @ 0b01 if rd != zreg & rd != sp & imm17 @ imm1612 != 0b000000

function clause execute (C_LUI(imm, rd)) =
  let res : bits(20) = EXTS(imm) in
  execute(UTYPE(res, rd, RISCV_LUI))

mapping clause assembly = C_LUI(imm, rd) if rd != zreg & rd != sp & imm != 0b000000 <-> "c.lui" ^ spc() ^ reg_name(rd) ^ sep() ^ hex_bits_6(imm) if rd != zreg & rd != sp & imm != 0b000000

/* ****************************************************************** */
union clause ast = C_SRLI : (bits(6), cregbits)

mapping clause encdec_compressed = C_SRLI(nzui5 @ nzui40, rsd) if nzui5 @ nzui40 != 0b000000 <-> 0b100 @ nzui5 : bits(1) @ 0b00 @ rsd : cregbits @ nzui40 : bits(5) @ 0b01 if nzui5 @ nzui40 != 0b000000

function clause execute (C_SRLI(shamt, rsd)) =
  let rsd = creg2reg_bits(rsd)  in
  execute(SHIFTIOP(shamt, rsd, rsd, RISCV_SRLI))

mapping clause assembly = C_SRLI(shamt, rsd) if shamt != 0b000000 <-> "c.srli" ^ spc() ^ creg_name(rsd) ^ sep() ^ hex_bits_6(shamt) if shamt != 0b000000

/* ****************************************************************** */
union clause ast = C_SRAI : (bits(6), cregbits)

mapping clause encdec_compressed = C_SRAI(nzui5 @ nzui40, rsd) if nzui5 @ nzui40 != 0b000000 <-> 0b100 @ nzui5 : bits(1) @ 0b01 @ rsd : cregbits @ nzui40 : bits(5) @ 0b01 if nzui5 @ nzui40 != 0b000000

function clause execute (C_SRAI(shamt, rsd)) =
  let rsd = creg2reg_bits(rsd)  in
  execute(SHIFTIOP(shamt, rsd, rsd, RISCV_SRAI))

mapping clause assembly = C_SRAI(shamt, rsd) if shamt != 0b000000 <-> "c.srai" ^ spc() ^ creg_name(rsd) ^ sep() ^ hex_bits_6(shamt) if shamt != 0b000000

/* ****************************************************************** */
union clause ast = C_ANDI : (bits(6), cregbits)

mapping clause encdec_compressed = C_ANDI(i5 @ i40, rsd) <-> 0b100 @ i5 : bits(1) @ 0b10 @ rsd : cregbits @ i40 : bits(5) @ 0b01

function clause execute (C_ANDI(imm, rsd)) =
  let rsd = creg2reg_bits(rsd) in
  execute(ITYPE(EXTS(imm), rsd, rsd, RISCV_ANDI))

mapping clause assembly = C_ANDI(imm, rsd) <-> "c.andi" ^ spc() ^ creg_name(rsd) ^ sep() ^ hex_bits_6(imm)

/* ****************************************************************** */
union clause ast = C_SUB : (cregbits, cregbits)

mapping clause encdec_compressed = C_SUB(rsd, rs2) <-> 0b100 @ 0b0 @ 0b11 @ rsd : cregbits @ 0b00 @ rs2 : cregbits @ 0b01

function clause execute (C_SUB(rsd, rs2)) =
  let rsd = creg2reg_bits(rsd) in
  let rs2 = creg2reg_bits(rs2) in
  execute(RTYPE(rs2, rsd, rsd, RISCV_SUB))

mapping clause assembly = C_SUB(rsd, rs2) <-> "c.sub" ^ spc() ^ creg_name(rsd) ^ sep() ^ creg_name(rs2)

/* ****************************************************************** */
union clause ast = C_XOR : (cregbits, cregbits)

mapping clause encdec_compressed = C_XOR(rsd, rs2) <-> 0b100 @ 0b0 @ 0b11 @ rsd : cregbits @ 0b01 @ rs2 : cregbits @ 0b01

function clause execute (C_XOR(rsd, rs2)) =
  let rsd = creg2reg_bits(rsd) in
  let rs2 = creg2reg_bits(rs2) in
  execute(RTYPE(rs2, rsd, rsd, RISCV_XOR))

mapping clause assembly = C_XOR(rsd, rs2) <-> "c.xor" ^ spc() ^ creg_name(rsd) ^ sep() ^ creg_name(rs2)

/* ****************************************************************** */
union clause ast = C_OR : (cregbits, cregbits)

mapping clause encdec_compressed = C_OR(rsd, rs2) <-> 0b100 @ 0b0 @ 0b11 @ rsd : cregbits @ 0b10 @ rs2 : cregbits @ 0b01

function clause execute (C_OR(rsd, rs2)) =
  let rsd = creg2reg_bits(rsd) in
  let rs2 = creg2reg_bits(rs2) in
  execute(RTYPE(rs2, rsd, rsd, RISCV_OR))

mapping clause assembly = C_OR(rsd, rs2) <-> "c.or" ^ spc() ^ creg_name(rsd) ^ sep() ^ creg_name(rs2)

/* ****************************************************************** */
union clause ast = C_AND : (cregbits, cregbits)

mapping clause encdec_compressed = C_AND(rsd, rs2) <-> 0b100 @ 0b0 @ 0b11 @ rsd : cregbits @ 0b11 @ rs2 : cregbits @ 0b01

function clause execute (C_AND(rsd, rs2)) =
  let rsd = creg2reg_bits(rsd) in
  let rs2 = creg2reg_bits(rs2) in
  execute(RTYPE(rs2, rsd, rsd, RISCV_AND))

mapping clause assembly = C_AND(rsd, rs2) <-> "c.and" ^ spc() ^ creg_name(rsd) ^ sep() ^ creg_name(rs2)

/* ****************************************************************** */
union clause ast = C_SUBW : (cregbits, cregbits)

/* TODO: invalid on RV32 */
mapping clause encdec_compressed = C_SUBW(rsd, rs2) <-> 0b100 @ 0b1 @ 0b11 @ rsd : cregbits @ 0b00 @ rs2 : cregbits @ 0b01

function clause execute (C_SUBW(rsd, rs2)) =
  let rsd = creg2reg_bits(rsd) in
  let rs2 = creg2reg_bits(rs2) in
  execute(RTYPEW(rs2, rsd, rsd, RISCV_SUBW))

mapping clause assembly = C_SUBW(rsd, rs2) <-> "c.subw" ^ spc() ^ creg_name(rsd) ^ sep() ^ creg_name(rs2)

/* ****************************************************************** */
union clause ast = C_ADDW : (cregbits, cregbits)

/* TODO: invalid on RV32 */
mapping clause encdec_compressed = C_ADDW(rsd, rs2) <-> 0b100 @ 0b1 @ 0b11 @ rsd : cregbits @ 0b01 @ rs2 : cregbits @ 0b01

function clause execute (C_ADDW(rsd, rs2)) =
  let rsd = creg2reg_bits(rsd) in
  let rs2 = creg2reg_bits(rs2) in
  execute(RTYPEW(rs2, rsd, rsd, RISCV_ADDW))

mapping clause assembly = C_ADDW(rsd, rs2) <-> "c.addw" ^ spc() ^ creg_name(rsd) ^ sep() ^ creg_name(rs2)

/* ****************************************************************** */
union clause ast = C_J : (bits(11))

mapping clause encdec_compressed = C_J(i11 @ i10 @ i98 @ i7 @ i6 @ i5 @ i4 @ i31) <-> 0b101 @ i11 : bits(1) @ i4 : bits(1) @ i98 : bits(2) @ i10 : bits(1) @ i6 : bits(1) @ i7 : bits(1) @ i31 : bits(3) @ i5 : bits(1) @ 0b01

function clause execute (C_J(imm)) =
  execute(RISCV_JAL(EXTS(imm @ 0b0), zreg))

mapping clause assembly = C_J(imm) <-> "c.j" ^ spc() ^ hex_bits_11(imm)

/* ****************************************************************** */
union clause ast = C_BEQZ : (bits(8), cregbits)

mapping clause encdec_compressed = C_BEQZ(i8 @ i76 @ i5 @ i43 @ i21, rs) <-> 0b110 @ i8 : bits(1) @ i43 : bits(2) @ rs : cregbits @ i76 : bits(2) @ i21 : bits(2) @ i5 : bits(1) @ 0b01

function clause execute (C_BEQZ(imm, rs)) =
  execute(BTYPE(EXTS(imm @ 0b0), zreg, creg2reg_bits(rs), RISCV_BEQ))

mapping clause assembly = C_BEQZ(imm, rs) <-> "c.beqz" ^ spc() ^ creg_name(rs) ^ sep() ^ hex_bits_8(imm)

/* ****************************************************************** */
union clause ast = C_BNEZ : (bits(8), cregbits)

mapping clause encdec_compressed = C_BNEZ(i8 @ i76 @ i5 @ i43 @ i21, rs) <-> 0b111 @ i8 : bits(1) @ i43 : bits(2) @ rs : cregbits @ i76 : bits(2) @ i21 : bits(2) @ i5 : bits(1) @ 0b01

function clause execute (C_BNEZ(imm, rs)) =
  execute(BTYPE(EXTS(imm @ 0b0), zreg, creg2reg_bits(rs), RISCV_BNE))

mapping clause assembly = C_BNEZ(imm, rs) <-> "c.bnez" ^ spc() ^ creg_name(rs) ^ sep() ^ hex_bits_8(imm)

/* ****************************************************************** */
union clause ast = C_SLLI : (bits(6), regbits)

/* TODO: On RV32, also need shamt[5] == 0 */
mapping clause encdec_compressed = C_SLLI(nzui5 @ nzui40, rsd) if nzui5 @ nzui40 != 0b000000 & rsd != zreg
                                 <-> 0b000 @ nzui5 : bits(1) @ rsd : regbits @ nzui40 : bits(5) @ 0b10 if nzui5 @ nzui40 != 0b000000 & rsd != zreg

function clause execute (C_SLLI(shamt, rsd)) =
  execute(SHIFTIOP(shamt, rsd, rsd, RISCV_SLLI))

mapping clause assembly = C_SLLI(shamt, rsd) if shamt != 0b000000 & rsd != zreg
                        <-> "c.slli" ^ spc() ^ reg_name(rsd) ^ sep() ^ hex_bits_6(shamt) if shamt != 0b000000 & rsd != zreg

/* ****************************************************************** */
union clause ast = C_LWSP : (bits(6), regbits)

mapping clause encdec_compressed = C_LWSP(ui76 @ ui5 @ ui42, rd) if rd != zreg
                                 <-> 0b010 @ ui5 : bits(1) @ rd : regbits @ ui42 : bits(3) @ ui76 : bits(2) @ 0b10 if rd != zreg

function clause execute (C_LWSP(uimm, rd)) =
  let imm : bits(12) = EXTZ(uimm @ 0b00) in
  execute(LOAD(imm, sp, rd, false, WORD, false, false))

mapping clause assembly = C_LWSP(uimm, rd) if rd != zreg <-> "c.lwsp" ^ spc() ^ reg_name(rd) ^ sep() ^ hex_bits_6(uimm) if rd != zreg

/* ****************************************************************** */
union clause ast = C_LDSP : (bits(6), regbits)

mapping clause encdec_compressed = C_LDSP(ui86 @ ui5 @ ui43, rd) if rd != zreg <-> 0b011 @ ui5 : bits(1) @ rd : regbits @ ui43 : bits(2) @ ui86 : bits(3) @ 0b10 if rd != zreg

function clause execute (C_LDSP(uimm, rd)) =
  let imm : bits(12) = EXTZ(uimm @ 0b000) in
  execute(LOAD(imm, sp, rd, false, DOUBLE, false, false))

mapping clause assembly = C_LDSP(uimm, rd) if rd != zreg <-> "c.ldsp" ^ spc() ^ reg_name(rd) ^ sep() ^ hex_bits_6(uimm) if rd != zreg

/* ****************************************************************** */
union clause ast = C_SWSP : (bits(6), regbits)

mapping clause encdec_compressed = C_SWSP(ui76 @ ui52, rs2) <-> 0b110 @ ui52 : bits(4) @ ui76 : bits(2) @ rs2 : regbits @ 0b10

function clause execute (C_SWSP(uimm, rs2)) =
  let imm : bits(12) = EXTZ(uimm @ 0b00) in
  execute(STORE(imm, rs2, sp, WORD, false, false))

mapping clause assembly = C_SWSP(uimm, rd) <-> "c.swsp" ^ spc() ^ reg_name(rd) ^ sep() ^ hex_bits_6(uimm)

/* ****************************************************************** */
union clause ast = C_SDSP : (bits(6), regbits)

mapping clause encdec_compressed = C_SDSP(ui86 @ ui53, rs2) <-> 0b111 @ ui53 : bits(3) @ ui86 : bits(3) @ rs2 : regbits @ 0b10

function clause execute (C_SDSP(uimm, rs2)) =
  let imm : bits(12) = EXTZ(uimm @ 0b000) in
  execute(STORE(imm, rs2, sp, DOUBLE, false, false))

mapping clause assembly = C_SDSP(uimm, rs2) <-> "c.sdsp" ^ spc() ^ reg_name(rs2) ^ sep() ^ hex_bits_6(uimm)

/* ****************************************************************** */
union clause ast = C_JR : (regbits)

mapping clause encdec_compressed = C_JR(rs1) if rs1 != zreg <-> 0b100 @ 0b0 @ rs1 : regbits @ 0b00000 @ 0b10 if rs1 != zreg

function clause execute (C_JR(rs1)) =
  execute(RISCV_JALR(EXTZ(0b0), rs1, zreg))

mapping clause assembly = C_JR(rs1) if rs1 != zreg <-> "c.jr" ^ spc() ^ reg_name(rs1) if rs1 != zreg

/* ****************************************************************** */
union clause ast = C_JALR : (regbits)

mapping clause encdec_compressed = C_JALR(rs1) if rs1 != zreg <-> 0b100 @ 0b1 @ rs1 : regbits @ 0b00000 @ 0b10 if rs1 != zreg

function clause execute (C_JALR(rs1)) =
  execute(RISCV_JALR(EXTZ(0b0), rs1, ra))

mapping clause assembly = C_JALR(rs1) if rs1 != zreg <-> "c.jalr" ^ spc() ^ reg_name(rs1) if rs1 != zreg

/* ****************************************************************** */
union clause ast = C_MV : (regbits, regbits)

mapping clause encdec_compressed = C_MV(rd, rs2) if rd != zreg & rs2 != zreg <-> 0b100 @ 0b0 @ rd : regbits @ rs2 : regbits @ 0b10 if rd != zreg & rs2 != zreg

function clause execute (C_MV(rd, rs2)) =
  execute(RTYPE(rs2, zreg, rd, RISCV_ADD))

mapping clause assembly = C_MV(rd, rs2) if rd != zreg & rs2 != zreg <-> "c.mv" ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs2) if rd != zreg & rs2 != zreg

/* ****************************************************************** */
union clause ast = C_EBREAK : unit

mapping clause encdec_compressed = C_EBREAK() <-> 0b100 @ 0b1 @ 0b00000 @ 0b00000 @ 0b10

function clause execute C_EBREAK() =
  execute(EBREAK())

mapping clause assembly = C_EBREAK() <-> "c.ebreak"

/* ****************************************************************** */
union clause ast = C_ADD : (regbits, regbits)

mapping clause encdec_compressed = C_ADD(rsd, rs2) if rsd != zreg & rs2 != zreg <-> 0b100 @ 0b1 @ rsd : regbits @ rs2 : regbits @ 0b10 if rsd != zreg & rs2 != zreg

function clause execute (C_ADD(rsd, rs2)) =
  execute(RTYPE(rs2, rsd, rsd, RISCV_ADD))

mapping clause assembly = C_ADD(rsd, rs2) if rsd != zreg & rs2 != zreg <-> "c.add" ^ spc() ^ reg_name(rsd) ^ sep() ^ reg_name(rs2) if rsd != zreg & rs2 != zreg

/* ****************************************************************** */

union clause ast = STOP_FETCHING : unit

/* RMEM stop fetching sentinel, using RISCV encoding space custom-0 */
mapping clause encdec = STOP_FETCHING() <-> 0xfade @ 0b00000000 @ 0b0 @ 0b00 @ 0b010 @ 0b11

function clause execute (STOP_FETCHING()) = true

mapping clause assembly = STOP_FETCHING() <-> "stop_fetching"

union clause ast = THREAD_START : unit

/* RMEM thread start sentinel, using RISCV encoding space custom-0 */
mapping clause encdec = THREAD_START() <-> 0xc0de @ 0b00000000 @ 0b0 @ 0b00 @ 0b010 @ 0b11

function clause execute (THREAD_START()) = true

mapping clause assembly = THREAD_START() <-> "thread_start"


/* ****************************************************************** */

union clause ast = ILLEGAL : word

mapping clause encdec = ILLEGAL(s) <-> s

function clause execute (ILLEGAL(s)) = { handle_illegal(); false }

mapping clause assembly = ILLEGAL(s) <-> "illegal" ^ spc() ^ hex_bits_32(s)



/* ****************************************************************** */

union clause ast = C_ILLEGAL : half

mapping clause encdec_compressed = C_ILLEGAL(s) <-> s

function clause execute C_ILLEGAL(s) = { handle_illegal(); false }

mapping clause assembly = C_ILLEGAL(s) <-> "c.illegal" ^ spc() ^ hex_bits_16(s)

/* ****************************************************************** */
