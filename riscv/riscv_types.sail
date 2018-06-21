/* basic types */

let xlen = 64
type xlenbits = bits(64)
let xlen_max_unsigned = 2 ^ xlen - 1
let xlen_max_signed = 2 ^ (xlen - 1) - 1
let xlen_min_signed = 0 - 2 ^ (xlen - 1)

type half = bits(16)
type word = bits(32)

type regno ('n : Int), 0 <= 'n < 32 = atom('n)
type regbits = bits(5)
type cregbits = bits(3)
type csreg = bits(12)

val cast regbits_to_regno : bits(5) -> {'n, 0 <= 'n < 32. regno('n)}
function regbits_to_regno b = let 'r = unsigned(b) in r

val creg2reg_bits : cregbits -> regbits
function creg2reg_bits(creg) = 0b01 @ creg

/* some arch and ABI relevant registers */

let zreg : regbits = 0b00000
let ra : regbits = 0b00001  /* x1 */
let sp : regbits = 0b00010  /* x2 */

register PC : xlenbits
register nextPC : xlenbits

/* register file and accessors */

register Xs : vector(32, dec, xlenbits)

register x1  : xlenbits
register x2  : xlenbits
register x3  : xlenbits
register x4  : xlenbits
register x5  : xlenbits
register x6  : xlenbits
register x7  : xlenbits
register x8  : xlenbits
register x9  : xlenbits
register x10 : xlenbits
register x11 : xlenbits
register x12 : xlenbits
register x13 : xlenbits
register x14 : xlenbits
register x15 : xlenbits
register x16 : xlenbits
register x17 : xlenbits
register x18 : xlenbits
register x19 : xlenbits
register x20 : xlenbits
register x21 : xlenbits
register x22 : xlenbits
register x23 : xlenbits
register x24 : xlenbits
register x25 : xlenbits
register x26 : xlenbits
register x27 : xlenbits
register x28 : xlenbits
register x29 : xlenbits
register x30 : xlenbits
register x31 : xlenbits

val rX : forall 'n, 0 <= 'n < 32. regno('n) -> xlenbits effect {rreg}
/*function rX 0 = 0x0000000000000000
and rX (r if r > 0) = Xs[r]*/
function rX r = match r {
  0 => 0x0000000000000000,
  1 => x1,
  2 => x2,
  3 => x3,
  4 => x4,
  5 => x5,
  6 => x6,
  7 => x7,
  8 => x8,
  9 => x9,
  10 => x10,
  11 => x11,
  12 => x12,
  13 => x13,
  14 => x14,
  15 => x15,
  16 => x16,
  17 => x17,
  18 => x18,
  19 => x19,
  20 => x20,
  21 => x21,
  22 => x22,
  23 => x23,
  24 => x24,
  25 => x25,
  26 => x26,
  27 => x27,
  28 => x28,
  29 => x29,
  30 => x30,
  31 => x31
}

val wX : forall 'n, 0 <= 'n < 32. (regno('n), xlenbits) -> unit effect {wreg}
function wX (r, v) = {
  match r {
    0 => (),
    1 => x1 = v,
    2 => x2 = v,
    3 => x3 = v,
    4 => x4 = v,
    5 => x5 = v,
    6 => x6 = v,
    7 => x7 = v,
    8 => x8 = v,
    9 => x9 = v,
    10 => x10 = v,
    11 => x11 = v,
    12 => x12 = v,
    13 => x13 = v,
    14 => x14 = v,
    15 => x15 = v,
    16 => x16 = v,
    17 => x17 = v,
    18 => x18 = v,
    19 => x19 = v,
    20 => x20 = v,
    21 => x21 = v,
    22 => x22 = v,
    23 => x23 = v,
    24 => x24 = v,
    25 => x25 = v,
    26 => x26 = v,
    27 => x27 = v,
    28 => x28 = v,
    29 => x29 = v,
    30 => x30 = v,
    31 => x31 = v
  };
  if (r != 0) then {
     // Xs[r] = v;
     print("x" ^ string_of_int(r) ^ " <- " ^ BitStr(v));
  }
}

overload X = {rX, wX}

/* register name printers */

val cast reg_name_abi : regbits -> string

function reg_name_abi(r) = {
  match (r) {
    0b00000 => "zero",
    0b00001 => "ra",
    0b00010 => "sp",
    0b00011 => "gp",
    0b00100 => "tp",
    0b00101 => "t0",
    0b00110 => "t1",
    0b00111 => "t2",
    0b01000 => "fp",
    0b01001 => "s1",
    0b01010 => "a0",
    0b01011 => "a1",
    0b01100 => "a2",
    0b01101 => "a3",
    0b01110 => "a4",
    0b01111 => "a5",
    0b10000 => "a6",
    0b10001 => "a7",
    0b10010 => "s2",
    0b10011 => "s3",
    0b10100 => "s4",
    0b10101 => "s5",
    0b10110 => "s6",
    0b10111 => "s7",
    0b11000 => "s8",
    0b11001 => "s9",
    0b11010 => "s10",
    0b11011 => "s11",
    0b11100 => "t3",
    0b11101 => "t4",
    0b11110 => "t5",
    0b11111 => "t6"
  }
}

/* instruction fields */

type opcode = bits(7)
type imm12 = bits(12)
type imm20 = bits(20)
type amo = bits(1)

/* base architecture definitions */
enum Architecture = {RV32, RV64, RV128}
type arch_xlen = bits(2)
function architecture(a : arch_xlen) -> option(Architecture) =
  match (a) {
    0b01 => Some(RV32),
    0b10 => Some(RV64),
    0b11 => Some(RV128),
    _    => None()
  }

function arch_to_bits(a : Architecture) -> arch_xlen =
  match (a) {
    RV32  => 0b01,
    RV64  => 0b10,
    RV128 => 0b11
  }

/* privilege levels */

type priv_level = bits(2)
enum Privilege = {User, Supervisor, Machine}

val cast privLevel_to_bits : Privilege -> priv_level
function privLevel_to_bits (p) =
  match (p) {
    User => 0b00,
    Supervisor => 0b01,
    Machine => 0b11
  }

val cast privLevel_of_bits : priv_level -> Privilege
function privLevel_of_bits (p) =
  match (p) {
    0b00 => User,
    0b01 => Supervisor,
    0b11 => Machine
  }

val cast privLevel_to_str : Privilege -> string
function privLevel_to_str (p) =
  match (p) {
    User => "U",
    Supervisor => "S",
    Machine => "M"
  }

/* access types */

enum AccessType = {Read, Write, ReadWrite, Execute}
val cast accessType_to_str : AccessType -> string
function accessType_to_str (a) =
  match (a) {
    Read => "R",
    Write => "W",
    ReadWrite => "RW",
    Execute => "X"
  }

enum ReadType   = {Instruction, Data}
val cast readType_to_str : ReadType -> string
function readType_to_str (r) =
  match (r) {
    Instruction => "I",
    Data => "D"
  }

/* architectural exception and interrupt definitions */

type exc_code = bits(4)

enum ExceptionType = {
 E_Fetch_Addr_Align,
 E_Fetch_Access_Fault,
 E_Illegal_Instr,
 E_Breakpoint,
 E_Load_Addr_Align,
 E_Load_Access_Fault,
 E_SAMO_Addr_Align,
 E_SAMO_Access_Fault,
 E_U_EnvCall,
 E_S_EnvCall,
 E_Reserved_10,
 E_M_EnvCall,
 E_Fetch_Page_Fault,
 E_Load_Page_Fault,
 E_Reserved_14,
 E_SAMO_Page_Fault
}

val cast exceptionType_to_bits : ExceptionType -> exc_code
function exceptionType_to_bits(e) =
  match (e) {
    E_Fetch_Addr_Align => 0x0,
    E_Fetch_Access_Fault => 0x1,
    E_Illegal_Instr => 0x2,
    E_Breakpoint => 0x3,
    E_Load_Addr_Align => 0x4,
    E_Load_Access_Fault => 0x5,
    E_SAMO_Addr_Align => 0x6,
    E_SAMO_Access_Fault => 0x7,
    E_U_EnvCall => 0x8,
    E_S_EnvCall => 0x9,
    E_Reserved_10 => 0xa,
    E_M_EnvCall => 0xb,
    E_Fetch_Page_Fault => 0xc,
    E_Load_Page_Fault => 0xd,
    E_Reserved_14 => 0xe,
    E_SAMO_Page_Fault => 0xf
  }

val cast exceptionType_to_str : ExceptionType -> string
function exceptionType_to_str(e) =
  match (e) {
    E_Fetch_Addr_Align => "fisaligned-fetch",
    E_Fetch_Access_Fault => "fetch-access-fault",
    E_Illegal_Instr => "illegal-instruction",
    E_Breakpoint => "breakpoint",
    E_Load_Addr_Align => "misaligned-load",
    E_Load_Access_Fault => "load-access-fault",
    E_SAMO_Addr_Align => "misaliged-store/amo",
    E_SAMO_Access_Fault => "store/amo-access-fault",
    E_U_EnvCall => "u-call",
    E_S_EnvCall => "s-call",
    E_Reserved_10 => "reserved-0",
    E_M_EnvCall => "m-call",
    E_Fetch_Page_Fault => "fetch-page-fault",
    E_Load_Page_Fault => "load-page-fault",
    E_Reserved_14 => "reserved-1",
    E_SAMO_Page_Fault => "store/amo-page-fault"
  }

enum InterruptType = {
  I_U_Software,
  I_S_Software,
  I_M_Software,
  I_U_Timer,
  I_S_Timer,
  I_M_Timer,
  I_U_External,
  I_S_External,
  I_M_External
}

val cast interruptType_to_bits : InterruptType -> exc_code
function interruptType_to_bits (i) =
  match (i) {
    I_U_Software => 0x0,
    I_S_Software => 0x1,
    I_M_Software => 0x3,
    I_U_Timer    => 0x4,
    I_S_Timer    => 0x5,
    I_M_Timer    => 0x7,
    I_U_External => 0x8,
    I_S_External => 0x9,
    I_M_External => 0xb
  }

type tv_mode = bits(2)
enum TrapVectorMode = {TV_Direct, TV_Vector, TV_Reserved}

val cast trapVectorMode_of_bits : tv_mode -> TrapVectorMode
function trapVectorMode_of_bits (m) =
  match (m) {
    0b00 => TV_Direct,
    0b01 => TV_Vector,
    _    => TV_Reserved
  }

/* other exceptions */

union exception = {
  Error_not_implemented : string,
  Error_internal_error : unit
}

val not_implemented : forall ('a : Type). string -> 'a effect {escape}
function not_implemented message = throw(Error_not_implemented(message))

val internal_error : forall ('a : Type). string -> 'a effect {escape}
function internal_error(s) = {
    assert (false, s);
    throw Error_internal_error()
}

/* extension context status */

type ext_status = bits(2)
enum ExtStatus = {Off, Initial, Clean, Dirty}

val cast extStatus_to_bits : ExtStatus -> ext_status
function extStatus_to_bits(e) =
  match (e) {
    Off => 0b00,
    Initial => 0b01,
    Clean => 0b10,
    Dirty => 0b11
  }

val cast extStatus_of_bits : ext_status -> ExtStatus
function extStatus_of_bits(e) =
  match (e) {
    0b00 => Off,
    0b01 => Initial,
    0b10 => Clean,
    0b11 => Dirty
  }

/* supervisor-level address translation modes */

type satp_mode = bits(4)
enum SATPMode = {Sbare, Sv32, Sv39}

function satpMode_of_bits(a : Architecture, m : satp_mode) -> option(SATPMode) =
  match (a, m) {
    (_, 0x0)    => Some(Sbare),
    (RV32, 0x1) => Some(Sv32),
    (RV64, 0x8) => Some(Sv39),
    (_, _)      => None()
  }

/* CSR access control bits (from CSR addresses) */
type csrRW = bits(2)  /* read/write */

enum uop = {RISCV_LUI, RISCV_AUIPC} /* upper immediate ops */
enum bop = {RISCV_BEQ, RISCV_BNE, RISCV_BLT, RISCV_BGE, RISCV_BLTU, RISCV_BGEU} /* branch ops */
enum iop = {RISCV_ADDI, RISCV_SLTI, RISCV_SLTIU, RISCV_XORI, RISCV_ORI, RISCV_ANDI} /* immediate ops */
enum sop = {RISCV_SLLI, RISCV_SRLI, RISCV_SRAI} /* shift ops */
enum rop = {RISCV_ADD, RISCV_SUB, RISCV_SLL, RISCV_SLT, RISCV_SLTU, RISCV_XOR, RISCV_SRL, RISCV_SRA, RISCV_OR, RISCV_AND} /* reg-reg ops */
enum ropw = {RISCV_ADDW, RISCV_SUBW, RISCV_SLLW, RISCV_SRLW, RISCV_SRAW} /* reg-reg 32-bit ops */
enum amoop = {AMOSWAP, AMOADD, AMOXOR, AMOAND, AMOOR, AMOMIN, AMOMAX, AMOMINU, AMOMAXU} /* AMO ops */
enum csrop = {CSRRW, CSRRS, CSRRC}
enum word_width = {BYTE, HALF, WORD, DOUBLE}

/* mappings for assembly */

val reg_name : bits(5) <-> string
mapping reg_name = {
    0b00000 <-> "zero",
    0b00001 <-> "ra",
    0b00010 <-> "sp",
    0b00011 <-> "gp",
    0b00100 <-> "tp",
    0b00101 <-> "t0",
    0b00110 <-> "t1",
    0b00111 <-> "t2",
    0b01000 <-> "fp",
    0b01001 <-> "s1",
    0b01010 <-> "a0",
    0b01011 <-> "a1",
    0b01100 <-> "a2",
    0b01101 <-> "a3",
    0b01110 <-> "a4",
    0b01111 <-> "a5",
    0b10000 <-> "a6",
    0b10001 <-> "a7",
    0b10010 <-> "s2",
    0b10011 <-> "s3",
    0b10100 <-> "s4",
    0b10101 <-> "s5",
    0b10110 <-> "s6",
    0b10111 <-> "s7",
    0b11000 <-> "s8",
    0b11001 <-> "s9",
    0b11010 <-> "s10",
    0b11011 <-> "s11",
    0b11100 <-> "t3",
    0b11101 <-> "t4",
    0b11110 <-> "t5",
    0b11111 <-> "t6"
}

val sep : unit <-> string
mapping sep = {
  () <-> opt_spc() ^ "," ^ def_spc()
}

mapping bool_bits : bool <-> bits(1) = {
  true <-> 0b1,
  false <-> 0b0
}

mapping bool_not_bits : bool <-> bits(1) = {
  true <-> 0b0,
  false <-> 0b1
}


mapping size_bits : word_width <-> bits(2) = {
  BYTE <-> 0b00,
  HALF <-> 0b01,
  WORD <-> 0b10,
  DOUBLE <-> 0b11
}

mapping size_mnemonic : word_width <-> string = {
  BYTE <-> "b",
  HALF <-> "h",
  WORD <-> "w",
  DOUBLE <-> "d"
}
