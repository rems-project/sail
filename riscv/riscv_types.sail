val not_implemented : forall ('a : Type). string -> 'a effect {escape}

function not_implemented message = throw(Error_not_implemented(message))

val internal_error : forall ('a : Type). string -> 'a effect {escape}
function internal_error(s) = {
    assert (false, s);
    throw (Error_internal_error)
}

type regval = bits(64)

type regno ('n : Int), 0 <= 'n < 32 = atom('n)
type regbits = bits(5)
type cregbits = bits(3)

val cast regbits_to_regno : bits(5) -> {'n, 0 <= 'n < 32. regno('n)}
function regbits_to_regno b = let 'r = unsigned(b) in r

val creg2reg_bits : cregbits -> regbits
function creg2reg_bits(creg) = 0b10 @ creg

/* register x0 : regval is hard-wired zero */
register x1 : regval
register x2 : regval
register x3 : regval
register x4 : regval
register x5 : regval
register x6 : regval
register x7 : regval
register x8 : regval
register x9 : regval
register x10 : regval
register x11 : regval
register x12 : regval
register x13 : regval
register x14 : regval
register x15 : regval
register x16 : regval
register x17 : regval
register x18 : regval
register x19 : regval
register x20 : regval
register x21 : regval
register x22 : regval
register x23 : regval
register x24 : regval
register x25 : regval
register x26 : regval
register x27 : regval
register x28 : regval
register x29 : regval
register x30 : regval
register x31 : regval

/* some arch and ABI relevant registers */
let zreg : regbits = 0b00000
let ra : regbits = 0b00001  /* x1 */
let sp : regbits = 0b00010  /* x2 */

register PC : bits(64)
register nextPC : bits(64)

let GPRs : vector(31, dec, register(regval)) =
  [ ref x31, ref x30, ref x29, ref x28,
    ref x27, ref x26, ref x25, ref x24,
    ref x23, ref x22, ref x21, ref x20,
    ref x19, ref x18, ref x17, ref x16,
    ref x15, ref x14, ref x13, ref x12,
    ref x11, ref x10, ref x9, ref x8,
    ref x7, ref x6, ref x5, ref x4,
    ref x3, ref x2, ref x1 /* ref x0 */
  ]

/* Getters and setters for registers */
val rGPR : forall 'n, 0 <= 'n < 32. regno('n) -> regval effect {rreg}

function rGPR 0 = 0x0000000000000000
and rGPR (r if r > 0) = reg_deref(GPRs[r - 1])

/*val wGPR : forall 'n, 0 <= 'n < 32. (regno('n), regval) -> unit effect {wreg}*/
val wGPR : forall 'n, 0 <= 'n < 32. (regno('n), regval) -> unit effect {wreg}

function wGPR (r, v) = 
  if (r != 0) then {
     (*GPRs[r - 1]) = v;
     print_int("GPR ", r);
     print_bits("<- ", v);
  }

function check_alignment (addr : bits(64), width : atom('n)) -> forall 'n. unit =
  if unsigned(addr) % width != 0 then throw(Error_misaligned_access) else ()

val MEMr                         : forall 'n. (bits(64), atom('n)) -> bits(8 * 'n) effect {rmem}
val MEMr_acquire                 : forall 'n. (bits(64), atom('n)) -> bits(8 * 'n) effect {rmem}
val MEMr_strong_acquire          : forall 'n. (bits(64), atom('n)) -> bits(8 * 'n) effect {rmem}
val MEMr_reserved                : forall 'n. (bits(64), atom('n)) -> bits(8 * 'n) effect {rmem}
val MEMr_reserved_acquire        : forall 'n. (bits(64), atom('n)) -> bits(8 * 'n) effect {rmem}
val MEMr_reserved_strong_acquire : forall 'n. (bits(64), atom('n)) -> bits(8 * 'n) effect {rmem}

function MEMr                         (addr, width) = __RISCV_read(addr, width)
function MEMr_acquire                 (addr, width) = __RISCV_read(addr, width)
function MEMr_strong_acquire          (addr, width) = __RISCV_read(addr, width)
function MEMr_reserved                (addr, width) = __RISCV_read(addr, width)
function MEMr_reserved_acquire        (addr, width) = __RISCV_read(addr, width)
function MEMr_reserved_strong_acquire (addr, width) = __RISCV_read(addr, width)

val mem_read : forall 'n. (bits(64), atom('n), bool, bool, bool) -> bits(8 * 'n) effect {rmem, escape}

function mem_read (addr, width, aq, rl, res) = {
  if aq | res then check_alignment(addr, width);

  match (aq, rl, res) {
    (false, false, false) => MEMr(addr, width),
    (true,  false, false) => MEMr_acquire(addr, width),
    (false, false, true)  => MEMr_reserved(addr, width),
    (true,  false, true)  => MEMr_reserved_acquire(addr, width),
    (false, true,  false) => throw(Error_not_implemented("load.rl")),
    (true,  true,  false) => MEMr_strong_acquire(addr, width),
    (false, true,  true)  => throw(Error_not_implemented("lr.rl")),
    (true,  true,  true)  => MEMr_reserved_strong_acquire(addr, width)
  }
}

val MEMea = {ocaml: "memea", lem: "MEMea"} : forall 'n.
  (bits(64), atom('n)) -> unit effect {eamem}
val MEMea_release = {ocaml: "memea", lem: "MEMea_release"} : forall 'n.
  (bits(64), atom('n)) -> unit effect {eamem}
val MEMea_strong_release = {ocaml: "memea", lem: "MEMea_strong_release"} : forall 'n.
  (bits(64), atom('n)) -> unit effect {eamem}
val MEMea_conditional = {ocaml: "memea", lem: "MEMea_conditional"} : forall 'n.
  (bits(64), atom('n)) -> unit effect {eamem}
val MEMea_conditional_release = {ocaml: "memea", lem: "MEMea_conditional_release"} : forall 'n.
  (bits(64), atom('n)) -> unit effect {eamem}
val MEMea_conditional_strong_release = {ocaml: "memea", lem: "MEMea_conditional_strong_release"} : forall 'n.
  (bits(64), atom('n)) -> unit effect {eamem}

val mem_write_ea : forall 'n. (bits(64), atom('n), bool, bool, bool) -> unit effect {eamem, escape}

function mem_write_ea (addr, width, aq, rl, con) = {
  if rl | con then check_alignment(addr, width);

  match (aq, rl, con) {
    (false, false, false) => MEMea(addr, width),
    (false, true,  false) => MEMea_release(addr, width),
    (false, false, true)  => MEMea_conditional(addr, width),
    (false, true , true)  => MEMea_conditional_release(addr, width),
    (true,  false, false) => throw(Error_not_implemented("store.aq")),
    (true,  true,  false) => MEMea_strong_release(addr, width),
    (true,  false, true)  => throw(Error_not_implemented("sc.aq")),
    (true,  true , true)  => MEMea_conditional_strong_release(addr, width)
  }
}

val MEMval                            : forall 'n. (bits(64), atom('n), bits(8 * 'n)) -> unit effect {wmv}
val MEMval_release                    : forall 'n. (bits(64), atom('n), bits(8 * 'n)) -> unit effect {wmv}
val MEMval_strong_release             : forall 'n. (bits(64), atom('n), bits(8 * 'n)) -> unit effect {wmv}
val MEMval_conditional                : forall 'n. (bits(64), atom('n), bits(8 * 'n)) -> unit effect {wmv}
val MEMval_conditional_release        : forall 'n. (bits(64), atom('n), bits(8 * 'n)) -> unit effect {wmv}
val MEMval_conditional_strong_release : forall 'n. (bits(64), atom('n), bits(8 * 'n)) -> unit effect {wmv}

function MEMval                            (addr, width, data) = __RISCV_write(addr, width, data)
function MEMval_release                    (addr, width, data) = __RISCV_write(addr, width, data)
function MEMval_strong_release             (addr, width, data) = __RISCV_write(addr, width, data)
function MEMval_conditional                (addr, width, data) = __RISCV_write(addr, width, data)
function MEMval_conditional_release        (addr, width, data) = __RISCV_write(addr, width, data)
function MEMval_conditional_strong_release (addr, width, data) = __RISCV_write(addr, width, data)

val mem_write_value : forall 'n. (bits(64), atom('n), bits(8 * 'n), bool, bool, bool) -> unit effect {wmv, escape}

function mem_write_value (addr, width, value, aq, rl, con) = {
  if rl | con then check_alignment(addr, width);

  match (aq, rl, con) {
    (false, false, false) => MEMval(addr, width, value),
    (false, true,  false) => MEMval_release(addr, width, value),
    (false, false, true)  => MEMval_conditional(addr, width, value),
    (false, true,  true)  => MEMval_conditional_release(addr, width, value),
    (true,  false, false) => throw(Error_not_implemented("store.aq")),
    (true,  true,  false) => MEMval_strong_release(addr, width, value),
    (true,  false, true)  => throw(Error_not_implemented("sc.aq")),
    (true,  true,  true)  => MEMval_conditional_strong_release(addr, width, value)
  }
}

val "speculate_conditional_success" : unit -> bool effect {exmem}

val MEM_fence_rw_rw = {ocaml: "skip", lem: "MEM_fence_rw_rw"} : unit -> unit effect {barr}
val MEM_fence_r_rw  = {ocaml: "skip", lem: "MEM_fence_r_rw"}  : unit -> unit effect {barr}
val MEM_fence_r_r   = {ocaml: "skip", lem: "MEM_fence_r_r"}   : unit -> unit effect {barr}
val MEM_fence_rw_w  = {ocaml: "skip", lem: "MEM_fence_rw_w"}  : unit -> unit effect {barr}
val MEM_fence_w_w   = {ocaml: "skip", lem: "MEM_fence_w_w"}   : unit -> unit effect {barr}
val MEM_fence_i     = {ocaml: "skip", lem: "MEM_fence_i"}     : unit -> unit effect {barr}

enum uop = {RISCV_LUI, RISCV_AUIPC} /* upper immediate ops */
enum bop = {RISCV_BEQ, RISCV_BNE, RISCV_BLT, RISCV_BGE, RISCV_BLTU, RISCV_BGEU} /* branch ops */
enum iop = {RISCV_ADDI, RISCV_SLTI, RISCV_SLTIU, RISCV_XORI, RISCV_ORI, RISCV_ANDI} /* immediate ops */
enum sop = {RISCV_SLLI, RISCV_SRLI, RISCV_SRAI} /* shift ops */
enum rop = {RISCV_ADD, RISCV_SUB, RISCV_SLL, RISCV_SLT, RISCV_SLTU, RISCV_XOR, RISCV_SRL, RISCV_SRA, RISCV_OR, RISCV_AND} /* reg-reg ops */
enum ropw = {RISCV_ADDW, RISCV_SUBW, RISCV_SLLW, RISCV_SRLW, RISCV_SRAW} /* reg-reg 32-bit ops */
enum amoop = {AMOSWAP, AMOADD, AMOXOR, AMOAND, AMOOR, AMOMIN, AMOMAX, AMOMINU, AMOMAXU} /* AMO ops */
enum csrop = {CSRRW, CSRRS, CSRRC}
enum word_width = {BYTE, HALF, WORD, DOUBLE}

/* Ideally these would be sail builtin */

function shift_right_arith64 (v : bits(64), shift : bits(6)) -> bits(64) =
    let v128 : bits(128) = EXTS(v) in
    (v128 >> shift)[63..0]

function shift_right_arith32 (v : bits(32), shift : bits(5)) -> bits(32) =
    let v64 : bits(64) = EXTS(v) in
    (v64 >> shift)[31..0]
