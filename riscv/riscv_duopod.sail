
type xlen = atom(64)
type xlen_t = bits(64)

type regno ('n : Int), 0 <= 'n < 32 = atom('n)
type regbits = bits(5)

val cast regbits_to_regno : bits(5) -> {'n, 0 <= 'n < 32. regno('n)}
function regbits_to_regno b = let r as atom(_) = unsigned(b) in r

/* Architectural state */

register PC : xlen_t
register nextPC : xlen_t

register Xs : vector(32, dec, xlen_t)

/* Getters and setters for X registers (special case for zeros register, x0) */
val rX : forall 'n, 0 <= 'n < 32. regno('n) -> xlen_t effect {rreg}

function rX 0 = 0x0000000000000000
and rX (r if r > 0) = Xs[r]

val wX : forall 'n, 0 <= 'n < 32. (regno('n), xlen_t) -> unit effect {wreg}

function wX (r, v) =
  if (r != 0) then {
     Xs[r] = v;
  }

overload X = {rX, wX}

/* Accessors for memory */

val MEMr : forall 'n. (xlen_t, atom('n)) -> bits(8 * 'n) effect {rmem}
function MEMr (addr, width) = __RISCV_read(addr, width)

/* Instruction decode and execute */
enum iop = {RISCV_ADDI, RISCV_SLTI, RISCV_SLTIU, RISCV_XORI, RISCV_ORI, RISCV_ANDI} /* immediate ops */
scattered union ast

val decode : bits(32) -> option(ast) effect pure
scattered function decode

val execute : ast -> unit effect {rmem, rreg, wreg}
scattered function execute

/* ****************************************************************** */

/* ADDI */

union clause ast = ITYPE : (bits(12), regbits, regbits, iop)

function clause decode imm : bits(12) @ rs1 : regbits @ 0b000 @ rd : regbits @ 0b0010011
  = Some(ITYPE(imm, rs1, rd, RISCV_ADDI))

function clause execute (ITYPE (imm, rs1, rd, RISCV_ADDI)) =
  let rs1_val = X(rs1) in
  let imm_ext : xlen_t = EXTS(imm) in
  let result = rs1_val + imm_ext in
  X(rd) = result

/* ****************************************************************** */

/* Load double */
union clause ast = LOAD : (bits(12), regbits, regbits)

function clause decode imm : bits(12) @ rs1 : regbits @ 0b011 @ rd : regbits @ 0b0000011
  = Some(LOAD(imm, rs1, rd))

function clause execute(LOAD(imm, rs1, rd)) =
    let addr : xlen_t = X(rs1) + EXTS(imm) in
    let result : xlen_t = MEMr(addr, 8) in
    X(rd) = result

/* ****************************************************************** */

function clause decode _ = None()

end ast
end decode
end execute
