
type regval = bits(64)

type regno ('n : Int), 0 <= 'n < 32 = atom('n)
type regbits = bits(5)

val cast regbits_to_regno : bits(5) -> {'n, 0 <= 'n < 32. regno('n)}
function regbits_to_regno b = let 'r = unsigned(b) in r

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

val wGPR : forall 'n, 0 <= 'n < 32. (regno('n), regval) -> unit effect {wreg}

function wGPR (r, v) = 
  if (r != 0) then {
     (*GPRs[r - 1]) = v;
     print_int("GPR ", r);
     print_bits("<- ", v);
  }

function check_alignment (addr : bits(64), width : atom('n)) -> forall 'n. unit =
  if unsigned(addr) % width != 0 then throw(Error_misaligned_access) else ()

val MEMr : forall 'n. (bits(64), atom('n)) -> bits(8 * 'n) effect {rmem}
function MEMr (addr, width) = __RISCV_read(addr, width)

scattered union ast

val decode : bits(32) -> option(ast) effect pure
scattered function decode

val execute : ast -> unit effect {rmem, rreg, wreg}
scattered function execute

/* ****************************************************************** */

/* ADDI */
union clause ast = ITYPE : (bits(12), regbits, regbits)

function clause decode imm : bits(12) @ rs1 : regbits @ 0b000 @ rd : regbits @ 0b0010011 = Some(ITYPE(imm, rs1, rd))

function clause execute (ITYPE (imm, rs1, rd)) =
  let rs1_val = rGPR(rs1) in
  let imm64 : bits(64) = EXTS(imm) in
  let result : bits(64) = rs1_val + imm64 in
  wGPR(rd, result)


/* ****************************************************************** */

/* Load double */
union clause ast = LOAD : (bits(12), regbits, regbits)

function clause decode imm : bits(12) @ rs1 : regbits @ 0b011 @ rd : regbits @ 0b0000011 = Some(LOAD(imm, rs1, rd))

function clause execute(LOAD(imm, rs1, rd)) =
    let addr : bits(64) = rGPR(rs1) + EXTS(imm) in
    let result : bits(64) = MEMr(addr, 8) in
    wGPR(rd, result)

function clause decode _ = None

end ast
end decode
end execute
