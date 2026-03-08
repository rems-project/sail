default Order dec

$include <prelude.sail>

val zero_extend : forall 'n 'm, 'n >= 0 & 'm >= 'n. (implicit('m), bits('n)) -> bits('m)

function zero_extend(m, bv) = sail_zero_extend(bv, m)

type regidx = bits(1)

register X : bits(16)
register Y : bits(16)

val get_R : regidx -> bits(16)

function get_R(0b0) = X
and      get_R(0b1) = Y

val set_R : (regidx, bits(16)) -> unit

function set_R(0b0, v) = X = v
and      set_R(0b1, v) = Y = v

overload R = {get_R, set_R}

union instruction_format = {
    AType : { opcode : bits(4), rd : regidx, r1 : regidx, r2 : regidx },
    BType : { opcode : bits(2), rd : regidx, r1 : regidx, imm : bits(3) }
}

mapping encdec_format : bits(8) <-> instruction_format = {
    0b0 @ opcode : bits(4) @ rd : regidx @ r1 : regidx @ r2 : regidx <-> AType(struct { opcode, rd, r1, r2 }),
    0b1 @ opcode : bits(2) @ rd : regidx @ r1 : regidx @ imm : bits(3) <-> BType(struct { opcode, rd, r1, imm })
}

scattered union instr

val execute : instr -> unit

scattered function execute

val encdec : instruction_format <-> instr

scattered mapping encdec

/*!
The ADD instruction
*/
union clause instr = ADD : { rd : regidx, r1 : regidx, r2 : regidx }

mapping clause encdec =
    AType(struct { opcode = 0b0000, rd, r1, r2 }) <-> ADD(struct { rd, r1, r2 })

function clause execute(ADD(struct { rd, r1, r2 })) = {
    R(rd) = R(r1) + R(r2)
}

/*!
The AND instruction. Compute the logical and of two registers `r1` and
`r2`, placing the result in `rd`.
*/
union clause instr = AND : { rd : regidx, r1 : regidx, r2 : regidx }

mapping clause encdec =
    AType(struct { opcode = 0b0001, rd, r1, r2 }) <-> AND(struct { rd, r1, r2 })

function clause execute(AND(struct { rd, r1, r2 })) = {
    R(rd) = R(r1) & R(r2)
}

/*!
The ADDI instruction. Add an immediate value to r1 and place the result in rd
*/
union clause instr = ADDI : (regidx, regidx, bits(3))

mapping clause encdec =
    BType(struct { opcode = 0b00, rd, r1, imm }) <-> ADDI(rd, r1, imm)

function clause execute(ADDI(rd, r1, imm)) = {
    R(rd) = R(r1) + zero_extend(imm)
}

val main : unit -> unit

function main() = {
    execute(ADDI(0b0, 0b0, 0b111));
    print_bits("X = ", X);
    execute(ADDI(0b1, 0b0, 0b001));
    print_bits("Y = ", Y);
    execute(AND(struct { rd = 0b0, r1 = 0b0, r2 = 0b1 }));
    print_bits("X = ", X);
    execute(ADD(struct { rd = 0b1, r1 = 0b1, r2 = 0b1 }));
    print_bits("Y = ", Y);
}
