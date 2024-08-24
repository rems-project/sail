default Order dec

$include <prelude.sail>
$include <string.sail>

register R1 : bits(32)
register R2 : bits(32)
register R3 : bits(32)
register R4 : bits(32)
register R5 : bits(32)
register R6 : bits(32)
register R7 : bits(32)
register R8 : bits(32)
register R9 : bits(32)
register R10 : bits(32)
register R11 : bits(32)
register R12 : bits(32)
register R13 : bits(32)
register R14 : bits(32)
register R15 : bits(32)

$[jib_debug]
function set_R(r : bits(4), x : bits(32)) -> unit = {
    match r {
        0x0 => (), // zero register
        0x1 => R1 = x,
        0x2 => R2 = x,
        0x3 => R3 = x,
        0x4 => R4 = x,
        0x5 => R5 = x,
        0x6 => R6 = x,
        0x7 => R7 = x,
        0x8 => R8 = x,
        0x9 => R9 = x,
        0xA => R10 = x,
        0xB => R11 = x,
        0xC => R12 = x,
        0xD => R13 = x,
        0xE => R14 = x,
        0xF => R15 = x,
    }
}

function get_R(r : bits(4)) -> bits(32) = {
    match r {
        0x0 => 0x0000_0000,
        0x1 => R1,
        0x2 => R2,
        0x3 => R3,
        0x4 => R4,
        0x5 => R5,
        0x6 => R6,
        0x7 => R7,
        0x8 => R8,
        0x9 => R9,
        0xA => R10,
        0xB => R11,
        0xC => R12,
        0xD => R13,
        0xE => R14,
        0xF => R15,
    }
}

overload R = {set_R, get_R}

enum iop = {OP_ADD, OP_SUB}

val itype : (bits(12), bits(4), bits(4), iop) -> unit

function itype(imm, rs1, rd, op) = {
    R(rd) = R(rs1)
}

val main : unit -> unit

function main() = {
    itype(0x000, 0xA, 0xB, OP_ADD);
    print_endline("ok")
}
