default Order dec

$include <prelude.sail>

val foo : bits(20) -> unit

function foo imm[19] @ imm[9..0] @ imm[10] @ imm[18..11] = {
    print_bits("imm = ", imm)
}

val main : unit -> unit

function main() = {
    foo(0xABCDE)
}
