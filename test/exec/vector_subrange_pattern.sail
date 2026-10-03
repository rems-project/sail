default Order dec

$include <prelude.sail>

val foo : bits(8) -> unit

function foo imm[3..0] @ imm[7..4] = print_bits("imm = ", imm)

val bar : bits(16) -> unit

function bar imm1[3..0] @ imm1[7..4] @ imm2[7..4] @ imm2[3..0] = {
    print_bits("imm1 = ", imm1);
    print_bits("imm2 = ", imm2);
}

val main : unit -> unit

function main() = {
    foo(0xAB);
    bar(0xABCD);
}
