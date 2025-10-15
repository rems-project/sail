default Order inc

$include <prelude.sail>

val foo : bits(20) -> unit

function foo imm[19] @ imm[1..9] @ imm[10] @ imm[11..18] = {
    print_bits("imm = ", imm)
}

val main : unit -> unit

function main() = {
    foo(0xABCDE)
}
