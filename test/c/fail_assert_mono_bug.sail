default Order dec

$include <prelude.sail>

union exception = {
    E_anything: unit
}

type xlen: Int = 32

val test : forall 'n, 'n > 0. bits('n) -> bits('n) effect {escape}

function test(_) = {
    assert(sizeof(xlen) == 64, "64-bit only");
    0x0000_0000_0000_0000
}

val main : unit -> unit effect {escape}

function main() = {
    let _ = test(0xFFFF_FFFF);
    ()
}