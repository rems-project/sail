default Order dec

$include <prelude.sail>

union two_bitvectors('n : Int) = {
    BV1 : bits('n),
    BV2 : bits('n),
}

val get_value32 : two_bitvectors(32) -> bits(32)

function get_value32(tbv) = {
    match tbv {
        BV1(bs) => bs,
        BV2(bs) => bs,
    }
}

register R : bits(32)

val test : forall 'n. bits('n) -> unit

function test(bv) = {
    let x : two_bitvectors('n) = BV2(bv);
    if length(bv) == 32 then {
        R = get_value32(x);
    }
}

val main : unit -> unit

function main() = {
    test(0xABCD_0000);
    print_endline("ok")
}
