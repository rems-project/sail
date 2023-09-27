default Order dec

$include <prelude.sail>
$include <generic_equality.sail>
$include <string.sail>

$option -undefined_gen

val split : forall 'n 'm, 'n * 'm == 64 & 'n in {1, 2, 4, 8}. (int('n), int('m), bits(64)) -> vector('n, dec, bits('m)) effect {undef}

function split(n, m, bv) = {
    var result: vector('n, dec, bits('m)) = undefined;

    foreach (i from 0 to (n - 1)) {
        result[i] = sail_shiftright(bv, i * m)[m - 1 .. 0]
    };

    result
}

val main : unit -> unit effect {escape, undef}

function main() = {
    assert(split(8,  8, 0xAAAABBBBCCCCDDDD) == [0xAA, 0xAA, 0xBB, 0xBB, 0xCC, 0xCC, 0xDD, 0xDD]);
    assert(split(4, 16, 0xAAAABBBBCCCCDDDD) == [0xAAAA, 0xBBBB, 0xCCCC, 0xDDDD]);
    assert(split(2, 32, 0xAAAABBBBCCCCDDDD) == [0xAAAABBBB, 0xCCCCDDDD]);
    assert(split(1, 64, 0xAAAABBBBCCCCDDDD) == [0xAAAABBBBCCCCDDDD]);

    assert(split(4, 16, 0xAAAABBBBCCCCDDDD) != [0xDDDD, 0xCCCC, 0xBBBB, 0xAAAA]);

    print_endline("ok");
}
