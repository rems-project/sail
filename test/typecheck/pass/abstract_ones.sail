default Order dec

$include <prelude.sail>

$option --abstract-types
$option --instantiate xlen=32

type xlen : Int

constraint xlen in {32, 64}

val main : unit -> unit

function main() = {
    let x : bits(xlen) = sail_ones(sizeof(xlen));
}
