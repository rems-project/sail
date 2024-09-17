default Order dec

$include <prelude.sail>

$option --abstract-types
$option --instantiate xlen=32

type xlen : Int

constraint xlen in {32, 64}

val foo : unit -> {'n, 0 < 'n <= 32. int('n)}

val main : unit -> unit

function main() = {
    let x : bits(xlen) = sail_zero_extend(sail_ones(foo()), sizeof(xlen));
}
