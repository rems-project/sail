default Order dec

$include <prelude.sail>

$option --config ../typecheck/pass/config_bits_types.json

type xlen = 32

val main : unit -> unit

function main() = {
    let _ : bits(64) = config c1;
    let _ : bits(3) = config c2;
    let _ : {'n, 'n >= 0. bits('n)} = config c3;
    let _ : {'n, xlen >= 'n > 0 | 'n == 64. bits('n)} = config c4;
}
