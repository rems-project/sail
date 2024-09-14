default Order dec
$include <prelude.sail>

$option --abstract-types

type xlen : Int

constraint xlen in {32, 64}

// If we are generating C, then we can instantiate the abstract
// type at runtime in the main function (in a kind-of hacky way
// here to make this work as a single file test case).
//
// Otherwise, use the --instantiate flag to set it at build time.
$iftarget c
$c_in_main sail_set_abstract_xlen(32);
$else
$option --instantiate xlen=32
$endif

register R : bits(xlen)

val main : unit -> unit

function main() = {
    if sizeof(xlen) == 32 then {
        R = 0x3232_3232
    } else {
        R = 0x6464_6464_6464_6464
    };

    print_bits("R = ", R)
}
