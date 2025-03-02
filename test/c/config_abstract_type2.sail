default Order dec
$include <prelude.sail>

$option --abstract-types

type xlen : Int = config arch.xlen

constraint xlen >= 0

// This test is similar to abstract_type.sail, but instantiating the
// type from the configuration file rather than the command line.
$iftarget c
$c_in_main sail_config_set_file("config_abstract_type.json");
$c_in_main sail_set_abstract_xlen();
$c_in_main_post sail_config_cleanup();
$else
$option --config ../c/config_abstract_type.json
$endif

register R : bits(xlen)

val main : unit -> unit

function main() = {
    let v : bits(xlen) = config registers.R.init;

    if sizeof(xlen) == 32 then {
        R = v
    } else {
        R = sail_mask(sizeof(xlen), 0x6464_6464_6464_6464)
    };

    print_bits("R = ", R)
}
