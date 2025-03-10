default Order dec

$include <prelude.sail>

$iftarget c
$c_in_main sail_config_set_file("config_test.json");
$c_in_main_post sail_config_cleanup();
$else
$option --config ../c/config_test.json
$endif

$iftarget systemverilog
$option --sv-int-size 256
$endif

val main : unit -> unit

function main() = {
    print_endline(config hello.world);
    print_int("n = ", config hello.number : int);
    print_bits("bv = ", config hello.bits : bits(5));
}
