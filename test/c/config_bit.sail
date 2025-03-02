default Order dec

$include <prelude.sail>

$iftarget c
$c_in_main sail_config_set_file("config_bit.json");
$c_in_main_post sail_config_cleanup();
$else
$option --config ../c/config_bit.json
$endif

val main : unit -> unit

function main() = {
  if config some.single_bit == bitone then {
    print_endline("Hello, World!")
  }
}
