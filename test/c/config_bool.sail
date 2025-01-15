default Order dec

$include <prelude.sail>

$iftarget c
$c_in_main sail_config_set_file("config_bool.json");
$c_in_main_post sail_config_cleanup();
$else
$option --config ../c/config_bool.json
$endif

val main : unit -> unit

function main() = {
  if config some.boolean then {
    print_endline("Hello, World!")
  }
}
