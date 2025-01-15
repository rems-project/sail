default Order dec

$include <prelude.sail>

$iftarget c
$c_in_main sail_config_set_file("config_unit.json");
$c_in_main_post sail_config_cleanup();
$else
$option --config ../c/config_unit.json
$endif

val main : unit -> unit

function main() = {
  let x : unit = config c1;
  print_endline("ok")
}
