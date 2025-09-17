default Order dec

$include <prelude.sail>

$iftarget c cpp
$c_in_main sail_config_set_file("config_let.json");
$c_in_main_post sail_config_cleanup();
$else
$option --config ../c/config_let.json
$endif

let x : int = config y

function main() -> unit = {
  print_int("x = ", x)
}
