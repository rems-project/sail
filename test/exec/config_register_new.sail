default Order dec

$include <prelude.sail>

$iftarget c cpp
$c_in_main sail_config_set_file("config_register_new.json");
$c_in_main_post sail_config_cleanup();
$else
$option --config ../c/config_register_new.json
$endif

register x : int = config y

function main() -> unit = {
  print_int("x = ", x)
}
