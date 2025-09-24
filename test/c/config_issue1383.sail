default Order dec

$include <prelude.sail>

$iftarget c cpp
$c_in_main sail_config_set_file("config_issue1383.json");
$c_in_main_post sail_config_cleanup();
$else
$option --config ../c/config_issue1383.json
$endif

type foo : Int = config foo
let foo = sizeof(foo)
constraint foo >= 1
constraint foo <= 8

val main : unit -> unit

function main() = {
  print_endline("ok")
}
