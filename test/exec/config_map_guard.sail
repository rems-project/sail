default Order dec

$include <prelude.sail>

$iftarget c cpp
$c_in_main sail_config_set_file("config_map_guard.json");
$c_in_main_post sail_config_cleanup();
$else
$option --config ../c/config_map_guard.json
$endif

struct S = {
  num : int,
  flag : bool
}

val foo : int <-> S

mapping foo = {
  x <-> struct { num = x, flag = true } when (config bar : bool),
  x <-> struct { num = x, flag = false },
}

val main : unit -> unit

function main() = {
  if foo(2).flag then {
    print_endline("ok")
  }
}
