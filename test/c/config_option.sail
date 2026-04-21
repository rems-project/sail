default Order dec
$include <prelude.sail>

$iftarget c cpp
$c_in_main sail_config_set_file("config_option.json");
$c_in_main_post sail_config_cleanup();
$else
$option --config ../c/config_option.json
$endif

enum E = { A, B }

struct S = {
  field1 : int,
  field2 : option(E),
}

let s : S = config cfg_struct

val main : unit -> unit

function main() = {
  print_int("", s.field1)
}
