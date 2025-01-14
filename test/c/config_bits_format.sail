default Order dec

$include <prelude.sail>

$iftarget c
$c_in_main sail_config_set_file("config_bits_format.json");
$c_in_main_post sail_config_cleanup();
$else
$option --config ../c/config_bits_format.json
$endif

val main : unit -> unit

function main() = {
  let x : bits(16) = config c1;
  let y : bits(16) = config c2;
  let z : bits(16) = config c3;
  let w : bits(16) = config c4;
  print_bits("xyzw = ", x @ y @ z @ w)
}
