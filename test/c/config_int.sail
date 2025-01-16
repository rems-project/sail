default Order dec

$include <prelude.sail>

$iftarget c
$c_in_main sail_config_set_file("config_int.json");
$c_in_main_post sail_config_cleanup();
$else
$option --config ../c/config_int.json
$endif

$option --sv-int-size 256

val main : unit -> unit

function main() = {
  let x : range(0, 64) = config c1;
  print_int("x = ", x);
  let y : range(0, 1) = config c2;
  print_int("y = ", y);
  let z : int = config c3;
  print_int("z = ", z);
  let w : {'n, 'n >= 0. int('n)} = config c4;
  print_int("w = ", w);
}
