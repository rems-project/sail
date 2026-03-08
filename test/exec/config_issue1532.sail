default Order dec

$include <prelude.sail>

$iftarget c cpp
$c_in_main sail_config_set_file("config_issue1532.json");
$c_in_main_post sail_config_cleanup();
$else
$option --config ../c/config_issue1532.json
$endif

type xlen : Int = config base.xlen

constraint xlen >= 1

$[jib_debug]
function identity(x : bits(xlen)) -> bits(xlen) = x

constraint xlen <= 32

function main() -> unit = {
  let x : bits(xlen) = sail_ones(sizeof(xlen));
  print_endline(bits_str(identity(x)));
  print_endline(bits_str(identity(x)));
}
