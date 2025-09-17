default Order dec
$include <prelude.sail>

$iftarget c cpp
$c_in_main sail_config_set_file("config_abstract_clash.json");
$c_in_main_post sail_config_cleanup();
$else
$option --config ../c/config_abstract_clash.json
$endif

type xlen : Int = config base.xlen
let xlen = sizeof(xlen)

function main() -> unit = {
  print_endline(dec_str(xlen));
}
