default Order dec

$include <prelude.sail>

$iftarget c cpp
$c_in_main sail_config_set_file("config_issue1498.json");
$c_in_main_post sail_config_cleanup();
$else
$option --config ../c/config_issue1498.json
$endif

type xlen : Int = config base.xlen
let xlen = sizeof(xlen)
constraint xlen >= 1

type xlenbits = bits(xlen)

constraint xlen <= 32

$option --c-preserve foo

function foo(s : xlenbits) -> unit = {
  assert(s == sail_zeros(sizeof(xlen)))
}

function main() -> unit = print_endline("ok")
