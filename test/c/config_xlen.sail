default Order dec

$iftarget c cpp
$c_in_main sail_config_set_file("config_xlen.json");
$c_in_main_post sail_config_cleanup();
$else
$option --config ../c/config_xlen.json
$endif

$include <prelude.sail>

type xlen : Int = config xlen

constraint xlen in {32, 64}

register bar : bits(xlen)

val foo : unit -> range(0, 11)

function foo() = config foo

val main : unit -> unit

function main() = {
  print_int("foo = ", foo())
}
