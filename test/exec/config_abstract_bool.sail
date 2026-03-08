default Order dec

$include <prelude.sail>

$iftarget c cpp
$c_in_main sail_config_set_file("config_abstract_bool.json");
$c_in_main_post sail_config_cleanup();
$else
$option --config ../c/config_abstract_bool.json
$endif

type have_ext : Bool = config have.ext

type bits_conf = bits(if have_ext then 4 else 5)

register R : bits_conf

val main : unit -> unit

function main() = {
  let x = R;
  if length(x) == 4 then {
    R = 0xF;
    print_bits("R = ", R)
  }
}
