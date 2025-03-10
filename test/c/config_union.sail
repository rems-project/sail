default Order dec

$include <prelude.sail>
$include <option.sail>

$iftarget c
$c_in_main sail_config_set_file("config_union.json");
$c_in_main_post sail_config_cleanup();
$else
$option --config ../c/config_union.json
$endif

val main : unit -> unit

function main() = {
  let x : option(int) = config c1;
  match x {
    Some(n) => print_int("n = ", n),
    None()  => (),
  };
  let y : option(string) = config c2;
  match y {
    Some(_) => (),
    None() => print_endline("None"),
  }
}
