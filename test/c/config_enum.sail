default Order dec

$include <prelude.sail>
$include <option.sail>

$iftarget c
$c_in_main sail_config_set_file("config_enum.json");
$c_in_main_post sail_config_cleanup();
$else
$option --config ../c/config_enum.json
$endif

enum E = {A, B, C}

val main : unit -> unit

function main() = {
  let x : E = config some.member;
  match x {
    A => print_endline("A"),
    B => print_endline("B"),
    C => print_endline("C"),
  }
}
