default Order dec

$include <prelude.sail>

$iftarget c
$c_in_main sail_config_set_file("config_struct.json");
$c_in_main_post sail_config_cleanup();
$else
$option --config ../c/config_struct.json
$endif

struct S1('n) = {
  foo : bits('n),
  bar : string,
}

struct S2 = {
  foo : bits(32),
  bar : string,
}

val main : unit -> unit

function main() = {
  let x : S1(32) = config c1;
  let y : S2 = config c1;
  print_bits("x.foo = ", x.foo);
  print_endline(x.bar);
}
