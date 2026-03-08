default Order dec

$include <prelude.sail>

$[test]
function test_0() -> unit = {
  print_endline("test_0");
}

$[test]
val test_1 : unit -> unit

function test_1() = {
  print_endline("test_1");
}

$[test]
val test_2 : unit -> unit

function test_2() -> unit = {
  print_endline("test_2");
}

$c_in_main_post model_test();

$iftarget c cpp

function main() -> unit = {
  print_endline("ok");
}

$else

function main() -> unit = {
  print_endline("ok");
  print_endline("Testing test_0");
  print_endline("test_0");
  print_endline("Pass");
  print_endline("Testing test_1");
  print_endline("test_1");
  print_endline("Pass");
  print_endline("Testing test_2");
  print_endline("test_2");
  print_endline("Pass");
}

$endif
