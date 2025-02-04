default Order dec

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

function main() -> unit = {
  print_endline("ok");
}
