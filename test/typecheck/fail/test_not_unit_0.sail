default Order dec

$include <prelude.sail>

$[test]
function test_good() -> unit = {
  print_endline("test_good");
}

$[test]
function test_bad() -> int = 5

function main() -> unit = ()
