default Order dec

$include <prelude.sail>

function test(() : unit, i : int) -> int = i

function main() -> unit = {
  var i : int = 0;
  let j = test(i = i + 1, i);
  print_int("j = ", j)
}
