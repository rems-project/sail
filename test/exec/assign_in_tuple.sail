default Order dec

$include <prelude.sail>

function main() -> unit = {
  var i : int = 0;
  let (_, j) = (i = i + 1, i);
  print_int("j = ", j)
}
