default Order dec

$include <prelude.sail>

register R : bool = true

function main() -> unit = {
  var x : int = 3;
  var y : int = 3;
  if R then {
    x = x + 1
  };
  y = y + 1;
  print_int("y = ", y);
  x = y;
  print_int("x = ", x);
}
