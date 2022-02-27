default Order dec

$include <prelude.sail>

let x: int = {
  var y: int = 3;
  y = y + 1;
  y
}
