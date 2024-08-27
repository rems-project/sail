default Order dec

$include <prelude.sail>

$property
function prop() -> bool = {
  let x = 0b00;
  let y = [x[0]];
  let z = 0b01;
  let w = [z[0]];
  y == 0b0 & w == 0b1
}
