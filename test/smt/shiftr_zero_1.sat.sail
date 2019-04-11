default Order dec

$include <prelude.sail>

register R : bits(64)

$property
function prop((): unit) -> bool = {
  let x = sail_shiftright(R, 63);
  x == 0x0000_0000_0000_0000
}