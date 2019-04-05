default Order dec

$include <prelude.sail>

register R : bits(64)

function check_sat((): unit) -> bool = {
  let x = sail_shiftright(R, 63);
  not_bool(x == 0x0000_0000_0000_0000)
}