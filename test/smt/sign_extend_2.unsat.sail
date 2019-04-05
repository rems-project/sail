default Order dec

$include <prelude.sail>

function check_sat(xs: bits(16)) -> bool = {
  var p: bool = true;
  if xs[15] == bitzero then {
    p = 0x0000 @ xs == sail_sign_extend(xs, 32);
  } else {
    p = 0xFFFF @ xs == sail_sign_extend(xs, 32);
  };
  not_bool(p)
}