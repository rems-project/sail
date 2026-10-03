default Order dec

$include <prelude.sail>

function main((): unit) -> unit = {
  let x = sail_sign_extend(0xFF, 32);
  let y = sail_zero_extend(x, 64);
  print_bits("x = ", x);
  print_bits("y = ", y)
}