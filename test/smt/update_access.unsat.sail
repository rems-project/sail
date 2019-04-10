default Order dec

$include <vector_dec.sail>

function check_sat(xs: bits(65), x: bit) -> bool = {
  ys = xs;
  ys[63] = x;
  ys[64] = x;
  ys[42] = x;
  ys[0] = x;
  not_bool(ys[64] == x & ys[63] == x & ys[42] == x & ys[0] == x)
}