default Order dec

$include <vector_dec.sail>

$property
function prop(xs: bits(65), ys: bits(5)) -> bool = {
  xs' = xs;
  xs'[63..59] = ys;
  xs'[46..42] = ys;
  xs'[4..0] = ys;
  xs'[63..59] == ys & xs'[46..42] == ys & xs'[4..0] == ys
}
