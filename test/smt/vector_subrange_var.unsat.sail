default Order dec

$include <prelude.sail>

/* A subrange with a variable start has the length of the range, not the
   length of the bitvector. */
$property
function prop(x : bits(16), b : bits(4), c : bits(2)) -> bool = {
  let u = unsigned(b);
  let lo : range(0, 12) = if u > 12 then 12 else u;
  let w : range(1, 4) = unsigned(c) + 1;
  let r = x[lo + w - 1 .. lo];
  length(r) == w & unsigned(r) == emod_int(ediv_int(unsigned(x), pow2(lo)), pow2(w))
}
