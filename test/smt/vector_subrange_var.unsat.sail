default Order dec

$include <prelude.sail>

/* A subrange with a variable start has the length of the range, not the
   length of the bitvector. */
$property
function prop(x : bits(16), b : bits(4)) -> bool = {
  let u = unsigned(b);
  let lo : range(0, 12) = if u > 12 then 12 else u;
  let r = x[lo + 3 .. lo];
  length(r) == 4 & unsigned(r) == emod_int(ediv_int(unsigned(x), pow2(lo)), 16)
}
