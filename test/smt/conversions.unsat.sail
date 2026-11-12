default Order dec

$include <prelude.sail>

/* Counting zeros, get_slice_int and set_slice_bits, at fixed and variable
   widths, with negative and out-of-range offsets. */
$property
function prop(x : bits(8), a : bits(3), mb : bits(12), sb : bits(6)) -> bool = {
  let z = sail_zero_extend(x, 8 + unsigned(a));
  let p1 = count_leading_zeros(z) == count_leading_zeros(x) + unsigned(a);
  let p2 = count_trailing_zeros(z) == (if x == 0x00 then length(z) else count_trailing_zeros(x));
  let m = signed(mb);
  let o = signed(sb);
  let r : bits(8) = get_slice_int(8, m, o);
  let p3 = unsigned(r) == (if o >= 0 then emod_int(ediv_int(m, pow2(o)), 256) else emod_int(m * pow2(0 - o), 256));
  let out = sail_zero_extend(x, 16);
  let s = set_slice_bits(16, 4, out, o, 0xF);
  let M = sail_shiftleft(0x000F, o);
  let p4 = s == (out | M);
  p1 & p2 & p3 & p4
}
