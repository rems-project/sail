val ASR_C : forall ('N : Int), 'N >= 0 & 'N >= 0 & 1 >= 0.
  (bits('N), int) -> (bits('N), bits(1)) effect {escape}

function ASR_C (x, shift) = {
  assert(shift > 0, "(shift > 0)");
  result : bits('N) = arith_shiftright(x, shift);
  carry_out : bits(1) = if shift > 'N then [x['N - 1]] else [x[shift - 1]];
  return((result, carry_out))
}
