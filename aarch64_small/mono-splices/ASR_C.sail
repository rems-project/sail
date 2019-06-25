val ASR_C : forall 'N 'S, 'N >= 1 & 'S >= 1.
  (bits('N), int('S)) -> (bits('N), bit) effect {escape}

function ASR_C (x, shift) = {
  result : bits('N) = sail_arith_shiftright(x, shift);
  carry_out : bit = if shift > 'N then x['N - 1] else x[shift - 1];
  return((result, carry_out))
}
