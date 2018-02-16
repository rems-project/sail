val LSL_C : forall ('N : Int), 'N >= 0 & 'N >= 0 & 1 >= 0.
  (bits('N), int) -> (bits('N), bits(1)) effect {escape}

function LSL_C (x, shift) = {
  assert(shift > 0, "(shift > 0)");
  result : bits('N) = x << shift;
  carry_out : bits(1) = if shift > 'N then 0b0 else [x['N - shift]];
  return((result, carry_out))
}
