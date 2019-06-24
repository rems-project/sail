val LSL_C : forall 'N 'S, 'N >= 0 & 'S >= 1.
  (bits('N), int('S)) -> (bits('N), bits(1)) effect pure

function LSL_C (x, shift) = {
  result : bits('N) = x << shift;
  carry_out : bits(1) = if shift > 'N then 0b0 else [x['N - shift]];
  return((result, carry_out))
}
