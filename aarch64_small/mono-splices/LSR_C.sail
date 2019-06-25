val LSR_C : forall 'N 'S, 'N >= 1 & 'S >= 1.
  (bits('N), int('S)) -> (bits('N), bit) effect pure

function LSR_C (x, shift) = {
  result : bits('N) = x >> shift;
  carry_out : bit = if shift > 'N then bitzero else x[shift - 1];
  return((result, carry_out))
}
