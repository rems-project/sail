val ZeroExtend__0 : forall ('M : Int) ('N : Int), 'M >= 0 & 'N >= 0.
  (bits('M), atom('N)) -> bits('N) effect {escape}

function ZeroExtend__0 (x, N) = {
  assert(true);
  extzv(x)
}