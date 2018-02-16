val SignExtend__0 : forall ('M : Int) ('N : Int), 'M >= 0 & 'N >= 0.
  (bits('M), atom('N)) -> bits('N) effect {escape}

function SignExtend__0 (x, N) = {
  assert('N >= 'M);
  return(extsv(x))
}
