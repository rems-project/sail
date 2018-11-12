val FPMin : forall ('N : Int), 'N >= 0 & 'N >= 0 & 32 >= 0 & 'N >= 0.
  (bits('N), bits('N), bits(32)) -> bits('N) effect {escape, rreg, undef, wreg}
val FPMinNum : forall ('N : Int), 'N >= 0 & 'N >= 0 & 32 >= 0 & 'N >= 0.
  (bits('N), bits('N), bits(32)) -> bits('N) effect {escape, rreg, undef, wreg}
val FPMax : forall ('N : Int), 'N >= 0 & 'N >= 0 & 32 >= 0 & 'N >= 0.
  (bits('N), bits('N), bits(32)) -> bits('N) effect {escape, rreg, undef, wreg}
val FPMaxNum : forall ('N : Int), 'N >= 0 & 'N >= 0 & 32 >= 0 & 'N >= 0.
  (bits('N), bits('N), bits(32)) -> bits('N) effect {escape, rreg, undef, wreg}
val FPAdd : forall ('N : Int), 'N >= 0 & 'N >= 0 & 32 >= 0 & 'N >= 0.
  (bits('N), bits('N), bits(32)) -> bits('N) effect {escape, rreg, undef, wreg}

enum ReduceOp = {
  ReduceOp_FMINNUM,
  ReduceOp_FMAXNUM,
  ReduceOp_FMIN,
  ReduceOp_FMAX,
  ReduceOp_FADD,
  ReduceOp_ADD
}
register FPCR : bits(32)


val Reduce : forall ('N : Int) ('esize : Int), 'N >= 0 & 'esize >= 0.
  (ReduceOp, bits('N), atom('esize)) -> bits('esize) effect {escape, rreg, undef, wreg}

function Reduce (op, input, esize) = {
  hi : bits('esize) = undefined;
  lo : bits('esize) = undefined;
  result : bits('esize) = undefined;
  if 'N == 'esize then return(input) else ();
  let 'half = 'N / 2;
  assert(constraint('half * 2 = 'N));
  hi = Reduce(op, slice(input, half, negate(half) + 'N), 'esize);
  lo = Reduce(op, slice(input, 0, half), 'esize);
  match op {
    ReduceOp_FMINNUM => result = FPMinNum(lo, hi, FPCR),
    ReduceOp_FMAXNUM => result = FPMaxNum(lo, hi, FPCR),
    ReduceOp_FMIN => result = FPMin(lo, hi, FPCR),
    ReduceOp_FMAX => result = FPMax(lo, hi, FPCR),
    ReduceOp_FADD => result = FPAdd(lo, hi, FPCR),
    ReduceOp_ADD => result = lo + hi
  };
  return(result)
}
