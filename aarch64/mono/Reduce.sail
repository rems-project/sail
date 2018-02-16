val Reduce : forall ('N : Int) ('esize : Int), 'N >= 0 & 'esize >= 0.
  (ReduceOp, bits('N), atom('esize)) -> bits('esize) effect {escape, rreg, undef, wreg}

function Reduce (op, input, esize) = {
  result : bits('esize) = input['esize - 1 .. 0];
  if 'N > 'esize then
    foreach (i from 'esize to ('N - 1) by 'esize) {
      operand : bits('esize) = input[i+'esize - 1 .. i];
      match op {
        ReduceOp_FMINNUM => result = FPMinNum(result, operand, FPCR),
        ReduceOp_FMAXNUM => result = FPMaxNum(result, operand, FPCR),
        ReduceOp_FMIN => result = FPMin(result, operand, FPCR),
        ReduceOp_FMAX => result = FPMax(result, operand, FPCR),
        ReduceOp_FADD => result = FPAdd(result, operand, FPCR),
        ReduceOp_ADD => result = result + operand
      };
    };
  return(result)
}
