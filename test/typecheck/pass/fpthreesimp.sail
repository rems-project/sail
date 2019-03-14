default Order dec

$include <prelude.sail>

val Zeros : forall 'N, 'N >= 0. int('N) -> bits('N)

type FPExponent ('N : Int) = {'E, ('N == 16 & 'E == 5) | ('N == 32 & 'E == 8) | ('N == 64 & 'E == 11). int('E)}

val FPThree : forall 'N, 'N in {16, 32, 64}. (implicit('N), bits(1)) -> bits('N)

function FPThree(N, sign) = {
  let E : FPExponent('N) = if 'N == 16 then 5 else if 'N == 32 then 8 else 11;
  sign @ 0b1 @ Zeros(E - 1) @ 0b1 @ Zeros('N - E - 2)
}