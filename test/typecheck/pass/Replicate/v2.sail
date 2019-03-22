default Order dec

$include <prelude.sail>

overload operator / = {tdiv_int}
overload operator % = {tmod_int}

val Replicate : forall ('M : Int) ('N : Int), 'M >= 1.
  (implicit('N), bits('M)) -> bits('N) effect {escape}

function Replicate (N, x) = {
    assert('N % 'M == 0);
    replicate_bits(x, 'N / 'M)
}