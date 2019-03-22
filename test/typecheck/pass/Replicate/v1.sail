default Order dec

$include <smt.sail>
$include <prelude.sail>

overload operator / = {ediv_int}
overload operator % = {emod_int}

val Replicate : forall ('M : Int) ('N : Int), 'M >= 0.
  (implicit('N), bits('M)) -> bits('N) effect {escape}

function Replicate (N, x) = {
    assert('N % 'M == 0);
    replicate_bits(x, 'N / 'M)
}