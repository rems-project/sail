default Order dec

$include <prelude.sail>

// In the calls to sail_zeros below the Coq version needs to end up with
// 'n for the argument, rather than the literal 8 or 16.  We currently do
// this by replacing the literal with an underscore and letting Coq figure
// it out.

val test : forall 'n, 'n in {8,16}. atom('n) -> bits('n)

function test(8) = sail_zeros(8)
and test(16) = sail_zeros(16)
