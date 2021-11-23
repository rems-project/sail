default Order dec
$include <prelude.sail>

val f: forall 'n, 'n in {2,3}. (bits(32), bits('n)) -> bit
function f(v,n) = v[unsigned(n)]