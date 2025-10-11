default Order dec
$include <prelude.sail>

val foo_0 : forall 'n, 'n in {32, 64}. bits('n) -> bool
function foo_0(x : bits('n)) = 'n == 64

function foo_1 forall 'n, 'n in {32, 64} . (x : bits('n)) -> bool = 'n == 64

val foo_2 : forall 'n, 'n in {32, 64}. bits('n) -> bool
function foo_2(x) = 'n == 64
