default Order dec
$include <prelude.sail>

val f : forall 'n 'm, 'n >= 0 & 'm >= 0. (int('n), int('m)) -> vector(1, bits('n * ('m * 8)))

function f (n,m) = [sail_zeros(n * m * 8)]

val g : forall 'n 'm, 'n >= 0 & 'm >= 0. (int('n), int('m)) -> vector(1, bits('n * 'm * 8))

function g(n,m) = f(n,m)
