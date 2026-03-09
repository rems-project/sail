default Order dec

$include <prelude.sail>

val foo : forall 'n, 'n >= 0. (int('n),bits('n)) -> bits(5 + 'n)

function foo(n,x) = {
  let (n as 'm) = 5 in
  (append((x : bits('n)),sail_ones(n)) : bits('m + 'n))
}
