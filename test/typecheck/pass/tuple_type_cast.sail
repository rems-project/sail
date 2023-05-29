default Order dec
$include <prelude.sail>

val source : forall 'n, 'n > 0. (bool, int('n)) -> (bool, bits('n))

function source(b, n) = {
  if b then (false, sail_zeros(n)) else (true, sail_ones(n))
}

val test : forall 'n, 'n > 0. int('n) -> int

function test(n) = {
  v : bits('n + 2 - 'n + 2) = 0x2;
  if n > 5 then {
    let (_, w : bits('n + 2 - 'n + 2)) = source(n > 10, 4);
    v = w
  };
  unsigned(v)
}
