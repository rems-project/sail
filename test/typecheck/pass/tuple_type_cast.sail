default Order dec
$include <prelude.sail>

// An example with a let-binding where a type in a nested pattern is
// different but equivalent to the inferred type.  The Coq backend used
// to ignore these, leading to type mismatches.

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

// The same, but with an assert providing a side-effect

val effectful_source : forall 'n, 'n > 0. (bool, int('n)) -> (bool, bits('n))

function effectful_source(b, n) = {
  assert(n > 1);
  if b then (false, sail_zeros(n)) else (true, sail_ones(n))
}

val effectful_test : forall 'n, 'n > 0. int('n) -> int

function effectful_test(n) = {
  v : bits('n + 2 - 'n + 2) = 0x2;
  if n > 5 then {
    let (_, w : bits('n + 2 - 'n + 2)) = effectful_source(n > 10, 4);
    v = w
  };
  unsigned(v)
}
