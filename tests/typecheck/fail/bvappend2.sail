val forall Nat 'n, 'n IN {4}. bit['n] -> bit[2 * 'n] effect pure test

function forall Nat 'n, 'n IN {4}. bit[2 * 'n] test (bit['n]) v =
{
  v : v   
}

val forall Nat 'n, Nat 'm. (bit['n], bit['m]) -> bit['n + 'm] effect pure bvappend

function forall Nat 'n, Nat 'm. bit['n + 'm] bvappend ((bit['n]) x, (bit['m]) y) =
{
  x : y
}

let (bit[50]) z = bvappend (test ((bit[4]) 0), test ((bit[4]) 0))
