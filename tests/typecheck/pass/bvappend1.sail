val forall Nat 'n, 'n IN {4}. bit['n] -> bit[2 * 'n] effect pure test

function forall Nat 'n, 'n IN {4}. bit[2 * 'n] test (bit['n]) v =
{
  v : v   
}

let (bit[16]) x = test ((bit[4]) 0) : test ((bit[4]) 0)
