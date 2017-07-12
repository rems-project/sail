
val forall Nat 'n, Nat 'm, Order 'o. vector<'n,'m,'o,bit> -> vector<'n,'m,'o,bit> effect pure bitwise_not

default Order dec

val forall 'n. bit['n] -> bit['n] effect pure test

function forall 'n. bit['n] test ((bit['n]) x) = bitwise_not(bitwise_not(x))
