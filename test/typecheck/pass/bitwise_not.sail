val forall Nat 'n, Nat 'm, Order 'o. vector<'n,'m,'o,bit> -> vector<'n,'m,'o,bit> effect pure bitwise_not

default Order dec
    
val bit[5] -> bit[5] effect pure test
    
function bit[5] test ((bit[5]) x) = bitwise_not(x)