
val extern forall Nat 'n1, Nat 'l1, Nat 'n2, Nat 'l2, Order 'o, 'l1 >= 0, 'l2 >= 0.
  (vector<'n1,'l1,'o,bit>, vector<'n2,'l2,'o,bit>) -> vector<'n1,'l1 + 'l2,'o,bit> effect pure vector_append = "bitvector_concat"

default Order inc

val forall 'n, 'm, 'n >= 0, 'm >= 0. (bit['n], bit['m]) -> bit['n + 'm] effect pure test
    
function forall 'n, 'm. bit['n + 'm] test (v1, v2) =
{
  vector_append(v1, v2);
}
