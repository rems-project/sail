
val extern forall Nat 'n1, Nat 'l1, Nat 'n2, Nat 'l2, Order 'o, 'l1 >= 0, 'l2 >= 0.
  (vector<'n1,'l1,'o,bit>, vector<'n2,'l2,'o,bit>) -> vector<'n1,'l1 + 'l2,'o,bit> effect pure vector_append = "bitvector_concat"

default Order inc

val (bit[4], bit[4]) -> bit[8] effect pure test
    
function bit[8] test (v1, v2) =
{
  zv := vector_append(v1, v2);
  zv := v1 : v2;
  zv
}
