
val forall Nat 'n, Nat 'l, Order 'o, Type 'a, 'l >= 0. (vector<'n,'l,'o,'a>, [|'n:'n + 'l - 1|]) -> 'a effect pure vector_access

val forall Nat 'n1, Nat 'l1, Nat 'n2, Nat 'l2, Order 'o, Type 'a, 'l1 >= 0, 'l2 >= 0.
  (vector<'n1,'l1,'o,'a>, vector<'n2,'l2,'o,'a>) -> vector<'n1,'l1 + 'l2,'o,'a> effect pure vector_append

default Order inc

val (bit[4], bit[4]) -> bit[8] effect pure test
    
function bit[8] test (v1, v2) =
{
  z := vector_access(v1, 3);
  z := v1[0];
  zv := vector_append(v1, v2);
  zv := v1 : v2;
  zv
}