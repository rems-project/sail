
val forall Nat 'n, Nat 'l, Order 'o, Type 'a, 'l >= 0. (vector<'n,'l,'o,'a>, [|'n:'n + 'l - 1|]) -> 'a effect pure vector_access

val forall Nat 'n1, Nat 'l1, Nat 'n2, Nat 'l2, Order 'o, Type 'a, 'l1 >= 0, 'l2 >= 0.
  (vector<'n1,'l1,'o,'a>, vector<'n2,'l2,'o,'a>) -> vector<'n1,'l1 + 'l2,'o,'a> effect pure vector_append

val extern forall Num 'n, Num 'l, Num 'm, Num 'o, 'l >= 0, 'm <= 'o, 'o <= 'l.
  (vector<'n,'l,inc,bit>, [:'m:], [:'o:]) -> vector<'m,('o - 'm) + 1,inc,bit> effect pure vector_subrange = "bitvector_subrange_inc"

val forall Nat 'n, Nat 'm. ([:'n:], [:'m:]) -> [:'n - 'm:] effect pure sub

default Order inc

val forall 'n, 'm, 'n >= 5. bit['n] -> bit['n - 1] effect pure test

function forall 'n, 'n >= 5. bit['n - 1] test v =
{
  z := vector_subrange(v, 0, sub(sizeof 'n, 2));
  z := v[0 .. sub(sizeof 'n, 2)];
  z
}
