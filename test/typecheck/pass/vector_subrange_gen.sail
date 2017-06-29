
val forall Nat 'n, Nat 'l, Order 'o, Type 'a, 'l >= 0. (vector<'n,'l,'o,'a>, [|'n:'n + 'l - 1|]) -> 'a effect pure vector_access

val forall Nat 'n1, Nat 'l1, Nat 'n2, Nat 'l2, Order 'o, Type 'a, 'l1 >= 0, 'l2 >= 0.
  (vector<'n1,'l1,'o,'a>, vector<'n2,'l2,'o,'a>) -> vector<'n1,'l1 + 'l2,'o,'a> effect pure vector_append

val forall Nat 'n, Nat 'l, Nat 'm, Nat 'u, Order 'o, Type 'a, 'l >= 0, 'm <= 'u, 'u <= 'l. (vector<'n,'l,'o,'a>, [:'m:], [:'u:]) -> vector<'m,'u - 'm,'o,'a> effect pure vector_subrange

val forall Nat 'n, Nat 'm. ([:'n:], [:'m:]) -> [:'n - 'm:] effect pure minus

default Order inc

val forall 'n, 'm, 'n >= 5. bit['n] -> bit['n - 2] effect pure test

function forall 'n, 'n >= 5. bit['n - 2] test v =
{
  z := vector_subrange(v, 0, minus(sizeof 'n, 2));
  z := v[0 .. minus(sizeof 'n, 2)];
  z
}