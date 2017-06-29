val forall Nat 'n, Nat 'l, Type 'a, 'l >= 0. (vector<'n,'l,dec,'a>, [|'n - 'l + 1:'n|]) -> 'a effect pure vector_access_dec
val forall Nat 'n, Nat 'l, Type 'a, 'l >= 0. (vector<'n,'l,inc,'a>, [|'n:'n + 'l - 1|]) -> 'a effect pure vector_access_inc

overload vector_access [vector_access_inc; vector_access_dec]

val cast bit -> bool effect pure cast_bit_bool

function bool bv ((bit[64]) x) =
{
  x[32]
}
