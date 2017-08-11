val forall Nat 'n, Nat 'l, 'l >= 0. (vector<'n,'l,dec,bit>, [|'n - 'l + 1:'n|]) -> bit effect pure bitvector_access_dec
val forall Nat 'n, Nat 'l, 'l >= 0. (vector<'n,'l,inc,bit>, [|'n:'n + 'l - 1|]) -> bit effect pure bitvector_access_inc

overload vector_access [bitvector_access_inc; bitvector_access_dec]

function bit bv ((bit[64]) x) =
{
  x[32]
}
