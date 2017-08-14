default Order inc

val extern forall Num 'n. (bit['n], bit['n]) -> bit['n] effect pure bv_add = "add_vec"

val extern forall Num 'n, Num 'l, Num 'm, Num 'o, 'l >= 0, 'm <= 'o, 'o <= 'l.
  (vector<'n,'l,inc,bit>, [:'m:], [:'o:]) -> vector<'m,'o + 1 - 'm,inc,bit> effect pure vector_subrange = "bitvector_subrange_inc"

val forall Num 'n, Num 'm, Num 'o, Num 'p.
  (vector<'n,'m,inc,bit>, vector<'o,'p,inc,bit>) -> vector<'n,'m + 'p,inc,bit>
  effect pure bitvector_concat

overload (deinfix +) [bv_add]
overload vector_append [bitvector_concat]

val (bit[3], bit[3]) -> bit[3] effect pure test

function bit[3] test (((bit[1]) x : 0b1 : 0b0), z) =
{
  (x : 0b11) + z
}
