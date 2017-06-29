default Order inc

val extern forall Num 'n. (bit['n], bit['n]) -> bit['n] effect pure bv_add = "bv_add_inc"

val forall Num 'n, Num 'm, Num 'o, Num 'p, Type 'a.
  (vector<'n,'m,inc,'a>, vector<'o,'p,inc,'a>) -> vector<'n,'m + 'p,inc,'a>
  effect pure vector_append_inc

overload (deinfix +) [bv_add]
overload vector_append [vector_append_inc]

val (bit[3], bit[3]) -> bit[3] effect pure test

function bit[3] test (((bit[1]) x : 0b1 : 0b0), z) =
{
  (x : 0b11) + z
}
