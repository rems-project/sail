default Order inc

val extern forall Nat 'n. (bit['n], bit['n]) -> bit['n] effect pure bv_add = "bv_add_inc"
  
overload (deinfix +) [bv_add]

val (bit[3], bit[3]) -> bit[3] effect pure test

function bit[3] test (x, y) =
{
  x + y
}
