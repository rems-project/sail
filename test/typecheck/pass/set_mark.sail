
val cast forall Num 'n, Num 'm, Order 'ord. [:0:] -> vector<'n,'m,'ord,bit> effect pure cast_zero_bv

function forall Num 'N, 'N IN {32}. bit['N] Foo32( (bit['N]) x) = x

let x = Foo32( (bit[32]) 0)
