
val extern forall Num 'l, Num 'm. ([:'l:], [:'m:], int) -> vector<'l,'m,dec,bit> effect pure to_vec_dec

val cast forall Num 'n, Num 'm. [:0:] -> vector<'n,'m,dec,bit> effect pure cast_0_vec
function forall Num 'n, Num 'm. (vector<'n,'m,dec,bit>) cast_0_vec i = to_vec_dec (sizeof 'n, sizeof 'm, i)

default Order dec

function forall Num 'N, 'N IN {32}. bit['N] Foo32( (bit['N]) x) = x

let x = Foo32( (bit[32]) 0)
