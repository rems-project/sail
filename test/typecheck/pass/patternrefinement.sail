default Order dec

val extern forall Num 'n, Num 'm, Num 'o, Num 'p, Order 'ord.
    vector<'o, 'n, 'ord, bit> -> vector<'p, 'm, 'ord, bit> effect pure extz
val extern forall Num 'n, Num 'm, Order 'ord, Type 'a. vector<'n,'m,'ord,'a> -> [:'m:] effect pure length
val extern forall Num 'n, Num 'm, Order 'ord. (vector<'n,'m,'ord,bit>, vector<'n,'m,'ord,bit>) -> bool effect pure eq_vec
val extern forall Num 'n, Num 'm. ([:'n:],[:'m:]) -> bool effect pure eq_atom
val extern forall Type 'a. ('a, 'a) -> bool effect pure eq
overload (deinfix ==) [eq_vec; eq_atom; eq]


val forall 'n, 'n in {32,64}. bit['n] -> bit[64] effect pure test

function test(v) = {
  switch (length(v)) {
  case 32 -> extz(v)
  case 64 -> v
  }
}
