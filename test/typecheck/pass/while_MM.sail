default Order dec

val extern forall Num 'n, Num 'm, Num 'o, Num 'p.
    ([|'n:'m|], [|'o:'p|]) -> [|'n + 'o:'m + 'p|] effect pure add_range = "add"
val extern (int, int) -> int effect pure add_int = "add"
val forall Num 'n, Num 'o, Order 'ord.
    (vector<'o, 'n, 'ord, bit>, int) -> vector<'o, 'n, 'ord, bit> effect pure add_vec_int
overload (deinfix +) [add_vec_int; add_range; add_int]

val extern bool -> bool effect pure bool_not = "not"

val cast forall Num 'n, Num 'l. [:0:] -> vector<'n,'l,dec,bit> effect pure cast_0_vec_dec

register (bit[64]) COUNT
register (bool) INT

function (unit) test () = {
  COUNT := 0;
  while (bool_not(INT)) do {
    COUNT := COUNT + 1;
  }
}

