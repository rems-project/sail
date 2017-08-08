default Order inc

val extern forall Num 'n. (bit['n], bit['n]) -> bit['n] effect pure add_vec = "add_vec"
val extern forall Num 'n, Num 'm, Num 'o, Num 'p. ([|'n:'m|], [|'o:'p|]) -> [|'n+'o:'m+'p|] effect pure add_range = "add_range"

val cast forall Num 'n. bit['n] -> [|0: 2** 'n - 1|] effect pure unsigned

overload (deinfix +) [add_vec; add_range]

let (range<0,30>) x = 0xF + 0x2
