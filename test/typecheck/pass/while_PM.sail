default Order dec

val extern forall Num 'n, Num 'm, Num 'o. ([|'n:'m|], [:'o:]) -> bool effect pure lt_range_atom = "lt"
val extern (int, int) -> bool effect pure lt_int = "lt"
overload (deinfix <) [lt_range_atom; lt_int]

val extern forall Num 'n, Num 'm, Num 'o, Num 'p.
    ([|'n:'m|], [|'o:'p|]) -> [|'n + 'o:'m + 'p|] effect pure add_range = "add"
val extern (int, int) -> int effect pure add_int = "add"
overload (deinfix +) [add_range; add_int]

val extern forall Num 'n, Num 'l, 'l >= 0. (vector<'n,'l,dec,bit>, int) -> bit effect pure vector_access = "bitvector_access_dec"

register (bit[64]) GPR00

function (unit) test ((bit) b) = {
  (int) i := 0;
  while (i < 64) do {
    GPR00[i] := b;
    i := i + 1;
  }
}

