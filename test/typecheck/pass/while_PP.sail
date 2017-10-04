default Order dec

val extern forall Num 'n, Num 'm, Num 'o. ([|'n:'m|], [:'o:]) -> bool effect pure lt_range_atom = "lt"
val extern (int, int) -> bool effect pure lt_int = "lt"
overload (deinfix <) [lt_range_atom; lt_int]

val (int, int) -> int effect pure mult_int
overload (deinfix * ) [mult_int]

val extern forall Num 'n, Num 'm, Num 'o, Num 'p.
    ([|'n:'m|], [|'o:'p|]) -> [|'n + 'o:'m + 'p|] effect pure add_range = "add"
val extern (int, int) -> int effect pure add_int = "add"
overload (deinfix +) [add_range; add_int]

function (int) test ((int) n) = {
  (int) i := 1;
  (int) j := 1;
  while (i < n) do {
    j := i * j;
    i := i + 1;
  };
  j
}

