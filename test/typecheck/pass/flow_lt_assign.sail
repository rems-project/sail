default Order inc

val forall Num 'n, Num 'm, Num 'o, Num 'p. ([|'n:'m|], [|'o:'p|]) -> [|'n+'o:'m+'p|] effect pure add_range

val forall Num 'n, Num 'm, Num 'o, Num 'p. ([|'n:'m|], [|'o:'p|]) -> [|'n-'p:'m-'o|] effect pure sub_range

val forall Num 'n, Num 'm, Num 'o. ([|'n:'m|], [:'o:]) -> bool effect pure lt_range_atom
val forall Num 'n, Num 'm, Num 'o. ([:'n:], [|'m:'o|]) -> bool effect pure lt_atom_range

overload (deinfix +) [add_range]
overload (deinfix -) [sub_range]
overload (deinfix <) [lt_atom_range; lt_range_atom]

function ([|63|]) branch (([|63|]) x) =
{
  y := x;
  if (y < 32)
  then {
    y := 31;
    y + 32
  }
  else y - 32
}
