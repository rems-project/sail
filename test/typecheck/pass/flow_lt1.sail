default Order inc

val extern forall Num 'n, Num 'm, Num 'o, Num 'p. ([|'n:'m|], [|'o:'p|]) -> [|'n+'o:'m+'p|] effect pure add_range = "add"

val extern forall Num 'n, Num 'm, Num 'o, Num 'p. ([|'n:'m|], [|'o:'p|]) -> [|'n-'p:'m-'o|] effect pure sub_range = "sub"

val extern forall Num 'n, Num 'm, Num 'o. ([|'n:'m|], [:'o:]) -> bool effect pure lt_range_atom = "lt"
val extern forall Num 'n, Num 'm, Num 'o. ([|'n:'m|], [:'o:]) -> bool effect pure lteq_range_atom = "lteq"
val extern forall Num 'n, Num 'm, Num 'o. ([|'n:'m|], [:'o:]) -> bool effect pure gt_range_atom = "gt"
val extern forall Num 'n, Num 'm, Num 'o. ([|'n:'m|], [:'o:]) -> bool effect pure gteq_range_atom = "gteq"
val extern forall Num 'n, Num 'm, Num 'o. ([:'n:], [|'m:'o|]) -> bool effect pure lt_atom_range = "lt"
val extern forall Num 'n, Num 'm, Num 'o. ([:'n:], [|'m:'o|]) -> bool effect pure lteq_atom_range = "lteq"
val extern forall Num 'n, Num 'm, Num 'o. ([:'n:], [|'m:'o|]) -> bool effect pure gt_atom_range = "gt"
val extern forall Num 'n, Num 'm, Num 'o. ([:'n:], [|'m:'o|]) -> bool effect pure gteq_atom_range = "gteq"

overload (deinfix +) [add_range]
overload (deinfix -) [sub_range]
overload (deinfix <) [lt_atom_range; lt_range_atom]

function ([|63|]) branch (([|63|]) x) =
{
  if (x < 32)
  then x + 32
  else x - 32
}
