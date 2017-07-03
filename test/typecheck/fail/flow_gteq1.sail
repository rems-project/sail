default Order inc

val forall Num 'n, Num 'm, Num 'o, Num 'p. ([|'n:'m|], [|'o:'p|]) -> [|'n+'o:'m+'p|] effect pure add_range

val forall Num 'n, Num 'm, Num 'o, Num 'p. ([|'n:'m|], [|'o:'p|]) -> [|'n-'p:'m-'o|] effect pure sub_range

val forall Num 'n, Num 'm, Num 'o. ([|'n:'m|], [:'o:]) -> bool effect pure lt_range_atom
val forall Num 'n, Num 'm, Num 'o. ([|'n:'m|], [:'o:]) -> bool effect pure lteq_range_atom
val forall Num 'n, Num 'm, Num 'o. ([|'n:'m|], [:'o:]) -> bool effect pure gt_range_atom
val forall Num 'n, Num 'm, Num 'o. ([|'n:'m|], [:'o:]) -> bool effect pure gteq_range_atom
val forall Num 'n, Num 'm, Num 'o. ([:'n:], [|'m:'o|]) -> bool effect pure lt_atom_range
val forall Num 'n, Num 'm, Num 'o. ([:'n:], [|'m:'o|]) -> bool effect pure lteq_atom_range
val forall Num 'n, Num 'm, Num 'o. ([:'n:], [|'m:'o|]) -> bool effect pure gt_atom_range
val forall Num 'n, Num 'm, Num 'o. ([:'n:], [|'m:'o|]) -> bool effect pure gteq_atom_range

overload (deinfix +) [add_range]
overload (deinfix -) [sub_range]
overload (deinfix <) [lt_atom_range; lt_range_atom]
overload (deinfix <=) [lteq_atom_range; lteq_range_atom]
overload (deinfix >) [gt_atom_range; gt_range_atom]
overload (deinfix >=) [gteq_atom_range; gteq_range_atom]

function ([|63|]) branch (([|63|]) x) =
{
  if (x >= 32)
  then x - 33
  else x + 32
}
