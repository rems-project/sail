
val extern (int, int) -> bool effect pure gt_int

(* val cast forall Num 'n, Num 'm. [|'n:'m|] -> int effect pure cast_range_int *)

overload (deinfix >) [gt_int]

register int z

val forall Nat 'n. unit -> unit effect {wreg} test

function forall Nat 'n. unit test () =
{
  if sizeof 'n > 3
  then z := 0
  else z := 1
}
