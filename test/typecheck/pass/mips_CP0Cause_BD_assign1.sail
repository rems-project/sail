val cast forall Num 'n. [:1:] -> vector<'n,1,dec,bit> effect pure cast_1_vec
val cast forall Num 'n. [:0:] -> vector<'n,1,dec,bit> effect pure cast_0_vec

val extern forall Num 'm. ([:'l:], [:'m:], int) -> vector<'l,'m,dec,bit> effect pure to_vec_dec

function forall Num 'n. (vector<'n,1,dec,bit>) cast_1_vec i = to_vec_dec (sizeof 'n, 1, i)
function forall Num 'n. (vector<'n,1,dec,bit>) cast_0_vec i = to_vec_dec (sizeof 'n, 1, i)

default Order dec

typedef CauseReg = register bits [ 31 : 0 ] {
  31       : BD; (* branch delay *)
  (*30       : Z0;*)
  29 .. 28 : CE; (* for coprocessor enable exception *)
  (*27 .. 24 : Z1;*)
  23       : IV; (* special interrupt vector not supported *)
  22       : WP; (* watchpoint exception occurred *)
  (*21 .. 16 : Z2; *)
  15 .. 8  : IP; (* interrupt pending bits *)
  (*7        : Z3;*)
  6 .. 2   : ExcCode; (* code of last exception *)
  (*1 .. 0   : Z4;*)
}

register (CauseReg) CP0Cause

val unit -> unit effect {wreg} test

function unit test () =
{
  CP0Cause.BD := 1
}
