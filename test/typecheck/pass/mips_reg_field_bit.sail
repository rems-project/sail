val cast forall Nat 'n, Nat 'm, Nat 'o, 'o >= 'm - 1.
  vector<'n,'m,dec,bit> -> vector<'o,'m,dec,bit>
  effect pure ADJUST

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
  (CP0Cause.CE)[28] := bitone
}
