(* val forall Nat 'n, Nat 'm, Nat 'o, 'o >= 'm - 1.
  vector<'n,'m,dec,bit> -> vector<'o,'m,dec,bit>
  effect pure ADJUST
*)

val extern forall Num 'n, Num 'l, 'l >= 0. (vector<'n,'l,dec,bit>, [|'n - 'l + 1:'n|]) -> bit effect pure bitvector_access_dec
val extern forall Nat 'n, Nat 'l, 'l >= 0. (vector<'n,'l,inc,bit>, [|'n:'n + 'l - 1|]) -> bit effect pure bitvector_access_inc

overload vector_access [bitvector_access_inc; bitvector_access_dec]
    
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

val unit -> bit effect {rreg} test

function bit test () =
{
  CP0Cause[30]
}
