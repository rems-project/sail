(*========================================================================*)
(*                                                                        *)
(*  Copyright (c) 2015-2017 Gabriel Kerneis, Susmit Sarkar, Kathyrn Gray  *)
(*  Copyright (c) 2015-2017 Peter Sewell                                  *)
(*  All rights reserved.                                                  *)
(*                                                                        *)
(*  This software was developed by the University of Cambridge Computer   *)
(*  Laboratory as part of the Rigorous Engineering of Mainstream Systems  *)
(*  (REMS) project, funded by EPSRC grant EP/K008528/1.                   *)
(*                                                                        *)
(*  Redistribution and use in source and binary forms, with or without    *)
(*  modification, are permitted provided that the following conditions    *)
(*  are met:                                                              *)
(*  1. Redistributions of source code must retain the above copyright     *)
(*     notice, this list of conditions and the following disclaimer.      *)
(*  2. Redistributions in binary form must reproduce the above copyright  *)
(*     notice, this list of conditions and the following disclaimer in    *)
(*     the documentation and/or other materials provided with the         *)
(*     distribution.                                                      *)
(*                                                                        *)
(*  THIS SOFTWARE IS PROVIDED BY THE AUTHOR AND CONTRIBUTORS ``AS IS''    *)
(*  AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED     *)
(*  TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A       *)
(*  PARTICULAR PURPOSE ARE DISCLAIMED.  IN NO EVENT SHALL THE AUTHOR OR   *)
(*  CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,          *)
(*  SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT      *)
(*  LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF      *)
(*  USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND   *)
(*  ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,    *)
(*  OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT    *)
(*  OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF    *)
(*  SUCH DAMAGE.                                                          *)
(*========================================================================*)

(* XXX binary coded decimal *)
(*function bit[12] DEC_TO_BCD ( (bit[10]) declet ) = {
  (bit[4]) hundreds := 0;
  (bit[4]) tens := 0;
  (bit[4]) ones := 0;
  foreach (i from 0 to 9) {
    if hundreds >= 5 then hundreds := hundreds + 3;
    if tens >= 5 then tens := tens + 3;
    if ones >= 5 then ones := ones + 3;
    hundreds := hundreds << 1;
    hundreds[3] := tens[0];
    tens := tens << 1;
    tens[3] := ones[0];
    ones := ones << 1;
    ones[3] := declet[i] };
  hundreds:tens:ones }*)

function bit[12] DEC_TO_BCD ( (bit[10]) [p,q,r,s,t,u,v,w,x,y]) = {
  a := ((~(s) & v & w) | (t & v & w & s) | (v & w & ~(x)));
  b := ((p & s & x & ~(t)) | (p & ~(w)) | (p & ~(v)));
  c := ((q & s & x & ~(t)) | (q & ~(w)) | (q & ~(v)));
  d := r;

  e := ((v & ~(w) & x) | (s & v & w & x) | (~(t) & v & x & w));
  f := ((p & t & v & w & x & ~(s)) | (s & ~(x) & v) | (s & ~(v)));
  g := ((q & t & w & v & x & ~(s)) | (t & ~(x) & v) | (t & ~(v)));
  h := u;

  i := ((t & v & w & x) | (s & v & w & x) | (v & ~(w) & ~(x)));
  j := ((p & ~(s) & ~(t) & w & v) | (s & v & ~(w) & x) | (p & w & ~(x) & v) | (w & ~(v)));
  k := ((q & ~(s) & ~(t) & v & w) | (t & v & ~(w) & x) | (q & v & w & ~(x)) | (x & ~(v)));
  m := y;
  [a,b,c,d,e,f,g,h,i,j,k,m]
}

(*function bit[10] BCD_TO_DEC ( (bit[12]) bcd ) = 
   (bit[10]) (([|2** 10|]) (bcd[0..3] * 100)) + ([|2** 7|]) ((([|2** 7|]) (bcd[4..7] * 10)) + bcd[8..11])
*)

function bit[10] BCD_TO_DEC ( (bit[12]) [a,b,c,d,e,f,g,h,i,j,k,m] ) = {
   p := ((f & a & i & ~(e)) | (j & a & ~(i)) | (b & ~(a)));
   q := ((g & a & i & ~(e)) | (k & a & ~(i)) | (c & ~(a)));
   r := d;
   s := ((j & ~(a) & e & ~(i)) | (f & ~(i) & ~(e)) | (f & ~(a) & ~(e)) | (e & i));
   t := ((k & ~(a) & e & ~(i)) | (g & ~(i) & ~(e)) | (g & ~(a) & ~(e)) | (a & i));
   u := h;
   v := (a | e | i);
   w := ((~(e) & j & ~(i)) | (e & i) | a);
   x := ((~(a) & k & ~(i)) | (a & i) | e);
   y := m;
   [p,q,r,s,t,u,v,w,x,y]
}

(* XXX carry out *)
function forall Nat 'a . bit carry_out ( (bit['a]) _,carry ) = carry
(* XXX Storage control *)
function forall Type 'a . 'a real_addr ( x ) = x
(* XXX For stvxl and lvxl - what does that do? *)
function forall Type 'a . unit mark_as_not_likely_to_be_needed_again_anytime_soon ( x ) = ()

(* XXX *)
val extern forall Nat 'k, Nat 'r,
  0 <= 'k, 'k <= 64, 'r + 'k = 64.
  (bit[64], [|'k|]) -> [|0:'r|] effect pure countLeadingZeroes

function forall Nat 'n, Nat 'm .
  bit['m] EXTS_EXPLICIT((bit['n]) v, ([:'m:]) m) =
  (v[0] ^^ (m - length(v))) : v

val forall Nat 'n, Nat 'm, 0 <= 'n, 'n <= 'm, 'm <= 63 .
  ([|'n|],[|'m|]) -> bit[64]
  effect pure
  MASK

function (bit[64]) MASK(start, stop) = {
  (bit[64]) mask_temp := 0;
  if(start > stop) then {
    mask_temp[start .. 63] := bitone ^^ sub(64, start);
    mask_temp[0 .. stop] := bitone ^^ (stop + 1);
  } else {
    mask_temp[start .. stop ] := bitone ^^ (stop - start + 1);
  };
  mask_temp;
}

val forall Nat 'n, 0 <= 'n, 'n <= 63 .
  (bit[64], [|'n|]) -> bit[64] effect pure ROTL

function (bit[64]) ROTL(v, n) = v[n .. 63] : v[0 .. (n - 1)]

(* Branch facility registers *)

typedef cr = register bits [ 32 : 63 ] {
  32 .. 35 : CR0;
    32 : LT; 33 : GT; 34 : EQ; 35 : SO;
  36 .. 39 : CR1;
    36 : FX; 37 : FEX; 38 : VX; 39 : OX;
  40 .. 43 : CR2;
  44 .. 47 : CR3;
  48 .. 51 : CR4;
  52 .. 55 : CR5;
  56 .. 59 : CR6;
    (* name clashing - do we need hierarchical naming for fields, or do
    we just don't care? LT, GT, etc. are not used in the code anyway.
    56 : LT; 57 : GT; 58 : EQ; 59 : SO;
    *)
  60 .. 63 : CR7;
}
register (cr) CR

register (bit[64]) CTR
register (bit[64]) LR

typedef xer = register bits [ 0 : 63 ] {
  32 : SO;
  33 : OV;
  34 : CA;
}
register (xer) XER

register alias CA = XER.CA

(* Fixed-point registers *)

register (bit[64]) GPR0
register (bit[64]) GPR1
register (bit[64]) GPR2
register (bit[64]) GPR3
register (bit[64]) GPR4
register (bit[64]) GPR5
register (bit[64]) GPR6
register (bit[64]) GPR7
register (bit[64]) GPR8
register (bit[64]) GPR9
register (bit[64]) GPR10
register (bit[64]) GPR11
register (bit[64]) GPR12
register (bit[64]) GPR13
register (bit[64]) GPR14
register (bit[64]) GPR15
register (bit[64]) GPR16
register (bit[64]) GPR17
register (bit[64]) GPR18
register (bit[64]) GPR19
register (bit[64]) GPR20
register (bit[64]) GPR21
register (bit[64]) GPR22
register (bit[64]) GPR23
register (bit[64]) GPR24
register (bit[64]) GPR25
register (bit[64]) GPR26
register (bit[64]) GPR27
register (bit[64]) GPR28
register (bit[64]) GPR29
register (bit[64]) GPR30
register (bit[64]) GPR31

let (vector <0, 32, inc, (register<(bit[64])>) >) GPR =
  [ GPR0, GPR1, GPR2, GPR3, GPR4, GPR5, GPR6, GPR7, GPR8, GPR9, GPR10,
  GPR11, GPR12, GPR13, GPR14, GPR15, GPR16, GPR17, GPR18, GPR19, GPR20,
  GPR21, GPR22, GPR23, GPR24, GPR25, GPR26, GPR27, GPR28, GPR29, GPR30, GPR31
  ]

register (bit[32:63]) VRSAVE

register (bit[64]) SPRG3
register (bit[64]) SPRG4
register (bit[64]) SPRG5
register (bit[64]) SPRG6
register (bit[64]) SPRG7

let (vector <0, 1024, inc, (register<(bit[64])>) >) SPR =
  [ 1=XER, 8=LR, 9=CTR(*, 256=VRSAVE (*32 bit, so not 64, caught by type checker at last*)*), 259=SPRG3, 260=SPRG4, 261=SPRG5, 262=SPRG6, 263=SPRG7
  ]

(* XXX DCR is implementation-dependent; also, some DCR are only 32 bits
 instead of 64, and mtdcrux/mfdcrux do special tricks in that case, not
 shown in pseudo-code. We just define two dummy DCR here, using sparse
 vector definition. *)
register (vector <0, 64, inc, bit>) DCR0
register (vector <0, 64, inc, bit>) DCR1
let (vector <0, 1024, inc, (register<(vector<0, 64, inc, bit>)>) >) DCR = {
  v = undefined;
  v[0] = DCR0;
  v[1] = DCR1;
  v
}

(* Floating-point registers *)

register (bit[64]) FPR0
register (bit[64]) FPR1
register (bit[64]) FPR2
register (bit[64]) FPR3
register (bit[64]) FPR4
register (bit[64]) FPR5
register (bit[64]) FPR6
register (bit[64]) FPR7
register (bit[64]) FPR8
register (bit[64]) FPR9
register (bit[64]) FPR10
register (bit[64]) FPR11
register (bit[64]) FPR12
register (bit[64]) FPR13
register (bit[64]) FPR14
register (bit[64]) FPR15
register (bit[64]) FPR16
register (bit[64]) FPR17
register (bit[64]) FPR18
register (bit[64]) FPR19
register (bit[64]) FPR20
register (bit[64]) FPR21
register (bit[64]) FPR22
register (bit[64]) FPR23
register (bit[64]) FPR24
register (bit[64]) FPR25
register (bit[64]) FPR26
register (bit[64]) FPR27
register (bit[64]) FPR28
register (bit[64]) FPR29
register (bit[64]) FPR30
register (bit[64]) FPR31

let (vector <0, 32, inc, (register<(bit[64])>) >) FPR =
  [ FPR0, FPR1, FPR2, FPR3, FPR4, FPR5, FPR6, FPR7, FPR8, FPR9, FPR10,
  FPR11, FPR12, FPR13, FPR14, FPR15, FPR16, FPR17, FPR18, FPR19, FPR20,
  FPR21, FPR22, FPR23, FPR24, FPR25, FPR26, FPR27, FPR28, FPR29, FPR30, FPR31
  ]

typedef fpscr = register bits [ 0 : 63 ] {
  32 : FX;
  33 : FEX;
  34 : VX;
  35 : OX;
  36 : UX;
  37 : ZX;
  38 : XX;
  39 : VXSNAN;
  40 : VXISI;
  41 : VXIDI;
  42 : VXZDZ;
  43 : VXIMZ;
  44 : VXVC;
  45 : FR;
  46 : FI;
  47 .. 51 : FPRF;
  47 : C;
  48 .. 51 : FPCC;
    48 : FL; 49 : FG; 50 : FE; 51 : FU;
  53 : VXSOFT;
  54 : VXSQRT;
  55 : VXCVI;
  56 : VE;
  57 : OE;
  58 : UE;
  59 : ZE;
  60 : XE;
  61 : NI;
  62 .. 63 : RN;
}
register (fpscr) FPSCR

(* Pair-wise access to FPR registers *)

register alias FPRp0 = FPR0 : FPR1
register alias FPRp2 = FPR2 : FPR3
register alias FPRp4 = FPR4 : FPR5
register alias FPRp6 = FPR6 : FPR7
register alias FPRp8 = FPR8 : FPR9
register alias FPRp10 = FPR10 : FPR11
register alias FPRp12 = FPR12 : FPR13
register alias FPRp14 = FPR14 : FPR15
register alias FPRp16 = FPR16 : FPR17
register alias FPRp18 = FPR18 : FPR19
register alias FPRp20 = FPR20 : FPR21
register alias FPRp22 = FPR22 : FPR23
register alias FPRp24 = FPR24 : FPR25
register alias FPRp26 = FPR26 : FPR27
register alias FPRp28 = FPR28 : FPR29
register alias FPRp30 = FPR30 : FPR31

let (vector <0, 32, inc, (register<(bit[128])>)>) FPRp =
  [ 0 = FPRp0, 2 = FPRp2, 4 = FPRp4, 6 = FPRp6, 8 = FPRp8, 10 = FPRp10,
  12 = FPRp12, 14 = FPRp14, 16 = FPRp16, 18 = FPRp18, 20 = FPRp20, 22 =
  FPRp22, 24 = FPRp24, 26 = FPRp26, 28 = FPRp28, 30 = FPRp30 ]


val bit[32] -> bit[64] effect pure DOUBLE
val bit[64] -> bit[32] effect { undef } SINGLE

function  bit[64] DOUBLE word = {
  (bit[64]) temp := 0;
  if word[1..8] > 0 & word[1..8] < 255
  then {
    temp[0..1] := word[0..1];
    temp[2] := ~(word[1]);
    temp[3] := ~(word[1]);
    temp[4] := ~(word[1]);
    temp[5..63] := word[2..31] : 0b00000000000000000000000000000;
  } else if word[1..8] == 0 & word[9..31] != 0 
  then {
    sign := word[0];
    exp := 0 - 126;
    (bit[53]) frac := 0b0 : word[9..31] : 0b00000000000000000000000000000;
    foreach (i from 0 to 52) {
      if frac[0] == 0 
      then { frac[0..52] := frac[1..52] : 0b0;
             exp := exp - 1; }
      else ()
     };
     temp[0] := sign;
     temp[1..11] := (bit[1:11]) exp + 1023;
     temp[12..63] := frac[1..52];
   } else {
     temp[0..1] := word[0..1];
     temp[2] := word[1];
     temp[3] := word[1];
     temp[4] := word[1];
     temp[5..63] := word[2..31] : 0b00000000000000000000000000000;
   };
   temp
}

function bit[32] SINGLE ((bit[64]) frs) = {
  (bit[32]) word := 0;
  if (frs[1..11] > 896) | (frs[1..63] == 0) 
  then { word[0..1] := frs[0..1];
         word[2..31] := frs[5..34]; }
  else if (874 <= frs[1..11]) & (frs[1..11] <= 896)
  then { 
   sign := frs[0];
   (bit[11]) exp := frs[1..11] - 1023;
   (bit[53]) frac := 0b1 : frs[12..63];
   foreach (i from 0 to 53) {
     if exp < sub(0, 126)
     then { frac[0..52] := 0b0 : frac[0..51];
            exp := exp + 1; }
     else ()};
   } else word := undefined;
   word   
}

(* Vector registers *)

register (bit[128]) VR0
register (bit[128]) VR1
register (bit[128]) VR2
register (bit[128]) VR3
register (bit[128]) VR4
register (bit[128]) VR5
register (bit[128]) VR6
register (bit[128]) VR7
register (bit[128]) VR8
register (bit[128]) VR9
register (bit[128]) VR10
register (bit[128]) VR11
register (bit[128]) VR12
register (bit[128]) VR13
register (bit[128]) VR14
register (bit[128]) VR15
register (bit[128]) VR16
register (bit[128]) VR17
register (bit[128]) VR18
register (bit[128]) VR19
register (bit[128]) VR20
register (bit[128]) VR21
register (bit[128]) VR22
register (bit[128]) VR23
register (bit[128]) VR24
register (bit[128]) VR25
register (bit[128]) VR26
register (bit[128]) VR27
register (bit[128]) VR28
register (bit[128]) VR29
register (bit[128]) VR30
register (bit[128]) VR31

let (vector <0, 32, inc, (register<(bit[128])>) >) VR =
  [ VR0, VR1, VR2, VR3, VR4, VR5, VR6, VR7, VR8, VR9, VR10,
  VR11, VR12, VR13, VR14, VR15, VR16, VR17, VR18, VR19, VR20,
  VR21, VR22, VR23, VR24, VR25, VR26, VR27, VR28, VR29, VR30, VR31
  ]

typedef vscr = register bits [ 96 : 127 ] {
  111 : NJ;
  127 : SAT;
}
register (vscr) VSCR

(*(* XXX extend with zeroes -- the resulting size in completely unknown and depends of context *)
val extern forall Nat 'n, Nat 'm. (implicit<'m>,bit['n]) -> bit['m] effect pure EXTZ*)

(* Chop has a very weird definition where the resulting size depends of
   context, but in practice it is used with the following definition everywhere,
   except in vaddcuw which probably needs to be patched accordingly. *)
val forall Nat 'n, Nat 'm, 'm <= 'n. (bit['n], [:'m:]) -> bit['m] effect pure Chop
function forall Nat 'n, Nat 'm. (bit['m]) Chop(x, y) = x[0..y]

val forall Nat 'o, Nat 'n, Nat 'm, Nat 'k, 'n <= 0.
  (implicit<'k>, [:'o:], [:'n:], [|'m|]) -> bit['k] effect { wreg } Clamp

function forall Nat 'o,Nat 'n, Nat 'm, Nat 'k, 'n <= 0. (bit['k])
Clamp(([:'o:]) x, ([:'n:]) y, ([|'m|]) z) = {
  ([|'n:'m|]) result := 0;
  if (x<y) then {
    result := y;
    VSCR.SAT := 1;
  } else if (x > z) then {
    result := z;
    VSCR.SAT := 1;
  } else {
    result := x;
  };
  (bit['k]) result;
}

(* XXX *)
val extern bit[32] -> bit[32] effect pure RoundToSPIntCeil
val extern bit[32] -> bit[32] effect pure RoundToSPIntFloor
val extern bit[32] -> bit[32] effect pure RoundToSPIntNear
val extern bit[32] -> bit[32] effect pure RoundToSPIntTrunc
val extern bit[32] -> bit[32] effect pure RoundToNearSP
val extern bit[32] -> bit[32] effect pure ReciprocalEstimateSP
val extern bit[32] -> bit[32] effect pure ReciprocalSquareRootEstimateSP
val extern bit[32] -> bit[32] effect pure LogBase2EstimateSP
val extern bit[32] -> bit[32] effect pure Power2EstimateSP
val extern (bit[32], bit[5]) -> bit[32] effect pure ConvertSPtoSXWsaturate
val extern (bit[32], bit[5]) -> bit[32] effect pure ConvertSPtoUXWsaturate


register (bit[64]) NIA (* next instruction address *)
register (bit[64]) CIA (* current instruction address *)


val extern forall Nat 'n. ( bit[64] , [|'n|] , bit[8*'n]) -> unit effect { wmv } MEMw'
val extern forall Nat 'n. ( bit[64] , [|'n|] ) -> (bit[8 * 'n]) effect { rmem } MEMr'
val extern forall Nat 'n. ( bit[64] , [|'n|] ) -> (bit[8 * 'n]) effect { rmem } MEMr_reserve'
val extern forall Nat 'n. ( bit[64] , [|'n|] , bit[8*'n]) -> bool effect { wmv } MEMw_conditional'

(* announce write address for plain write *)
val extern forall Nat 'N, 'N IN {1,2,4,8,16}. (bit[64] (*address*), [:'N:] (*size*)) -> unit effect {eamem} MEMw_EA

(* announce write address for write conditional *)
val extern forall Nat 'N, 'N IN {1,2,4,8,16}. (bit[64] (*address*), [:'N:] (*size*)) -> unit effect {eamem} MEMw_EA_cond

val extern unit -> unit effect { barr } I_Sync
val extern unit -> unit effect { barr } H_Sync (*corresponds to Sync in barrier kinds*)
val extern unit -> unit effect { barr } LW_Sync
val extern unit -> unit effect { barr } EIEIO_Sync

val extern unit -> unit effect { depend } recalculate_dependency

val forall Nat 'n, Nat 'm, 'n *8 = 'm. (implicit<'m>,(bit['m])) -> (bit['m]) effect pure byte_reverse
function forall Nat 'n, Nat 'm, 'n*8 = 'm. (bit['m]) effect pure byte_reverse((bit['m]) input) = {
  (bit['m]) output := 0;
  j := length(input);
  foreach (i from 0 to (length(input)) by 8) {
   output[i..i+7] := input[j - 7 ..j];
   j := j - 8; };
  output
}  

(* XXX effect for trap? *)
val extern unit -> unit effect {escape} trap

register (bit[1]) mode64bit
register (bit[1]) bigendianmode

val forall Nat 'W, 'W IN {8,16,32,64,128}. bit['W] -> bit['W] effect pure reverse_endianness
function rec forall Nat 'W, 'W IN {8, 16, 32, 64, 128}. bit['W] reverse_endianness ((bit['W]) value) =
{
    (nat) width := length(value);
    (nat) half := width quot 2;
    if width == 8 then value
    else reverse_endianness(value[half .. (width - 1)]) : reverse_endianness(value[0 .. (half - 1)]);
}

function forall Nat 'n. unit effect { wmv } MEMw ((bit[64]) ea, ([|'n|]) size, (bit[8*'n]) value) =
{
  if bigendianmode then
    MEMw'(ea, size, reverse_endianness(value))
  else
    MEMw'(ea, size, value)
}

function forall Nat 'n. (bit[8 * 'n]) effect { rmem } MEMr ((bit[64]) ea, ([|'n|]) size) =
{
  if bigendianmode then
    reverse_endianness(MEMr'(ea, size))
  else
    MEMr'(ea, size)
}

function forall Nat 'n. (bit[8 * 'n]) effect { rmem } MEMr_reserve ((bit[64]) ea, ([|'n|]) size) =
{
  if bigendianmode then
    reverse_endianness(MEMr_reserve'(ea, size))
  else
    MEMr_reserve'(ea, size)
}

function forall Nat 'n. bool effect { wmv } MEMw_conditional ((bit[64]) ea, ([|'n|]) size, (bit[8*'n]) value) =
{
  if bigendianmode then
    MEMw_conditional'(ea, size, reverse_endianness(value))
  else
    MEMw_conditional'(ea, size, value)
}



val (bit[64],bit) -> unit effect {rreg,wreg} set_overflow_cr0 
function (unit) set_overflow_cr0(target_register,new_xer_so) = {
  m:= 0;
  (bit[3]) c:= 0;
  (bit[64]) zero := 0;
  (if mode64bit
   then m := 0
   else m := 32);
  (if target_register[m..63] <_s zero[m..63]
  then c := 0b100
  else if target_register[m..63] >_s zero[m..63] 
  then c := 0b010
  else c := 0b001);
  CR.CR0 := c:[new_xer_so]
}

function (unit) set_SO_OV(overflow) =  {
  XER.OV := overflow;
  XER.SO := (XER.SO | overflow);
}

function forall Nat 'n. (bit['n]) zero_or_undef ((bit['n]) x) = {
  (bit['n]) out := 0;
  foreach (i from 0 to ((length(x)) - 1)) {
   out[i] := if x[i] then undefined else 0
  };
  out
}

scattered function unit execute
scattered typedef ast = const union

val bit[32] -> option<ast> effect pure decode

scattered function option<ast> decode

union ast member (bit[24], bit, bit) B

function clause decode (0b010010 : (bit[24]) LI : [AA] : [LK] as instr) = Some(B(LI,AA,LK))

function clause execute (B (LI, AA, LK)) =
  {
    if AA then NIA := EXTS(LI : 0b00) else NIA := CIA + EXTS(LI : 0b00);
    if LK then LR := CIA + 4 else ()
  }

union ast member (bit[5], bit[5], bit[14], bit, bit) Bc

function clause decode (0b010000 :
(bit[5]) BO :
(bit[5]) BI :
(bit[14]) BD :
[AA] :
[LK] as instr) =
  Some(Bc(BO,BI,BD,AA,LK))

function clause execute (Bc (BO, BI, BD, AA, LK)) =
  {
    if mode64bit then M := 0 else M := 32;
    (bit[64]) ctr_temp := CTR;
    if ~(BO[2])
    then {
      ctr_temp := ctr_temp - 1;
      CTR := ctr_temp
    }
    else ();
    ctr_ok := (BO[2] | ~(ctr_temp[M .. 63] == 0) ^ BO[3]);
    cond_ok := (BO[0] | CR[BI + 32] ^ ~(BO[1]));
    if ctr_ok & cond_ok
    then if AA then NIA := EXTS(BD : 0b00) else NIA := CIA + EXTS(BD : 0b00)
    else ();
    if LK then LR := CIA + 4 else ()
  }

union ast member (bit[5], bit[5], bit[2], bit) Bclr

function clause decode (0b010011 :
(bit[5]) BO :
(bit[5]) BI :
(bit[3]) _ :
(bit[2]) BH :
0b0000010000 :
[LK] as instr) =
  Some(Bclr(BO,BI,BH,LK))

function clause execute (Bclr (BO, BI, BH, LK)) =
  {
    if mode64bit then M := 0 else M := 32;
    (bit[64]) ctr_temp := CTR;
    if ~(BO[2])
    then {
      ctr_temp := ctr_temp - 1;
      CTR := ctr_temp
    }
    else ();
    ctr_ok := (BO[2] | ~(ctr_temp[M .. 63] == 0) ^ BO[3]);
    cond_ok := (BO[0] | CR[BI + 32] ^ ~(BO[1]));
    if ctr_ok & cond_ok then NIA := LR[0 .. 61] : 0b00 else ();
    if LK then LR := CIA + 4 else ()
  }

union ast member (bit[5], bit[5], bit[2], bit) Bcctr

function clause decode (0b010011 :
(bit[5]) BO :
(bit[5]) BI :
(bit[3]) _ :
(bit[2]) BH :
0b1000010000 :
[LK] as instr) =
  Some(Bcctr(BO,BI,BH,LK))

function clause execute (Bcctr (BO, BI, BH, LK)) =
  {
    cond_ok := (BO[0] | CR[BI + 32] ^ ~(BO[1]));
    if cond_ok then NIA := CTR[0 .. 61] : 0b00 else ();
    if LK then LR := CIA + 4 else ()
  }

union ast member (bit[5], bit[5], bit[5]) Crand

function clause decode (0b010011 :
(bit[5]) BT :
(bit[5]) BA :
(bit[5]) BB :
0b0100000001 :
(bit[1]) _ as instr) =
  Some(Crand(BT,BA,BB))

function clause execute (Crand (BT, BA, BB)) = CR[BT + 32] := (CR[BA + 32] & CR[BB + 32])

union ast member (bit[5], bit[5], bit[5]) Crnand

function clause decode (0b010011 :
(bit[5]) BT :
(bit[5]) BA :
(bit[5]) BB :
0b0011100001 :
(bit[1]) _ as instr) =
  Some(Crnand(BT,BA,BB))

function clause execute (Crnand (BT, BA, BB)) = CR[BT + 32] := ~(CR[BA + 32] & CR[BB + 32])

union ast member (bit[5], bit[5], bit[5]) Cror

function clause decode (0b010011 :
(bit[5]) BT :
(bit[5]) BA :
(bit[5]) BB :
0b0111000001 :
(bit[1]) _ as instr) =
  Some(Cror(BT,BA,BB))

function clause execute (Cror (BT, BA, BB)) = CR[BT + 32] := (CR[BA + 32] | CR[BB + 32])

union ast member (bit[5], bit[5], bit[5]) Crxor

function clause decode (0b010011 :
(bit[5]) BT :
(bit[5]) BA :
(bit[5]) BB :
0b0011000001 :
(bit[1]) _ as instr) =
  Some(Crxor(BT,BA,BB))

function clause execute (Crxor (BT, BA, BB)) = CR[BT + 32] := CR[BA + 32] ^ CR[BB + 32]

union ast member (bit[5], bit[5], bit[5]) Crnor

function clause decode (0b010011 :
(bit[5]) BT :
(bit[5]) BA :
(bit[5]) BB :
0b0000100001 :
(bit[1]) _ as instr) =
  Some(Crnor(BT,BA,BB))

function clause execute (Crnor (BT, BA, BB)) = CR[BT + 32] := ~(CR[BA + 32] | CR[BB + 32])

union ast member (bit[5], bit[5], bit[5]) Creqv

function clause decode (0b010011 :
(bit[5]) BT :
(bit[5]) BA :
(bit[5]) BB :
0b0100100001 :
(bit[1]) _ as instr) =
  Some(Creqv(BT,BA,BB))

function clause execute (Creqv (BT, BA, BB)) = CR[BT + 32] := CR[BA + 32] ^ ~(CR[BB + 32])

union ast member (bit[5], bit[5], bit[5]) Crandc

function clause decode (0b010011 :
(bit[5]) BT :
(bit[5]) BA :
(bit[5]) BB :
0b0010000001 :
(bit[1]) _ as instr) =
  Some(Crandc(BT,BA,BB))

function clause execute (Crandc (BT, BA, BB)) = CR[BT + 32] := (CR[BA + 32] & ~(CR[BB + 32]))

union ast member (bit[5], bit[5], bit[5]) Crorc

function clause decode (0b010011 :
(bit[5]) BT :
(bit[5]) BA :
(bit[5]) BB :
0b0110100001 :
(bit[1]) _ as instr) =
  Some(Crorc(BT,BA,BB))

function clause execute (Crorc (BT, BA, BB)) = CR[BT + 32] := (CR[BA + 32] | ~(CR[BB + 32]))

union ast member (bit[3], bit[3]) Mcrf

function clause decode (0b010011 :
(bit[3]) BF :
(bit[2]) _ :
(bit[3]) BFA :
(bit[2]) _ :
(bit[5]) _ :
0b0000000000 :
(bit[1]) _ as instr) =
  Some(Mcrf(BF,BFA))

function clause execute (Mcrf (BF, BFA)) =
  CR[4 * BF + 32..4 * BF + 35] := CR[4 * BFA + 32 .. 4 * BFA + 35]

union ast member (bit[7]) Sc

function clause decode (0b010001 :
(bit[5]) _ :
(bit[5]) _ :
(bit[4]) _ :
(bit[7]) LEV :
(bit[3]) _ :
0b1 :
(bit[1]) _ as instr) =
  Some(Sc(LEV))

function clause execute (Sc (LEV)) = ()

union ast member (bit[7]) Scv

function clause decode (0b010001 :
(bit[5]) _ :
(bit[5]) _ :
(bit[4]) _ :
(bit[7]) LEV :
(bit[3]) _ :
0b0 :
0b1 as instr) =
  Some(Scv(LEV))

function clause execute (Scv (LEV)) = ()

union ast member (bit[5], bit[5], bit[16]) Lbz

function clause decode (0b100010 :
(bit[5]) RT :
(bit[5]) RA :
(bit[16]) D as instr) =
  Some(Lbz(RT,RA,D))

function clause execute (Lbz (RT, RA, D)) =
  {
    (bit[64]) b := 0;
    (bit[64]) EA := 0;
    if RA == 0 then b := 0 else b := GPR[RA];
    EA := b + EXTS(D);
    GPR[RT] := 0b00000000000000000000000000000000000000000000000000000000 : MEMr(EA,1)
  }

union ast member (bit[5], bit[5], bit[5]) Lbzx

function clause decode (0b011111 :
(bit[5]) RT :
(bit[5]) RA :
(bit[5]) RB :
0b0001010111 :
(bit[1]) _ as instr) =
  Some(Lbzx(RT,RA,RB))

function clause execute (Lbzx (RT, RA, RB)) =
  {
    (bit[64]) b := 0;
    (bit[64]) EA := 0;
    if RA == 0 then b := 0 else b := GPR[RA];
    EA := b + GPR[RB];
    GPR[RT] := 0b00000000000000000000000000000000000000000000000000000000 : MEMr(EA,1)
  }

union ast member (bit[5], bit[5], bit[16]) Lbzu

function clause decode (0b100011 :
(bit[5]) RT :
(bit[5]) RA :
(bit[16]) D as instr) =
  Some(Lbzu(RT,RA,D))

function clause execute (Lbzu (RT, RA, D)) =
  {
    (bit[64]) EA := 0;
    EA := GPR[RA] + EXTS(D);
    GPR[RA] := EA;
    GPR[RT] := 0b00000000000000000000000000000000000000000000000000000000 : MEMr(EA,1)
  }

union ast member (bit[5], bit[5], bit[5]) Lbzux

function clause decode (0b011111 :
(bit[5]) RT :
(bit[5]) RA :
(bit[5]) RB :
0b0001110111 :
(bit[1]) _ as instr) =
  Some(Lbzux(RT,RA,RB))

function clause execute (Lbzux (RT, RA, RB)) =
  {
    (bit[64]) EA := 0;
    EA := GPR[RA] + GPR[RB];
    GPR[RA] := EA;
    GPR[RT] := 0b00000000000000000000000000000000000000000000000000000000 : MEMr(EA,1)
  }

union ast member (bit[5], bit[5], bit[16]) Lhz

function clause decode (0b101000 :
(bit[5]) RT :
(bit[5]) RA :
(bit[16]) D as instr) =
  Some(Lhz(RT,RA,D))

function clause execute (Lhz (RT, RA, D)) =
  {
    (bit[64]) b := 0;
    (bit[64]) EA := 0;
    if RA == 0 then b := 0 else b := GPR[RA];
    EA := b + EXTS(D);
    GPR[RT] := 0b000000000000000000000000000000000000000000000000 : MEMr(EA,2)
  }

union ast member (bit[5], bit[5], bit[5]) Lhzx

function clause decode (0b011111 :
(bit[5]) RT :
(bit[5]) RA :
(bit[5]) RB :
0b0100010111 :
(bit[1]) _ as instr) =
  Some(Lhzx(RT,RA,RB))

function clause execute (Lhzx (RT, RA, RB)) =
  {
    (bit[64]) b := 0;
    (bit[64]) EA := 0;
    if RA == 0 then b := 0 else b := GPR[RA];
    EA := b + GPR[RB];
    GPR[RT] := 0b000000000000000000000000000000000000000000000000 : MEMr(EA,2)
  }

union ast member (bit[5], bit[5], bit[16]) Lhzu

function clause decode (0b101001 :
(bit[5]) RT :
(bit[5]) RA :
(bit[16]) D as instr) =
  Some(Lhzu(RT,RA,D))

function clause execute (Lhzu (RT, RA, D)) =
  {
    (bit[64]) EA := 0;
    EA := GPR[RA] + EXTS(D);
    GPR[RA] := EA;
    GPR[RT] := 0b000000000000000000000000000000000000000000000000 : MEMr(EA,2)
  }

union ast member (bit[5], bit[5], bit[5]) Lhzux

function clause decode (0b011111 :
(bit[5]) RT :
(bit[5]) RA :
(bit[5]) RB :
0b0100110111 :
(bit[1]) _ as instr) =
  Some(Lhzux(RT,RA,RB))

function clause execute (Lhzux (RT, RA, RB)) =
  {
    (bit[64]) EA := 0;
    EA := GPR[RA] + GPR[RB];
    GPR[RA] := EA;
    GPR[RT] := 0b000000000000000000000000000000000000000000000000 : MEMr(EA,2)
  }

union ast member (bit[5], bit[5], bit[16]) Lha

function clause decode (0b101010 :
(bit[5]) RT :
(bit[5]) RA :
(bit[16]) D as instr) =
  Some(Lha(RT,RA,D))

function clause execute (Lha (RT, RA, D)) =
  {
    (bit[64]) b := 0;
    (bit[64]) EA := 0;
    if RA == 0 then b := 0 else b := GPR[RA];
    EA := b + EXTS(D);
    GPR[RT] := EXTS(MEMr(EA,2))
  }

union ast member (bit[5], bit[5], bit[5]) Lhax

function clause decode (0b011111 :
(bit[5]) RT :
(bit[5]) RA :
(bit[5]) RB :
0b0101010111 :
(bit[1]) _ as instr) =
  Some(Lhax(RT,RA,RB))

function clause execute (Lhax (RT, RA, RB)) =
  {
    (bit[64]) b := 0;
    (bit[64]) EA := 0;
    if RA == 0 then b := 0 else b := GPR[RA];
    EA := b + GPR[RB];
    GPR[RT] := EXTS(MEMr(EA,2))
  }

union ast member (bit[5], bit[5], bit[16]) Lhau

function clause decode (0b101011 :
(bit[5]) RT :
(bit[5]) RA :
(bit[16]) D as instr) =
  Some(Lhau(RT,RA,D))

function clause execute (Lhau (RT, RA, D)) =
  {
    (bit[64]) EA := 0;
    EA := GPR[RA] + EXTS(D);
    GPR[RA] := EA;
    GPR[RT] := EXTS(MEMr(EA,2))
  }

union ast member (bit[5], bit[5], bit[5]) Lhaux

function clause decode (0b011111 :
(bit[5]) RT :
(bit[5]) RA :
(bit[5]) RB :
0b0101110111 :
(bit[1]) _ as instr) =
  Some(Lhaux(RT,RA,RB))

function clause execute (Lhaux (RT, RA, RB)) =
  {
    (bit[64]) EA := 0;
    EA := GPR[RA] + GPR[RB];
    GPR[RA] := EA;
    GPR[RT] := EXTS(MEMr(EA,2))
  }

union ast member (bit[5], bit[5], bit[16]) Lwz

function clause decode (0b100000 :
(bit[5]) RT :
(bit[5]) RA :
(bit[16]) D as instr) =
  Some(Lwz(RT,RA,D))

function clause execute (Lwz (RT, RA, D)) =
  {
    (bit[64]) b := 0;
    (bit[64]) EA := 0;
    if RA == 0 then b := 0 else b := GPR[RA];
    EA := b + EXTS(D);
    GPR[RT] := 0b00000000000000000000000000000000 : MEMr(EA,4)
  }

union ast member (bit[5], bit[5], bit[5]) Lwzx

function clause decode (0b011111 :
(bit[5]) RT :
(bit[5]) RA :
(bit[5]) RB :
0b0000010111 :
(bit[1]) _ as instr) =
  Some(Lwzx(RT,RA,RB))

function clause execute (Lwzx (RT, RA, RB)) =
  {
    (bit[64]) b := 0;
    (bit[64]) EA := 0;
    if RA == 0 then b := 0 else b := GPR[RA];
    EA := b + GPR[RB];
    GPR[RT] := 0b00000000000000000000000000000000 : MEMr(EA,4)
  }

union ast member (bit[5], bit[5], bit[16]) Lwzu

function clause decode (0b100001 :
(bit[5]) RT :
(bit[5]) RA :
(bit[16]) D as instr) =
  Some(Lwzu(RT,RA,D))

function clause execute (Lwzu (RT, RA, D)) =
  {
    (bit[64]) EA := 0;
    EA := GPR[RA] + EXTS(D);
    GPR[RA] := EA;
    GPR[RT] := 0b00000000000000000000000000000000 : MEMr(EA,4)
  }

union ast member (bit[5], bit[5], bit[5]) Lwzux

function clause decode (0b011111 :
(bit[5]) RT :
(bit[5]) RA :
(bit[5]) RB :
0b0000110111 :
(bit[1]) _ as instr) =
  Some(Lwzux(RT,RA,RB))

function clause execute (Lwzux (RT, RA, RB)) =
  {
    (bit[64]) EA := 0;
    EA := GPR[RA] + GPR[RB];
    GPR[RA] := EA;
    GPR[RT] := 0b00000000000000000000000000000000 : MEMr(EA,4)
  }

union ast member (bit[5], bit[5], bit[14]) Lwa

function clause decode (0b111010 :
(bit[5]) RT :
(bit[5]) RA :
(bit[14]) DS :
0b10 as instr) =
  Some(Lwa(RT,RA,DS))

function clause execute (Lwa (RT, RA, DS)) =
  {
    (bit[64]) b := 0;
    (bit[64]) EA := 0;
    if RA == 0 then b := 0 else b := GPR[RA];
    EA := b + EXTS(DS : 0b00);
    GPR[RT] := EXTS(MEMr(EA,4))
  }

union ast member (bit[5], bit[5], bit[5]) Lwax

function clause decode (0b011111 :
(bit[5]) RT :
(bit[5]) RA :
(bit[5]) RB :
0b0101010101 :
(bit[1]) _ as instr) =
  Some(Lwax(RT,RA,RB))

function clause execute (Lwax (RT, RA, RB)) =
  {
    (bit[64]) b := 0;
    (bit[64]) EA := 0;
    if RA == 0 then b := 0 else b := GPR[RA];
    EA := b + GPR[RB];
    GPR[RT] := EXTS(MEMr(EA,4))
  }

union ast member (bit[5], bit[5], bit[5]) Lwaux

function clause decode (0b011111 :
(bit[5]) RT :
(bit[5]) RA :
(bit[5]) RB :
0b0101110101 :
(bit[1]) _ as instr) =
  Some(Lwaux(RT,RA,RB))

function clause execute (Lwaux (RT, RA, RB)) =
  {
    (bit[64]) EA := 0;
    EA := GPR[RA] + GPR[RB];
    GPR[RA] := EA;
    GPR[RT] := EXTS(MEMr(EA,4))
  }

union ast member (bit[5], bit[5], bit[14]) Ld

function clause decode (0b111010 :
(bit[5]) RT :
(bit[5]) RA :
(bit[14]) DS :
0b00 as instr) =
  Some(Ld(RT,RA,DS))

function clause execute (Ld (RT, RA, DS)) =
  {
    (bit[64]) b := 0;
    (bit[64]) EA := 0;
    if RA == 0 then b := 0 else b := GPR[RA];
    EA := b + EXTS(DS : 0b00);
    GPR[RT] := MEMr(EA,8)
  }

union ast member (bit[5], bit[5], bit[5]) Ldx

function clause decode (0b011111 :
(bit[5]) RT :
(bit[5]) RA :
(bit[5]) RB :
0b0000010101 :
(bit[1]) _ as instr) =
  Some(Ldx(RT,RA,RB))

function clause execute (Ldx (RT, RA, RB)) =
  {
    (bit[64]) b := 0;
    (bit[64]) EA := 0;
    if RA == 0 then b := 0 else b := GPR[RA];
    EA := b + GPR[RB];
    GPR[RT] := MEMr(EA,8)
  }

union ast member (bit[5], bit[5], bit[14]) Ldu

function clause decode (0b111010 :
(bit[5]) RT :
(bit[5]) RA :
(bit[14]) DS :
0b01 as instr) =
  Some(Ldu(RT,RA,DS))

function clause execute (Ldu (RT, RA, DS)) =
  {
    (bit[64]) EA := 0;
    EA := GPR[RA] + EXTS(DS : 0b00);
    GPR[RA] := EA;
    GPR[RT] := MEMr(EA,8)
  }

union ast member (bit[5], bit[5], bit[5]) Ldux

function clause decode (0b011111 :
(bit[5]) RT :
(bit[5]) RA :
(bit[5]) RB :
0b0000110101 :
(bit[1]) _ as instr) =
  Some(Ldux(RT,RA,RB))

function clause execute (Ldux (RT, RA, RB)) =
  {
    (bit[64]) EA := 0;
    EA := GPR[RA] + GPR[RB];
    GPR[RA] := EA;
    GPR[RT] := MEMr(EA,8)
  }

union ast member (bit[5], bit[5], bit[16]) Stb

function clause decode (0b100110 :
(bit[5]) RS :
(bit[5]) RA :
(bit[16]) D as instr) =
  Some(Stb(RS,RA,D))

function clause execute (Stb (RS, RA, D)) =
  {
    (bit[64]) b := 0;
    (bit[64]) EA := 0;
    if RA == 0 then b := 0 else b := GPR[RA];
    EA := b + EXTS(D);
    MEMw_EA(EA,1);
    MEMw(EA,1) := (GPR[RS])[56 .. 63]
  }

union ast member (bit[5], bit[5], bit[5]) Stbx

function clause decode (0b011111 :
(bit[5]) RS :
(bit[5]) RA :
(bit[5]) RB :
0b0011010111 :
(bit[1]) _ as instr) =
  Some(Stbx(RS,RA,RB))

function clause execute (Stbx (RS, RA, RB)) =
  {
    (bit[64]) b := 0;
    (bit[64]) EA := 0;
    if RA == 0 then b := 0 else b := GPR[RA];
    EA := b + GPR[RB];
    MEMw_EA(EA,1);
    MEMw(EA,1) := (GPR[RS])[56 .. 63]
  }

union ast member (bit[5], bit[5], bit[16]) Stbu

function clause decode (0b100111 :
(bit[5]) RS :
(bit[5]) RA :
(bit[16]) D as instr) =
  Some(Stbu(RS,RA,D))

function clause execute (Stbu (RS, RA, D)) =
  {
    (bit[64]) EA := 0;
    EA := GPR[RA] + EXTS(D);
    MEMw_EA(EA,1);
    GPR[RA] := EA;
    MEMw(EA,1) := (GPR[RS])[56 .. 63]
  }

union ast member (bit[5], bit[5], bit[5]) Stbux

function clause decode (0b011111 :
(bit[5]) RS :
(bit[5]) RA :
(bit[5]) RB :
0b0011110111 :
(bit[1]) _ as instr) =
  Some(Stbux(RS,RA,RB))

function clause execute (Stbux (RS, RA, RB)) =
  {
    (bit[64]) EA := 0;
    EA := GPR[RA] + GPR[RB];
    MEMw_EA(EA,1);
    GPR[RA] := EA;
    MEMw(EA,1) := (GPR[RS])[56 .. 63]
  }

union ast member (bit[5], bit[5], bit[16]) Sth

function clause decode (0b101100 :
(bit[5]) RS :
(bit[5]) RA :
(bit[16]) D as instr) =
  Some(Sth(RS,RA,D))

function clause execute (Sth (RS, RA, D)) =
  {
    (bit[64]) b := 0;
    (bit[64]) EA := 0;
    if RA == 0 then b := 0 else b := GPR[RA];
    EA := b + EXTS(D);
    MEMw_EA(EA,2);
    MEMw(EA,2) := (GPR[RS])[48 .. 63]
  }

union ast member (bit[5], bit[5], bit[5]) Sthx

function clause decode (0b011111 :
(bit[5]) RS :
(bit[5]) RA :
(bit[5]) RB :
0b0110010111 :
(bit[1]) _ as instr) =
  Some(Sthx(RS,RA,RB))

function clause execute (Sthx (RS, RA, RB)) =
  {
    (bit[64]) b := 0;
    (bit[64]) EA := 0;
    if RA == 0 then b := 0 else b := GPR[RA];
    EA := b + GPR[RB];
    MEMw_EA(EA,2);
    MEMw(EA,2) := (GPR[RS])[48 .. 63]
  }

union ast member (bit[5], bit[5], bit[16]) Sthu

function clause decode (0b101101 :
(bit[5]) RS :
(bit[5]) RA :
(bit[16]) D as instr) =
  Some(Sthu(RS,RA,D))

function clause execute (Sthu (RS, RA, D)) =
  {
    (bit[64]) EA := 0;
    EA := GPR[RA] + EXTS(D);
    MEMw_EA(EA,2);
    GPR[RA] := EA;
    MEMw(EA,2) := (GPR[RS])[48 .. 63]
  }

union ast member (bit[5], bit[5], bit[5]) Sthux

function clause decode (0b011111 :
(bit[5]) RS :
(bit[5]) RA :
(bit[5]) RB :
0b0110110111 :
(bit[1]) _ as instr) =
  Some(Sthux(RS,RA,RB))

function clause execute (Sthux (RS, RA, RB)) =
  {
    (bit[64]) EA := 0;
    EA := GPR[RA] + GPR[RB];
    MEMw_EA(EA,2);
    GPR[RA] := EA;
    MEMw(EA,2) := (GPR[RS])[48 .. 63]
  }

union ast member (bit[5], bit[5], bit[16]) Stw

function clause decode (0b100100 :
(bit[5]) RS :
(bit[5]) RA :
(bit[16]) D as instr) =
  Some(Stw(RS,RA,D))

function clause execute (Stw (RS, RA, D)) =
  {
    (bit[64]) b := 0;
    (bit[64]) EA := 0;
    if RA == 0 then b := 0 else b := GPR[RA];
    EA := b + EXTS(D);
    MEMw_EA(EA,4);
    MEMw(EA,4) := (GPR[RS])[32 .. 63]
  }

union ast member (bit[5], bit[5], bit[5]) Stwx

function clause decode (0b011111 :
(bit[5]) RS :
(bit[5]) RA :
(bit[5]) RB :
0b0010010111 :
(bit[1]) _ as instr) =
  Some(Stwx(RS,RA,RB))

function clause execute (Stwx (RS, RA, RB)) =
  {
    (bit[64]) b := 0;
    (bit[64]) EA := 0;
    if RA == 0 then b := 0 else b := GPR[RA];
    EA := b + GPR[RB];
    MEMw_EA(EA,4);
    MEMw(EA,4) := (GPR[RS])[32 .. 63]
  }

union ast member (bit[5], bit[5], bit[16]) Stwu

function clause decode (0b100101 :
(bit[5]) RS :
(bit[5]) RA :
(bit[16]) D as instr) =
  Some(Stwu(RS,RA,D))

function clause execute (Stwu (RS, RA, D)) =
  {
    (bit[64]) EA := 0;
    EA := GPR[RA] + EXTS(D);
    MEMw_EA(EA,4);
    GPR[RA] := EA;
    MEMw(EA,4) := (GPR[RS])[32 .. 63]
  }

union ast member (bit[5], bit[5], bit[5]) Stwux

function clause decode (0b011111 :
(bit[5]) RS :
(bit[5]) RA :
(bit[5]) RB :
0b0010110111 :
(bit[1]) _ as instr) =
  Some(Stwux(RS,RA,RB))

function clause execute (Stwux (RS, RA, RB)) =
  {
    (bit[64]) EA := 0;
    EA := GPR[RA] + GPR[RB];
    MEMw_EA(EA,4);
    GPR[RA] := EA;
    MEMw(EA,4) := (GPR[RS])[32 .. 63]
  }

union ast member (bit[5], bit[5], bit[14]) Std

function clause decode (0b111110 :
(bit[5]) RS :
(bit[5]) RA :
(bit[14]) DS :
0b00 as instr) =
  Some(Std(RS,RA,DS))

function clause execute (Std (RS, RA, DS)) =
  {
    (bit[64]) b := 0;
    (bit[64]) EA := 0;
    if RA == 0 then b := 0 else b := GPR[RA];
    EA := b + EXTS(DS : 0b00);
    MEMw_EA(EA,8);
    MEMw(EA,8) := GPR[RS]
  }

union ast member (bit[5], bit[5], bit[5]) Stdx

function clause decode (0b011111 :
(bit[5]) RS :
(bit[5]) RA :
(bit[5]) RB :
0b0010010101 :
(bit[1]) _ as instr) =
  Some(Stdx(RS,RA,RB))

function clause execute (Stdx (RS, RA, RB)) =
  {
    (bit[64]) b := 0;
    (bit[64]) EA := 0;
    if RA == 0 then b := 0 else b := GPR[RA];
    EA := b + GPR[RB];
    MEMw_EA(EA,8);
    MEMw(EA,8) := GPR[RS]
  }

union ast member (bit[5], bit[5], bit[14]) Stdu

function clause decode (0b111110 :
(bit[5]) RS :
(bit[5]) RA :
(bit[14]) DS :
0b01 as instr) =
  Some(Stdu(RS,RA,DS))

function clause execute (Stdu (RS, RA, DS)) =
  {
    (bit[64]) EA := 0;
    EA := GPR[RA] + EXTS(DS : 0b00);
    MEMw_EA(EA,8);
    GPR[RA] := EA;
    MEMw(EA,8) := GPR[RS]
  }

union ast member (bit[5], bit[5], bit[5]) Stdux

function clause decode (0b011111 :
(bit[5]) RS :
(bit[5]) RA :
(bit[5]) RB :
0b0010110101 :
(bit[1]) _ as instr) =
  Some(Stdux(RS,RA,RB))

function clause execute (Stdux (RS, RA, RB)) =
  {
    (bit[64]) EA := 0;
    EA := GPR[RA] + GPR[RB];
    MEMw_EA(EA,8);
    GPR[RA] := EA;
    MEMw(EA,8) := GPR[RS]
  }

union ast member (bit[5], bit[5], bit[12], bit[4]) Lq

function clause decode (0b111000 :
(bit[5]) RTp :
(bit[5]) RA :
(bit[12]) DQ :
(bit[4]) PT as instr) =
  Some(Lq(RTp,RA,DQ,PT))

function clause execute (Lq (RTp, RA, DQ, PT)) =
  {
    (bit[64]) EA := 0;
    (bit[64]) b := 0;
    if RA == 0 then b := 0 else b := GPR[RA];
    EA := b + EXTS(DQ : 0b0000);
    (bit[128]) mem := MEMr(EA,16);
    if bigendianmode
    then {
      GPR[RTp] := mem[0 .. 63];
      GPR[RTp + 1] := mem[64 .. 127]
    }
    else {
      (bit[128]) bytereverse := byte_reverse(mem);
      GPR[RTp] := bytereverse[0 .. 63];
      GPR[RTp + 1] := bytereverse[64 .. 127]
    }
  }

union ast member (bit[5], bit[5], bit[14]) Stq

function clause decode (0b111110 :
(bit[5]) RSp :
(bit[5]) RA :
(bit[14]) DS :
0b10 as instr) =
  Some(Stq(RSp,RA,DS))

function clause execute (Stq (RSp, RA, DS)) =
  {
    (bit[64]) b := 0;
    (bit[64]) EA := 0;
    if RA == 0 then b := 0 else b := GPR[RA];
    EA := b + EXTS(DS : 0b00);
    MEMw_EA(EA,16);
    (bit[128]) mem := 0;
    mem[0..63] := GPR[RSp];
    mem[64..127] := GPR[RSp + 1];
    if ~(bigendianmode) then mem := byte_reverse(mem) else ();
    MEMw(EA,16) := mem
  }

union ast member (bit[5], bit[5], bit[5]) Lhbrx

function clause decode (0b011111 :
(bit[5]) RT :
(bit[5]) RA :
(bit[5]) RB :
0b1100010110 :
(bit[1]) _ as instr) =
  Some(Lhbrx(RT,RA,RB))

function clause execute (Lhbrx (RT, RA, RB)) =
  {
    (bit[64]) b := 0;
    (bit[64]) EA := 0;
    if RA == 0 then b := 0 else b := GPR[RA];
    EA := b + GPR[RB];
    load_data := MEMr(EA,2);
    GPR[RT] :=
      0b000000000000000000000000000000000000000000000000 : load_data[8 .. 15] : load_data[0 .. 7]
  }

union ast member (bit[5], bit[5], bit[5]) Sthbrx

function clause decode (0b011111 :
(bit[5]) RS :
(bit[5]) RA :
(bit[5]) RB :
0b1110010110 :
(bit[1]) _ as instr) =
  Some(Sthbrx(RS,RA,RB))

function clause execute (Sthbrx (RS, RA, RB)) =
  {
    (bit[64]) b := 0;
    (bit[64]) EA := 0;
    if RA == 0 then b := 0 else b := GPR[RA];
    EA := b + GPR[RB];
    MEMw_EA(EA,2);
    MEMw(EA,2) := (GPR[RS])[56 .. 63] : (GPR[RS])[48 .. 55]
  }

union ast member (bit[5], bit[5], bit[5]) Lwbrx

function clause decode (0b011111 :
(bit[5]) RT :
(bit[5]) RA :
(bit[5]) RB :
0b1000010110 :
(bit[1]) _ as instr) =
  Some(Lwbrx(RT,RA,RB))

function clause execute (Lwbrx (RT, RA, RB)) =
  {
    (bit[64]) b := 0;
    (bit[64]) EA := 0;
    if RA == 0 then b := 0 else b := GPR[RA];
    EA := b + GPR[RB];
    load_data := MEMr(EA,4);
    GPR[RT] :=
      0b00000000000000000000000000000000 :
        load_data[24 .. 31] : load_data[16 .. 23] : load_data[8 .. 15] : load_data[0 .. 7]
  }

union ast member (bit[5], bit[5], bit[5]) Stwbrx

function clause decode (0b011111 :
(bit[5]) RS :
(bit[5]) RA :
(bit[5]) RB :
0b1010010110 :
(bit[1]) _ as instr) =
  Some(Stwbrx(RS,RA,RB))

function clause execute (Stwbrx (RS, RA, RB)) =
  {
    (bit[64]) b := 0;
    (bit[64]) EA := 0;
    if RA == 0 then b := 0 else b := GPR[RA];
    EA := b + GPR[RB];
    MEMw_EA(EA,4);
    MEMw(EA,4) :=
      (GPR[RS])[56 .. 63] : (GPR[RS])[48 .. 55] : (GPR[RS])[40 .. 47] : (GPR[RS])[32 .. 39]
  }

union ast member (bit[5], bit[5], bit[5]) Ldbrx

function clause decode (0b011111 :
(bit[5]) RT :
(bit[5]) RA :
(bit[5]) RB :
0b1000010100 :
(bit[1]) _ as instr) =
  Some(Ldbrx(RT,RA,RB))

function clause execute (Ldbrx (RT, RA, RB)) =
  {
    (bit[64]) b := 0;
    (bit[64]) EA := 0;
    if RA == 0 then b := 0 else b := GPR[RA];
    EA := b + GPR[RB];
    load_data := MEMr(EA,8);
    GPR[RT] :=
      load_data[56 .. 63] :
        load_data[48 .. 55] :
          load_data[40 .. 47] :
            load_data[32 .. 39] :
              load_data[24 .. 31] : load_data[16 .. 23] : load_data[8 .. 15] : load_data[0 .. 7]
  }

union ast member (bit[5], bit[5], bit[5]) Stdbrx

function clause decode (0b011111 :
(bit[5]) RS :
(bit[5]) RA :
(bit[5]) RB :
0b1010010100 :
(bit[1]) _ as instr) =
  Some(Stdbrx(RS,RA,RB))

function clause execute (Stdbrx (RS, RA, RB)) =
  {
    (bit[64]) b := 0;
    (bit[64]) EA := 0;
    if RA == 0 then b := 0 else b := GPR[RA];
    EA := b + GPR[RB];
    MEMw_EA(EA,8);
    MEMw(EA,8) :=
      (GPR[RS])[56 .. 63] :
        (GPR[RS])[48 .. 55] :
          (GPR[RS])[40 .. 47] :
            (GPR[RS])[32 .. 39] :
              (GPR[RS])[24 .. 31] : (GPR[RS])[16 .. 23] : (GPR[RS])[8 .. 15] : (GPR[RS])[0 .. 7]
  }

union ast member (bit[5], bit[5], bit[16]) Lmw

function clause decode (0b101110 :
(bit[5]) RT :
(bit[5]) RA :
(bit[16]) D as instr) =
  Some(Lmw(RT,RA,D))

function clause execute (Lmw (RT, RA, D)) =
  {
    (bit[64]) b := 0;
    (bit[64]) EA := 0;
    if RA == 0 then b := 0 else b := GPR[RA];
    EA := b + EXTS(D);
    size := ([|32|])(sub(32, RT)) * 4;
    buffer := MEMr(EA,size);
    i := 0;
    foreach (r from RT to 31 by 1 in inc)
    {
      GPR[r] := 0b00000000000000000000000000000000 : buffer[i .. i + 31];
      i := i + 32
    }
  }

union ast member (bit[5], bit[5], bit[16]) Stmw

function clause decode (0b101111 :
(bit[5]) RS :
(bit[5]) RA :
(bit[16]) D as instr) =
  Some(Stmw(RS,RA,D))

function clause execute (Stmw (RS, RA, D)) =
  {
    (bit[64]) b := 0;
    (bit[64]) EA := 0;
    if RA == 0 then b := 0 else b := GPR[RA];
    EA := b + EXTS(D);
    size := ([|32|]) (sub(32, RS)) * 4;
    MEMw_EA(EA,size);
    (bit[994]) buffer := zeros(994);
    i := 0;
    foreach (r from RS to 31 by 1 in inc)
    {
      buffer[i..i + 31] := (GPR[r])[32 .. 63];
      i := i + 32
    };
    MEMw(EA,size) := buffer[0 .. size * 8 - 1]
  }

union ast member (bit[5], bit[5], bit[5]) Lswi

function clause decode (0b011111 :
(bit[5]) RT :
(bit[5]) RA :
(bit[5]) NB :
0b1001010101 :
(bit[1]) _ as instr) =
  Some(Lswi(RT,RA,NB))

function clause execute (Lswi (RT, RA, NB)) =
  {
    (bit[64]) EA := 0;
    if RA == 0 then EA := 0 else EA := GPR[RA];
    ([|31|]) r := 0;
    r := RT - 1;
    ([|32|]) size := if NB == 0 then 32 else NB;
    (bit[256]) membuffer := MEMr(EA,size);
    j := 0;
    i := 32;
    foreach (n from (if NB == 0 then 32 else NB) to 1 by 1 in dec)
    {
      if i == 32
      then {
        r := ([|31|]) (r + 1) mod 32;
        GPR[r] := 0
      }
      else ();
      (GPR[r])[i..i + 7] := membuffer[j .. j + 7];
      j := j + 8;
      i := i + 8;
      if i == 64 then i := 32 else ();
      EA := EA + 1
    }
  }

union ast member (bit[5], bit[5], bit[5]) Lswx

function clause decode (0b011111 :
(bit[5]) RT :
(bit[5]) RA :
(bit[5]) RB :
0b1000010101 :
(bit[1]) _ as instr) =
  Some(Lswx(RT,RA,RB))

function clause execute (Lswx (RT, RA, RB)) =
  {
    (bit[64]) b := 0;
    (bit[64]) EA := 0;
    if RA == 0 then b := 0 else b := GPR[RA];
    ([|31|]) r := 0;
    EA := b + GPR[RB];
    r := RT - 1;
    i := 32;
    ([|128|]) n_top := XER[57 .. 63];
    recalculate_dependency(());
    if n_top == 0
    then GPR[RT] := undefined
    else {
      (bit[512]) membuffer := MEMr(EA,n_top);
      j := 0;
      n_r := n_top quot 4;
      n_mod := n_top mod 4;
      n_r := if n_mod == 0 then n_r else n_r + 1;
      foreach (n from n_r to 1 by 1 in dec)
      {
        r := ([|32|]) (r + 1) mod 32;
        (bit[64]) temp := 0;
        if n == 1
        then switch n_mod {
          case 0 -> temp[32..63] := membuffer[j .. j + 31]
          case 1 -> temp[32..39] := membuffer[j .. j + 7]
          case 2 -> temp[32..47] := membuffer[j .. j + 15]
          case 3 -> temp[32..55] := membuffer[j .. j + 23]
        }
        else temp[32..63] := membuffer[j .. j + 31];
        j := j + 32;
        GPR[r] := temp
      }
    }
  }

union ast member (bit[5], bit[5], bit[5]) Stswi

function clause decode (0b011111 :
(bit[5]) RS :
(bit[5]) RA :
(bit[5]) NB :
0b1011010101 :
(bit[1]) _ as instr) =
  Some(Stswi(RS,RA,NB))

function clause execute (Stswi (RS, RA, NB)) =
  {
    (bit[64]) EA := 0;
    if RA == 0 then EA := 0 else EA := GPR[RA];
    ([|31|]) r := 0;
    r := RS - 1;
    ([|32|]) size := if NB == 0 then 32 else NB;
    MEMw_EA(EA,size);
    (bit[256]) membuffer := zeros(255);
    j := 0;
    i := 32;
    foreach (n from (if NB == 0 then 32 else NB) to 1 by 1 in dec)
    {
      if i == 32 then r := ([|32|]) (r + 1) mod 32 else ();
      membuffer[j..j + 7] := (GPR[r])[i .. i + 7];
      j := j + 8;
      i := i + 8;
      if i == 64 then i := 32 else ()
    };
    MEMw(EA,size) := membuffer[0 .. size * 8 - 1]
  }

union ast member (bit[5], bit[5], bit[5]) Stswx

function clause decode (0b011111 :
(bit[5]) RS :
(bit[5]) RA :
(bit[5]) RB :
0b1010010101 :
(bit[1]) _ as instr) =
  Some(Stswx(RS,RA,RB))

function clause execute (Stswx (RS, RA, RB)) =
  {
    (bit[64]) b := 0;
    (bit[64]) EA := 0;
    if RA == 0 then b := 0 else b := GPR[RA];
    ([|31|]) r := 0;
    EA := b + GPR[RB];
    r := RS - 1;
    i := 32;
    ([|128|]) n_top := XER[57 .. 63];
    recalculate_dependency(());
    MEMw_EA(EA,n_top);
    (bit[512]) membuffer := zeros(512);
    j := 0;
    foreach (n from n_top to 1 by 1 in dec)
    {
      if i == 32 then r := ([|32|]) (r + 1) mod 32 else ();
      membuffer[j..j + 7] := (GPR[r])[i .. i + 7];
      i := i + 8;
      j := j + 8;
      if i == 64 then i := 32 else ()
    };
    if ~(n_top == 0) then MEMw(EA,n_top) := membuffer[0 .. n_top * 8 - 1] else ()
  }

union ast member (bit[5], bit[5], bit[16]) Addi

function clause decode (0b001110 :
(bit[5]) RT :
(bit[5]) RA :
(bit[16]) SI as instr) =
  Some(Addi(RT,RA,SI))

function clause execute (Addi (RT, RA, SI)) =
  if RA == 0 then GPR[RT] := EXTS(SI) else GPR[RT] := GPR[RA] + EXTS(SI)

union ast member (bit[5], bit[5], bit[16]) Addis

function clause decode (0b001111 :
(bit[5]) RT :
(bit[5]) RA :
(bit[16]) SI as instr) =
  Some(Addis(RT,RA,SI))

function clause execute (Addis (RT, RA, SI)) =
  if RA == 0
  then GPR[RT] := EXTS(SI : 0b0000000000000000)
  else GPR[RT] := GPR[RA] + EXTS(SI : 0b0000000000000000)

union ast member (bit[5], bit[5], bit[5], bit, bit) Add

function clause decode (0b011111 :
(bit[5]) RT :
(bit[5]) RA :
(bit[5]) RB :
[OE] :
0b100001010 :
[Rc] as instr) =
  Some(Add(RT,RA,RB,OE,Rc))

function clause execute (Add (RT, RA, RB, OE, Rc)) =
  let (temp, overflow, _) = (GPR[RA] +_s GPR[RB]) in
    {
      GPR[RT] := temp;
      if Rc
      then {
        (bit) xer_so := XER.SO;
        if OE & overflow then xer_so := overflow else ();
        set_overflow_cr0(temp,xer_so)
      }
      else ();
      if OE then set_SO_OV(overflow) else ()
    }

union ast member (bit[5], bit[5], bit[5], bit, bit) Subf

function clause decode (0b011111 :
(bit[5]) RT :
(bit[5]) RA :
(bit[5]) RB :
[OE] :
0b000101000 :
[Rc] as instr) =
  Some(Subf(RT,RA,RB,OE,Rc))

function clause execute (Subf (RT, RA, RB, OE, Rc)) =
  let (t1, o1, _) = (~(GPR[RA]) +_s GPR[RB]) in
    let (t2, o2, _) = (t1 +_s (bit) 1) in
      {
        (bit[64]) temp := t2;
        overflow := (o1 | o2);
        GPR[RT] := temp;
        if Rc
        then {
          (bit) xer_so := XER.SO;
          if OE & overflow then xer_so := overflow else ();
          set_overflow_cr0(temp,xer_so)
        }
        else ();
        if OE then set_SO_OV(overflow) else ()
      }

union ast member (bit[5], bit[5], bit[16]) Addic

function clause decode (0b001100 :
(bit[5]) RT :
(bit[5]) RA :
(bit[16]) SI as instr) =
  Some(Addic(RT,RA,SI))

function clause execute (Addic (RT, RA, SI)) =
  let (temp, _, carry) = (GPR[RA] +_s EXTS(SI)) in
    {
      GPR[RT] := temp;
      CA := carry
    }

union ast member (bit[5], bit[5], bit[16]) AddicDot

function clause decode (0b001101 :
(bit[5]) RT :
(bit[5]) RA :
(bit[16]) SI as instr) =
  Some(AddicDot(RT,RA,SI))

function clause execute (AddicDot (RT, RA, SI)) =
  let (temp, overflow, carry) = (GPR[RA] +_s EXTS(SI)) in
    {
      GPR[RT] := temp;
      CA := carry;
      set_overflow_cr0(temp,overflow | XER.SO)
    }

union ast member (bit[5], bit[5], bit[16]) Subfic

function clause decode (0b001000 :
(bit[5]) RT :
(bit[5]) RA :
(bit[16]) SI as instr) =
  Some(Subfic(RT,RA,SI))

function clause execute (Subfic (RT, RA, SI)) =
  let (t1, o1, c1) = (~(GPR[RA]) +_s EXTS(SI)) in
    let (t2, o2, c2) = (t1 +_s (bit) 1) in
      {
        (bit[64]) temp := t2;
        GPR[RT] := temp;
        CA := (c1 | c2)
      }

union ast member (bit[5], bit[5], bit[5], bit, bit) Addc

function clause decode (0b011111 :
(bit[5]) RT :
(bit[5]) RA :
(bit[5]) RB :
[OE] :
0b000001010 :
[Rc] as instr) =
  Some(Addc(RT,RA,RB,OE,Rc))

function clause execute (Addc (RT, RA, RB, OE, Rc)) =
  let (temp, overflow, carry) = (GPR[RA] +_s GPR[RB]) in
    {
      GPR[RT] := temp;
      if Rc
      then {
        (bit) xer_so := XER.SO;
        if OE & overflow then xer_so := overflow else ();
        set_overflow_cr0(temp,xer_so)
      }
      else ();
      CA := carry;
      if OE then set_SO_OV(overflow) else ()
    }

union ast member (bit[5], bit[5], bit[5], bit, bit) Subfc

function clause decode (0b011111 :
(bit[5]) RT :
(bit[5]) RA :
(bit[5]) RB :
[OE] :
0b000001000 :
[Rc] as instr) =
  Some(Subfc(RT,RA,RB,OE,Rc))

function clause execute (Subfc (RT, RA, RB, OE, Rc)) =
  let (t1, o1, c1) = (~(GPR[RA]) +_s GPR[RB]) in
    let (t2, o2, c2) = (t1 +_s (bit) 1) in
      {
        (bit[64]) temp := t2;
        overflow := (o1 | o2);
        carry := (c1 | c2);
        GPR[RT] := temp;
        if Rc
        then {
          (bit) xer_so := XER.SO;
          if OE & overflow then xer_so := overflow else ();
          set_overflow_cr0(temp,xer_so)
        }
        else ();
        CA := carry;
        if OE then set_SO_OV(overflow) else ()
      }

union ast member (bit[5], bit[5], bit[5], bit, bit) Adde

function clause decode (0b011111 :
(bit[5]) RT :
(bit[5]) RA :
(bit[5]) RB :
[OE] :
0b010001010 :
[Rc] as instr) =
  Some(Adde(RT,RA,RB,OE,Rc))

function clause execute (Adde (RT, RA, RB, OE, Rc)) =
  let (t1, o1, c1) = (GPR[RA] +_s GPR[RB]) in
    let (t2, o2, c2) = (t1 +_s (bit) CA) in
      {
        (bit[64]) temp := t2;
        overflow := (o1 | o2);
        carry := (c1 | c2);
        GPR[RT] := temp;
        if Rc
        then {
          (bit) xer_so := XER.SO;
          if OE & overflow then xer_so := overflow else ();
          set_overflow_cr0(temp,xer_so)
        }
        else ();
        CA := carry;
        if OE then set_SO_OV(overflow) else ()
      }

union ast member (bit[5], bit[5], bit[5], bit, bit) Subfe

function clause decode (0b011111 :
(bit[5]) RT :
(bit[5]) RA :
(bit[5]) RB :
[OE] :
0b010001000 :
[Rc] as instr) =
  Some(Subfe(RT,RA,RB,OE,Rc))

function clause execute (Subfe (RT, RA, RB, OE, Rc)) =
  let (t1, o1, c1) = (~(GPR[RA]) +_s GPR[RB]) in
    let (t2, o2, c2) = (t1 +_s (bit) CA) in
      {
        (bit[64]) temp := t2;
        overflow := (o1 | o2);
        carry := (c1 | c2);
        GPR[RT] := temp;
        if Rc
        then {
          (bit) xer_so := XER.SO;
          if OE & overflow then xer_so := overflow else ();
          set_overflow_cr0(temp,xer_so)
        }
        else ();
        CA := carry;
        if OE then set_SO_OV(overflow) else ()
      }

union ast member (bit[5], bit[5], bit, bit) Addme

function clause decode (0b011111 :
(bit[5]) RT :
(bit[5]) RA :
(bit[5]) _ :
[OE] :
0b011101010 :
[Rc] as instr) =
  Some(Addme(RT,RA,OE,Rc))

function clause execute (Addme (RT, RA, OE, Rc)) =
  let (t1, o1, c1) = (GPR[RA] +_s CA) in
    let (t2, o2, c2) = (t1 +_s 0b1111111111111111111111111111111111111111111111111111111111111111) in
      {
        (bit[64]) temp := t2;
        overflow := (o1 | o2);
        carry := (c1 | c2);
        GPR[RT] := temp;
        if Rc
        then {
          (bit) xer_so := XER.SO;
          if OE & overflow then xer_so := overflow else ();
          set_overflow_cr0(temp,xer_so)
        }
        else ();
        CA := carry;
        if OE then set_SO_OV(overflow) else ()
      }

union ast member (bit[5], bit[5], bit, bit) Subfme

function clause decode (0b011111 :
(bit[5]) RT :
(bit[5]) RA :
(bit[5]) _ :
[OE] :
0b011101000 :
[Rc] as instr) =
  Some(Subfme(RT,RA,OE,Rc))

function clause execute (Subfme (RT, RA, OE, Rc)) =
  let (t1, o1, c1) = (~(GPR[RA]) +_s CA) in
    let (t2, o2, c2) = (t1 +_s 0b1111111111111111111111111111111111111111111111111111111111111111) in
      {
        (bit[64]) temp := t2;
        overflow := (o1 | o2);
        carry := (c1 | c2);
        GPR[RT] := temp;
        if Rc
        then {
          (bit) xer_so := XER.SO;
          if OE & overflow then xer_so := overflow else ();
          set_overflow_cr0(temp,xer_so)
        }
        else ();
        CA := carry;
        if OE then set_SO_OV(overflow) else ()
      }

union ast member (bit[5], bit[5], bit, bit) Addze

function clause decode (0b011111 :
(bit[5]) RT :
(bit[5]) RA :
(bit[5]) _ :
[OE] :
0b011001010 :
[Rc] as instr) =
  Some(Addze(RT,RA,OE,Rc))

function clause execute (Addze (RT, RA, OE, Rc)) =
  let (temp, overflow, carry) = (GPR[RA] +_s CA) in
    {
      GPR[RT] := temp;
      if Rc
      then {
        (bit) xer_so := XER.SO;
        if OE & overflow then xer_so := overflow else ();
        set_overflow_cr0(temp,xer_so)
      }
      else ();
      CA := carry;
      if OE then set_SO_OV(overflow) else ()
    }

union ast member (bit[5], bit[5], bit, bit) Subfze

function clause decode (0b011111 :
(bit[5]) RT :
(bit[5]) RA :
(bit[5]) _ :
[OE] :
0b011001000 :
[Rc] as instr) =
  Some(Subfze(RT,RA,OE,Rc))

function clause execute (Subfze (RT, RA, OE, Rc)) =
  let (temp, overflow, carry) = (~(GPR[RA]) +_s CA) in
    {
      GPR[RT] := temp;
      if Rc
      then {
        (bit) xer_so := XER.SO;
        if OE & overflow then xer_so := overflow else ();
        set_overflow_cr0(temp,xer_so)
      }
      else ();
      CA := carry;
      if OE then set_SO_OV(overflow) else ()
    }

union ast member (bit[5], bit[5], bit, bit) Neg

function clause decode (0b011111 :
(bit[5]) RT :
(bit[5]) RA :
(bit[5]) _ :
[OE] :
0b001101000 :
[Rc] as instr) =
  Some(Neg(RT,RA,OE,Rc))

function clause execute (Neg (RT, RA, OE, Rc)) =
  let (temp, overflow, _) = (~(GPR[RA]) +_s (bit) 1) in
    {
      GPR[RT] := temp;
      if Rc then set_overflow_cr0(temp,XER.SO) else ();
      if OE then set_SO_OV(overflow) else ()
    }

union ast member (bit[5], bit[5], bit[16]) Mulli

function clause decode (0b000111 :
(bit[5]) RT :
(bit[5]) RA :
(bit[16]) SI as instr) =
  Some(Mulli(RT,RA,SI))

function clause execute (Mulli (RT, RA, SI)) =
  {
    (bit[128]) prod := GPR[RA] *_s EXTS(SI);
    GPR[RT] := prod[64 .. 127]
  }

union ast member (bit[5], bit[5], bit[5], bit, bit) Mullw

function clause decode (0b011111 :
(bit[5]) RT :
(bit[5]) RA :
(bit[5]) RB :
[OE] :
0b011101011 :
[Rc] as instr) =
  Some(Mullw(RT,RA,RB,OE,Rc))

function clause execute (Mullw (RT, RA, RB, OE, Rc)) =
  let (prod, overflow, _) = ((GPR[RA])[32 .. 63] *_s (GPR[RB])[32 .. 63]) in
    {
      GPR[RT] := prod;
      if Rc
      then {
        (bit) xer_so := XER.SO;
        if OE & overflow then xer_so := overflow else ();
        set_overflow_cr0(prod,xer_so)
      }
      else ();
      if OE then set_SO_OV(overflow) else ()
    }

union ast member (bit[5], bit[5], bit[5], bit) Mulhw

function clause decode (0b011111 :
(bit[5]) RT :
(bit[5]) RA :
(bit[5]) RB :
(bit[1]) _ :
0b001001011 :
[Rc] as instr) =
  Some(Mulhw(RT,RA,RB,Rc))

function clause execute (Mulhw (RT, RA, RB, Rc)) =
  {
    (bit[64]) prod := 0;
    (bit) overflow := 0;
    let (p, o, _) = ((GPR[RA])[32 .. 63] *_s (GPR[RB])[32 .. 63]) in
      {
        prod := p;
        overflow := o
      };
    (GPR[RT])[32..63] := prod[0 .. 31];
    (GPR[RT])[0..31] := undefined;
    if Rc
    then {
      (bit) xer_so := XER.SO;
      if mode64bit
      then CR.CR0 := [undefined,undefined,undefined,xer_so]
      else set_overflow_cr0(prod,xer_so)
    }
    else ()
  }

union ast member (bit[5], bit[5], bit[5], bit) Mulhwu

function clause decode (0b011111 :
(bit[5]) RT :
(bit[5]) RA :
(bit[5]) RB :
(bit[1]) _ :
0b000001011 :
[Rc] as instr) =
  Some(Mulhwu(RT,RA,RB,Rc))

function clause execute (Mulhwu (RT, RA, RB, Rc)) =
  {
    (bit[64]) prod := (GPR[RA])[32 .. 63] * (GPR[RB])[32 .. 63];
    (GPR[RT])[32..63] := prod[0 .. 31];
    (GPR[RT])[0..31] := undefined;
    if Rc
    then {
      (bit) xer_so := XER.SO;
      if mode64bit
      then CR.CR0 := [undefined,undefined,undefined,xer_so]
      else set_overflow_cr0(prod,xer_so)
    }
    else ()
  }

union ast member (bit[5], bit[5], bit[5], bit, bit) Divw

function clause decode (0b011111 :
(bit[5]) RT :
(bit[5]) RA :
(bit[5]) RB :
[OE] :
0b111101011 :
[Rc] as instr) =
  Some(Divw(RT,RA,RB,OE,Rc))

function clause execute (Divw (RT, RA, RB, OE, Rc)) =
  {
    (bit[32]) dividend := (GPR[RA])[32 .. 63];
    (bit[32]) divisor := (GPR[RB])[32 .. 63];
    (bit[64]) divided := 0b0000000000000000000000000000000000000000000000000000000000000000;
    (bit) overflow := 0;
    let (d, o, _) = (dividend quot_s divisor) in
      {
        divided[32..63] := d;
        overflow := o
      };
    (GPR[RT])[32..63] := divided[32 .. 63];
    (GPR[RT])[0..31] := undefined;
    if Rc
    then {
      (bit) xer_so := XER.SO;
      if OE & overflow then xer_so := overflow else ();
      if mode64bit | overflow
      then CR.CR0 := [undefined,undefined,undefined,xer_so]
      else set_overflow_cr0(divided,xer_so)
    }
    else ();
    if OE then set_SO_OV(overflow) else ()
  }

union ast member (bit[5], bit[5], bit[5], bit, bit) Divwu

function clause decode (0b011111 :
(bit[5]) RT :
(bit[5]) RA :
(bit[5]) RB :
[OE] :
0b111001011 :
[Rc] as instr) =
  Some(Divwu(RT,RA,RB,OE,Rc))

function clause execute (Divwu (RT, RA, RB, OE, Rc)) =
  {
    (bit[32]) dividend := (GPR[RA])[32 .. 63];
    (bit[32]) divisor := (GPR[RB])[32 .. 63];
    (bit[64]) divided := 0b0000000000000000000000000000000000000000000000000000000000000000;
    (bit) overflow := 0;
    let (d, o, _) = (dividend quot divisor) in
      {
        divided[32..63] := d;
        overflow := o
      };
    (GPR[RT])[32..63] := divided[32 .. 63];
    (GPR[RT])[0..31] := undefined;
    if Rc
    then {
      (bit) xer_so := XER.SO;
      if OE & overflow then xer_so := overflow else ();
      if mode64bit | overflow
      then CR.CR0 := [undefined,undefined,undefined,xer_so]
      else set_overflow_cr0(divided,xer_so)
    }
    else ();
    if OE then set_SO_OV(overflow) else ()
  }

union ast member (bit[5], bit[5], bit[5], bit, bit) Divwe

function clause decode (0b011111 :
(bit[5]) RT :
(bit[5]) RA :
(bit[5]) RB :
[OE] :
0b110101011 :
[Rc] as instr) =
  Some(Divwe(RT,RA,RB,OE,Rc))

function clause execute (Divwe (RT, RA, RB, OE, Rc)) =
  {
    (bit[64]) dividend := (GPR[RA])[32 .. 63] : 0b00000000000000000000000000000000;
    (bit[32]) divisor := (GPR[RB])[32 .. 63];
    (bit[64]) divided := 0b0000000000000000000000000000000000000000000000000000000000000000;
    (bit) overflow := 0;
    let (d, o, _) = (dividend quot_s divisor) in
      {
        divided[32..63] := d[32 .. 63];
        overflow := o
      };
    (GPR[RT])[32..63] := divided[32 .. 63];
    (GPR[RT])[0..31] := undefined;
    if Rc
    then {
      (bit) xer_so := XER.SO;
      if OE & overflow then xer_so := overflow else ();
      if mode64bit | overflow
      then CR.CR0 := [undefined,undefined,undefined,xer_so]
      else set_overflow_cr0(divided,xer_so)
    }
    else ();
    if OE then set_SO_OV(overflow) else ()
  }

union ast member (bit[5], bit[5], bit[5], bit, bit) Divweu

function clause decode (0b011111 :
(bit[5]) RT :
(bit[5]) RA :
(bit[5]) RB :
[OE] :
0b110001011 :
[Rc] as instr) =
  Some(Divweu(RT,RA,RB,OE,Rc))

function clause execute (Divweu (RT, RA, RB, OE, Rc)) =
  {
    (bit[64]) dividend := (GPR[RA])[32 .. 63] : 0b00000000000000000000000000000000;
    (bit[32]) divisor := (GPR[RB])[32 .. 63];
    (bit[64]) divided := 0b0000000000000000000000000000000000000000000000000000000000000000;
    (bit) overflow := 0;
    let (d, o, _) = (dividend quot divisor) in
      {
        divided[32..63] := d[32 .. 63];
        overflow := o
      };
    (GPR[RT])[32..63] := divided[32 .. 63];
    (GPR[RT])[0..31] := undefined;
    if Rc
    then {
      (bit) xer_so := XER.SO;
      if OE & overflow then xer_so := overflow else ();
      if mode64bit | overflow
      then CR.CR0 := [undefined,undefined,undefined,xer_so]
      else set_overflow_cr0(divided,xer_so)
    }
    else ();
    if OE then set_SO_OV(overflow) else ()
  }

union ast member (bit[5], bit[5], bit[5], bit, bit) Mulld

function clause decode (0b011111 :
(bit[5]) RT :
(bit[5]) RA :
(bit[5]) RB :
[OE] :
0b011101001 :
[Rc] as instr) =
  Some(Mulld(RT,RA,RB,OE,Rc))

function clause execute (Mulld (RT, RA, RB, OE, Rc)) =
  {
    (bit[128]) prod := 0;
    (bit) overflow := 0;
    let (p, o, _) = (GPR[RA] *_s GPR[RB]) in
      {
        prod := p;
        overflow := o
      };
    GPR[RT] := prod[64 .. 127];
    if Rc
    then {
      (bit) xer_so := XER.SO;
      if OE & overflow then xer_so := overflow else ();
      set_overflow_cr0(prod[64 .. 127],xer_so)
    }
    else ();
    if OE then set_SO_OV(overflow) else ()
  }

union ast member (bit[5], bit[5], bit[5], bit) Mulhd

function clause decode (0b011111 :
(bit[5]) RT :
(bit[5]) RA :
(bit[5]) RB :
(bit[1]) _ :
0b001001001 :
[Rc] as instr) =
  Some(Mulhd(RT,RA,RB,Rc))

function clause execute (Mulhd (RT, RA, RB, Rc)) =
  {
    (bit[128]) prod := GPR[RA] *_s GPR[RB];
    GPR[RT] := prod[0 .. 63];
    if Rc then set_overflow_cr0(prod[0 .. 63],XER.SO) else ()
  }

union ast member (bit[5], bit[5], bit[5], bit) Mulhdu

function clause decode (0b011111 :
(bit[5]) RT :
(bit[5]) RA :
(bit[5]) RB :
(bit[1]) _ :
0b000001001 :
[Rc] as instr) =
  Some(Mulhdu(RT,RA,RB,Rc))

function clause execute (Mulhdu (RT, RA, RB, Rc)) =
  {
    (bit[128]) prod := GPR[RA] * GPR[RB];
    GPR[RT] := prod[0 .. 63];
    if Rc then set_overflow_cr0(prod[0 .. 63],XER.SO) else ()
  }

union ast member (bit[5], bit[5], bit[5], bit, bit) Divd

function clause decode (0b011111 :
(bit[5]) RT :
(bit[5]) RA :
(bit[5]) RB :
[OE] :
0b111101001 :
[Rc] as instr) =
  Some(Divd(RT,RA,RB,OE,Rc))

function clause execute (Divd (RT, RA, RB, OE, Rc)) =
  {
    (bit[64]) dividend := GPR[RA];
    (bit[64]) divisor := GPR[RB];
    (bit[64]) divided := 0b0000000000000000000000000000000000000000000000000000000000000000;
    (bit) overflow := 0;
    let (d, o, _) = (dividend quot_s divisor) in
      {
        divided := d;
        overflow := o
      };
    GPR[RT] := divided;
    if OE then set_SO_OV(overflow) else ();
    if Rc then set_overflow_cr0(divided,overflow | XER.SO) else ()
  }

union ast member (bit[5], bit[5], bit[5], bit, bit) Divdu

function clause decode (0b011111 :
(bit[5]) RT :
(bit[5]) RA :
(bit[5]) RB :
[OE] :
0b111001001 :
[Rc] as instr) =
  Some(Divdu(RT,RA,RB,OE,Rc))

function clause execute (Divdu (RT, RA, RB, OE, Rc)) =
  {
    (bit[64]) dividend := GPR[RA];
    (bit[64]) divisor := GPR[RB];
    (bit[64]) divided := 0b0000000000000000000000000000000000000000000000000000000000000000;
    (bit) overflow := 0;
    let (d, o, _) = (dividend quot divisor) in
      {
        divided := d;
        overflow := o
      };
    GPR[RT] := divided;
    if OE then set_SO_OV(overflow) else ();
    if Rc then set_overflow_cr0(divided,overflow | XER.SO) else ()
  }

union ast member (bit[5], bit[5], bit[5], bit, bit) Divde

function clause decode (0b011111 :
(bit[5]) RT :
(bit[5]) RA :
(bit[5]) RB :
[OE] :
0b110101001 :
[Rc] as instr) =
  Some(Divde(RT,RA,RB,OE,Rc))

function clause execute (Divde (RT, RA, RB, OE, Rc)) =
  {
    (bit[128]) dividend :=
      GPR[RA] : 0b0000000000000000000000000000000000000000000000000000000000000000;
    (bit[64]) divisor := GPR[RB];
    (bit[128]) divided := 0;
    (bit) overflow := 0;
    let (d, o, _) = (dividend quot_s divisor) in
      {
        divided := d;
        overflow := o
      };
    GPR[RT] := divided[64 .. 127];
    if OE then set_SO_OV(overflow) else ();
    if Rc
    then {
      (bit) xer_so := XER.SO;
      if OE & overflow then xer_so := overflow else ();
      if overflow
      then CR.CR0 := [undefined,undefined,undefined,xer_so]
      else set_overflow_cr0(divided[64 .. 127],xer_so)
    }
    else ()
  }

union ast member (bit[5], bit[5], bit[5], bit, bit) Divdeu

function clause decode (0b011111 :
(bit[5]) RT :
(bit[5]) RA :
(bit[5]) RB :
[OE] :
0b110001001 :
[Rc] as instr) =
  Some(Divdeu(RT,RA,RB,OE,Rc))

function clause execute (Divdeu (RT, RA, RB, OE, Rc)) =
  {
    (bit[128]) dividend :=
      GPR[RA] : 0b0000000000000000000000000000000000000000000000000000000000000000;
    (bit[64]) divisor := GPR[RB];
    (bit[128]) divided := 0;
    (bit) overflow := 0;
    let (d, o, _) = (dividend quot divisor) in
      {
        divided := d;
        overflow := o
      };
    GPR[RT] := divided[64 .. 127];
    if OE then set_SO_OV(overflow) else ();
    if Rc
    then {
      (bit) xer_so := XER.SO;
      if OE & overflow then xer_so := overflow else ();
      if overflow
      then CR.CR0 := [undefined,undefined,undefined,xer_so]
      else set_overflow_cr0(divided[64 .. 127],xer_so)
    }
    else ()
  }

union ast member (bit[3], bit, bit[5], bit[16]) Cmpi

function clause decode (0b001011 :
(bit[3]) BF :
(bit[1]) _ :
[L] :
(bit[5]) RA :
(bit[16]) SI as instr) =
  Some(Cmpi(BF,L,RA,SI))

function clause execute (Cmpi (BF, L, RA, SI)) =
  {
    (bit[64]) a := 0;
    if L == 0 then a := EXTS((GPR[RA])[32 .. 63]) else a := GPR[RA];
    if a < EXTS(SI) then c := 0b100 else if a > EXTS(SI) then c := 0b010 else c := 0b001;
    CR[4 * BF + 32..4 * BF + 35] := c : [XER.SO]
  }

union ast member (bit[3], bit, bit[5], bit[5]) Cmp

function clause decode (0b011111 :
(bit[3]) BF :
(bit[1]) _ :
[L] :
(bit[5]) RA :
(bit[5]) RB :
0b0000000000 :
(bit[1]) _ as instr) =
  Some(Cmp(BF,L,RA,RB))

function clause execute (Cmp (BF, L, RA, RB)) =
  {
    (bit[64]) a := 0;
    (bit[64]) b := 0;
    if L == 0
    then {
      a := EXTS((GPR[RA])[32 .. 63]);
      b := EXTS((GPR[RB])[32 .. 63])
    }
    else {
      a := GPR[RA];
      b := GPR[RB]
    };
    if a < b then c := 0b100 else if a > b then c := 0b010 else c := 0b001;
    CR[4 * BF + 32..4 * BF + 35] := c : [XER.SO]
  }

union ast member (bit[3], bit, bit[5], bit[16]) Cmpli

function clause decode (0b001010 :
(bit[3]) BF :
(bit[1]) _ :
[L] :
(bit[5]) RA :
(bit[16]) UI as instr) =
  Some(Cmpli(BF,L,RA,UI))

function clause execute (Cmpli (BF, L, RA, UI)) =
  {
    (bit[64]) a := 0;
    (bit[3]) c := 0;
    if L == 0 then a := 0b00000000000000000000000000000000 : (GPR[RA])[32 .. 63] else a := GPR[RA];
    if a <_u 0b000000000000000000000000000000000000000000000000 : UI
    then c := 0b100
    else if a >_u 0b000000000000000000000000000000000000000000000000 : UI
    then c := 0b010
    else c := 0b001;
    CR[4 * BF + 32..4 * BF + 35] := c : [XER.SO]
  }

union ast member (bit[3], bit, bit[5], bit[5]) Cmpl

function clause decode (0b011111 :
(bit[3]) BF :
(bit[1]) _ :
[L] :
(bit[5]) RA :
(bit[5]) RB :
0b0000100000 :
(bit[1]) _ as instr) =
  Some(Cmpl(BF,L,RA,RB))

function clause execute (Cmpl (BF, L, RA, RB)) =
  {
    (bit[64]) a := 0;
    (bit[64]) b := 0;
    (bit[3]) c := 0;
    if L == 0
    then {
      a := 0b00000000000000000000000000000000 : (GPR[RA])[32 .. 63];
      b := 0b00000000000000000000000000000000 : (GPR[RB])[32 .. 63]
    }
    else {
      a := GPR[RA];
      b := GPR[RB]
    };
    if a <_u b then c := 0b100 else if a >_u b then c := 0b010 else c := 0b001;
    CR[4 * BF + 32..4 * BF + 35] := c : [XER.SO]
  }

union ast member (bit[5], bit[5], bit[5], bit[5]) Isel

function clause decode (0b011111 :
(bit[5]) RT :
(bit[5]) RA :
(bit[5]) RB :
(bit[5]) BC :
0b01111 :
(bit[1]) _ as instr) =
  Some(Isel(RT,RA,RB,BC))

function clause execute (Isel (RT, RA, RB, BC)) =
  {
    (bit[64]) a := 0;
    if RA == 0 then a := 0 else a := GPR[RA];
    if CR[BC + 32] == 1
    then {
      GPR[RT] := a;
      discard := GPR[RB]
    }
    else GPR[RT] := GPR[RB]
  }

union ast member (bit[5], bit[5], bit[16]) Andi

function clause decode (0b011100 :
(bit[5]) RS :
(bit[5]) RA :
(bit[16]) UI as instr) =
  Some(Andi(RS,RA,UI))

function clause execute (Andi (RS, RA, UI)) =
  {
    (bit[64]) temp := (GPR[RS] & 0b000000000000000000000000000000000000000000000000 : UI);
    GPR[RA] := temp;
    set_overflow_cr0(temp,XER.SO)
  }

union ast member (bit[5], bit[5], bit[16]) Andis

function clause decode (0b011101 :
(bit[5]) RS :
(bit[5]) RA :
(bit[16]) UI as instr) =
  Some(Andis(RS,RA,UI))

function clause execute (Andis (RS, RA, UI)) =
  {
    (bit[64]) temp := (GPR[RS] & 0b00000000000000000000000000000000 : UI : 0b0000000000000000);
    GPR[RA] := temp;
    set_overflow_cr0(temp,XER.SO)
  }

union ast member (bit[5], bit[5], bit[16]) Ori

function clause decode (0b011000 :
(bit[5]) RS :
(bit[5]) RA :
(bit[16]) UI as instr) =
  Some(Ori(RS,RA,UI))

function clause execute (Ori (RS, RA, UI)) =
  GPR[RA] := (GPR[RS] | 0b000000000000000000000000000000000000000000000000 : UI)

union ast member (bit[5], bit[5], bit[16]) Oris

function clause decode (0b011001 :
(bit[5]) RS :
(bit[5]) RA :
(bit[16]) UI as instr) =
  Some(Oris(RS,RA,UI))

function clause execute (Oris (RS, RA, UI)) =
  GPR[RA] := (GPR[RS] | 0b00000000000000000000000000000000 : UI : 0b0000000000000000)

union ast member (bit[5], bit[5], bit[16]) Xori

function clause decode (0b011010 :
(bit[5]) RS :
(bit[5]) RA :
(bit[16]) UI as instr) =
  Some(Xori(RS,RA,UI))

function clause execute (Xori (RS, RA, UI)) =
  GPR[RA] := GPR[RS] ^ 0b000000000000000000000000000000000000000000000000 : UI

union ast member (bit[5], bit[5], bit[16]) Xoris

function clause decode (0b011011 :
(bit[5]) RS :
(bit[5]) RA :
(bit[16]) UI as instr) =
  Some(Xoris(RS,RA,UI))

function clause execute (Xoris (RS, RA, UI)) =
  GPR[RA] := GPR[RS] ^ 0b00000000000000000000000000000000 : UI : 0b0000000000000000

union ast member (bit[5], bit[5], bit[5], bit) And

function clause decode (0b011111 :
(bit[5]) RS :
(bit[5]) RA :
(bit[5]) RB :
0b0000011100 :
[Rc] as instr) =
  Some(And(RS,RA,RB,Rc))

function clause execute (And (RS, RA, RB, Rc)) =
  {
    (bit[64]) temp := (GPR[RS] & GPR[RB]);
    GPR[RA] := temp;
    if Rc then set_overflow_cr0(temp,XER.SO) else ()
  }

union ast member (bit[5], bit[5], bit[5], bit) Xor

function clause decode (0b011111 :
(bit[5]) RS :
(bit[5]) RA :
(bit[5]) RB :
0b0100111100 :
[Rc] as instr) =
  Some(Xor(RS,RA,RB,Rc))

function clause execute (Xor (RS, RA, RB, Rc)) =
  {
    (bit[64]) temp := 0;
    if RS == RB
    then {
      temp := GPR[RS];
      temp := 0;
      GPR[RA] := 0
    }
    else {
      temp := GPR[RS] ^ GPR[RB];
      GPR[RA] := temp
    };
    if Rc then set_overflow_cr0(temp,XER.SO) else ()
  }

union ast member (bit[5], bit[5], bit[5], bit) Nand

function clause decode (0b011111 :
(bit[5]) RS :
(bit[5]) RA :
(bit[5]) RB :
0b0111011100 :
[Rc] as instr) =
  Some(Nand(RS,RA,RB,Rc))

function clause execute (Nand (RS, RA, RB, Rc)) =
  {
    (bit[64]) temp := ~(GPR[RS] & GPR[RB]);
    GPR[RA] := temp;
    if Rc then set_overflow_cr0(temp,XER.SO) else ()
  }

union ast member (bit[5], bit[5], bit[5], bit) Or

function clause decode (0b011111 :
(bit[5]) RS :
(bit[5]) RA :
(bit[5]) RB :
0b0110111100 :
[Rc] as instr) =
  Some(Or(RS,RA,RB,Rc))

function clause execute (Or (RS, RA, RB, Rc)) =
  {
    (bit[64]) temp := (GPR[RS] | GPR[RB]);
    GPR[RA] := temp;
    if Rc then set_overflow_cr0(temp,XER.SO) else ()
  }

union ast member (bit[5], bit[5], bit[5], bit) Nor

function clause decode (0b011111 :
(bit[5]) RS :
(bit[5]) RA :
(bit[5]) RB :
0b0001111100 :
[Rc] as instr) =
  Some(Nor(RS,RA,RB,Rc))

function clause execute (Nor (RS, RA, RB, Rc)) =
  {
    (bit[64]) temp := ~(GPR[RS] | GPR[RB]);
    GPR[RA] := temp;
    if Rc then set_overflow_cr0(temp,XER.SO) else ()
  }

union ast member (bit[5], bit[5], bit[5], bit) Eqv

function clause decode (0b011111 :
(bit[5]) RS :
(bit[5]) RA :
(bit[5]) RB :
0b0100011100 :
[Rc] as instr) =
  Some(Eqv(RS,RA,RB,Rc))

function clause execute (Eqv (RS, RA, RB, Rc)) =
  {
    (bit[64]) temp := GPR[RS] ^ ~(GPR[RB]);
    GPR[RA] := temp;
    if Rc then set_overflow_cr0(temp,XER.SO) else ()
  }

union ast member (bit[5], bit[5], bit[5], bit) Andc

function clause decode (0b011111 :
(bit[5]) RS :
(bit[5]) RA :
(bit[5]) RB :
0b0000111100 :
[Rc] as instr) =
  Some(Andc(RS,RA,RB,Rc))

function clause execute (Andc (RS, RA, RB, Rc)) =
  {
    (bit[64]) temp := (GPR[RS] & ~(GPR[RB]));
    GPR[RA] := temp;
    if Rc then set_overflow_cr0(temp,XER.SO) else ()
  }

union ast member (bit[5], bit[5], bit[5], bit) Orc

function clause decode (0b011111 :
(bit[5]) RS :
(bit[5]) RA :
(bit[5]) RB :
0b0110011100 :
[Rc] as instr) =
  Some(Orc(RS,RA,RB,Rc))

function clause execute (Orc (RS, RA, RB, Rc)) =
  {
    (bit[64]) temp := (GPR[RS] | ~(GPR[RB]));
    GPR[RA] := temp;
    if Rc then set_overflow_cr0(temp,XER.SO) else ()
  }

union ast member (bit[5], bit[5], bit) Extsb

function clause decode (0b011111 :
(bit[5]) RS :
(bit[5]) RA :
(bit[5]) _ :
0b1110111010 :
[Rc] as instr) =
  Some(Extsb(RS,RA,Rc))

function clause execute (Extsb (RS, RA, Rc)) =
  {
    (bit[64]) temp := 0;
    s := (GPR[RS])[56];
    temp[56..63] := (GPR[RS])[56 .. 63];
    (GPR[RA])[56..63] := temp[56 .. 63];
    temp[0..55] := s ^^ 56;
    (GPR[RA])[0..55] := temp[0 .. 55];
    if Rc then set_overflow_cr0(temp,XER.SO) else ()
  }

union ast member (bit[5], bit[5], bit) Extsh

function clause decode (0b011111 :
(bit[5]) RS :
(bit[5]) RA :
(bit[5]) _ :
0b1110011010 :
[Rc] as instr) =
  Some(Extsh(RS,RA,Rc))

function clause execute (Extsh (RS, RA, Rc)) =
  {
    (bit[64]) temp := 0;
    s := (GPR[RS])[48];
    temp[48..63] := (GPR[RS])[48 .. 63];
    (GPR[RA])[48..63] := temp[48 .. 63];
    temp[0..47] := s ^^ 48;
    (GPR[RA])[0..47] := temp[0 .. 47];
    if Rc then set_overflow_cr0(temp,XER.SO) else ()
  }

union ast member (bit[5], bit[5], bit) Cntlzw

function clause decode (0b011111 :
(bit[5]) RS :
(bit[5]) RA :
(bit[5]) _ :
0b0000011010 :
[Rc] as instr) =
  Some(Cntlzw(RS,RA,Rc))

function clause execute (Cntlzw (RS, RA, Rc)) =
  {
    temp := (bit[64]) (countLeadingZeroes(GPR[RS],32));
    GPR[RA] := temp;
    if Rc then set_overflow_cr0(temp,XER.SO) else ()
  }

union ast member (bit[5], bit[5], bit[5]) Cmpb

function clause decode (0b011111 :
(bit[5]) RS :
(bit[5]) RA :
(bit[5]) RB :
0b0111111100 :
(bit[1]) _ as instr) =
  Some(Cmpb(RS,RA,RB))

function clause execute (Cmpb (RS, RA, RB)) =
  foreach (n from 0 to 7 by 1 in inc)
  if (GPR[RS])[8 * n .. 8 * n + 7] == (GPR[RB])[8 * n .. 8 * n + 7]
  then (GPR[RA])[8 * n..8 * n + 7] := 0b11111111
  else (GPR[RA])[8 * n..8 * n + 7] := (bit[8]) 0

union ast member (bit[5], bit[5]) Popcntb

function clause decode (0b011111 :
(bit[5]) RS :
(bit[5]) RA :
(bit[5]) _ :
0b0001111010 :
(bit[1]) _ as instr) =
  Some(Popcntb(RS,RA))

function clause execute (Popcntb (RS, RA)) =
  foreach (i from 0 to 7 by 1 in inc)
  {
    ([|64|]) n := 0;
    foreach (j from 0 to 7 by 1 in inc) if (GPR[RS])[i * 8 + j] == 1 then n := n + 1 else ();
    (GPR[RA])[i * 8..i * 8 + 7] := (bit[8]) n
  }

union ast member (bit[5], bit[5]) Popcntw

function clause decode (0b011111 :
(bit[5]) RS :
(bit[5]) RA :
(bit[5]) _ :
0b0101111010 :
(bit[1]) _ as instr) =
  Some(Popcntw(RS,RA))

function clause execute (Popcntw (RS, RA)) =
  foreach (i from 0 to 1 by 1 in inc)
  {
    ([|64|]) n := 0;
    foreach (j from 0 to 31 by 1 in inc) if (GPR[RS])[i * 32 + j] == 1 then n := n + 1 else ();
    (GPR[RA])[i * 32..i * 32 + 31] := (bit[32]) n
  }

union ast member (bit[5], bit[5]) Prtyd

function clause decode (0b011111 :
(bit[5]) RS :
(bit[5]) RA :
(bit[5]) _ :
0b0010111010 :
(bit[1]) _ as instr) =
  Some(Prtyd(RS,RA))

function clause execute (Prtyd (RS, RA)) =
  {
    s := 0;
    foreach (i from 0 to 7 by 1 in inc) s := s ^ (GPR[RS])[i * 8 + 7];
    GPR[RA] := 0b000000000000000000000000000000000000000000000000000000000000000 : [s]
  }

union ast member (bit[5], bit[5]) Prtyw

function clause decode (0b011111 :
(bit[5]) RS :
(bit[5]) RA :
(bit[5]) _ :
0b0010011010 :
(bit[1]) _ as instr) =
  Some(Prtyw(RS,RA))

function clause execute (Prtyw (RS, RA)) =
  {
    s := 0;
    t := 0;
    foreach (i from 0 to 3 by 1 in inc) s := s ^ (GPR[RS])[i * 8 + 7];
    foreach (i from 4 to 7 by 1 in inc) t := t ^ (GPR[RS])[i * 8 + 7];
    (GPR[RA])[0..31] := 0b0000000000000000000000000000000 : [s];
    (GPR[RA])[32..63] := 0b0000000000000000000000000000000 : [t]
  }

union ast member (bit[5], bit[5], bit) Extsw

function clause decode (0b011111 :
(bit[5]) RS :
(bit[5]) RA :
(bit[5]) _ :
0b1111011010 :
[Rc] as instr) =
  Some(Extsw(RS,RA,Rc))

function clause execute (Extsw (RS, RA, Rc)) =
  {
    s := (GPR[RS])[32];
    (bit[64]) temp := 0;
    temp[32..63] := (GPR[RS])[32 .. 63];
    temp[0..31] := s ^^ 32;
    if Rc then set_overflow_cr0(temp,XER.SO) else ();
    GPR[RA] := temp
  }

union ast member (bit[5], bit[5], bit) Cntlzd

function clause decode (0b011111 :
(bit[5]) RS :
(bit[5]) RA :
(bit[5]) _ :
0b0000111010 :
[Rc] as instr) =
  Some(Cntlzd(RS,RA,Rc))

function clause execute (Cntlzd (RS, RA, Rc)) =
  {
    temp := (bit[64]) (countLeadingZeroes(GPR[RS],0));
    GPR[RA] := temp;
    if Rc then set_overflow_cr0(temp,XER.SO) else ()
  }

union ast member (bit[5], bit[5]) Popcntd

function clause decode (0b011111 :
(bit[5]) RS :
(bit[5]) RA :
(bit[5]) _ :
0b0111111010 :
(bit[1]) _ as instr) =
  Some(Popcntd(RS,RA))

function clause execute (Popcntd (RS, RA)) =
  {
    ([|64|]) n := 0;
    foreach (i from 0 to 63 by 1 in inc) if (GPR[RS])[i] == 1 then n := n + 1 else ();
    GPR[RA] := (bit[64]) n
  }

union ast member (bit[5], bit[5], bit[5]) Bpermd

function clause decode (0b011111 :
(bit[5]) RS :
(bit[5]) RA :
(bit[5]) RB :
0b0011111100 :
(bit[1]) _ as instr) =
  Some(Bpermd(RS,RA,RB))

function clause execute (Bpermd (RS, RA, RB)) =
  {
    (bit[8]) perm := 0;
    foreach (i from 0 to 7 by 1 in inc)
    {
      index := (GPR[RS])[8 * i .. 8 * i + 7];
      if index <_u (bit[8]) 64
      then perm[i] := (GPR[RB])[index]
      else {
        perm[i] := 0;
        discard := GPR[RB]
      }
    };
    GPR[RA] := 0b00000000000000000000000000000000000000000000000000000000 : perm[0 .. 7]
  }

union ast member (bit[5], bit[5], bit[5], bit[5], bit[5], bit) Rlwinm

function clause decode (0b010101 :
(bit[5]) RS :
(bit[5]) RA :
(bit[5]) SH :
(bit[5]) MB :
(bit[5]) ME :
[Rc] as instr) =
  Some(Rlwinm(RS,RA,SH,MB,ME,Rc))

function clause execute (Rlwinm (RS, RA, SH, MB, ME, Rc)) =
  {
    n := SH;
    r := ROTL((GPR[RS])[32 .. 63] : (GPR[RS])[32 .. 63],n);
    m := MASK(MB + 32,ME + 32);
    (bit[64]) temp := (r & m);
    GPR[RA] := temp;
    if Rc then set_overflow_cr0(temp,XER.SO) else ()
  }

union ast member (bit[5], bit[5], bit[5], bit[5], bit[5], bit) Rlwnm

function clause decode (0b010111 :
(bit[5]) RS :
(bit[5]) RA :
(bit[5]) RB :
(bit[5]) MB :
(bit[5]) ME :
[Rc] as instr) =
  Some(Rlwnm(RS,RA,RB,MB,ME,Rc))

function clause execute (Rlwnm (RS, RA, RB, MB, ME, Rc)) =
  {
    n := (GPR[RB])[59 .. 63];
    r := ROTL((GPR[RS])[32 .. 63] : (GPR[RS])[32 .. 63],n);
    m := MASK(MB + 32,ME + 32);
    (bit[64]) temp := (r & m);
    GPR[RA] := temp;
    if Rc then set_overflow_cr0(temp,XER.SO) else ()
  }

union ast member (bit[5], bit[5], bit[5], bit[5], bit[5], bit) Rlwimi

function clause decode (0b010100 :
(bit[5]) RS :
(bit[5]) RA :
(bit[5]) SH :
(bit[5]) MB :
(bit[5]) ME :
[Rc] as instr) =
  Some(Rlwimi(RS,RA,SH,MB,ME,Rc))

function clause execute (Rlwimi (RS, RA, SH, MB, ME, Rc)) =
  {
    n := SH;
    r := ROTL((GPR[RS])[32 .. 63] : (GPR[RS])[32 .. 63],n);
    m := MASK(MB + 32,ME + 32);
    (bit[64]) temp := (r & m | GPR[RA] & ~(m));
    GPR[RA] := temp;
    if Rc then set_overflow_cr0(temp,XER.SO) else ()
  }

union ast member (bit[5], bit[5], bit[6], bit[6], bit) Rldicl

function clause decode (0b011110 :
(bit[5]) RS :
(bit[5]) RA :
(bit[5]) _ :
(bit[6]) mb :
0b000 :
(bit[1]) _ :
[Rc] as instr) =
  Some(Rldicl(RS,RA,instr[16 .. 20] : instr[30 .. 30],mb,Rc))

function clause execute (Rldicl (RS, RA, sh, mb, Rc)) =
  {
    n := [sh[5]] : sh[0 .. 4];
    r := ROTL(GPR[RS],n);
    b := [mb[5]] : mb[0 .. 4];
    m := MASK(b,63);
    (bit[64]) temp := (r & m);
    GPR[RA] := temp;
    if Rc then set_overflow_cr0(temp,XER.SO) else ()
  }

union ast member (bit[5], bit[5], bit[6], bit[6], bit) Rldicr

function clause decode (0b011110 :
(bit[5]) RS :
(bit[5]) RA :
(bit[5]) _ :
(bit[6]) me :
0b001 :
(bit[1]) _ :
[Rc] as instr) =
  Some(Rldicr(RS,RA,instr[16 .. 20] : instr[30 .. 30],me,Rc))

function clause execute (Rldicr (RS, RA, sh, me, Rc)) =
  {
    n := [sh[5]] : sh[0 .. 4];
    r := ROTL(GPR[RS],n);
    e := [me[5]] : me[0 .. 4];
    m := MASK(0,e);
    (bit[64]) temp := (r & m);
    GPR[RA] := temp;
    if Rc then set_overflow_cr0(temp,XER.SO) else ()
  }

union ast member (bit[5], bit[5], bit[6], bit[6], bit) Rldic

function clause decode (0b011110 :
(bit[5]) RS :
(bit[5]) RA :
(bit[5]) _ :
(bit[6]) mb :
0b010 :
(bit[1]) _ :
[Rc] as instr) =
  Some(Rldic(RS,RA,instr[16 .. 20] : instr[30 .. 30],mb,Rc))

function clause execute (Rldic (RS, RA, sh, mb, Rc)) =
  {
    n := [sh[5]] : sh[0 .. 4];
    r := ROTL(GPR[RS],n);
    b := [mb[5]] : mb[0 .. 4];
    m := MASK(b,(bit[6]) (~(n)));
    (bit[64]) temp := (r & m);
    GPR[RA] := temp;
    if Rc then set_overflow_cr0(temp,XER.SO) else ()
  }

union ast member (bit[5], bit[5], bit[5], bit[6], bit) Rldcl

function clause decode (0b011110 :
(bit[5]) RS :
(bit[5]) RA :
(bit[5]) RB :
(bit[6]) mb :
0b1000 :
[Rc] as instr) =
  Some(Rldcl(RS,RA,RB,mb,Rc))

function clause execute (Rldcl (RS, RA, RB, mb, Rc)) =
  {
    n := (GPR[RB])[58 .. 63];
    r := ROTL(GPR[RS],n);
    b := [mb[5]] : mb[0 .. 4];
    m := MASK(b,63);
    (bit[64]) temp := (r & m);
    GPR[RA] := temp;
    if Rc then set_overflow_cr0(temp,XER.SO) else ()
  }

union ast member (bit[5], bit[5], bit[5], bit[6], bit) Rldcr

function clause decode (0b011110 :
(bit[5]) RS :
(bit[5]) RA :
(bit[5]) RB :
(bit[6]) me :
0b1001 :
[Rc] as instr) =
  Some(Rldcr(RS,RA,RB,me,Rc))

function clause execute (Rldcr (RS, RA, RB, me, Rc)) =
  {
    n := (GPR[RB])[58 .. 63];
    r := ROTL(GPR[RS],n);
    e := [me[5]] : me[0 .. 4];
    m := MASK(0,e);
    (bit[64]) temp := (r & m);
    GPR[RA] := temp;
    if Rc then set_overflow_cr0(temp,XER.SO) else ()
  }

union ast member (bit[5], bit[5], bit[6], bit[6], bit) Rldimi

function clause decode (0b011110 :
(bit[5]) RS :
(bit[5]) RA :
(bit[5]) _ :
(bit[6]) mb :
0b011 :
(bit[1]) _ :
[Rc] as instr) =
  Some(Rldimi(RS,RA,instr[16 .. 20] : instr[30 .. 30],mb,Rc))

function clause execute (Rldimi (RS, RA, sh, mb, Rc)) =
  {
    n := [sh[5]] : sh[0 .. 4];
    r := ROTL(GPR[RS],n);
    b := [mb[5]] : mb[0 .. 4];
    m := MASK(b,(bit[6]) (~(n)));
    (bit[64]) temp := (r & m | GPR[RA] & ~(m));
    GPR[RA] := temp;
    if Rc then set_overflow_cr0(temp,XER.SO) else ()
  }

union ast member (bit[5], bit[5], bit[5], bit) Slw

function clause decode (0b011111 :
(bit[5]) RS :
(bit[5]) RA :
(bit[5]) RB :
0b0000011000 :
[Rc] as instr) =
  Some(Slw(RS,RA,RB,Rc))

function clause execute (Slw (RS, RA, RB, Rc)) =
  {
    n := (GPR[RB])[59 .. 63];
    r := ROTL((GPR[RS])[32 .. 63] : (GPR[RS])[32 .. 63],n);
    if (GPR[RB])[58] == 0
    then m := MASK(32,63 - n)
    else m := 0b0000000000000000000000000000000000000000000000000000000000000000;
    (bit[64]) temp := (r & m);
    GPR[RA] := temp;
    if Rc then set_overflow_cr0(temp,XER.SO) else ()
  }

union ast member (bit[5], bit[5], bit[5], bit) Srw

function clause decode (0b011111 :
(bit[5]) RS :
(bit[5]) RA :
(bit[5]) RB :
0b1000011000 :
[Rc] as instr) =
  Some(Srw(RS,RA,RB,Rc))

function clause execute (Srw (RS, RA, RB, Rc)) =
  {
    n := (GPR[RB])[59 .. 63];
    r := ROTL((GPR[RS])[32 .. 63] : (GPR[RS])[32 .. 63],64 - n);
    if (GPR[RB])[58] == 0
    then m := MASK(n + 32,63)
    else m := 0b0000000000000000000000000000000000000000000000000000000000000000;
    (bit[64]) temp := (r & m);
    GPR[RA] := temp;
    if Rc then set_overflow_cr0(temp,XER.SO) else ()
  }

union ast member (bit[5], bit[5], bit[5], bit) Srawi

function clause decode (0b011111 :
(bit[5]) RS :
(bit[5]) RA :
(bit[5]) SH :
0b1100111000 :
[Rc] as instr) =
  Some(Srawi(RS,RA,SH,Rc))

function clause execute (Srawi (RS, RA, SH, Rc)) =
  {
    n := SH;
    r := ROTL((GPR[RS])[32 .. 63] : (GPR[RS])[32 .. 63],64 - n);
    m := MASK(n + 32,63);
    s := (GPR[RS])[32];
    (bit[64]) temp := (r & m | s ^^ 64 & ~(m));
    GPR[RA] := temp;
    if Rc then set_overflow_cr0(temp,XER.SO) else ();
    XER.CA := if n >_u (bit[5]) 0 then s & ~((r & ~(m)) == 0) else 0
  }

union ast member (bit[5], bit[5], bit[5], bit) Sraw

function clause decode (0b011111 :
(bit[5]) RS :
(bit[5]) RA :
(bit[5]) RB :
0b1100011000 :
[Rc] as instr) =
  Some(Sraw(RS,RA,RB,Rc))

function clause execute (Sraw (RS, RA, RB, Rc)) =
  {
    n := (GPR[RB])[59 .. 63];
    r := ROTL((GPR[RS])[32 .. 63] : (GPR[RS])[32 .. 63],64 - n);
    if (GPR[RB])[58] == 0
    then m := MASK(n + 32,63)
    else m := 0b0000000000000000000000000000000000000000000000000000000000000000;
    s := (GPR[RS])[32];
    (bit[64]) temp := (r & m | s ^^ 64 & ~(m));
    GPR[RA] := temp;
    if Rc then set_overflow_cr0(temp,XER.SO) else ();
    XER.CA := if n >_u (bit[5]) 0 then s & ~((r & ~(m)) == 0) else 0
  }

union ast member (bit[5], bit[5], bit[5], bit) Sld

function clause decode (0b011111 :
(bit[5]) RS :
(bit[5]) RA :
(bit[5]) RB :
0b0000011011 :
[Rc] as instr) =
  Some(Sld(RS,RA,RB,Rc))

function clause execute (Sld (RS, RA, RB, Rc)) =
  {
    n := (GPR[RB])[58 .. 63];
    r := ROTL(GPR[RS],n);
    if (GPR[RB])[57] == 0
    then m := MASK(0,63 - n)
    else m := 0b0000000000000000000000000000000000000000000000000000000000000000;
    (bit[64]) temp := (r & m);
    GPR[RA] := temp;
    if Rc then set_overflow_cr0(temp,XER.SO) else ()
  }

union ast member (bit[5], bit[5], bit[5], bit) Srd

function clause decode (0b011111 :
(bit[5]) RS :
(bit[5]) RA :
(bit[5]) RB :
0b1000011011 :
[Rc] as instr) =
  Some(Srd(RS,RA,RB,Rc))

function clause execute (Srd (RS, RA, RB, Rc)) =
  {
    n := (GPR[RB])[58 .. 63];
    r := ROTL(GPR[RS],64 - n);
    if (GPR[RB])[57] == 0
    then m := MASK(n,63)
    else m := 0b0000000000000000000000000000000000000000000000000000000000000000;
    (bit[64]) temp := (r & m);
    GPR[RA] := temp;
    if Rc then set_overflow_cr0(temp,XER.SO) else ()
  }

union ast member (bit[5], bit[5], bit[6], bit) Sradi

function clause decode (0b011111 :
(bit[5]) RS :
(bit[5]) RA :
(bit[5]) _ :
0b110011101 :
(bit[1]) _ :
[Rc] as instr) =
  Some(Sradi(RS,RA,instr[16 .. 20] : instr[30 .. 30],Rc))

function clause execute (Sradi (RS, RA, sh, Rc)) =
  {
    n := [sh[5]] : sh[0 .. 4];
    r := ROTL(GPR[RS],64 - n);
    m := MASK(n,63);
    s := (GPR[RS])[0];
    (bit[64]) temp := (r & m | s ^^ 64 & ~(m));
    GPR[RA] := temp;
    if Rc then set_overflow_cr0(temp,XER.SO) else ();
    XER.CA := if n >_u (bit[6]) 0 then s & ~((r & ~(m)) == 0) else 0
  }

union ast member (bit[5], bit[5], bit[5], bit) Srad

function clause decode (0b011111 :
(bit[5]) RS :
(bit[5]) RA :
(bit[5]) RB :
0b1100011010 :
[Rc] as instr) =
  Some(Srad(RS,RA,RB,Rc))

function clause execute (Srad (RS, RA, RB, Rc)) =
  {
    n := (GPR[RB])[58 .. 63];
    r := ROTL(GPR[RS],64 - n);
    if (GPR[RB])[57] == 0
    then m := MASK(n,63)
    else m := 0b0000000000000000000000000000000000000000000000000000000000000000;
    s := (GPR[RS])[0];
    (bit[64]) temp := (r & m | s ^^ 64 & ~(m));
    GPR[RA] := temp;
    if Rc then set_overflow_cr0(temp,XER.SO) else ();
    XER.CA := if n >_u (bit[6]) 0 then s & ~((r & ~(m)) == 0) else 0
  }

union ast member (bit[5], bit[5]) Cdtbcd

function clause decode (0b011111 :
(bit[5]) RS :
(bit[5]) RA :
(bit[5]) _ :
0b0100011010 :
(bit[1]) _ as instr) =
  Some(Cdtbcd(RS,RA))

function clause execute (Cdtbcd (RS, RA)) =
  foreach (i from 0 to 1 by 1 in inc)
  {
    n := i * 32;
    (GPR[RA])[n + 0..n + 7] := (bit[8]) 0;
    (GPR[RA])[n + 8..n + 19] := DEC_TO_BCD((GPR[RS])[n + 12 .. n + 21]);
    (GPR[RA])[n + 20..n + 31] := DEC_TO_BCD((GPR[RS])[n + 22 .. n + 31])
  }

union ast member (bit[5], bit[5]) Cbcdtd

function clause decode (0b011111 :
(bit[5]) RS :
(bit[5]) RA :
(bit[5]) _ :
0b0100111010 :
(bit[1]) _ as instr) =
  Some(Cbcdtd(RS,RA))

function clause execute (Cbcdtd (RS, RA)) =
  foreach (i from 0 to 1 by 1 in inc)
  {
    n := i * 32;
    (GPR[RA])[n + 0..n + 11] := (bit[12]) 0;
    (GPR[RA])[n + 12..n + 21] := BCD_TO_DEC((GPR[RS])[n + 8 .. n + 19]);
    (GPR[RA])[n + 22..n + 31] := BCD_TO_DEC((GPR[RS])[n + 20 .. n + 31])
  }

union ast member (bit[5], bit[5], bit[5]) Addg6s

function clause decode (0b011111 :
(bit[5]) RT :
(bit[5]) RA :
(bit[5]) RB :
(bit[1]) _ :
0b001001010 :
(bit[1]) _ as instr) =
  Some(Addg6s(RT,RA,RB))

function clause execute (Addg6s (RT, RA, RB)) =
  {
    (bit[16]) dc := 0;
    foreach (i from 0 to 15 by 1 in inc)
    let (v, _, co) = ((GPR[RA])[4 * i .. 63] + (GPR[RB])[4 * i .. 63]) in dc[i] := carry_out(v,co);
    c :=
      (dc[0] ^^ 4) :
        (dc[1] ^^ 4) :
          (dc[2] ^^ 4) :
            (dc[3] ^^ 4) :
              (dc[4] ^^ 4) :
                (dc[5] ^^ 4) :
                  (dc[6] ^^ 4) :
                    (dc[7] ^^ 4) :
                      (dc[8] ^^ 4) :
                        (dc[9] ^^ 4) :
                          (dc[10] ^^ 4) :
                            (dc[11] ^^ 4) :
                              (dc[12] ^^ 4) : (dc[13] ^^ 4) : (dc[14] ^^ 4) : (dc[15] ^^ 4);
    GPR[RT] := (~(c) & 0b0110011001100110011001100110011001100110011001100110011001100110)
  }

union ast member (bit[5], bit[10]) Mtspr

function clause decode (0b011111 :
(bit[5]) RS :
(bit[10]) spr :
0b0111010011 :
(bit[1]) _ as instr) =
  Some(Mtspr(RS,spr))

function clause execute (Mtspr (RS, spr)) =
  {
    n := spr[5 .. 9] : spr[0 .. 4];
    if n == 13
    then trap(())
    else if n == 1
    then {
      (bit[64]) reg := GPR[RS];
      (bit[32]) front := zero_or_undef(reg[0 .. 31]);
      (bit) xer_so := reg[32];
      (bit) xer_ov := reg[33];
      (bit) xer_ca := reg[34];
      (bit[22]) mid := zero_or_undef(reg[35 .. 56]);
      (bit[7]) bot := reg[57 .. 63];
      XER := front : [xer_so] : [xer_ov] : [xer_ca] : mid : bot
    }
    else if length(SPR[n]) == 64
    then SPR[n] := GPR[RS]
    else if n == 152 then CTRL := (GPR[RS])[32 .. 63] else ()
  }

union ast member (bit[5], bit[10]) Mfspr

function clause decode (0b011111 :
(bit[5]) RT :
(bit[10]) spr :
0b0101010011 :
(bit[1]) _ as instr) =
  Some(Mfspr(RT,spr))

function clause execute (Mfspr (RT, spr)) =
  {
    n := spr[5 .. 9] : spr[0 .. 4];
    if length(SPR[n]) == 64
    then GPR[RT] := SPR[n]
    else GPR[RT] := 0b00000000000000000000000000000000 : SPR[n]
  }

union ast member (bit[5], bit[8]) Mtcrf

function clause decode (0b011111 :
(bit[5]) RS :
0b0 :
(bit[8]) FXM :
(bit[1]) _ :
0b0010010000 :
(bit[1]) _ as instr) =
  Some(Mtcrf(RS,FXM))

function clause execute (Mtcrf (RS, FXM)) =
  {
    mask :=
      (FXM[0] ^^ 4) :
        (FXM[1] ^^ 4) :
          (FXM[2] ^^ 4) :
            (FXM[3] ^^ 4) : (FXM[4] ^^ 4) : (FXM[5] ^^ 4) : (FXM[6] ^^ 4) : (FXM[7] ^^ 4);
    CR := ((bit[32]) ((GPR[RS])[32 .. 63] & mask) | (bit[32]) (CR & ~((bit[32]) mask)))
  }

union ast member (bit[5]) Mfcr

function clause decode (0b011111 :
(bit[5]) RT :
0b0 :
(bit[9]) _ :
0b0000010011 :
(bit[1]) _ as instr) =
  Some(Mfcr(RT))

function clause execute (Mfcr (RT)) = GPR[RT] := 0b00000000000000000000000000000000 : CR

union ast member (bit[5], bit[8]) Mtocrf

function clause decode (0b011111 :
(bit[5]) RS :
0b1 :
(bit[8]) FXM :
(bit[1]) _ :
0b0010010000 :
(bit[1]) _ as instr) =
  Some(Mtocrf(RS,FXM))

function clause execute (Mtocrf (RS, FXM)) =
  {
    ([|7|]) n := 0;
    count := 0;
    foreach (i from 0 to 7 by 1 in inc)
    if FXM[i] == 1
    then {
      n := i;
      count := count + 1
    }
    else ();
    if count == 1
    then CR[4 * n + 32..4 * n + 35] := (GPR[RS])[4 * n + 32 .. 4 * n + 35]
    else CR := undefined
  }

union ast member (bit[5], bit[8]) Mfocrf

function clause decode (0b011111 :
(bit[5]) RT :
0b1 :
(bit[8]) FXM :
(bit[1]) _ :
0b0000010011 :
(bit[1]) _ as instr) =
  Some(Mfocrf(RT,FXM))

function clause execute (Mfocrf (RT, FXM)) =
  {
    ([|7|]) n := 0;
    count := 0;
    foreach (i from 0 to 7 by 1 in inc)
    if FXM[i] == 1
    then {
      n := i;
      count := count + 1
    }
    else ();
    if count == 1
    then {
      (bit[64]) temp := undefined;
      temp[4 * n + 32..4 * n + 35] := CR[4 * n + 32 .. 4 * n + 35];
      GPR[RT] := temp
    }
    else GPR[RT] := undefined
  }

union ast member (bit[3]) Mcrxr

function clause decode (0b011111 :
(bit[3]) BF :
(bit[2]) _ :
(bit[5]) _ :
(bit[5]) _ :
0b1000000000 :
(bit[1]) _ as instr) =
  Some(Mcrxr(BF))

function clause execute (Mcrxr (BF)) =
  {
    CR[4 * BF + 32..4 * BF + 35] := XER[32 .. 35];
    XER[32..35] := 0b0000
  }

union ast member (bit[5], bit[5], bit[5], bit) Dlmzb

function clause decode (0b011111 :
(bit[5]) RS :
(bit[5]) RA :
(bit[5]) RB :
0b0001001110 :
[Rc] as instr) =
  Some(Dlmzb(RS,RA,RB,Rc))

function clause execute (Dlmzb (RS, RA, RB, Rc)) = ()

union ast member (bit[5], bit[5], bit[5], bit, bit) Macchw

function clause decode (0b000100 :
(bit[5]) RT :
(bit[5]) RA :
(bit[5]) RB :
[OE] :
0b010101100 :
[Rc] as instr) =
  Some(Macchw(RT,RA,RB,OE,Rc))

function clause execute (Macchw (RT, RA, RB, OE, Rc)) = ()

union ast member (bit[5], bit[5], bit[5], bit, bit) Macchws

function clause decode (0b000100 :
(bit[5]) RT :
(bit[5]) RA :
(bit[5]) RB :
[OE] :
0b011101100 :
[Rc] as instr) =
  Some(Macchws(RT,RA,RB,OE,Rc))

function clause execute (Macchws (RT, RA, RB, OE, Rc)) = ()

union ast member (bit[5], bit[5], bit[5], bit, bit) Macchwu

function clause decode (0b000100 :
(bit[5]) RT :
(bit[5]) RA :
(bit[5]) RB :
[OE] :
0b010001100 :
[Rc] as instr) =
  Some(Macchwu(RT,RA,RB,OE,Rc))

function clause execute (Macchwu (RT, RA, RB, OE, Rc)) = ()

union ast member (bit[5], bit[5], bit[5], bit, bit) Macchwsu

function clause decode (0b000100 :
(bit[5]) RT :
(bit[5]) RA :
(bit[5]) RB :
[OE] :
0b011001100 :
[Rc] as instr) =
  Some(Macchwsu(RT,RA,RB,OE,Rc))

function clause execute (Macchwsu (RT, RA, RB, OE, Rc)) = ()

union ast member (bit[5], bit[5], bit[5], bit, bit) Machhw

function clause decode (0b000100 :
(bit[5]) RT :
(bit[5]) RA :
(bit[5]) RB :
[OE] :
0b000101100 :
[Rc] as instr) =
  Some(Machhw(RT,RA,RB,OE,Rc))

function clause execute (Machhw (RT, RA, RB, OE, Rc)) = ()

union ast member (bit[5], bit[5], bit[5], bit, bit) Machhws

function clause decode (0b000100 :
(bit[5]) RT :
(bit[5]) RA :
(bit[5]) RB :
[OE] :
0b001101100 :
[Rc] as instr) =
  Some(Machhws(RT,RA,RB,OE,Rc))

function clause execute (Machhws (RT, RA, RB, OE, Rc)) = ()

union ast member (bit[5], bit[5], bit[5], bit, bit) Machhwu

function clause decode (0b000100 :
(bit[5]) RT :
(bit[5]) RA :
(bit[5]) RB :
[OE] :
0b000001100 :
[Rc] as instr) =
  Some(Machhwu(RT,RA,RB,OE,Rc))

function clause execute (Machhwu (RT, RA, RB, OE, Rc)) = ()

union ast member (bit[5], bit[5], bit[5], bit, bit) Machhwsu

function clause decode (0b000100 :
(bit[5]) RT :
(bit[5]) RA :
(bit[5]) RB :
[OE] :
0b001001100 :
[Rc] as instr) =
  Some(Machhwsu(RT,RA,RB,OE,Rc))

function clause execute (Machhwsu (RT, RA, RB, OE, Rc)) = ()

union ast member (bit[5], bit[5], bit[5], bit, bit) Maclhw

function clause decode (0b000100 :
(bit[5]) RT :
(bit[5]) RA :
(bit[5]) RB :
[OE] :
0b110101100 :
[Rc] as instr) =
  Some(Maclhw(RT,RA,RB,OE,Rc))

function clause execute (Maclhw (RT, RA, RB, OE, Rc)) = ()

union ast member (bit[5], bit[5], bit[5], bit, bit) Maclhws

function clause decode (0b000100 :
(bit[5]) RT :
(bit[5]) RA :
(bit[5]) RB :
[OE] :
0b111101100 :
[Rc] as instr) =
  Some(Maclhws(RT,RA,RB,OE,Rc))

function clause execute (Maclhws (RT, RA, RB, OE, Rc)) = ()

union ast member (bit[5], bit[5], bit[5], bit, bit) Maclhwu

function clause decode (0b000100 :
(bit[5]) RT :
(bit[5]) RA :
(bit[5]) RB :
[OE] :
0b110001100 :
[Rc] as instr) =
  Some(Maclhwu(RT,RA,RB,OE,Rc))

function clause execute (Maclhwu (RT, RA, RB, OE, Rc)) = ()

union ast member (bit[5], bit[5], bit[5], bit, bit) Maclhwsu

function clause decode (0b000100 :
(bit[5]) RT :
(bit[5]) RA :
(bit[5]) RB :
[OE] :
0b111001100 :
[Rc] as instr) =
  Some(Maclhwsu(RT,RA,RB,OE,Rc))

function clause execute (Maclhwsu (RT, RA, RB, OE, Rc)) = ()

union ast member (bit[5], bit[5], bit[5], bit) Mulchw

function clause decode (0b000100 :
(bit[5]) RT :
(bit[5]) RA :
(bit[5]) RB :
0b0010101000 :
[Rc] as instr) =
  Some(Mulchw(RT,RA,RB,Rc))

function clause execute (Mulchw (RT, RA, RB, Rc)) = ()

union ast member (bit[5], bit[5], bit[5], bit) Mulchwu

function clause decode (0b000100 :
(bit[5]) RT :
(bit[5]) RA :
(bit[5]) RB :
0b0010001000 :
[Rc] as instr) =
  Some(Mulchwu(RT,RA,RB,Rc))

function clause execute (Mulchwu (RT, RA, RB, Rc)) = ()

union ast member (bit[5], bit[5], bit[5], bit) Mulhhw

function clause decode (0b000100 :
(bit[5]) RT :
(bit[5]) RA :
(bit[5]) RB :
0b0000101000 :
[Rc] as instr) =
  Some(Mulhhw(RT,RA,RB,Rc))

function clause execute (Mulhhw (RT, RA, RB, Rc)) = ()

union ast member (bit[5], bit[5], bit[5], bit) Mulhhwu

function clause decode (0b000100 :
(bit[5]) RT :
(bit[5]) RA :
(bit[5]) RB :
0b0000001000 :
[Rc] as instr) =
  Some(Mulhhwu(RT,RA,RB,Rc))

function clause execute (Mulhhwu (RT, RA, RB, Rc)) = ()

union ast member (bit[5], bit[5], bit[5], bit) Mullhw

function clause decode (0b000100 :
(bit[5]) RT :
(bit[5]) RA :
(bit[5]) RB :
0b0110101000 :
[Rc] as instr) =
  Some(Mullhw(RT,RA,RB,Rc))

function clause execute (Mullhw (RT, RA, RB, Rc)) = ()

union ast member (bit[5], bit[5], bit[5], bit) Mullhwu

function clause decode (0b000100 :
(bit[5]) RT :
(bit[5]) RA :
(bit[5]) RB :
0b0110001000 :
[Rc] as instr) =
  Some(Mullhwu(RT,RA,RB,Rc))

function clause execute (Mullhwu (RT, RA, RB, Rc)) = ()

union ast member (bit[5], bit[5], bit[5], bit, bit) Nmacchw

function clause decode (0b000100 :
(bit[5]) RT :
(bit[5]) RA :
(bit[5]) RB :
[OE] :
0b010101110 :
[Rc] as instr) =
  Some(Nmacchw(RT,RA,RB,OE,Rc))

function clause execute (Nmacchw (RT, RA, RB, OE, Rc)) = ()

union ast member (bit[5], bit[5], bit[5], bit, bit) Nmacchws

function clause decode (0b000100 :
(bit[5]) RT :
(bit[5]) RA :
(bit[5]) RB :
[OE] :
0b011101110 :
[Rc] as instr) =
  Some(Nmacchws(RT,RA,RB,OE,Rc))

function clause execute (Nmacchws (RT, RA, RB, OE, Rc)) = ()

union ast member (bit[5], bit[5], bit[5], bit, bit) Nmachhw

function clause decode (0b000100 :
(bit[5]) RT :
(bit[5]) RA :
(bit[5]) RB :
[OE] :
0b000101110 :
[Rc] as instr) =
  Some(Nmachhw(RT,RA,RB,OE,Rc))

function clause execute (Nmachhw (RT, RA, RB, OE, Rc)) = ()

union ast member (bit[5], bit[5], bit[5], bit, bit) Nmachhws

function clause decode (0b000100 :
(bit[5]) RT :
(bit[5]) RA :
(bit[5]) RB :
[OE] :
0b001101110 :
[Rc] as instr) =
  Some(Nmachhws(RT,RA,RB,OE,Rc))

function clause execute (Nmachhws (RT, RA, RB, OE, Rc)) = ()

union ast member (bit[5], bit[5], bit[5], bit, bit) Nmaclhw

function clause decode (0b000100 :
(bit[5]) RT :
(bit[5]) RA :
(bit[5]) RB :
[OE] :
0b110101110 :
[Rc] as instr) =
  Some(Nmaclhw(RT,RA,RB,OE,Rc))

function clause execute (Nmaclhw (RT, RA, RB, OE, Rc)) = ()

union ast member (bit[5], bit[5], bit[5], bit, bit) Nmaclhws

function clause decode (0b000100 :
(bit[5]) RT :
(bit[5]) RA :
(bit[5]) RB :
[OE] :
0b111101110 :
[Rc] as instr) =
  Some(Nmaclhws(RT,RA,RB,OE,Rc))

function clause execute (Nmaclhws (RT, RA, RB, OE, Rc)) = ()

union ast member (bit[5], bit[5]) Icbi

function clause decode (0b011111 :
(bit[5]) _ :
(bit[5]) RA :
(bit[5]) RB :
0b1111010110 :
(bit[1]) _ as instr) =
  Some(Icbi(RA,RB))

function clause execute (Icbi (RA, RB)) = ()

union ast member (bit[4], bit[5], bit[5]) Icbt

function clause decode (0b011111 :
(bit[1]) _ :
(bit[4]) CT :
(bit[5]) RA :
(bit[5]) RB :
0b0000010110 :
(bit[1]) _ as instr) =
  Some(Icbt(CT,RA,RB))

function clause execute (Icbt (CT, RA, RB)) = ()

union ast member (bit[5], bit[5]) Dcba

function clause decode (0b011111 :
(bit[5]) _ :
(bit[5]) RA :
(bit[5]) RB :
0b1011110110 :
(bit[1]) _ as instr) =
  Some(Dcba(RA,RB))

function clause execute (Dcba (RA, RB)) = ()

union ast member (bit[5], bit[5], bit[5]) Dcbt

function clause decode (0b011111 :
(bit[5]) TH :
(bit[5]) RA :
(bit[5]) RB :
0b0100010110 :
(bit[1]) _ as instr) =
  Some(Dcbt(TH,RA,RB))

function clause execute (Dcbt (TH, RA, RB)) = ()

union ast member (bit[5], bit[5], bit[5]) Dcbtst

function clause decode (0b011111 :
(bit[5]) TH :
(bit[5]) RA :
(bit[5]) RB :
0b0011110110 :
(bit[1]) _ as instr) =
  Some(Dcbtst(TH,RA,RB))

function clause execute (Dcbtst (TH, RA, RB)) = ()

union ast member (bit[5], bit[5]) Dcbz

function clause decode (0b011111 :
(bit[5]) _ :
(bit[5]) RA :
(bit[5]) RB :
0b1111110110 :
(bit[1]) _ as instr) =
  Some(Dcbz(RA,RB))

function clause execute (Dcbz (RA, RB)) = ()

union ast member (bit[5], bit[5]) Dcbst

function clause decode (0b011111 :
(bit[5]) _ :
(bit[5]) RA :
(bit[5]) RB :
0b0000110110 :
(bit[1]) _ as instr) =
  Some(Dcbst(RA,RB))

function clause execute (Dcbst (RA, RB)) = ()

union ast member (bit[2], bit[5], bit[5]) Dcbf

function clause decode (0b011111 :
(bit[3]) _ :
(bit[2]) L :
(bit[5]) RA :
(bit[5]) RB :
0b0001010110 :
(bit[1]) _ as instr) =
  Some(Dcbf(L,RA,RB))

function clause execute (Dcbf (L, RA, RB)) = ()

union ast member Isync

function clause decode (0b010011 :
(bit[5]) _ :
(bit[5]) _ :
(bit[5]) _ :
0b0010010110 :
(bit[1]) _ as instr) =
  Some(Isync())

function clause execute Isync = I_Sync(())

union ast member (bit[5], bit[5], bit[5], bit) Lbarx

function clause decode (0b011111 :
(bit[5]) RT :
(bit[5]) RA :
(bit[5]) RB :
0b0000110100 :
[EH] as instr) =
  Some(Lbarx(RT,RA,RB,EH))

function clause execute (Lbarx (RT, RA, RB, EH)) =
  {
    (bit[64]) b := 0;
    (bit[64]) EA := 0;
    if RA == 0 then b := 0 else b := GPR[RA];
    EA := b + GPR[RB];
    GPR[RT] := 0b00000000000000000000000000000000000000000000000000000000 : MEMr_reserve(EA,1)
  }

union ast member (bit[5], bit[5], bit[5], bit) Lharx

function clause decode (0b011111 :
(bit[5]) RT :
(bit[5]) RA :
(bit[5]) RB :
0b0001110100 :
[EH] as instr) =
  Some(Lharx(RT,RA,RB,EH))

function clause execute (Lharx (RT, RA, RB, EH)) =
  {
    (bit[64]) b := 0;
    (bit[64]) EA := 0;
    if RA == 0 then b := 0 else b := GPR[RA];
    EA := b + GPR[RB];
    GPR[RT] := 0b000000000000000000000000000000000000000000000000 : MEMr_reserve(EA,2)
  }

union ast member (bit[5], bit[5], bit[5], bit) Lwarx

function clause decode (0b011111 :
(bit[5]) RT :
(bit[5]) RA :
(bit[5]) RB :
0b0000010100 :
[EH] as instr) =
  Some(Lwarx(RT,RA,RB,EH))

function clause execute (Lwarx (RT, RA, RB, EH)) =
  {
    (bit[64]) b := 0;
    (bit[64]) EA := 0;
    if RA == 0 then b := 0 else b := GPR[RA];
    EA := b + GPR[RB];
    GPR[RT] := 0b00000000000000000000000000000000 : MEMr_reserve(EA,4)
  }

union ast member (bit[5], bit[5], bit[5]) Stbcx

function clause decode (0b011111 :
(bit[5]) RS :
(bit[5]) RA :
(bit[5]) RB :
0b1010110110 :
0b1 as instr) =
  Some(Stbcx(RS,RA,RB))

function clause execute (Stbcx (RS, RA, RB)) =
  {
    (bit[64]) b := 0;
    (bit[64]) EA := 0;
    if RA == 0 then b := 0 else b := GPR[RA];
    EA := b + GPR[RB];
    MEMw_EA_cond(EA,1);
    status := MEMw_conditional(EA,1,(GPR[RS])[56 .. 63]);
    CR0 := 0b00 : [status] : [XER.SO]
  }

union ast member (bit[5], bit[5], bit[5]) Sthcx

function clause decode (0b011111 :
(bit[5]) RS :
(bit[5]) RA :
(bit[5]) RB :
0b1011010110 :
0b1 as instr) =
  Some(Sthcx(RS,RA,RB))

function clause execute (Sthcx (RS, RA, RB)) =
  {
    (bit[64]) b := 0;
    (bit[64]) EA := 0;
    if RA == 0 then b := 0 else b := GPR[RA];
    EA := b + GPR[RB];
    MEMw_EA_cond(EA,2);
    status := MEMw_conditional(EA,2,(GPR[RS])[48 .. 63]);
    CR0 := 0b00 : [status] : [XER.SO]
  }

union ast member (bit[5], bit[5], bit[5]) Stwcx

function clause decode (0b011111 :
(bit[5]) RS :
(bit[5]) RA :
(bit[5]) RB :
0b0010010110 :
0b1 as instr) =
  Some(Stwcx(RS,RA,RB))

function clause execute (Stwcx (RS, RA, RB)) =
  {
    (bit[64]) b := 0;
    (bit[64]) EA := 0;
    if RA == 0 then b := 0 else b := GPR[RA];
    EA := b + GPR[RB];
    MEMw_EA_cond(EA,4);
    status := MEMw_conditional(EA,4,(GPR[RS])[32 .. 63]);
    CR0 := 0b00 : [status] : [XER.SO]
  }

union ast member (bit[5], bit[5], bit[5], bit) Ldarx

function clause decode (0b011111 :
(bit[5]) RT :
(bit[5]) RA :
(bit[5]) RB :
0b0001010100 :
[EH] as instr) =
  Some(Ldarx(RT,RA,RB,EH))

function clause execute (Ldarx (RT, RA, RB, EH)) =
  {
    (bit[64]) b := 0;
    (bit[64]) EA := 0;
    if RA == 0 then b := 0 else b := GPR[RA];
    EA := b + GPR[RB];
    GPR[RT] := MEMr_reserve(EA,8)
  }

union ast member (bit[5], bit[5], bit[5]) Stdcx

function clause decode (0b011111 :
(bit[5]) RS :
(bit[5]) RA :
(bit[5]) RB :
0b0011010110 :
0b1 as instr) =
  Some(Stdcx(RS,RA,RB))

function clause execute (Stdcx (RS, RA, RB)) =
  {
    (bit[64]) b := 0;
    (bit[64]) EA := 0;
    if RA == 0 then b := 0 else b := GPR[RA];
    EA := b + GPR[RB];
    MEMw_EA_cond(EA,8);
    status := MEMw_conditional(EA,8,GPR[RS]);
    CR0 := 0b00 : [status] : [XER.SO]
  }

union ast member (bit[2]) Sync

function clause decode (0b011111 :
(bit[3]) _ :
(bit[2]) L :
(bit[5]) _ :
(bit[5]) _ :
0b1001010110 :
(bit[1]) _ as instr) =
  Some(Sync(L))

function clause execute (Sync (L)) =
  switch L { case 0b00 -> { H_Sync(()) } case 0b01 -> { LW_Sync(()) } }

union ast member Eieio

function clause decode (0b011111 :
(bit[5]) _ :
(bit[5]) _ :
(bit[5]) _ :
0b1101010110 :
(bit[1]) _ as instr) =
  Some(Eieio())

function clause execute Eieio = EIEIO_Sync(())

union ast member (bit[2]) Wait

function clause decode (0b011111 :
(bit[3]) _ :
(bit[2]) WC :
(bit[5]) _ :
(bit[5]) _ :
0b0000111110 :
(bit[1]) _ as instr) =
  Some(Wait(WC))

function clause execute (Wait (WC)) = ()


typedef decode_failure = enumerate { no_matching_pattern; unsupported_instruction; illegal_instruction } 

function clause decode _ = None

end decode
end execute
end ast

val ast -> option<ast> effect pure supported_instructions
function option<ast> supported_instructions ((ast) instr) = {
  switch instr {
    (* case (Mbar(_)) -> None *)
    case (Sync(0b10)) -> None
    case (Sync(0b11)) -> None
    case _ -> Some(instr)
   }
}

val ast -> bit effect pure illegal_instructions_pred
function bit illegal_instructions_pred ((ast) instr) = {
     switch instr {
        case (Bcctr(BO,BI,BH,LK)) -> ~(BO[2])
        case (Lbzu(RT,RA,D)) -> (RA == 0) | (RA == RT) 
        case (Lbzux(RT,RA,_)) ->(RA == 0) | (RA == RT) 
        case (Lhzu(RT,RA,D)) -> (RA == 0) | (RA == RT)
        case (Lhzux(RT,RA,RB)) -> (RA == 0) | (RA == RT)
        case (Lhau(RT,RA,D)) -> (RA == 0) | (RA == RT)
        case (Lhaux(RT,RA,RB)) -> (RA == 0) | (RA == RT)
        case (Lwzu(RA,RT,D)) -> (RA == 0) | (RA == RT)
        case (Lwzux(RT,RA,RB)) -> (RA == 0) | (RA == RT)
        case (Lwaux(RA,RT,RB)) -> (RA == 0) | (RA == RT)
        case (Ldu(RT,RA,DS)) -> (RA == 0) | (RA == RT)
        case (Ldux(RT,RA,RB)) -> (RA == 0) | (RA == RT)
        case (Stbu(RS,RA,D)) -> (RA == 0)
        case (Stbux(RS,RA,RB)) -> (RA == 0)
        case (Sthu(RS,RA,RB)) -> (RA == 0)
        case (Sthux(RS,RA,RB)) -> (RA == 0)
        case (Stwu(RS,RA,D)) -> (RA == 0)
        case (Stwux(RS,RA,RB)) -> (RA == 0)
        case (Stdu(RS,RA,DS)) -> (RA == 0)
        case (Stdux(RS,RA,RB)) -> (RA == 0)
        case (Lmw(RT,RA,D)) -> (RA == 0) | ((RT <= RA) & (RA <= 31))
        case (Lswi(RT,RA,NB)) ->
           let (([|32|]) n) = (if ~(NB == 0) then NB else 32) in
           let ceil =
             (if (n mod 4) == 0
             then n quot 4 else (n quot 4) + 1) in
           (RT <= RA) & (RA <= ((bit[5]) (((bit[5]) (RT + ceil)) - 1)))
        (* Can't read XER at the time meant, so will need to rethink *)
       (* case (Lswx(RT,RA,RB)) ->
           let (([|32|]) n) = (XER[57..63]) in
           let ceil =
             (if (n mod 4 == 0)
             then n quot 4 else (n quot 4) + 1) in
           let ((bit[5]) upper_bound) = (RT + ceil) in
           (RT <= RA & RA <= upper_bound) |
           (RT <= RB & RB <= upper_bound) |
          (RT == RA) | (RT == RB)*)
(*Floating point instructions*)
(*        case (Lfsu(FRT,RA,D)) -> (RA == 0)
        case (Lfsux(FRT,RA,RB)) -> (RA == 0)
        case (Lfdu(FRT,RA,D)) -> (RA == 0)
        case (Lfdux(FRT,RA,RB)) -> (RA == 0)
        case (Stfsu(FRS,RA,D)) -> (RA == 0)
        case (Stfsux(FRS,RA,RB)) -> (RA == 0)
        case (Stfdu(FRS,D,RA)) -> (RA == 0)
        case (Stfdux(FRS,RA,RB)) -> (RA == 0)
        case (Lfdp(FRTp,RA,DS)) -> (FRTp mod 2 == 1)
        case (Stfdp(FRSp,RA,DS)) -> (FRSp mod 2 == 1)
        case (Lfdpx(FRTp,RA,RB)) -> (FRTp mod 2 == 1)
        case (Stfdpx(FRSp,RA,RB)) -> (FRSp mod 2 == 1)*)
        case (Lq(RTp,RA,DQ,Pt)) -> ((RTp mod 2 ==1) | RTp == RA)
        case (Stq(RSp,RA,RS)) -> (RSp mod 2 == 1)
        case (Mtspr(RS, spr)) ->
          ~ ((spr == 1) | (spr == 8) | (spr == 9) | (spr == 256) |
            (spr == 512) | (spr == 896) | (spr == 898))
(*One of these causes a stack overflow error, don't want to debug why now*)
        (*case (Mfspr(RT, spr)) ->
           ~ ((spr == 1) | (spr == 8) | (spr == 9) | (spr == 136) |
           (spr == 256) | (spr == 259) | (spr == 260) | (spr == 261) |
           (spr == 262) | (spr == 263) | (spr == 268) | (spr == 268) |
           (spr == 269) | (spr == 512) | (spr == 526) | (spr == 526) |
           (spr == 527) | (spr == 896) | (spr == 898))
        case (Se_illegal) -> true
        case (E_lhau(RT,RA,D8)) -> (RA == 0 | RA == RT)
        case (E_Lhzu(RT,RA,D8)) -> (RA == 0 | RA == RT)
        case (E_lwzu(RT,RA,D8)) -> (RA == 0 | RA == RT)
        case (E_stbu(RS,RA,D8)) -> (RA == 0)
        case (E_sthu(RS,RA,D8)) -> (RA == 0)
        case (E_stwu(RS,RA,D8)) -> (RA == 0)
        case (E_lmw(RT,RA,D8)) -> (RT <= RA & RA <= 31)*)
        case _ -> false
     }
}

val ast -> option<ast> effect pure illegal_instructions
function option<ast> illegal_instructions instr =
  if (illegal_instructions_pred (instr))
  then None else Some(instr)

(* old fetch-decode-execute *)
(*function unit fde () = {
  NIA := CIA + 4;
  instr := decode(MEMr(CIA, 4));
  instr := supported_instructions(instr);
  execute(instr);
  CIA := NIA;
}*)
