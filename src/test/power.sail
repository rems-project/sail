val extern forall Nat 'm, Nat 'n. (implicit<'m>,bit['n]) -> bit['m] effect pure EXTS

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
    mask_temp[start .. 63] := bitone ^^ (64 - start);
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
let (vector <0, 2** 64, inc, (register<(vector<0, 64, inc, bit>)>) >) DCR =
  [ 0=DCR0, 1=DCR1 ; default=undefined]

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
    exp := -126;
    (bit[53]) frac := 0b0 : word[9..31] : 0b00000000000000000000000000000;
    foreach (i from 0 to 52) {
      if frac[0] == 0 
      then { frac[0..52] := frac[1..52] : 0b0;
             exp := exp - 1; }
      else ()
     };
     temp[0] := sign;
     temp[1..11] := (bit[11]) exp + 1023;
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
     if exp < (0 - 126) 
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

(* XXX extend with zeroes -- the resulting size in completely unknown and depends of context *)
val extern forall Nat 'n, Nat 'm. (implicit<'m>,bit['n]) -> bit['m] effect pure EXTZ

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


val extern forall Nat 'n. ( bit[64] , [|'n|] , bit[8*'n]) -> unit effect { wmem } MEMw
val extern forall Nat 'n. ( bit[64] , [|'n|] ) -> (bit[8 * 'n]) effect { rmem } MEMr
val extern forall Nat 'n. ( bit[64] , [|'n|] ) -> (bit[8 * 'n]) effect { rmem } MEMr_reserve
val extern forall Nat 'n. ( bit[64] , [|'n|] , bit[8*'n]) -> bool effect { wmem } MEMw_conditional

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
val extern unit -> unit effect pure trap

register (bit[1]) mode64bit
register (bit[1]) bigendianmode

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

val bit[32] -> ast effect pure decode

scattered function ast decode

union ast member (bit[24], bit, bit) B

function clause decode (0b010010 :
(bit[24]) LI :
[AA] :
[LK] as instr) =
  B (LI,AA,LK)

function clause execute (B (LI, AA, LK)) =
  {
    if AA then NIA := EXTS (LI : 0b00) else NIA := CIA + EXTS (LI : 0b00);
    if LK then LR := CIA + 4 else ()
  }

union ast member (bit[5], bit[5], bit[14], bit, bit) Bc

function clause decode (0b010000 :
(bit[5]) BO :
(bit[5]) BI :
(bit[14]) BD :
[AA] :
[LK] as instr) =
  Bc (BO,BI,BD,AA,LK)

function clause execute (Bc (BO, BI, BD, AA, LK)) =
  {
    if mode64bit then M := 0 else M := 32;
    ctr_temp := CTR;
    if ~ (BO[2])
    then {
      ctr_temp := ctr_temp - 1;
      CTR := ctr_temp
    }
    else ();
    ctr_ok := (BO[2] | ~ (ctr_temp[M .. 63] == 0) ^ BO[3]);
    cond_ok := (BO[0] | CR[BI + 32] ^ ~ (BO[1]));
    if ctr_ok & cond_ok
    then if AA then NIA := EXTS (BD : 0b00) else NIA := CIA + EXTS (BD : 0b00)
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
  Bclr (BO,BI,BH,LK)

function clause execute (Bclr (BO, BI, BH, LK)) =
  {
    if mode64bit then M := 0 else M := 32;
    ctr_temp := CTR;
    if ~ (BO[2])
    then {
      ctr_temp := ctr_temp - 1;
      CTR := ctr_temp
    }
    else ();
    ctr_ok := (BO[2] | ~ (ctr_temp[M .. 63] == 0) ^ BO[3]);
    cond_ok := (BO[0] | CR[BI + 32] ^ ~ (BO[1]));
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
  Bcctr (BO,BI,BH,LK)

function clause execute (Bcctr (BO, BI, BH, LK)) =
  {
    cond_ok := (BO[0] | CR[BI + 32] ^ ~ (BO[1]));
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
  Crand (BT,BA,BB)

function clause execute (Crand (BT, BA, BB)) =
  CR[BT + 32] := (CR[BA + 32] & CR[BB + 32])

union ast member (bit[5], bit[5], bit[5]) Crnand

function clause decode (0b010011 :
(bit[5]) BT :
(bit[5]) BA :
(bit[5]) BB :
0b0011100001 :
(bit[1]) _ as instr) =
  Crnand (BT,BA,BB)

function clause execute (Crnand (BT, BA, BB)) =
  CR[BT + 32] := ~ (CR[BA + 32] & CR[BB + 32])

union ast member (bit[5], bit[5], bit[5]) Cror

function clause decode (0b010011 :
(bit[5]) BT :
(bit[5]) BA :
(bit[5]) BB :
0b0111000001 :
(bit[1]) _ as instr) =
  Cror (BT,BA,BB)

function clause execute (Cror (BT, BA, BB)) =
  CR[BT + 32] := (CR[BA + 32] | CR[BB + 32])

union ast member (bit[5], bit[5], bit[5]) Crxor

function clause decode (0b010011 :
(bit[5]) BT :
(bit[5]) BA :
(bit[5]) BB :
0b0011000001 :
(bit[1]) _ as instr) =
  Crxor (BT,BA,BB)

function clause execute (Crxor (BT, BA, BB)) =
  CR[BT + 32] := CR[BA + 32] ^ CR[BB + 32]

union ast member (bit[5], bit[5], bit[5]) Crnor

function clause decode (0b010011 :
(bit[5]) BT :
(bit[5]) BA :
(bit[5]) BB :
0b0000100001 :
(bit[1]) _ as instr) =
  Crnor (BT,BA,BB)

function clause execute (Crnor (BT, BA, BB)) =
  CR[BT + 32] := ~ (CR[BA + 32] | CR[BB + 32])

union ast member (bit[5], bit[5], bit[5]) Creqv

function clause decode (0b010011 :
(bit[5]) BT :
(bit[5]) BA :
(bit[5]) BB :
0b0100100001 :
(bit[1]) _ as instr) =
  Creqv (BT,BA,BB)

function clause execute (Creqv (BT, BA, BB)) =
  CR[BT + 32] := CR[BA + 32] ^ ~ (CR[BB + 32])

union ast member (bit[5], bit[5], bit[5]) Crandc

function clause decode (0b010011 :
(bit[5]) BT :
(bit[5]) BA :
(bit[5]) BB :
0b0010000001 :
(bit[1]) _ as instr) =
  Crandc (BT,BA,BB)

function clause execute (Crandc (BT, BA, BB)) =
  CR[BT + 32] := (CR[BA + 32] & ~ (CR[BB + 32]))

union ast member (bit[5], bit[5], bit[5]) Crorc

function clause decode (0b010011 :
(bit[5]) BT :
(bit[5]) BA :
(bit[5]) BB :
0b0110100001 :
(bit[1]) _ as instr) =
  Crorc (BT,BA,BB)

function clause execute (Crorc (BT, BA, BB)) =
  CR[BT + 32] := (CR[BA + 32] | ~ (CR[BB + 32]))

union ast member (bit[3], bit[3]) Mcrf

function clause decode (0b010011 :
(bit[3]) BF :
(bit[2]) _ :
(bit[3]) BFA :
(bit[2]) _ :
(bit[5]) _ :
0b0000000000 :
(bit[1]) _ as instr) =
  Mcrf (BF,BFA)

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
  Sc (LEV)

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
  Scv (LEV)

function clause execute (Scv (LEV)) = ()

union ast member (bit[5], bit[5], bit[16]) Lbz

function clause decode (0b100010 :
(bit[5]) RT :
(bit[5]) RA :
(bit[16]) D as instr) =
  Lbz (RT,RA,D)

function clause execute (Lbz (RT, RA, D)) =
  {
    (bit[64]) b := 0;
    (bit[64]) EA := 0;
    if RA == 0 then b := 0 else b := GPR[RA];
    EA := b + EXTS (D);
    GPR[RT] :=
      0b00000000000000000000000000000000000000000000000000000000 : MEMr (EA,1)
  }

union ast member (bit[5], bit[5], bit[5]) Lbzx

function clause decode (0b011111 :
(bit[5]) RT :
(bit[5]) RA :
(bit[5]) RB :
0b0001010111 :
(bit[1]) _ as instr) =
  Lbzx (RT,RA,RB)

function clause execute (Lbzx (RT, RA, RB)) =
  {
    (bit[64]) b := 0;
    (bit[64]) EA := 0;
    if RA == 0 then b := 0 else b := GPR[RA];
    EA := b + GPR[RB];
    GPR[RT] :=
      0b00000000000000000000000000000000000000000000000000000000 : MEMr (EA,1)
  }

union ast member (bit[5], bit[5], bit[16]) Lbzu

function clause decode (0b100011 :
(bit[5]) RT :
(bit[5]) RA :
(bit[16]) D as instr) =
  Lbzu (RT,RA,D)

function clause execute (Lbzu (RT, RA, D)) =
  {
    (bit[64]) EA := 0;
    EA := GPR[RA] + EXTS (D);
    GPR[RA] := EA;
    GPR[RT] :=
      0b00000000000000000000000000000000000000000000000000000000 : MEMr (EA,1)
  }

union ast member (bit[5], bit[5], bit[5]) Lbzux

function clause decode (0b011111 :
(bit[5]) RT :
(bit[5]) RA :
(bit[5]) RB :
0b0001110111 :
(bit[1]) _ as instr) =
  Lbzux (RT,RA,RB)

function clause execute (Lbzux (RT, RA, RB)) =
  {
    (bit[64]) EA := 0;
    EA := GPR[RA] + GPR[RB];
    GPR[RA] := EA;
    GPR[RT] :=
      0b00000000000000000000000000000000000000000000000000000000 : MEMr (EA,1)
  }

union ast member (bit[5], bit[5], bit[16]) Lhz

function clause decode (0b101000 :
(bit[5]) RT :
(bit[5]) RA :
(bit[16]) D as instr) =
  Lhz (RT,RA,D)

function clause execute (Lhz (RT, RA, D)) =
  {
    (bit[64]) b := 0;
    (bit[64]) EA := 0;
    if RA == 0 then b := 0 else b := GPR[RA];
    EA := b + EXTS (D);
    GPR[RT] := 0b000000000000000000000000000000000000000000000000 : MEMr (EA,2)
  }

union ast member (bit[5], bit[5], bit[5]) Lhzx

function clause decode (0b011111 :
(bit[5]) RT :
(bit[5]) RA :
(bit[5]) RB :
0b0100010111 :
(bit[1]) _ as instr) =
  Lhzx (RT,RA,RB)

function clause execute (Lhzx (RT, RA, RB)) =
  {
    (bit[64]) b := 0;
    (bit[64]) EA := 0;
    if RA == 0 then b := 0 else b := GPR[RA];
    EA := b + GPR[RB];
    GPR[RT] := 0b000000000000000000000000000000000000000000000000 : MEMr (EA,2)
  }

union ast member (bit[5], bit[5], bit[16]) Lhzu

function clause decode (0b101001 :
(bit[5]) RT :
(bit[5]) RA :
(bit[16]) D as instr) =
  Lhzu (RT,RA,D)

function clause execute (Lhzu (RT, RA, D)) =
  {
    (bit[64]) EA := 0;
    EA := GPR[RA] + EXTS (D);
    GPR[RA] := EA;
    GPR[RT] := 0b000000000000000000000000000000000000000000000000 : MEMr (EA,2)
  }

union ast member (bit[5], bit[5], bit[5]) Lhzux

function clause decode (0b011111 :
(bit[5]) RT :
(bit[5]) RA :
(bit[5]) RB :
0b0100110111 :
(bit[1]) _ as instr) =
  Lhzux (RT,RA,RB)

function clause execute (Lhzux (RT, RA, RB)) =
  {
    (bit[64]) EA := 0;
    EA := GPR[RA] + GPR[RB];
    GPR[RA] := EA;
    GPR[RT] := 0b000000000000000000000000000000000000000000000000 : MEMr (EA,2)
  }

union ast member (bit[5], bit[5], bit[16]) Lha

function clause decode (0b101010 :
(bit[5]) RT :
(bit[5]) RA :
(bit[16]) D as instr) =
  Lha (RT,RA,D)

function clause execute (Lha (RT, RA, D)) =
  {
    (bit[64]) b := 0;
    (bit[64]) EA := 0;
    if RA == 0 then b := 0 else b := GPR[RA];
    EA := b + EXTS (D);
    GPR[RT] := EXTS (MEMr (EA,2))
  }

union ast member (bit[5], bit[5], bit[5]) Lhax

function clause decode (0b011111 :
(bit[5]) RT :
(bit[5]) RA :
(bit[5]) RB :
0b0101010111 :
(bit[1]) _ as instr) =
  Lhax (RT,RA,RB)

function clause execute (Lhax (RT, RA, RB)) =
  {
    (bit[64]) b := 0;
    (bit[64]) EA := 0;
    if RA == 0 then b := 0 else b := GPR[RA];
    EA := b + GPR[RB];
    GPR[RT] := EXTS (MEMr (EA,2))
  }

union ast member (bit[5], bit[5], bit[16]) Lhau

function clause decode (0b101011 :
(bit[5]) RT :
(bit[5]) RA :
(bit[16]) D as instr) =
  Lhau (RT,RA,D)

function clause execute (Lhau (RT, RA, D)) =
  {
    (bit[64]) EA := 0;
    EA := GPR[RA] + EXTS (D);
    GPR[RA] := EA;
    GPR[RT] := EXTS (MEMr (EA,2))
  }

union ast member (bit[5], bit[5], bit[5]) Lhaux

function clause decode (0b011111 :
(bit[5]) RT :
(bit[5]) RA :
(bit[5]) RB :
0b0101110111 :
(bit[1]) _ as instr) =
  Lhaux (RT,RA,RB)

function clause execute (Lhaux (RT, RA, RB)) =
  {
    (bit[64]) EA := 0;
    EA := GPR[RA] + GPR[RB];
    GPR[RA] := EA;
    GPR[RT] := EXTS (MEMr (EA,2))
  }

union ast member (bit[5], bit[5], bit[16]) Lwz

function clause decode (0b100000 :
(bit[5]) RT :
(bit[5]) RA :
(bit[16]) D as instr) =
  Lwz (RT,RA,D)

function clause execute (Lwz (RT, RA, D)) =
  {
    (bit[64]) b := 0;
    (bit[64]) EA := 0;
    if RA == 0 then b := 0 else b := GPR[RA];
    EA := b + EXTS (D);
    GPR[RT] := 0b00000000000000000000000000000000 : MEMr (EA,4)
  }

union ast member (bit[5], bit[5], bit[5]) Lwzx

function clause decode (0b011111 :
(bit[5]) RT :
(bit[5]) RA :
(bit[5]) RB :
0b0000010111 :
(bit[1]) _ as instr) =
  Lwzx (RT,RA,RB)

function clause execute (Lwzx (RT, RA, RB)) =
  {
    (bit[64]) b := 0;
    (bit[64]) EA := 0;
    if RA == 0 then b := 0 else b := GPR[RA];
    EA := b + GPR[RB];
    GPR[RT] := 0b00000000000000000000000000000000 : MEMr (EA,4)
  }

union ast member (bit[5], bit[5], bit[16]) Lwzu

function clause decode (0b100001 :
(bit[5]) RT :
(bit[5]) RA :
(bit[16]) D as instr) =
  Lwzu (RT,RA,D)

function clause execute (Lwzu (RT, RA, D)) =
  {
    (bit[64]) EA := 0;
    EA := GPR[RA] + EXTS (D);
    GPR[RA] := EA;
    GPR[RT] := 0b00000000000000000000000000000000 : MEMr (EA,4)
  }

union ast member (bit[5], bit[5], bit[5]) Lwzux

function clause decode (0b011111 :
(bit[5]) RT :
(bit[5]) RA :
(bit[5]) RB :
0b0000110111 :
(bit[1]) _ as instr) =
  Lwzux (RT,RA,RB)

function clause execute (Lwzux (RT, RA, RB)) =
  {
    (bit[64]) EA := 0;
    EA := GPR[RA] + GPR[RB];
    GPR[RA] := EA;
    GPR[RT] := 0b00000000000000000000000000000000 : MEMr (EA,4)
  }

union ast member (bit[5], bit[5], bit[14]) Lwa

function clause decode (0b111010 :
(bit[5]) RT :
(bit[5]) RA :
(bit[14]) DS :
0b10 as instr) =
  Lwa (RT,RA,DS)

function clause execute (Lwa (RT, RA, DS)) =
  {
    (bit[64]) b := 0;
    (bit[64]) EA := 0;
    if RA == 0 then b := 0 else b := GPR[RA];
    EA := b + EXTS (DS : 0b00);
    GPR[RT] := EXTS (MEMr (EA,4))
  }

union ast member (bit[5], bit[5], bit[5]) Lwax

function clause decode (0b011111 :
(bit[5]) RT :
(bit[5]) RA :
(bit[5]) RB :
0b0101010101 :
(bit[1]) _ as instr) =
  Lwax (RT,RA,RB)

function clause execute (Lwax (RT, RA, RB)) =
  {
    (bit[64]) b := 0;
    (bit[64]) EA := 0;
    if RA == 0 then b := 0 else b := GPR[RA];
    EA := b + GPR[RB];
    GPR[RT] := EXTS (MEMr (EA,4))
  }

union ast member (bit[5], bit[5], bit[5]) Lwaux

function clause decode (0b011111 :
(bit[5]) RT :
(bit[5]) RA :
(bit[5]) RB :
0b0101110101 :
(bit[1]) _ as instr) =
  Lwaux (RT,RA,RB)

function clause execute (Lwaux (RT, RA, RB)) =
  {
    (bit[64]) EA := 0;
    EA := GPR[RA] + GPR[RB];
    GPR[RA] := EA;
    GPR[RT] := EXTS (MEMr (EA,4))
  }

union ast member (bit[5], bit[5], bit[14]) Ld

function clause decode (0b111010 :
(bit[5]) RT :
(bit[5]) RA :
(bit[14]) DS :
0b00 as instr) =
  Ld (RT,RA,DS)

function clause execute (Ld (RT, RA, DS)) =
  {
    (bit[64]) b := 0;
    (bit[64]) EA := 0;
    if RA == 0 then b := 0 else b := GPR[RA];
    EA := b + EXTS (DS : 0b00);
    GPR[RT] := MEMr (EA,8)
  }

union ast member (bit[5], bit[5], bit[5]) Ldx

function clause decode (0b011111 :
(bit[5]) RT :
(bit[5]) RA :
(bit[5]) RB :
0b0000010101 :
(bit[1]) _ as instr) =
  Ldx (RT,RA,RB)

function clause execute (Ldx (RT, RA, RB)) =
  {
    (bit[64]) b := 0;
    (bit[64]) EA := 0;
    if RA == 0 then b := 0 else b := GPR[RA];
    EA := b + GPR[RB];
    GPR[RT] := MEMr (EA,8)
  }

union ast member (bit[5], bit[5], bit[14]) Ldu

function clause decode (0b111010 :
(bit[5]) RT :
(bit[5]) RA :
(bit[14]) DS :
0b01 as instr) =
  Ldu (RT,RA,DS)

function clause execute (Ldu (RT, RA, DS)) =
  {
    (bit[64]) EA := 0;
    EA := GPR[RA] + EXTS (DS : 0b00);
    GPR[RA] := EA;
    GPR[RT] := MEMr (EA,8)
  }

union ast member (bit[5], bit[5], bit[5]) Ldux

function clause decode (0b011111 :
(bit[5]) RT :
(bit[5]) RA :
(bit[5]) RB :
0b0000110101 :
(bit[1]) _ as instr) =
  Ldux (RT,RA,RB)

function clause execute (Ldux (RT, RA, RB)) =
  {
    (bit[64]) EA := 0;
    EA := GPR[RA] + GPR[RB];
    GPR[RA] := EA;
    GPR[RT] := MEMr (EA,8)
  }

union ast member (bit[5], bit[5], bit[16]) Stb

function clause decode (0b100110 :
(bit[5]) RS :
(bit[5]) RA :
(bit[16]) D as instr) =
  Stb (RS,RA,D)

function clause execute (Stb (RS, RA, D)) =
  {
    (bit[64]) b := 0;
    (bit[64]) EA := 0;
    if RA == 0 then b := 0 else b := GPR[RA];
    EA := b + EXTS (D);
    MEMw(EA,1) := (GPR[RS])[56 .. 63]
  }

union ast member (bit[5], bit[5], bit[5]) Stbx

function clause decode (0b011111 :
(bit[5]) RS :
(bit[5]) RA :
(bit[5]) RB :
0b0011010111 :
(bit[1]) _ as instr) =
  Stbx (RS,RA,RB)

function clause execute (Stbx (RS, RA, RB)) =
  {
    (bit[64]) b := 0;
    (bit[64]) EA := 0;
    if RA == 0 then b := 0 else b := GPR[RA];
    EA := b + GPR[RB];
    MEMw(EA,1) := (GPR[RS])[56 .. 63]
  }

union ast member (bit[5], bit[5], bit[16]) Stbu

function clause decode (0b100111 :
(bit[5]) RS :
(bit[5]) RA :
(bit[16]) D as instr) =
  Stbu (RS,RA,D)

function clause execute (Stbu (RS, RA, D)) =
  {
    (bit[64]) EA := 0;
    EA := GPR[RA] + EXTS (D);
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
  Stbux (RS,RA,RB)

function clause execute (Stbux (RS, RA, RB)) =
  {
    (bit[64]) EA := 0;
    EA := GPR[RA] + GPR[RB];
    GPR[RA] := EA;
    MEMw(EA,1) := (GPR[RS])[56 .. 63]
  }

union ast member (bit[5], bit[5], bit[16]) Sth

function clause decode (0b101100 :
(bit[5]) RS :
(bit[5]) RA :
(bit[16]) D as instr) =
  Sth (RS,RA,D)

function clause execute (Sth (RS, RA, D)) =
  {
    (bit[64]) b := 0;
    (bit[64]) EA := 0;
    if RA == 0 then b := 0 else b := GPR[RA];
    EA := b + EXTS (D);
    MEMw(EA,2) := (GPR[RS])[48 .. 63]
  }

union ast member (bit[5], bit[5], bit[5]) Sthx

function clause decode (0b011111 :
(bit[5]) RS :
(bit[5]) RA :
(bit[5]) RB :
0b0110010111 :
(bit[1]) _ as instr) =
  Sthx (RS,RA,RB)

function clause execute (Sthx (RS, RA, RB)) =
  {
    (bit[64]) b := 0;
    (bit[64]) EA := 0;
    if RA == 0 then b := 0 else b := GPR[RA];
    EA := b + GPR[RB];
    MEMw(EA,2) := (GPR[RS])[48 .. 63]
  }

union ast member (bit[5], bit[5], bit[16]) Sthu

function clause decode (0b101101 :
(bit[5]) RS :
(bit[5]) RA :
(bit[16]) D as instr) =
  Sthu (RS,RA,D)

function clause execute (Sthu (RS, RA, D)) =
  {
    (bit[64]) EA := 0;
    EA := GPR[RA] + EXTS (D);
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
  Sthux (RS,RA,RB)

function clause execute (Sthux (RS, RA, RB)) =
  {
    (bit[64]) EA := 0;
    EA := GPR[RA] + GPR[RB];
    GPR[RA] := EA;
    MEMw(EA,2) := (GPR[RS])[48 .. 63]
  }

union ast member (bit[5], bit[5], bit[16]) Stw

function clause decode (0b100100 :
(bit[5]) RS :
(bit[5]) RA :
(bit[16]) D as instr) =
  Stw (RS,RA,D)

function clause execute (Stw (RS, RA, D)) =
  {
    (bit[64]) b := 0;
    (bit[64]) EA := 0;
    if RA == 0 then b := 0 else b := GPR[RA];
    EA := b + EXTS (D);
    MEMw(EA,4) := (GPR[RS])[32 .. 63]
  }

union ast member (bit[5], bit[5], bit[5]) Stwx

function clause decode (0b011111 :
(bit[5]) RS :
(bit[5]) RA :
(bit[5]) RB :
0b0010010111 :
(bit[1]) _ as instr) =
  Stwx (RS,RA,RB)

function clause execute (Stwx (RS, RA, RB)) =
  {
    (bit[64]) b := 0;
    (bit[64]) EA := 0;
    if RA == 0 then b := 0 else b := GPR[RA];
    EA := b + GPR[RB];
    MEMw(EA,4) := (GPR[RS])[32 .. 63]
  }

union ast member (bit[5], bit[5], bit[16]) Stwu

function clause decode (0b100101 :
(bit[5]) RS :
(bit[5]) RA :
(bit[16]) D as instr) =
  Stwu (RS,RA,D)

function clause execute (Stwu (RS, RA, D)) =
  {
    (bit[64]) EA := 0;
    EA := GPR[RA] + EXTS (D);
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
  Stwux (RS,RA,RB)

function clause execute (Stwux (RS, RA, RB)) =
  {
    (bit[64]) EA := 0;
    EA := GPR[RA] + GPR[RB];
    GPR[RA] := EA;
    MEMw(EA,4) := (GPR[RS])[32 .. 63]
  }

union ast member (bit[5], bit[5], bit[14]) Std

function clause decode (0b111110 :
(bit[5]) RS :
(bit[5]) RA :
(bit[14]) DS :
0b00 as instr) =
  Std (RS,RA,DS)

function clause execute (Std (RS, RA, DS)) =
  {
    (bit[64]) b := 0;
    (bit[64]) EA := 0;
    if RA == 0 then b := 0 else b := GPR[RA];
    EA := b + EXTS (DS : 0b00);
    MEMw(EA,8) := GPR[RS]
  }

union ast member (bit[5], bit[5], bit[5]) Stdx

function clause decode (0b011111 :
(bit[5]) RS :
(bit[5]) RA :
(bit[5]) RB :
0b0010010101 :
(bit[1]) _ as instr) =
  Stdx (RS,RA,RB)

function clause execute (Stdx (RS, RA, RB)) =
  {
    (bit[64]) b := 0;
    (bit[64]) EA := 0;
    if RA == 0 then b := 0 else b := GPR[RA];
    EA := b + GPR[RB];
    MEMw(EA,8) := GPR[RS]
  }

union ast member (bit[5], bit[5], bit[14]) Stdu

function clause decode (0b111110 :
(bit[5]) RS :
(bit[5]) RA :
(bit[14]) DS :
0b01 as instr) =
  Stdu (RS,RA,DS)

function clause execute (Stdu (RS, RA, DS)) =
  {
    (bit[64]) EA := 0;
    EA := GPR[RA] + EXTS (DS : 0b00);
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
  Stdux (RS,RA,RB)

function clause execute (Stdux (RS, RA, RB)) =
  {
    (bit[64]) EA := 0;
    EA := GPR[RA] + GPR[RB];
    GPR[RA] := EA;
    MEMw(EA,8) := GPR[RS]
  }

union ast member (bit[5], bit[5], bit[12], bit[4]) Lq

function clause decode (0b111000 :
(bit[5]) RTp :
(bit[5]) RA :
(bit[12]) DQ :
(bit[4]) PT as instr) =
  Lq (RTp,RA,DQ,PT)

function clause execute (Lq (RTp, RA, DQ, PT)) =
  {
    (bit[64]) EA := 0;
    (bit[64]) b := 0;
    if RA == 0 then b := 0 else b := GPR[RA];
    EA := b + EXTS (DQ : 0b0000);
    (bit[128]) mem := MEMr (EA,16);
    if bigendianmode
    then {
      GPR[RTp] := mem[0 .. 63];
      GPR[RTp + 1] := mem[64 .. 127]
    }
    else {
      (bit[128]) bytereverse := byte_reverse (mem);
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
  Stq (RSp,RA,DS)

function clause execute (Stq (RSp, RA, DS)) =
  {
    (bit[64]) b := 0;
    (bit[64]) EA := 0;
    {
      (bit[64]) EA := 0;
      (bit[64]) b := 0;
      if RA == 0 then b := 0 else b := GPR[RA];
      EA := b + EXTS (DS : 0b00);
      (bit[128]) mem := 0;
      mem[0..63] := GPR[RSp];
      mem[64..127] := GPR[RSp + 1];
      if ~ (bigendianmode) then mem := byte_reverse (mem) else ();
      MEMw(EA,16) := mem
    };
    EA := b + EXTS (DS : 0b00);
    MEMw(EA,8) := RSp
  }

union ast member (bit[5], bit[5], bit[5]) Lhbrx

function clause decode (0b011111 :
(bit[5]) RT :
(bit[5]) RA :
(bit[5]) RB :
0b1100010110 :
(bit[1]) _ as instr) =
  Lhbrx (RT,RA,RB)

function clause execute (Lhbrx (RT, RA, RB)) =
  {
    (bit[64]) b := 0;
    (bit[64]) EA := 0;
    if RA == 0 then b := 0 else b := GPR[RA];
    EA := b + GPR[RB];
    load_data := MEMr (EA,2);
    GPR[RT] :=
      0b000000000000000000000000000000000000000000000000 :
        load_data[8 .. 15] : load_data[0 .. 7]
  }

union ast member (bit[5], bit[5], bit[5]) Sthbrx

function clause decode (0b011111 :
(bit[5]) RS :
(bit[5]) RA :
(bit[5]) RB :
0b1110010110 :
(bit[1]) _ as instr) =
  Sthbrx (RS,RA,RB)

function clause execute (Sthbrx (RS, RA, RB)) =
  {
    (bit[64]) b := 0;
    (bit[64]) EA := 0;
    if RA == 0 then b := 0 else b := GPR[RA];
    EA := b + GPR[RB];
    MEMw(EA,2) := (GPR[RS])[56 .. 63] : (GPR[RS])[48 .. 55]
  }

union ast member (bit[5], bit[5], bit[5]) Lwbrx

function clause decode (0b011111 :
(bit[5]) RT :
(bit[5]) RA :
(bit[5]) RB :
0b1000010110 :
(bit[1]) _ as instr) =
  Lwbrx (RT,RA,RB)

function clause execute (Lwbrx (RT, RA, RB)) =
  {
    (bit[64]) b := 0;
    (bit[64]) EA := 0;
    if RA == 0 then b := 0 else b := GPR[RA];
    EA := b + GPR[RB];
    load_data := MEMr (EA,4);
    GPR[RT] :=
      0b00000000000000000000000000000000 :
        load_data[24 .. 31] :
          load_data[16 .. 23] : load_data[8 .. 15] : load_data[0 .. 7]
  }

union ast member (bit[5], bit[5], bit[5]) Stwbrx

function clause decode (0b011111 :
(bit[5]) RS :
(bit[5]) RA :
(bit[5]) RB :
0b1010010110 :
(bit[1]) _ as instr) =
  Stwbrx (RS,RA,RB)

function clause execute (Stwbrx (RS, RA, RB)) =
  {
    (bit[64]) b := 0;
    (bit[64]) EA := 0;
    if RA == 0 then b := 0 else b := GPR[RA];
    EA := b + GPR[RB];
    MEMw(EA,4) :=
      (GPR[RS])[56 .. 63] :
        (GPR[RS])[48 .. 55] : (GPR[RS])[40 .. 47] : (GPR[RS])[32 .. 39]
  }

union ast member (bit[5], bit[5], bit[5]) Ldbrx

function clause decode (0b011111 :
(bit[5]) RT :
(bit[5]) RA :
(bit[5]) RB :
0b1000010100 :
(bit[1]) _ as instr) =
  Ldbrx (RT,RA,RB)

function clause execute (Ldbrx (RT, RA, RB)) =
  {
    (bit[64]) b := 0;
    (bit[64]) EA := 0;
    if RA == 0 then b := 0 else b := GPR[RA];
    EA := b + GPR[RB];
    load_data := MEMr (EA,8);
    GPR[RT] :=
      load_data[56 .. 63] :
        load_data[48 .. 55] :
          load_data[40 .. 47] :
            load_data[32 .. 39] :
              load_data[24 .. 31] :
                load_data[16 .. 23] : load_data[8 .. 15] : load_data[0 .. 7]
  }

union ast member (bit[5], bit[5], bit[5]) Stdbrx

function clause decode (0b011111 :
(bit[5]) RS :
(bit[5]) RA :
(bit[5]) RB :
0b1010010100 :
(bit[1]) _ as instr) =
  Stdbrx (RS,RA,RB)

function clause execute (Stdbrx (RS, RA, RB)) =
  {
    (bit[64]) b := 0;
    (bit[64]) EA := 0;
    if RA == 0 then b := 0 else b := GPR[RA];
    EA := b + GPR[RB];
    MEMw(EA,8) :=
      (GPR[RS])[56 .. 63] :
        (GPR[RS])[48 .. 55] :
          (GPR[RS])[40 .. 47] :
            (GPR[RS])[32 .. 39] :
              (GPR[RS])[24 .. 31] :
                (GPR[RS])[16 .. 23] : (GPR[RS])[8 .. 15] : (GPR[RS])[0 .. 7]
  }

union ast member (bit[5], bit[5], bit[16]) Lmw

function clause decode (0b101110 :
(bit[5]) RT :
(bit[5]) RA :
(bit[16]) D as instr) =
  Lmw (RT,RA,D)

function clause execute (Lmw (RT, RA, D)) =
  {
    (bit[64]) b := 0;
    (bit[64]) EA := 0;
    if RA == 0 then b := 0 else b := GPR[RA];
    EA := b + EXTS (D);
    size := ([|32|]) (32 - RT) * 4;
    buffer := MEMr (EA,size);
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
  Stmw (RS,RA,D)

function clause execute (Stmw (RS, RA, D)) =
  {
    (bit[64]) b := 0;
    (bit[64]) EA := 0;
    if RA == 0 then b := 0 else b := GPR[RA];
    EA := b + EXTS (D);
    size := ([|32|]) (32 - RS) * 4;
    (bit[994]) buffer := [0 = 0,993 = 0; default=0];
    i := 0;
    foreach (r from RS to 31 by 1 in inc)
    {
      buffer[i..i + 31] := (GPR[r])[32 .. 63];
      i := i + 32
    };
    MEMw(EA,size) := buffer[0 .. size * 8]
  }

union ast member (bit[5], bit[5], bit[5]) Lswi

function clause decode (0b011111 :
(bit[5]) RT :
(bit[5]) RA :
(bit[5]) NB :
0b1001010101 :
(bit[1]) _ as instr) =
  Lswi (RT,RA,NB)

function clause execute (Lswi (RT, RA, NB)) =
  {
    (bit[64]) EA := 0;
    if RA == 0 then EA := 0 else EA := GPR[RA];
    ([|31|]) r := 0;
    r := RT - 1;
    ([|32|]) size := if NB == 0 then 32 else NB;
    (bit[256]) membuffer := MEMr (EA,size);
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
  Lswx (RT,RA,RB)

function clause execute (Lswx (RT, RA, RB)) =
  {
    (bit[64]) b := 0;
    (bit[64]) EA := 0;
    if RA == 0 then b := 0 else b := GPR[RA];
    ([|31|]) r := 0;
    EA := b + GPR[RB];
    r := RT - 1;
    i := 32;
    ([|64|]) n_top := XER[57 .. 63];
    recalculate_dependency (());
    if n_top == 0
    then GPR[RT] := undefined
    else {
      (bit[512]) membuffer := MEMr (EA,n_top);
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
  Stswi (RS,RA,NB)

function clause execute (Stswi (RS, RA, NB)) =
  {
    (bit[64]) EA := 0;
    if RA == 0 then EA := 0 else EA := GPR[RA];
    ([|31|]) r := 0;
    r := RS - 1;
    ([|32|]) size := if NB == 0 then 32 else NB;
    (bit[256]) membuffer := [0 = 0,255 = 0; default=0];
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
    MEMw(EA,size) := membuffer[0 .. size * 8]
  }

union ast member (bit[5], bit[5], bit[5]) Stswx

function clause decode (0b011111 :
(bit[5]) RS :
(bit[5]) RA :
(bit[5]) RB :
0b1010010101 :
(bit[1]) _ as instr) =
  Stswx (RS,RA,RB)

function clause execute (Stswx (RS, RA, RB)) =
  {
    (bit[64]) b := 0;
    (bit[64]) EA := 0;
    if RA == 0 then b := 0 else b := GPR[RA];
    ([|31|]) r := 0;
    EA := b + GPR[RB];
    r := RS - 1;
    i := 32;
    ([|64|]) n_top := XER[57 .. 63];
    recalculate_dependency (());
    (bit[512]) membuffer := [0 = 0,511 = 0; default=0];
    j := 0;
    foreach (n from n_top to 1 by 1 in dec)
    {
      if i == 32 then r := ([|32|]) (r + 1) mod 32 else ();
      membuffer[j..j + 7] := (GPR[r])[i .. i + 7];
      i := i + 8;
      j := j + 8;
      if i == 64 then i := 32 else ()
    };
    if ~ (n_top == 0) then MEMw(EA,n_top) := membuffer[0 .. n_top * 8] else ()
  }

union ast member (bit[5], bit[5], bit[16]) Addi

function clause decode (0b001110 :
(bit[5]) RT :
(bit[5]) RA :
(bit[16]) SI as instr) =
  Addi (RT,RA,SI)

function clause execute (Addi (RT, RA, SI)) =
  if RA == 0 then GPR[RT] := EXTS (SI) else GPR[RT] := GPR[RA] + EXTS (SI)

union ast member (bit[5], bit[5], bit[16]) Addis

function clause decode (0b001111 :
(bit[5]) RT :
(bit[5]) RA :
(bit[16]) SI as instr) =
  Addis (RT,RA,SI)

function clause execute (Addis (RT, RA, SI)) =
  if RA == 0
  then GPR[RT] := EXTS (SI : 0b0000000000000000)
  else GPR[RT] := GPR[RA] + EXTS (SI : 0b0000000000000000)

union ast member (bit[5], bit[5], bit[5], bit, bit) Add

function clause decode (0b011111 :
(bit[5]) RT :
(bit[5]) RA :
(bit[5]) RB :
[OE] :
0b100001010 :
[Rc] as instr) =
  Add (RT,RA,RB,OE,Rc)

function clause execute (Add (RT, RA, RB, OE, Rc)) =
  let (temp, overflow, _) = (GPR[RA] +_s GPR[RB]) in
    {
      GPR[RT] := temp;
      if Rc
      then {
        xer_so := XER.SO;
        if OE & overflow then xer_so := overflow else ();
        set_overflow_cr0 (temp,xer_so)
      }
      else ();
      if OE then set_SO_OV (overflow) else ()
    }

union ast member (bit[5], bit[5], bit[5], bit, bit) Subf

function clause decode (0b011111 :
(bit[5]) RT :
(bit[5]) RA :
(bit[5]) RB :
[OE] :
0b000101000 :
[Rc] as instr) =
  Subf (RT,RA,RB,OE,Rc)

function clause execute (Subf (RT, RA, RB, OE, Rc)) =
  let (t1, o1, _) = (~ (GPR[RA]) +_s GPR[RB]) in
    let (t2, o2, _) = (t1 +_s (bit) 1) in
      {
        (bit[64]) temp := t2;
        overflow := (o1 | o2);
        GPR[RT] := temp;
        if Rc
        then {
          xer_so := XER.SO;
          if OE & overflow then xer_so := overflow else ();
          set_overflow_cr0 (temp,xer_so)
        }
        else ();
        if OE then set_SO_OV (overflow) else ()
      }

union ast member (bit[5], bit[5], bit[16]) Addic

function clause decode (0b001100 :
(bit[5]) RT :
(bit[5]) RA :
(bit[16]) SI as instr) =
  Addic (RT,RA,SI)

function clause execute (Addic (RT, RA, SI)) =
  let (temp, _, carry) = (GPR[RA] +_s EXTS (SI)) in
    {
      GPR[RT] := temp;
      CA := carry
    }

union ast member (bit[5], bit[5], bit[16]) AddicDot

function clause decode (0b001101 :
(bit[5]) RT :
(bit[5]) RA :
(bit[16]) SI as instr) =
  AddicDot (RT,RA,SI)

function clause execute (AddicDot (RT, RA, SI)) =
  let (temp, overflow, carry) = (GPR[RA] +_s EXTS (SI)) in
    {
      GPR[RT] := temp;
      CA := carry;
      set_overflow_cr0 (temp,overflow | XER.SO)
    }

union ast member (bit[5], bit[5], bit[16]) Subfic

function clause decode (0b001000 :
(bit[5]) RT :
(bit[5]) RA :
(bit[16]) SI as instr) =
  Subfic (RT,RA,SI)

function clause execute (Subfic (RT, RA, SI)) =
  let (t1, o1, c1) = (~ (GPR[RA]) +_s EXTS (SI)) in
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
  Addc (RT,RA,RB,OE,Rc)

function clause execute (Addc (RT, RA, RB, OE, Rc)) =
  let (temp, overflow, carry) = (GPR[RA] +_s GPR[RB]) in
    {
      GPR[RT] := temp;
      if Rc
      then {
        xer_so := XER.SO;
        if OE & overflow then xer_so := overflow else ();
        set_overflow_cr0 (temp,xer_so)
      }
      else ();
      CA := carry;
      if OE then set_SO_OV (overflow) else ()
    }

union ast member (bit[5], bit[5], bit[5], bit, bit) Subfc

function clause decode (0b011111 :
(bit[5]) RT :
(bit[5]) RA :
(bit[5]) RB :
[OE] :
0b000001000 :
[Rc] as instr) =
  Subfc (RT,RA,RB,OE,Rc)

function clause execute (Subfc (RT, RA, RB, OE, Rc)) =
  let (t1, o1, c1) = (~ (GPR[RA]) +_s GPR[RB]) in
    let (t2, o2, c2) = (t1 +_s (bit) 1) in
      {
        (bit[64]) temp := t2;
        overflow := (o1 | o2);
        carry := (c1 | c2);
        GPR[RT] := temp;
        if Rc
        then {
          xer_so := XER.SO;
          if OE & overflow then xer_so := overflow else ();
          set_overflow_cr0 (temp,xer_so)
        }
        else ();
        CA := carry;
        if OE then set_SO_OV (overflow) else ()
      }

union ast member (bit[5], bit[5], bit[5], bit, bit) Adde

function clause decode (0b011111 :
(bit[5]) RT :
(bit[5]) RA :
(bit[5]) RB :
[OE] :
0b010001010 :
[Rc] as instr) =
  Adde (RT,RA,RB,OE,Rc)

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
          xer_so := XER.SO;
          if OE & overflow then xer_so := overflow else ();
          set_overflow_cr0 (temp,xer_so)
        }
        else ();
        CA := carry;
        if OE then set_SO_OV (overflow) else ()
      }

union ast member (bit[5], bit[5], bit[5], bit, bit) Subfe

function clause decode (0b011111 :
(bit[5]) RT :
(bit[5]) RA :
(bit[5]) RB :
[OE] :
0b010001000 :
[Rc] as instr) =
  Subfe (RT,RA,RB,OE,Rc)

function clause execute (Subfe (RT, RA, RB, OE, Rc)) =
  let (t1, o1, c1) = (~ (GPR[RA]) +_s GPR[RB]) in
    let (t2, o2, c2) = (t1 +_s (bit) CA) in
      {
        (bit[64]) temp := t2;
        overflow := (o1 | o2);
        carry := (c1 | c2);
        GPR[RT] := temp;
        if Rc
        then {
          xer_so := XER.SO;
          if OE & overflow then xer_so := overflow else ();
          set_overflow_cr0 (temp,xer_so)
        }
        else ();
        CA := carry;
        if OE then set_SO_OV (overflow) else ()
      }

union ast member (bit[5], bit[5], bit, bit) Addme

function clause decode (0b011111 :
(bit[5]) RT :
(bit[5]) RA :
(bit[5]) _ :
[OE] :
0b011101010 :
[Rc] as instr) =
  Addme (RT,RA,OE,Rc)

function clause execute (Addme (RT, RA, OE, Rc)) =
  let (t1, o1, c1) = (GPR[RA] +_s CA) in
    let (t2, o2, c2) =
      (t1 +_s 0b1111111111111111111111111111111111111111111111111111111111111111) in
      {
        (bit[64]) temp := t2;
        overflow := (o1 | o2);
        carry := (c1 | c2);
        GPR[RT] := temp;
        if Rc
        then {
          xer_so := XER.SO;
          if OE & overflow then xer_so := overflow else ();
          set_overflow_cr0 (temp,xer_so)
        }
        else ();
        CA := carry;
        if OE then set_SO_OV (overflow) else ()
      }

union ast member (bit[5], bit[5], bit, bit) Subfme

function clause decode (0b011111 :
(bit[5]) RT :
(bit[5]) RA :
(bit[5]) _ :
[OE] :
0b011101000 :
[Rc] as instr) =
  Subfme (RT,RA,OE,Rc)

function clause execute (Subfme (RT, RA, OE, Rc)) =
  let (t1, o1, c1) = (~ (GPR[RA]) +_s CA) in
    let (t2, o2, c2) =
      (t1 +_s 0b1111111111111111111111111111111111111111111111111111111111111111) in
      {
        (bit[64]) temp := t2;
        overflow := (o1 | o2);
        carry := (c1 | c2);
        GPR[RT] := temp;
        if Rc
        then {
          xer_so := XER.SO;
          if OE & overflow then xer_so := overflow else ();
          set_overflow_cr0 (temp,xer_so)
        }
        else ();
        CA := carry;
        if OE then set_SO_OV (overflow) else ()
      }

union ast member (bit[5], bit[5], bit, bit) Addze

function clause decode (0b011111 :
(bit[5]) RT :
(bit[5]) RA :
(bit[5]) _ :
[OE] :
0b011001010 :
[Rc] as instr) =
  Addze (RT,RA,OE,Rc)

function clause execute (Addze (RT, RA, OE, Rc)) =
  let (temp, overflow, carry) = (GPR[RA] +_s CA) in
    {
      GPR[RT] := temp;
      if Rc
      then {
        xer_so := XER.SO;
        if OE & overflow then xer_so := overflow else ();
        set_overflow_cr0 (temp,xer_so)
      }
      else ();
      CA := carry;
      if OE then set_SO_OV (overflow) else ()
    }

union ast member (bit[5], bit[5], bit, bit) Subfze

function clause decode (0b011111 :
(bit[5]) RT :
(bit[5]) RA :
(bit[5]) _ :
[OE] :
0b011001000 :
[Rc] as instr) =
  Subfze (RT,RA,OE,Rc)

function clause execute (Subfze (RT, RA, OE, Rc)) =
  let (temp, overflow, carry) = (~ (GPR[RA]) +_s CA) in
    {
      GPR[RT] := temp;
      if Rc
      then {
        xer_so := XER.SO;
        if OE & overflow then xer_so := overflow else ();
        set_overflow_cr0 (temp,xer_so)
      }
      else ();
      CA := carry;
      if OE then set_SO_OV (overflow) else ()
    }

union ast member (bit[5], bit[5], bit, bit) Neg

function clause decode (0b011111 :
(bit[5]) RT :
(bit[5]) RA :
(bit[5]) _ :
[OE] :
0b001101000 :
[Rc] as instr) =
  Neg (RT,RA,OE,Rc)

function clause execute (Neg (RT, RA, OE, Rc)) =
  let (temp, overflow, _) = (~ (GPR[RA]) +_s (bit) 1) in
    {
      GPR[RT] := temp;
      if Rc then set_overflow_cr0 (temp,XER.SO) else ();
      if OE then set_SO_OV (overflow) else ()
    }

union ast member (bit[5], bit[5], bit[16]) Mulli

function clause decode (0b000111 :
(bit[5]) RT :
(bit[5]) RA :
(bit[16]) SI as instr) =
  Mulli (RT,RA,SI)

function clause execute (Mulli (RT, RA, SI)) =
  {
    (bit[128]) prod := GPR[RA] *_s EXTS (SI);
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
  Mullw (RT,RA,RB,OE,Rc)

function clause execute (Mullw (RT, RA, RB, OE, Rc)) =
  let (prod, overflow, _) = ((GPR[RA])[32 .. 63] *_s (GPR[RB])[32 .. 63]) in
    {
      GPR[RT] := prod;
      if Rc
      then {
        xer_so := XER.SO;
        if OE & overflow then xer_so := overflow else ();
        set_overflow_cr0 (prod,xer_so)
      }
      else ();
      if OE then set_SO_OV (overflow) else ()
    }

union ast member (bit[5], bit[5], bit[5], bit) Mulhw

function clause decode (0b011111 :
(bit[5]) RT :
(bit[5]) RA :
(bit[5]) RB :
(bit[1]) _ :
0b001001011 :
[Rc] as instr) =
  Mulhw (RT,RA,RB,Rc)

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
    (GPR[RT])[0..31] := (bit[32]) undefined;
    if Rc
    then {
      xer_so := XER.SO;
      if mode64bit
      then CR.CR0 := [undefined,undefined,undefined,xer_so]
      else set_overflow_cr0 (prod,xer_so)
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
  Mulhwu (RT,RA,RB,Rc)

function clause execute (Mulhwu (RT, RA, RB, Rc)) =
  {
    (bit[64]) prod := (GPR[RA])[32 .. 63] * (GPR[RB])[32 .. 63];
    (GPR[RT])[32..63] := prod[0 .. 31];
    (GPR[RT])[0..31] := (bit[32]) undefined;
    if Rc
    then {
      xer_so := XER.SO;
      if mode64bit
      then CR.CR0 := [undefined,undefined,undefined,xer_so]
      else set_overflow_cr0 (prod,xer_so)
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
  Divw (RT,RA,RB,OE,Rc)

function clause execute (Divw (RT, RA, RB, OE, Rc)) =
  {
    (bit[32]) dividend := (GPR[RA])[32 .. 63];
    (bit[32]) divisor := (GPR[RB])[32 .. 63];
    (bit[64]) divided :=
      0b0000000000000000000000000000000000000000000000000000000000000000;
    (bit) overflow := 0;
    let (d, o, _) = (dividend quot_s divisor) in
      {
        divided[32..63] := d;
        overflow := o
      };
    (GPR[RT])[32..63] := divided[32 .. 63];
    (GPR[RT])[0..31] := (bit[32]) undefined;
    if Rc
    then {
      xer_so := XER.SO;
      if OE & overflow then xer_so := overflow else ();
      if mode64bit | overflow
      then CR.CR0 := [undefined,undefined,undefined,xer_so]
      else set_overflow_cr0 (divided,xer_so)
    }
    else ();
    if OE then set_SO_OV (overflow) else ()
  }

union ast member (bit[5], bit[5], bit[5], bit, bit) Divwu

function clause decode (0b011111 :
(bit[5]) RT :
(bit[5]) RA :
(bit[5]) RB :
[OE] :
0b111001011 :
[Rc] as instr) =
  Divwu (RT,RA,RB,OE,Rc)

function clause execute (Divwu (RT, RA, RB, OE, Rc)) =
  {
    (bit[32]) dividend := (GPR[RA])[32 .. 63];
    (bit[32]) divisor := (GPR[RB])[32 .. 63];
    (bit[64]) divided :=
      0b0000000000000000000000000000000000000000000000000000000000000000;
    (bit) overflow := 0;
    let (d, o, _) = (dividend quot divisor) in
      {
        divided[32..63] := d;
        overflow := o
      };
    (GPR[RT])[32..63] := divided[32 .. 63];
    (GPR[RT])[0..31] := (bit[32]) undefined;
    if Rc
    then {
      xer_so := XER.SO;
      if OE & overflow then xer_so := overflow else ();
      if mode64bit | overflow
      then CR.CR0 := [undefined,undefined,undefined,xer_so]
      else set_overflow_cr0 (divided,xer_so)
    }
    else ();
    if OE then set_SO_OV (overflow) else ()
  }

union ast member (bit[5], bit[5], bit[5], bit, bit) Divwe

function clause decode (0b011111 :
(bit[5]) RT :
(bit[5]) RA :
(bit[5]) RB :
[OE] :
0b110101011 :
[Rc] as instr) =
  Divwe (RT,RA,RB,OE,Rc)

function clause execute (Divwe (RT, RA, RB, OE, Rc)) =
  {
    (bit[64]) dividend :=
      (GPR[RA])[32 .. 63] : 0b00000000000000000000000000000000;
    (bit[32]) divisor := (GPR[RB])[32 .. 63];
    (bit[64]) divided :=
      0b0000000000000000000000000000000000000000000000000000000000000000;
    (bit) overflow := 0;
    let (d, o, _) = (dividend quot_s divisor) in
      {
        divided[32..63] := d[32 .. 63];
        overflow := o
      };
    (GPR[RT])[32..63] := divided[32 .. 63];
    (GPR[RT])[0..31] := (bit[32]) undefined;
    if Rc
    then {
      xer_so := XER.SO;
      if OE & overflow then xer_so := overflow else ();
      if mode64bit | overflow
      then CR.CR0 := [undefined,undefined,undefined,xer_so]
      else set_overflow_cr0 (divided,xer_so)
    }
    else ();
    if OE then set_SO_OV (overflow) else ()
  }

union ast member (bit[5], bit[5], bit[5], bit, bit) Divweu

function clause decode (0b011111 :
(bit[5]) RT :
(bit[5]) RA :
(bit[5]) RB :
[OE] :
0b110001011 :
[Rc] as instr) =
  Divweu (RT,RA,RB,OE,Rc)

function clause execute (Divweu (RT, RA, RB, OE, Rc)) =
  {
    (bit[64]) dividend :=
      (GPR[RA])[32 .. 63] : 0b00000000000000000000000000000000;
    (bit[32]) divisor := (GPR[RB])[32 .. 63];
    (bit[64]) divided :=
      0b0000000000000000000000000000000000000000000000000000000000000000;
    (bit) overflow := 0;
    let (d, o, _) = (dividend quot divisor) in
      {
        divided[32..63] := d[32 .. 63];
        overflow := o
      };
    (GPR[RT])[32..63] := divided[32 .. 63];
    (GPR[RT])[0..31] := (bit[32]) undefined;
    if Rc
    then {
      xer_so := XER.SO;
      if OE & overflow then xer_so := overflow else ();
      if mode64bit | overflow
      then CR.CR0 := [undefined,undefined,undefined,xer_so]
      else set_overflow_cr0 (divided,xer_so)
    }
    else ();
    if OE then set_SO_OV (overflow) else ()
  }

union ast member (bit[5], bit[5], bit[5], bit, bit) Mulld

function clause decode (0b011111 :
(bit[5]) RT :
(bit[5]) RA :
(bit[5]) RB :
[OE] :
0b011101001 :
[Rc] as instr) =
  Mulld (RT,RA,RB,OE,Rc)

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
      xer_so := XER.SO;
      if OE & overflow then xer_so := overflow else ();
      set_overflow_cr0 (prod[64 .. 127],xer_so)
    }
    else ();
    if OE then set_SO_OV (overflow) else ()
  }

union ast member (bit[5], bit[5], bit[5], bit) Mulhd

function clause decode (0b011111 :
(bit[5]) RT :
(bit[5]) RA :
(bit[5]) RB :
(bit[1]) _ :
0b001001001 :
[Rc] as instr) =
  Mulhd (RT,RA,RB,Rc)

function clause execute (Mulhd (RT, RA, RB, Rc)) =
  {
    (bit[128]) prod := GPR[RA] *_s GPR[RB];
    GPR[RT] := prod[0 .. 63];
    if Rc then set_overflow_cr0 (prod[0 .. 63],XER.SO) else ()
  }

union ast member (bit[5], bit[5], bit[5], bit) Mulhdu

function clause decode (0b011111 :
(bit[5]) RT :
(bit[5]) RA :
(bit[5]) RB :
(bit[1]) _ :
0b000001001 :
[Rc] as instr) =
  Mulhdu (RT,RA,RB,Rc)

function clause execute (Mulhdu (RT, RA, RB, Rc)) =
  {
    (bit[128]) prod := GPR[RA] * GPR[RB];
    GPR[RT] := prod[0 .. 63];
    if Rc then set_overflow_cr0 (prod[0 .. 63],XER.SO) else ()
  }

union ast member (bit[5], bit[5], bit[5], bit, bit) Divd

function clause decode (0b011111 :
(bit[5]) RT :
(bit[5]) RA :
(bit[5]) RB :
[OE] :
0b111101001 :
[Rc] as instr) =
  Divd (RT,RA,RB,OE,Rc)

function clause execute (Divd (RT, RA, RB, OE, Rc)) =
  {
    (bit[64]) dividend := GPR[RA];
    (bit[64]) divisor := GPR[RB];
    (bit[64]) divided :=
      0b0000000000000000000000000000000000000000000000000000000000000000;
    (bit) overflow := 0;
    let (d, o, _) = (dividend quot_s divisor) in
      {
        divided := d;
        overflow := o
      };
    GPR[RT] := divided;
    if OE then set_SO_OV (overflow) else ();
    if Rc then set_overflow_cr0 (divided,overflow | XER.SO) else ()
  }

union ast member (bit[5], bit[5], bit[5], bit, bit) Divdu

function clause decode (0b011111 :
(bit[5]) RT :
(bit[5]) RA :
(bit[5]) RB :
[OE] :
0b111001001 :
[Rc] as instr) =
  Divdu (RT,RA,RB,OE,Rc)

function clause execute (Divdu (RT, RA, RB, OE, Rc)) =
  {
    (bit[64]) dividend := GPR[RA];
    (bit[64]) divisor := GPR[RB];
    (bit[64]) divided :=
      0b0000000000000000000000000000000000000000000000000000000000000000;
    (bit) overflow := 0;
    let (d, o, _) = (dividend quot divisor) in
      {
        divided := d;
        overflow := o
      };
    GPR[RT] := divided;
    if OE then set_SO_OV (overflow) else ();
    if Rc then set_overflow_cr0 (divided,overflow | XER.SO) else ()
  }

union ast member (bit[5], bit[5], bit[5], bit, bit) Divde

function clause decode (0b011111 :
(bit[5]) RT :
(bit[5]) RA :
(bit[5]) RB :
[OE] :
0b110101001 :
[Rc] as instr) =
  Divde (RT,RA,RB,OE,Rc)

function clause execute (Divde (RT, RA, RB, OE, Rc)) =
  {
    (bit[128]) dividend :=
      GPR[RA] :
        0b0000000000000000000000000000000000000000000000000000000000000000;
    (bit[64]) divisor := GPR[RB];
    (bit[128]) divided := 0;
    (bit) overflow := 0;
    let (d, o, _) = (dividend quot_s divisor) in
      {
        divided := d;
        overflow := o
      };
    GPR[RT] := divided[64 .. 127];
    if OE then set_SO_OV (overflow) else ();
    if Rc
    then {
      xer_so := XER.SO;
      if OE & overflow then xer_so := overflow else ();
      if overflow
      then CR.CR0 := [undefined,undefined,undefined,xer_so]
      else set_overflow_cr0 (divided[64 .. 127],xer_so)
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
  Divdeu (RT,RA,RB,OE,Rc)

function clause execute (Divdeu (RT, RA, RB, OE, Rc)) =
  {
    (bit[128]) dividend :=
      GPR[RA] :
        0b0000000000000000000000000000000000000000000000000000000000000000;
    (bit[64]) divisor := GPR[RB];
    (bit[128]) divided := 0;
    (bit) overflow := 0;
    let (d, o, _) = (dividend quot divisor) in
      {
        divided := d;
        overflow := o
      };
    GPR[RT] := divided[64 .. 127];
    if OE then set_SO_OV (overflow) else ();
    if Rc
    then {
      xer_so := XER.SO;
      if OE & overflow then xer_so := overflow else ();
      if overflow
      then CR.CR0 := [undefined,undefined,undefined,xer_so]
      else set_overflow_cr0 (divided[64 .. 127],xer_so)
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
  Cmpi (BF,L,RA,SI)

function clause execute (Cmpi (BF, L, RA, SI)) =
  {
    (bit[64]) a := 0;
    if L == 0 then a := EXTS ((GPR[RA])[32 .. 63]) else a := GPR[RA];
    if a < EXTS (SI)
    then c := 0b100
    else if a > EXTS (SI) then c := 0b010 else c := 0b001;
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
  Cmp (BF,L,RA,RB)

function clause execute (Cmp (BF, L, RA, RB)) =
  {
    (bit[64]) a := 0;
    (bit[64]) b := 0;
    if L == 0
    then {
      a := EXTS ((GPR[RA])[32 .. 63]);
      b := EXTS ((GPR[RB])[32 .. 63])
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
  Cmpli (BF,L,RA,UI)

function clause execute (Cmpli (BF, L, RA, UI)) =
  {
    (bit[64]) a := 0;
    (bit[3]) c := 0;
    if L == 0
    then a := 0b00000000000000000000000000000000 : (GPR[RA])[32 .. 63]
    else a := GPR[RA];
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
  Cmpl (BF,L,RA,RB)

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

union ast member (bit[5], bit[5], bit[16]) Twi

function clause decode (0b000011 :
(bit[5]) TO :
(bit[5]) RA :
(bit[16]) SI as instr) =
  Twi (TO,RA,SI)

function clause execute (Twi (TO, RA, SI)) =
  {
    a := EXTS ((GPR[RA])[32 .. 63]);
    if a < EXTS (SI) & TO[0] then trap () else ();
    if a > EXTS (SI) & TO[1] then trap () else ();
    if a == EXTS (SI) & TO[2] then trap () else ();
    if a <_u EXTS (SI) & TO[3] then trap () else ();
    if a >_u EXTS (SI) & TO[4] then trap () else ()
  }

union ast member (bit[5], bit[5], bit[5]) Tw

function clause decode (0b011111 :
(bit[5]) TO :
(bit[5]) RA :
(bit[5]) RB :
0b0000000100 :
(bit[1]) _ as instr) =
  Tw (TO,RA,RB)

function clause execute (Tw (TO, RA, RB)) =
  {
    a := EXTS ((GPR[RA])[32 .. 63]);
    b := EXTS ((GPR[RB])[32 .. 63]);
    if a < b & TO[0] then trap () else ();
    if a > b & TO[1] then trap () else ();
    if a == b & TO[2] then trap () else ();
    if a <_u b & TO[3] then trap () else ();
    if a >_u b & TO[4] then trap () else ()
  }

union ast member (bit[5], bit[5], bit[16]) Tdi

function clause decode (0b000010 :
(bit[5]) TO :
(bit[5]) RA :
(bit[16]) SI as instr) =
  Tdi (TO,RA,SI)

function clause execute (Tdi (TO, RA, SI)) = ()

union ast member (bit[5], bit[5], bit[5]) Td

function clause decode (0b011111 :
(bit[5]) TO :
(bit[5]) RA :
(bit[5]) RB :
0b0001000100 :
(bit[1]) _ as instr) =
  Td (TO,RA,RB)

function clause execute (Td (TO, RA, RB)) = ()

union ast member (bit[5], bit[5], bit[5], bit[5]) Isel

function clause decode (0b011111 :
(bit[5]) RT :
(bit[5]) RA :
(bit[5]) RB :
(bit[5]) BC :
0b01111 :
(bit[1]) _ as instr) =
  Isel (RT,RA,RB,BC)

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
  Andi (RS,RA,UI)

function clause execute (Andi (RS, RA, UI)) =
  {
    (bit[64]) temp :=
      (GPR[RS] & 0b000000000000000000000000000000000000000000000000 : UI);
    GPR[RA] := temp;
    set_overflow_cr0 (temp,XER.SO)
  }

union ast member (bit[5], bit[5], bit[16]) Andis

function clause decode (0b011101 :
(bit[5]) RS :
(bit[5]) RA :
(bit[16]) UI as instr) =
  Andis (RS,RA,UI)

function clause execute (Andis (RS, RA, UI)) =
  {
    (bit[64]) temp :=
      (GPR[RS] & 0b00000000000000000000000000000000 : UI : 0b0000000000000000);
    GPR[RA] := temp;
    set_overflow_cr0 (temp,XER.SO)
  }

union ast member (bit[5], bit[5], bit[16]) Ori

function clause decode (0b011000 :
(bit[5]) RS :
(bit[5]) RA :
(bit[16]) UI as instr) =
  Ori (RS,RA,UI)

function clause execute (Ori (RS, RA, UI)) =
  GPR[RA] := (GPR[RS] | 0b000000000000000000000000000000000000000000000000 : UI)

union ast member (bit[5], bit[5], bit[16]) Oris

function clause decode (0b011001 :
(bit[5]) RS :
(bit[5]) RA :
(bit[16]) UI as instr) =
  Oris (RS,RA,UI)

function clause execute (Oris (RS, RA, UI)) =
  GPR[RA] :=
    (GPR[RS] | 0b00000000000000000000000000000000 : UI : 0b0000000000000000)

union ast member (bit[5], bit[5], bit[16]) Xori

function clause decode (0b011010 :
(bit[5]) RS :
(bit[5]) RA :
(bit[16]) UI as instr) =
  Xori (RS,RA,UI)

function clause execute (Xori (RS, RA, UI)) =
  GPR[RA] := GPR[RS] ^ 0b000000000000000000000000000000000000000000000000 : UI

union ast member (bit[5], bit[5], bit[16]) Xoris

function clause decode (0b011011 :
(bit[5]) RS :
(bit[5]) RA :
(bit[16]) UI as instr) =
  Xoris (RS,RA,UI)

function clause execute (Xoris (RS, RA, UI)) =
  GPR[RA] :=
    GPR[RS] ^ 0b00000000000000000000000000000000 : UI : 0b0000000000000000

union ast member (bit[5], bit[5], bit[5], bit) And

function clause decode (0b011111 :
(bit[5]) RS :
(bit[5]) RA :
(bit[5]) RB :
0b0000011100 :
[Rc] as instr) =
  And (RS,RA,RB,Rc)

function clause execute (And (RS, RA, RB, Rc)) =
  {
    (bit[64]) temp := (GPR[RS] & GPR[RB]);
    GPR[RA] := temp;
    if Rc then set_overflow_cr0 (temp,XER.SO) else ()
  }

union ast member (bit[5], bit[5], bit[5], bit) Xor

function clause decode (0b011111 :
(bit[5]) RS :
(bit[5]) RA :
(bit[5]) RB :
0b0100111100 :
[Rc] as instr) =
  Xor (RS,RA,RB,Rc)

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
    if Rc then set_overflow_cr0 (temp,XER.SO) else ()
  }

union ast member (bit[5], bit[5], bit[5], bit) Nand

function clause decode (0b011111 :
(bit[5]) RS :
(bit[5]) RA :
(bit[5]) RB :
0b0111011100 :
[Rc] as instr) =
  Nand (RS,RA,RB,Rc)

function clause execute (Nand (RS, RA, RB, Rc)) =
  {
    (bit[64]) temp := ~ (GPR[RS] & GPR[RB]);
    GPR[RA] := temp;
    if Rc then set_overflow_cr0 (temp,XER.SO) else ()
  }

union ast member (bit[5], bit[5], bit[5], bit) Or

function clause decode (0b011111 :
(bit[5]) RS :
(bit[5]) RA :
(bit[5]) RB :
0b0110111100 :
[Rc] as instr) =
  Or (RS,RA,RB,Rc)

function clause execute (Or (RS, RA, RB, Rc)) =
  {
    (bit[64]) temp := (GPR[RS] | GPR[RB]);
    GPR[RA] := temp;
    if Rc then set_overflow_cr0 (temp,XER.SO) else ()
  }

union ast member (bit[5], bit[5], bit[5], bit) Nor

function clause decode (0b011111 :
(bit[5]) RS :
(bit[5]) RA :
(bit[5]) RB :
0b0001111100 :
[Rc] as instr) =
  Nor (RS,RA,RB,Rc)

function clause execute (Nor (RS, RA, RB, Rc)) =
  {
    (bit[64]) temp := ~ (GPR[RS] | GPR[RB]);
    GPR[RA] := temp;
    if Rc then set_overflow_cr0 (temp,XER.SO) else ()
  }

union ast member (bit[5], bit[5], bit[5], bit) Eqv

function clause decode (0b011111 :
(bit[5]) RS :
(bit[5]) RA :
(bit[5]) RB :
0b0100011100 :
[Rc] as instr) =
  Eqv (RS,RA,RB,Rc)

function clause execute (Eqv (RS, RA, RB, Rc)) =
  {
    (bit[64]) temp := GPR[RS] ^ ~ (GPR[RB]);
    GPR[RA] := temp;
    if Rc then set_overflow_cr0 (temp,XER.SO) else ()
  }

union ast member (bit[5], bit[5], bit[5], bit) Andc

function clause decode (0b011111 :
(bit[5]) RS :
(bit[5]) RA :
(bit[5]) RB :
0b0000111100 :
[Rc] as instr) =
  Andc (RS,RA,RB,Rc)

function clause execute (Andc (RS, RA, RB, Rc)) =
  {
    (bit[64]) temp := (GPR[RS] & ~ (GPR[RB]));
    GPR[RA] := temp;
    if Rc then set_overflow_cr0 (temp,XER.SO) else ()
  }

union ast member (bit[5], bit[5], bit[5], bit) Orc

function clause decode (0b011111 :
(bit[5]) RS :
(bit[5]) RA :
(bit[5]) RB :
0b0110011100 :
[Rc] as instr) =
  Orc (RS,RA,RB,Rc)

function clause execute (Orc (RS, RA, RB, Rc)) =
  {
    (bit[64]) temp := (GPR[RS] | ~ (GPR[RB]));
    GPR[RA] := temp;
    if Rc then set_overflow_cr0 (temp,XER.SO) else ()
  }

union ast member (bit[5], bit[5], bit) Extsb

function clause decode (0b011111 :
(bit[5]) RS :
(bit[5]) RA :
(bit[5]) _ :
0b1110111010 :
[Rc] as instr) =
  Extsb (RS,RA,Rc)

function clause execute (Extsb (RS, RA, Rc)) =
  {
    (bit[64]) temp := 0;
    s := (GPR[RS])[56];
    temp[56..63] := (GPR[RS])[56 .. 63];
    (GPR[RA])[56..63] := temp[56 .. 63];
    temp[0..55] := s ^^ 56;
    (GPR[RA])[0..55] := temp[0 .. 55];
    if Rc then set_overflow_cr0 (temp,XER.SO) else ()
  }

union ast member (bit[5], bit[5], bit) Extsh

function clause decode (0b011111 :
(bit[5]) RS :
(bit[5]) RA :
(bit[5]) _ :
0b1110011010 :
[Rc] as instr) =
  Extsh (RS,RA,Rc)

function clause execute (Extsh (RS, RA, Rc)) =
  {
    (bit[64]) temp := 0;
    s := (GPR[RS])[48];
    temp[48..63] := (GPR[RS])[48 .. 63];
    (GPR[RA])[48..63] := temp[48 .. 63];
    temp[0..47] := s ^^ 48;
    (GPR[RA])[0..47] := temp[0 .. 47];
    if Rc then set_overflow_cr0 (temp,XER.SO) else ()
  }

union ast member (bit[5], bit[5], bit) Cntlzw

function clause decode (0b011111 :
(bit[5]) RS :
(bit[5]) RA :
(bit[5]) _ :
0b0000011010 :
[Rc] as instr) =
  Cntlzw (RS,RA,Rc)

function clause execute (Cntlzw (RS, RA, Rc)) =
  {
    temp := (bit[64]) (countLeadingZeroes (GPR[RS],32));
    GPR[RA] := temp;
    if Rc then set_overflow_cr0 (temp,XER.SO) else ()
  }

union ast member (bit[5], bit[5], bit[5]) Cmpb

function clause decode (0b011111 :
(bit[5]) RS :
(bit[5]) RA :
(bit[5]) RB :
0b0111111100 :
(bit[1]) _ as instr) =
  Cmpb (RS,RA,RB)

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
  Popcntb (RS,RA)

function clause execute (Popcntb (RS, RA)) =
  foreach (i from 0 to 7 by 1 in inc)
  {
    ([|64|]) n := 0;
    foreach (j from 0 to 7 by 1 in inc)
    if (GPR[RS])[i * 8 + j] == 1 then n := n + 1 else ();
    (GPR[RA])[i * 8..i * 8 + 7] := (bit[8]) n
  }

union ast member (bit[5], bit[5]) Popcntw

function clause decode (0b011111 :
(bit[5]) RS :
(bit[5]) RA :
(bit[5]) _ :
0b0101111010 :
(bit[1]) _ as instr) =
  Popcntw (RS,RA)

function clause execute (Popcntw (RS, RA)) =
  foreach (i from 0 to 1 by 1 in inc)
  {
    ([|64|]) n := 0;
    foreach (j from 0 to 31 by 1 in inc)
    if (GPR[RS])[i * 32 + j] == 1 then n := n + 1 else ();
    (GPR[RA])[i * 32..i * 32 + 31] := (bit[32]) n
  }

union ast member (bit[5], bit[5]) Prtyd

function clause decode (0b011111 :
(bit[5]) RS :
(bit[5]) RA :
(bit[5]) _ :
0b0010111010 :
(bit[1]) _ as instr) =
  Prtyd (RS,RA)

function clause execute (Prtyd (RS, RA)) =
  {
    s := 0;
    foreach (i from 0 to 7 by 1 in inc) s := s ^ (GPR[RS])[i * 8 + 7];
    GPR[RA] :=
      0b000000000000000000000000000000000000000000000000000000000000000 : [s]
  }

union ast member (bit[5], bit[5]) Prtyw

function clause decode (0b011111 :
(bit[5]) RS :
(bit[5]) RA :
(bit[5]) _ :
0b0010011010 :
(bit[1]) _ as instr) =
  Prtyw (RS,RA)

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
  Extsw (RS,RA,Rc)

function clause execute (Extsw (RS, RA, Rc)) =
  {
    s := (GPR[RS])[32];
    (bit[64]) temp := 0;
    temp[32..63] := (GPR[RS])[32 .. 63];
    temp[0..31] := s ^^ 32;
    if Rc then set_overflow_cr0 (temp,XER.SO) else ();
    GPR[RA] := temp
  }

union ast member (bit[5], bit[5], bit) Cntlzd

function clause decode (0b011111 :
(bit[5]) RS :
(bit[5]) RA :
(bit[5]) _ :
0b0000111010 :
[Rc] as instr) =
  Cntlzd (RS,RA,Rc)

function clause execute (Cntlzd (RS, RA, Rc)) =
  {
    temp := (bit[64]) (countLeadingZeroes (GPR[RS],0));
    GPR[RA] := temp;
    if Rc then set_overflow_cr0 (temp,XER.SO) else ()
  }

union ast member (bit[5], bit[5]) Popcntd

function clause decode (0b011111 :
(bit[5]) RS :
(bit[5]) RA :
(bit[5]) _ :
0b0111111010 :
(bit[1]) _ as instr) =
  Popcntd (RS,RA)

function clause execute (Popcntd (RS, RA)) =
  {
    ([|64|]) n := 0;
    foreach (i from 0 to 63 by 1 in inc)
    if (GPR[RS])[i] == 1 then n := n + 1 else ();
    GPR[RA] := (bit[64]) n
  }

union ast member (bit[5], bit[5], bit[5]) Bpermd

function clause decode (0b011111 :
(bit[5]) RS :
(bit[5]) RA :
(bit[5]) RB :
0b0011111100 :
(bit[1]) _ as instr) =
  Bpermd (RS,RA,RB)

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
    GPR[RA] :=
      0b00000000000000000000000000000000000000000000000000000000 : perm[0 .. 7]
  }

union ast member (bit[5], bit[5], bit[5], bit[5], bit[5], bit) Rlwinm

function clause decode (0b010101 :
(bit[5]) RS :
(bit[5]) RA :
(bit[5]) SH :
(bit[5]) MB :
(bit[5]) ME :
[Rc] as instr) =
  Rlwinm (RS,RA,SH,MB,ME,Rc)

function clause execute (Rlwinm (RS, RA, SH, MB, ME, Rc)) =
  {
    n := SH;
    r := ROTL ((GPR[RS])[32 .. 63] : (GPR[RS])[32 .. 63],n);
    m := MASK (MB + 32,ME + 32);
    (bit[64]) temp := (r & m);
    GPR[RA] := temp;
    if Rc then set_overflow_cr0 (temp,XER.SO) else ()
  }

union ast member (bit[5], bit[5], bit[5], bit[5], bit[5], bit) Rlwnm

function clause decode (0b010111 :
(bit[5]) RS :
(bit[5]) RA :
(bit[5]) RB :
(bit[5]) MB :
(bit[5]) ME :
[Rc] as instr) =
  Rlwnm (RS,RA,RB,MB,ME,Rc)

function clause execute (Rlwnm (RS, RA, RB, MB, ME, Rc)) =
  {
    n := (GPR[RB])[59 .. 63];
    r := ROTL ((GPR[RS])[32 .. 63] : (GPR[RS])[32 .. 63],n);
    m := MASK (MB + 32,ME + 32);
    (bit[64]) temp := (r & m);
    GPR[RA] := temp;
    if Rc then set_overflow_cr0 (temp,XER.SO) else ()
  }

union ast member (bit[5], bit[5], bit[5], bit[5], bit[5], bit) Rlwimi

function clause decode (0b010100 :
(bit[5]) RS :
(bit[5]) RA :
(bit[5]) SH :
(bit[5]) MB :
(bit[5]) ME :
[Rc] as instr) =
  Rlwimi (RS,RA,SH,MB,ME,Rc)

function clause execute (Rlwimi (RS, RA, SH, MB, ME, Rc)) =
  {
    n := SH;
    r := ROTL ((GPR[RS])[32 .. 63] : (GPR[RS])[32 .. 63],n);
    m := MASK (MB + 32,ME + 32);
    (bit[64]) temp := (r & m | GPR[RA] & ~ (m));
    GPR[RA] := temp;
    if Rc then set_overflow_cr0 (temp,XER.SO) else ()
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
  Rldicl (RS,RA,instr[16 .. 20] : instr[30 .. 30],mb,Rc)

function clause execute (Rldicl (RS, RA, sh, mb, Rc)) =
  {
    n := [sh[5]] : sh[0 .. 4];
    r := ROTL (GPR[RS],n);
    b := [mb[5]] : mb[0 .. 4];
    m := MASK (b,63);
    (bit[64]) temp := (r & m);
    GPR[RA] := temp;
    if Rc then set_overflow_cr0 (temp,XER.SO) else ()
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
  Rldicr (RS,RA,instr[16 .. 20] : instr[30 .. 30],me,Rc)

function clause execute (Rldicr (RS, RA, sh, me, Rc)) =
  {
    n := [sh[5]] : sh[0 .. 4];
    r := ROTL (GPR[RS],n);
    e := [me[5]] : me[0 .. 4];
    m := MASK (0,e);
    (bit[64]) temp := (r & m);
    GPR[RA] := temp;
    if Rc then set_overflow_cr0 (temp,XER.SO) else ()
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
  Rldic (RS,RA,instr[16 .. 20] : instr[30 .. 30],mb,Rc)

function clause execute (Rldic (RS, RA, sh, mb, Rc)) =
  {
    n := [sh[5]] : sh[0 .. 4];
    r := ROTL (GPR[RS],n);
    b := [mb[5]] : mb[0 .. 4];
    m := MASK (b,(bit[6]) (~ (n)));
    (bit[64]) temp := (r & m);
    GPR[RA] := temp;
    if Rc then set_overflow_cr0 (temp,XER.SO) else ()
  }

union ast member (bit[5], bit[5], bit[5], bit[6], bit) Rldcl

function clause decode (0b011110 :
(bit[5]) RS :
(bit[5]) RA :
(bit[5]) RB :
(bit[6]) mb :
0b1000 :
[Rc] as instr) =
  Rldcl (RS,RA,RB,mb,Rc)

function clause execute (Rldcl (RS, RA, RB, mb, Rc)) =
  {
    n := (GPR[RB])[58 .. 63];
    r := ROTL (GPR[RS],n);
    b := [mb[5]] : mb[0 .. 4];
    m := MASK (b,63);
    (bit[64]) temp := (r & m);
    GPR[RA] := temp;
    if Rc then set_overflow_cr0 (temp,XER.SO) else ()
  }

union ast member (bit[5], bit[5], bit[5], bit[6], bit) Rldcr

function clause decode (0b011110 :
(bit[5]) RS :
(bit[5]) RA :
(bit[5]) RB :
(bit[6]) me :
0b1001 :
[Rc] as instr) =
  Rldcr (RS,RA,RB,me,Rc)

function clause execute (Rldcr (RS, RA, RB, me, Rc)) =
  {
    n := (GPR[RB])[58 .. 63];
    r := ROTL (GPR[RS],n);
    e := [me[5]] : me[0 .. 4];
    m := MASK (0,e);
    (bit[64]) temp := (r & m);
    GPR[RA] := temp;
    if Rc then set_overflow_cr0 (temp,XER.SO) else ()
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
  Rldimi (RS,RA,instr[16 .. 20] : instr[30 .. 30],mb,Rc)

function clause execute (Rldimi (RS, RA, sh, mb, Rc)) =
  {
    n := [sh[5]] : sh[0 .. 4];
    r := ROTL (GPR[RS],n);
    b := [mb[5]] : mb[0 .. 4];
    m := MASK (b,(bit[6]) (~ (n)));
    (bit[64]) temp := (r & m | GPR[RA] & ~ (m));
    GPR[RA] := temp;
    if Rc then set_overflow_cr0 (temp,XER.SO) else ()
  }

union ast member (bit[5], bit[5], bit[5], bit) Slw

function clause decode (0b011111 :
(bit[5]) RS :
(bit[5]) RA :
(bit[5]) RB :
0b0000011000 :
[Rc] as instr) =
  Slw (RS,RA,RB,Rc)

function clause execute (Slw (RS, RA, RB, Rc)) =
  {
    n := (GPR[RB])[59 .. 63];
    r := ROTL ((GPR[RS])[32 .. 63] : (GPR[RS])[32 .. 63],n);
    if (GPR[RB])[58] == 0
    then m := MASK (32,63 - n)
    else m := 0b0000000000000000000000000000000000000000000000000000000000000000;
    (bit[64]) temp := (r & m);
    GPR[RA] := temp;
    if Rc then set_overflow_cr0 (temp,XER.SO) else ()
  }

union ast member (bit[5], bit[5], bit[5], bit) Srw

function clause decode (0b011111 :
(bit[5]) RS :
(bit[5]) RA :
(bit[5]) RB :
0b1000011000 :
[Rc] as instr) =
  Srw (RS,RA,RB,Rc)

function clause execute (Srw (RS, RA, RB, Rc)) =
  {
    n := (GPR[RB])[59 .. 63];
    r := ROTL ((GPR[RS])[32 .. 63] : (GPR[RS])[32 .. 63],64 - n);
    if (GPR[RB])[58] == 0
    then m := MASK (n + 32,63)
    else m := 0b0000000000000000000000000000000000000000000000000000000000000000;
    (bit[64]) temp := (r & m);
    GPR[RA] := temp;
    if Rc then set_overflow_cr0 (temp,XER.SO) else ()
  }

union ast member (bit[5], bit[5], bit[5], bit) Srawi

function clause decode (0b011111 :
(bit[5]) RS :
(bit[5]) RA :
(bit[5]) SH :
0b1100111000 :
[Rc] as instr) =
  Srawi (RS,RA,SH,Rc)

function clause execute (Srawi (RS, RA, SH, Rc)) =
  {
    n := SH;
    r := ROTL ((GPR[RS])[32 .. 63] : (GPR[RS])[32 .. 63],64 - n);
    m := MASK (n + 32,63);
    s := (GPR[RS])[32];
    (bit[64]) temp := (r & m | s ^^ 64 & ~ (m));
    GPR[RA] := temp;
    if Rc then set_overflow_cr0 (temp,XER.SO) else ();
    XER.CA := if n >_u (bit[5]) 0 then s & ~ ((r & ~ (m)) == 0) else 0
  }

union ast member (bit[5], bit[5], bit[5], bit) Sraw

function clause decode (0b011111 :
(bit[5]) RS :
(bit[5]) RA :
(bit[5]) RB :
0b1100011000 :
[Rc] as instr) =
  Sraw (RS,RA,RB,Rc)

function clause execute (Sraw (RS, RA, RB, Rc)) =
  {
    n := (GPR[RB])[59 .. 63];
    r := ROTL ((GPR[RS])[32 .. 63] : (GPR[RS])[32 .. 63],64 - n);
    if (GPR[RB])[58] == 0
    then m := MASK (n + 32,63)
    else m := 0b0000000000000000000000000000000000000000000000000000000000000000;
    s := (GPR[RS])[32];
    (bit[64]) temp := (r & m | s ^^ 64 & ~ (m));
    GPR[RA] := temp;
    if Rc then set_overflow_cr0 (temp,XER.SO) else ();
    XER.CA := if n >_u (bit[5]) 0 then s & ~ ((r & ~ (m)) == 0) else 0
  }

union ast member (bit[5], bit[5], bit[5], bit) Sld

function clause decode (0b011111 :
(bit[5]) RS :
(bit[5]) RA :
(bit[5]) RB :
0b0000011011 :
[Rc] as instr) =
  Sld (RS,RA,RB,Rc)

function clause execute (Sld (RS, RA, RB, Rc)) =
  {
    n := (GPR[RB])[58 .. 63];
    r := ROTL (GPR[RS],n);
    if (GPR[RB])[57] == 0
    then m := MASK (0,63 - n)
    else m := 0b0000000000000000000000000000000000000000000000000000000000000000;
    (bit[64]) temp := (r & m);
    GPR[RA] := temp;
    if Rc then set_overflow_cr0 (temp,XER.SO) else ()
  }

union ast member (bit[5], bit[5], bit[5], bit) Srd

function clause decode (0b011111 :
(bit[5]) RS :
(bit[5]) RA :
(bit[5]) RB :
0b1000011011 :
[Rc] as instr) =
  Srd (RS,RA,RB,Rc)

function clause execute (Srd (RS, RA, RB, Rc)) =
  {
    n := (GPR[RB])[58 .. 63];
    r := ROTL (GPR[RS],64 - n);
    if (GPR[RB])[57] == 0
    then m := MASK (n,63)
    else m := 0b0000000000000000000000000000000000000000000000000000000000000000;
    (bit[64]) temp := (r & m);
    GPR[RA] := temp;
    if Rc then set_overflow_cr0 (temp,XER.SO) else ()
  }

union ast member (bit[5], bit[5], bit[6], bit) Sradi

function clause decode (0b011111 :
(bit[5]) RS :
(bit[5]) RA :
(bit[5]) _ :
0b110011101 :
(bit[1]) _ :
[Rc] as instr) =
  Sradi (RS,RA,instr[16 .. 20] : instr[30 .. 30],Rc)

function clause execute (Sradi (RS, RA, sh, Rc)) =
  {
    n := [sh[5]] : sh[0 .. 4];
    r := ROTL (GPR[RS],64 - n);
    m := MASK (n,63);
    s := (GPR[RS])[0];
    (bit[64]) temp := (r & m | s ^^ 64 & ~ (m));
    GPR[RA] := temp;
    if Rc then set_overflow_cr0 (temp,XER.SO) else ();
    XER.CA := if n >_u (bit[6]) 0 then s & ~ ((r & ~ (m)) == 0) else 0
  }

union ast member (bit[5], bit[5], bit[5], bit) Srad

function clause decode (0b011111 :
(bit[5]) RS :
(bit[5]) RA :
(bit[5]) RB :
0b1100011010 :
[Rc] as instr) =
  Srad (RS,RA,RB,Rc)

function clause execute (Srad (RS, RA, RB, Rc)) =
  {
    n := (GPR[RB])[58 .. 63];
    r := ROTL (GPR[RS],64 - n);
    if (GPR[RB])[57] == 0
    then m := MASK (n,63)
    else m := 0b0000000000000000000000000000000000000000000000000000000000000000;
    s := (GPR[RS])[0];
    (bit[64]) temp := (r & m | s ^^ 64 & ~ (m));
    GPR[RA] := temp;
    if Rc then set_overflow_cr0 (temp,XER.SO) else ();
    XER.CA := if n >_u (bit[6]) 0 then s & ~ ((r & ~ (m)) == 0) else 0
  }

union ast member (bit[5], bit[5]) Cdtbcd

function clause decode (0b011111 :
(bit[5]) RS :
(bit[5]) RA :
(bit[5]) _ :
0b0100011010 :
(bit[1]) _ as instr) =
  Cdtbcd (RS,RA)

function clause execute (Cdtbcd (RS, RA)) =
  foreach (i from 0 to 1 by 1 in inc)
  {
    n := i * 32;
    (GPR[RA])[n + 0..n + 7] := (bit[8]) 0;
    (GPR[RA])[n + 8..n + 19] := DEC_TO_BCD ((GPR[RS])[n + 12 .. n + 21]);
    (GPR[RA])[n + 20..n + 31] := DEC_TO_BCD ((GPR[RS])[n + 22 .. n + 31])
  }

union ast member (bit[5], bit[5]) Cbcdtd

function clause decode (0b011111 :
(bit[5]) RS :
(bit[5]) RA :
(bit[5]) _ :
0b0100111010 :
(bit[1]) _ as instr) =
  Cbcdtd (RS,RA)

function clause execute (Cbcdtd (RS, RA)) =
  foreach (i from 0 to 1 by 1 in inc)
  {
    n := i * 32;
    (GPR[RA])[n + 0..n + 11] := (bit[12]) 0;
    (GPR[RA])[n + 12..n + 21] := BCD_TO_DEC ((GPR[RS])[n + 8 .. n + 19]);
    (GPR[RA])[n + 22..n + 31] := BCD_TO_DEC ((GPR[RS])[n + 20 .. n + 31])
  }

union ast member (bit[5], bit[5], bit[5]) Addg6s

function clause decode (0b011111 :
(bit[5]) RT :
(bit[5]) RA :
(bit[5]) RB :
(bit[1]) _ :
0b001001010 :
(bit[1]) _ as instr) =
  Addg6s (RT,RA,RB)

function clause execute (Addg6s (RT, RA, RB)) =
  {
    (bit[16]) dc := 0;
    foreach (i from 0 to 15 by 1 in inc)
    let (v, _, co) = ((GPR[RA])[4 * i .. 63] + (GPR[RB])[4 * i .. 63]) in
      dc[i] := carry_out (v,co);
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
                              (dc[12] ^^ 4) :
                                (dc[13] ^^ 4) : (dc[14] ^^ 4) : (dc[15] ^^ 4);
    GPR[RT] :=
      (~ (c) &
        0b0110011001100110011001100110011001100110011001100110011001100110)
  }

union ast member (bit[5], bit[10]) Mtspr

function clause decode (0b011111 :
(bit[5]) RS :
(bit[10]) spr :
0b0111010011 :
(bit[1]) _ as instr) =
  Mtspr (RS,spr)

function clause execute (Mtspr (RS, spr)) =
  {
    n := spr[5 .. 9] : spr[0 .. 4];
    if n == 13
    then trap (())
    else if n == 1
    then {
      (bit[64]) reg := GPR[RS];
      (bit[32]) front := zero_or_undef (reg[0 .. 31]);
      (bit) xer_so := reg[32];
      (bit) xer_ov := reg[33];
      (bit) xer_ca := reg[34];
      (bit[22]) mid := zero_or_undef (reg[35 .. 56]);
      (bit[7]) bot := reg[57 .. 63];
      XER := front : [xer_so] : [xer_ov] : [xer_ca] : mid : bot
    }
    else if length (SPR[n]) == 64
    then SPR[n] := GPR[RS]
    else SPR[n] := ((bit[32]) 0):(GPR[RS])[32 .. 63]
  }

union ast member (bit[5], bit[10]) Mfspr

function clause decode (0b011111 :
(bit[5]) RT :
(bit[10]) spr :
0b0101010011 :
(bit[1]) _ as instr) =
  Mfspr (RT,spr)

function clause execute (Mfspr (RT, spr)) =
  {
    n := spr[5 .. 9] : spr[0 .. 4];
    if length (SPR[n]) == 64
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
  Mtcrf (RS,FXM)

function clause execute (Mtcrf (RS, FXM)) =
  {
    mask :=
      (FXM[0] ^^ 4) :
        (FXM[1] ^^ 4) :
          (FXM[2] ^^ 4) :
            (FXM[3] ^^ 4) :
              (FXM[4] ^^ 4) : (FXM[5] ^^ 4) : (FXM[6] ^^ 4) : (FXM[7] ^^ 4);
    CR :=
      ((bit[32]) ((GPR[RS])[32 .. 63] & mask) |
        (bit[32]) (CR & ~ ((bit[32]) mask)))
  }

union ast member (bit[5]) Mfcr

function clause decode (0b011111 :
(bit[5]) RT :
0b0 :
(bit[9]) _ :
0b0000010011 :
(bit[1]) _ as instr) =
  Mfcr (RT)

function clause execute (Mfcr (RT)) =
  GPR[RT] := 0b00000000000000000000000000000000 : CR

union ast member (bit[5], bit[8]) Mtocrf

function clause decode (0b011111 :
(bit[5]) RS :
0b1 :
(bit[8]) FXM :
(bit[1]) _ :
0b0010010000 :
(bit[1]) _ as instr) =
  Mtocrf (RS,FXM)

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
  Mfocrf (RT,FXM)

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
  Mcrxr (BF)

function clause execute (Mcrxr (BF)) =
  {
    CR[4 * BF + 32..4 * BF + 35] := XER[32 .. 35];
    XER[32..35] := 0b0000
  }

union ast member (bit[5], bit[5]) Mtdcrux

function clause decode (0b011111 :
(bit[5]) RS :
(bit[5]) RA :
(bit[5]) _ :
0b0110100011 :
(bit[1]) _ as instr) =
  Mtdcrux (RS,RA)

function clause execute (Mtdcrux (RS, RA)) =
  {
    DCRN := GPR[RA];
    DCR[DCRN] := GPR[RS]
  }

union ast member (bit[5], bit[5]) Mfdcrux

function clause decode (0b011111 :
(bit[5]) RT :
(bit[5]) RA :
(bit[5]) _ :
0b0100100011 :
(bit[1]) _ as instr) =
  Mfdcrux (RT,RA)

function clause execute (Mfdcrux (RT, RA)) =
  {
    DCRN := GPR[RA];
    GPR[RT] := DCR[DCRN]
  }

union ast member (bit[5], bit[5], bit[16]) Lfs

function clause decode (0b110000 :
(bit[5]) FRT :
(bit[5]) RA :
(bit[16]) D as instr) =
  Lfs (FRT,RA,D)

function clause execute (Lfs (FRT, RA, D)) =
  {
    (bit[64]) b := 0;
    (bit[64]) EA := 0;
    if RA == 0 then b := 0 else b := GPR[RA];
    EA := b + EXTS (D);
    FPR[FRT] := DOUBLE (MEMr (EA,4))
  }

union ast member (bit[5], bit[5], bit[5]) Lfsx

function clause decode (0b011111 :
(bit[5]) FRT :
(bit[5]) RA :
(bit[5]) RB :
0b1000010111 :
(bit[1]) _ as instr) =
  Lfsx (FRT,RA,RB)

function clause execute (Lfsx (FRT, RA, RB)) =
  {
    (bit[64]) b := 0;
    (bit[64]) EA := 0;
    if RA == 0 then b := 0 else b := GPR[RA];
    EA := b + GPR[RB];
    FPR[FRT] := DOUBLE (MEMr (EA,4))
  }

union ast member (bit[5], bit[5], bit[16]) Lfsu

function clause decode (0b110001 :
(bit[5]) FRT :
(bit[5]) RA :
(bit[16]) D as instr) =
  Lfsu (FRT,RA,D)

function clause execute (Lfsu (FRT, RA, D)) =
  {
    (bit[64]) EA := 0;
    EA := GPR[RA] + EXTS (D);
    FPR[FRT] := DOUBLE (MEMr (EA,4));
    GPR[RA] := EA
  }

union ast member (bit[5], bit[5], bit[5]) Lfsux

function clause decode (0b011111 :
(bit[5]) FRT :
(bit[5]) RA :
(bit[5]) RB :
0b1000110111 :
(bit[1]) _ as instr) =
  Lfsux (FRT,RA,RB)

function clause execute (Lfsux (FRT, RA, RB)) =
  {
    (bit[64]) EA := 0;
    EA := GPR[RA] + GPR[RB];
    FPR[FRT] := DOUBLE (MEMr (EA,4));
    GPR[RA] := EA
  }

union ast member (bit[5], bit[5], bit[16]) Lfd

function clause decode (0b110010 :
(bit[5]) FRT :
(bit[5]) RA :
(bit[16]) D as instr) =
  Lfd (FRT,RA,D)

function clause execute (Lfd (FRT, RA, D)) =
  {
    (bit[64]) b := 0;
    (bit[64]) EA := 0;
    if RA == 0 then b := 0 else b := GPR[RA];
    EA := b + EXTS (D);
    FPR[FRT] := MEMr (EA,8)
  }

union ast member (bit[5], bit[5], bit[5]) Lfdx

function clause decode (0b011111 :
(bit[5]) FRT :
(bit[5]) RA :
(bit[5]) RB :
0b1001010111 :
(bit[1]) _ as instr) =
  Lfdx (FRT,RA,RB)

function clause execute (Lfdx (FRT, RA, RB)) =
  {
    (bit[64]) b := 0;
    (bit[64]) EA := 0;
    if RA == 0 then b := 0 else b := GPR[RA];
    EA := b + GPR[RB];
    FPR[FRT] := MEMr (EA,8)
  }

union ast member (bit[5], bit[5], bit[16]) Lfdu

function clause decode (0b110011 :
(bit[5]) FRT :
(bit[5]) RA :
(bit[16]) D as instr) =
  Lfdu (FRT,RA,D)

function clause execute (Lfdu (FRT, RA, D)) =
  {
    (bit[64]) EA := 0;
    EA := GPR[RA] + EXTS (D);
    FPR[FRT] := MEMr (EA,8);
    GPR[RA] := EA
  }

union ast member (bit[5], bit[5], bit[5]) Lfdux

function clause decode (0b011111 :
(bit[5]) FRT :
(bit[5]) RA :
(bit[5]) RB :
0b1001110111 :
(bit[1]) _ as instr) =
  Lfdux (FRT,RA,RB)

function clause execute (Lfdux (FRT, RA, RB)) =
  {
    (bit[64]) EA := 0;
    EA := GPR[RA] + GPR[RB];
    FPR[FRT] := MEMr (EA,8);
    GPR[RA] := EA
  }

union ast member (bit[5], bit[5], bit[5]) Lfiwax

function clause decode (0b011111 :
(bit[5]) FRT :
(bit[5]) RA :
(bit[5]) RB :
0b1101010111 :
(bit[1]) _ as instr) =
  Lfiwax (FRT,RA,RB)

function clause execute (Lfiwax (FRT, RA, RB)) =
  {
    (bit[64]) b := 0;
    (bit[64]) EA := 0;
    if RA == 0 then b := 0 else b := GPR[RA];
    EA := b + GPR[RB];
    FPR[FRT] := EXTS (MEMr (EA,4))
  }

union ast member (bit[5], bit[5], bit[5]) Lfiwzx

function clause decode (0b011111 :
(bit[5]) FRT :
(bit[5]) RA :
(bit[5]) RB :
0b1101110111 :
(bit[1]) _ as instr) =
  Lfiwzx (FRT,RA,RB)

function clause execute (Lfiwzx (FRT, RA, RB)) =
  {
    (bit[64]) b := 0;
    (bit[64]) EA := 0;
    if RA == 0 then b := 0 else b := GPR[RA];
    EA := b + GPR[RB];
    FPR[FRT] := 0b00000000000000000000000000000000 : MEMr (EA,4)
  }

union ast member (bit[5], bit[5], bit[16]) Stfs

function clause decode (0b110100 :
(bit[5]) FRS :
(bit[5]) RA :
(bit[16]) D as instr) =
  Stfs (FRS,RA,D)

function clause execute (Stfs (FRS, RA, D)) =
  {
    (bit[64]) b := 0;
    (bit[64]) EA := 0;
    if RA == 0 then b := 0 else b := GPR[RA];
    EA := b + EXTS (D);
    MEMw(EA,4) := SINGLE (FPR[FRS])
  }

union ast member (bit[5], bit[5], bit[5]) Stfsx

function clause decode (0b011111 :
(bit[5]) FRS :
(bit[5]) RA :
(bit[5]) RB :
0b1010010111 :
(bit[1]) _ as instr) =
  Stfsx (FRS,RA,RB)

function clause execute (Stfsx (FRS, RA, RB)) =
  {
    (bit[64]) b := 0;
    (bit[64]) EA := 0;
    if RA == 0 then b := 0 else b := GPR[RA];
    EA := b + GPR[RB];
    MEMw(EA,4) := SINGLE (FPR[FRS])
  }

union ast member (bit[5], bit[5], bit[16]) Stfsu

function clause decode (0b110101 :
(bit[5]) FRS :
(bit[5]) RA :
(bit[16]) D as instr) =
  Stfsu (FRS,RA,D)

function clause execute (Stfsu (FRS, RA, D)) =
  {
    (bit[64]) EA := 0;
    EA := GPR[RA] + EXTS (D);
    MEMw(EA,4) := SINGLE (FPR[FRS]);
    GPR[RA] := EA
  }

union ast member (bit[5], bit[5], bit[5]) Stfsux

function clause decode (0b011111 :
(bit[5]) FRS :
(bit[5]) RA :
(bit[5]) RB :
0b1010110111 :
(bit[1]) _ as instr) =
  Stfsux (FRS,RA,RB)

function clause execute (Stfsux (FRS, RA, RB)) =
  {
    (bit[64]) EA := 0;
    EA := GPR[RA] + GPR[RB];
    MEMw(EA,4) := SINGLE (FPR[FRS]);
    GPR[RA] := EA
  }

union ast member (bit[5], bit[5], bit[16]) Stfd

function clause decode (0b110110 :
(bit[5]) FRS :
(bit[5]) RA :
(bit[16]) D as instr) =
  Stfd (FRS,RA,D)

function clause execute (Stfd (FRS, RA, D)) =
  {
    (bit[64]) b := 0;
    (bit[64]) EA := 0;
    if RA == 0 then b := 0 else b := GPR[RA];
    EA := b + EXTS (D);
    MEMw(EA,8) := FPR[FRS]
  }

union ast member (bit[5], bit[5], bit[5]) Stfdx

function clause decode (0b011111 :
(bit[5]) FRS :
(bit[5]) RA :
(bit[5]) RB :
0b1011010111 :
(bit[1]) _ as instr) =
  Stfdx (FRS,RA,RB)

function clause execute (Stfdx (FRS, RA, RB)) =
  {
    (bit[64]) b := 0;
    (bit[64]) EA := 0;
    if RA == 0 then b := 0 else b := GPR[RA];
    EA := b + GPR[RB];
    MEMw(EA,8) := FPR[FRS]
  }

union ast member (bit[5], bit[5], bit[16]) Stfdu

function clause decode (0b110111 :
(bit[5]) FRS :
(bit[5]) RA :
(bit[16]) D as instr) =
  Stfdu (FRS,RA,D)

function clause execute (Stfdu (FRS, RA, D)) =
  {
    (bit[64]) EA := 0;
    EA := GPR[RA] + EXTS (D);
    MEMw(EA,8) := FPR[FRS];
    GPR[RA] := EA
  }

union ast member (bit[5], bit[5], bit[5]) Stfdux

function clause decode (0b011111 :
(bit[5]) FRS :
(bit[5]) RA :
(bit[5]) RB :
0b1011110111 :
(bit[1]) _ as instr) =
  Stfdux (FRS,RA,RB)

function clause execute (Stfdux (FRS, RA, RB)) =
  {
    (bit[64]) EA := 0;
    EA := GPR[RA] + GPR[RB];
    MEMw(EA,8) := FPR[FRS];
    GPR[RA] := EA
  }

union ast member (bit[5], bit[5], bit[5]) Stfiwx

function clause decode (0b011111 :
(bit[5]) FRS :
(bit[5]) RA :
(bit[5]) RB :
0b1111010111 :
(bit[1]) _ as instr) =
  Stfiwx (FRS,RA,RB)

function clause execute (Stfiwx (FRS, RA, RB)) =
  {
    (bit[64]) b := 0;
    (bit[64]) EA := 0;
    if RA == 0 then b := 0 else b := GPR[RA];
    EA := b + GPR[RB];
    MEMw(EA,4) := (FPR[FRS])[32 .. 63]
  }

union ast member (bit[5], bit[5], bit[14]) Lfdp

function clause decode (0b111001 :
(bit[5]) FRTp :
(bit[5]) RA :
(bit[14]) DS :
0b0 :
0b0 as instr) =
  Lfdp (FRTp,RA,DS)

function clause execute (Lfdp (FRTp, RA, DS)) =
  {
    (bit[64]) b := 0;
    (bit[64]) EA := 0;
    if RA == 0 then b := 0 else b := GPR[RA];
    EA := b + EXTS (DS : 0b00);
    FPRp[FRTp] := MEMr (EA,16)
  }

union ast member (bit[5], bit[5], bit[5]) Lfdpx

function clause decode (0b011111 :
(bit[5]) FRTp :
(bit[5]) RA :
(bit[5]) RB :
0b1100010111 :
(bit[1]) _ as instr) =
  Lfdpx (FRTp,RA,RB)

function clause execute (Lfdpx (FRTp, RA, RB)) =
  {
    (bit[64]) b := 0;
    (bit[64]) EA := 0;
    if RA == 0 then b := 0 else b := GPR[RA];
    EA := b + GPR[RB];
    FPRp[FRTp] := MEMr (EA,16)
  }

union ast member (bit[5], bit[5], bit[14]) Stfdp

function clause decode (0b111101 :
(bit[5]) FRSp :
(bit[5]) RA :
(bit[14]) DS :
0b0 :
0b0 as instr) =
  Stfdp (FRSp,RA,DS)

function clause execute (Stfdp (FRSp, RA, DS)) =
  {
    (bit[64]) b := 0;
    (bit[64]) EA := 0;
    if RA == 0 then b := 0 else b := GPR[RA];
    EA := b + EXTS (DS : 0b00);
    MEMw(EA,16) := FPRp[FRSp]
  }

union ast member (bit[5], bit[5], bit[5]) Stfdpx

function clause decode (0b011111 :
(bit[5]) FRSp :
(bit[5]) RA :
(bit[5]) RB :
0b1110010111 :
(bit[1]) _ as instr) =
  Stfdpx (FRSp,RA,RB)

function clause execute (Stfdpx (FRSp, RA, RB)) =
  {
    (bit[64]) b := 0;
    (bit[64]) EA := 0;
    if RA == 0 then b := 0 else b := GPR[RA];
    EA := b + GPR[RB];
    MEMw(EA,16) := FPRp[FRSp]
  }

union ast member (bit[5], bit[5], bit) Fmr

function clause decode (0b111111 :
(bit[5]) FRT :
(bit[5]) _ :
(bit[5]) FRB :
0b0001001000 :
[Rc] as instr) =
  Fmr (FRT,FRB,Rc)

function clause execute (Fmr (FRT, FRB, Rc)) = ()

union ast member (bit[5], bit[5], bit) Fneg

function clause decode (0b111111 :
(bit[5]) FRT :
(bit[5]) _ :
(bit[5]) FRB :
0b0000101000 :
[Rc] as instr) =
  Fneg (FRT,FRB,Rc)

function clause execute (Fneg (FRT, FRB, Rc)) = ()

union ast member (bit[5], bit[5], bit) Fabs

function clause decode (0b111111 :
(bit[5]) FRT :
(bit[5]) _ :
(bit[5]) FRB :
0b0100001000 :
[Rc] as instr) =
  Fabs (FRT,FRB,Rc)

function clause execute (Fabs (FRT, FRB, Rc)) = ()

union ast member (bit[5], bit[5], bit) Fnabs

function clause decode (0b111111 :
(bit[5]) FRT :
(bit[5]) _ :
(bit[5]) FRB :
0b0010001000 :
[Rc] as instr) =
  Fnabs (FRT,FRB,Rc)

function clause execute (Fnabs (FRT, FRB, Rc)) = ()

union ast member (bit[5], bit[5], bit[5], bit) Fcpsgn

function clause decode (0b111111 :
(bit[5]) FRT :
(bit[5]) FRA :
(bit[5]) FRB :
0b0000001000 :
[Rc] as instr) =
  Fcpsgn (FRT,FRA,FRB,Rc)

function clause execute (Fcpsgn (FRT, FRA, FRB, Rc)) = ()

union ast member (bit[5], bit[5], bit[5], bit) Fadds

function clause decode (0b111011 :
(bit[5]) FRT :
(bit[5]) FRA :
(bit[5]) FRB :
(bit[5]) _ :
0b10101 :
[Rc] as instr) =
  Fadds (FRT,FRA,FRB,Rc)

function clause execute (Fadds (FRT, FRA, FRB, Rc)) = ()

union ast member (bit[5], bit[5], bit[5], bit) Fadd

function clause decode (0b111111 :
(bit[5]) FRT :
(bit[5]) FRA :
(bit[5]) FRB :
(bit[5]) _ :
0b10101 :
[Rc] as instr) =
  Fadd (FRT,FRA,FRB,Rc)

function clause execute (Fadd (FRT, FRA, FRB, Rc)) = ()

union ast member (bit[5], bit[5], bit[5], bit) Fsubs

function clause decode (0b111011 :
(bit[5]) FRT :
(bit[5]) FRA :
(bit[5]) FRB :
(bit[5]) _ :
0b10100 :
[Rc] as instr) =
  Fsubs (FRT,FRA,FRB,Rc)

function clause execute (Fsubs (FRT, FRA, FRB, Rc)) = ()

union ast member (bit[5], bit[5], bit[5], bit) Fsub

function clause decode (0b111111 :
(bit[5]) FRT :
(bit[5]) FRA :
(bit[5]) FRB :
(bit[5]) _ :
0b10100 :
[Rc] as instr) =
  Fsub (FRT,FRA,FRB,Rc)

function clause execute (Fsub (FRT, FRA, FRB, Rc)) = ()

union ast member (bit[5], bit[5], bit[5], bit) Fmuls

function clause decode (0b111011 :
(bit[5]) FRT :
(bit[5]) FRA :
(bit[5]) _ :
(bit[5]) FRC :
0b11001 :
[Rc] as instr) =
  Fmuls (FRT,FRA,FRC,Rc)

function clause execute (Fmuls (FRT, FRA, FRC, Rc)) = ()

union ast member (bit[5], bit[5], bit[5], bit) Fmul

function clause decode (0b111111 :
(bit[5]) FRT :
(bit[5]) FRA :
(bit[5]) _ :
(bit[5]) FRC :
0b11001 :
[Rc] as instr) =
  Fmul (FRT,FRA,FRC,Rc)

function clause execute (Fmul (FRT, FRA, FRC, Rc)) = ()

union ast member (bit[5], bit[5], bit[5], bit) Fdivs

function clause decode (0b111011 :
(bit[5]) FRT :
(bit[5]) FRA :
(bit[5]) FRB :
(bit[5]) _ :
0b10010 :
[Rc] as instr) =
  Fdivs (FRT,FRA,FRB,Rc)

function clause execute (Fdivs (FRT, FRA, FRB, Rc)) = ()

union ast member (bit[5], bit[5], bit[5], bit) Fdiv

function clause decode (0b111111 :
(bit[5]) FRT :
(bit[5]) FRA :
(bit[5]) FRB :
(bit[5]) _ :
0b10010 :
[Rc] as instr) =
  Fdiv (FRT,FRA,FRB,Rc)

function clause execute (Fdiv (FRT, FRA, FRB, Rc)) = ()

union ast member (bit[5], bit[5], bit) Fsqrts

function clause decode (0b111011 :
(bit[5]) FRT :
(bit[5]) _ :
(bit[5]) FRB :
(bit[5]) _ :
0b10110 :
[Rc] as instr) =
  Fsqrts (FRT,FRB,Rc)

function clause execute (Fsqrts (FRT, FRB, Rc)) = ()

union ast member (bit[5], bit[5], bit) Fsqrt

function clause decode (0b111111 :
(bit[5]) FRT :
(bit[5]) _ :
(bit[5]) FRB :
(bit[5]) _ :
0b10110 :
[Rc] as instr) =
  Fsqrt (FRT,FRB,Rc)

function clause execute (Fsqrt (FRT, FRB, Rc)) = ()

union ast member (bit[5], bit[5], bit) Fres

function clause decode (0b111011 :
(bit[5]) FRT :
(bit[5]) _ :
(bit[5]) FRB :
(bit[5]) _ :
0b11000 :
[Rc] as instr) =
  Fres (FRT,FRB,Rc)

function clause execute (Fres (FRT, FRB, Rc)) = ()

union ast member (bit[5], bit[5], bit) Fre

function clause decode (0b111111 :
(bit[5]) FRT :
(bit[5]) _ :
(bit[5]) FRB :
(bit[5]) _ :
0b11000 :
[Rc] as instr) =
  Fre (FRT,FRB,Rc)

function clause execute (Fre (FRT, FRB, Rc)) = ()

union ast member (bit[5], bit[5], bit) Frsqrtes

function clause decode (0b111011 :
(bit[5]) FRT :
(bit[5]) _ :
(bit[5]) FRB :
(bit[5]) _ :
0b11010 :
[Rc] as instr) =
  Frsqrtes (FRT,FRB,Rc)

function clause execute (Frsqrtes (FRT, FRB, Rc)) = ()

union ast member (bit[5], bit[5], bit) Frsqrte

function clause decode (0b111111 :
(bit[5]) FRT :
(bit[5]) _ :
(bit[5]) FRB :
(bit[5]) _ :
0b11010 :
[Rc] as instr) =
  Frsqrte (FRT,FRB,Rc)

function clause execute (Frsqrte (FRT, FRB, Rc)) = ()

union ast member (bit[3], bit[5], bit[5]) Ftdiv

function clause decode (0b111111 :
(bit[3]) BF :
(bit[2]) _ :
(bit[5]) FRA :
(bit[5]) FRB :
0b0010000000 :
(bit[1]) _ as instr) =
  Ftdiv (BF,FRA,FRB)

function clause execute (Ftdiv (BF, FRA, FRB)) = ()

union ast member (bit[3], bit[5]) Ftsqrt

function clause decode (0b111111 :
(bit[3]) BF :
(bit[2]) _ :
(bit[5]) _ :
(bit[5]) FRB :
0b0010100000 :
(bit[1]) _ as instr) =
  Ftsqrt (BF,FRB)

function clause execute (Ftsqrt (BF, FRB)) = ()

union ast member (bit[5], bit[5], bit[5], bit[5], bit) Fmadds

function clause decode (0b111011 :
(bit[5]) FRT :
(bit[5]) FRA :
(bit[5]) FRB :
(bit[5]) FRC :
0b11101 :
[Rc] as instr) =
  Fmadds (FRT,FRA,FRB,FRC,Rc)

function clause execute (Fmadds (FRT, FRA, FRB, FRC, Rc)) = ()

union ast member (bit[5], bit[5], bit[5], bit[5], bit) Fmadd

function clause decode (0b111111 :
(bit[5]) FRT :
(bit[5]) FRA :
(bit[5]) FRB :
(bit[5]) FRC :
0b11101 :
[Rc] as instr) =
  Fmadd (FRT,FRA,FRB,FRC,Rc)

function clause execute (Fmadd (FRT, FRA, FRB, FRC, Rc)) = ()

union ast member (bit[5], bit[5], bit[5], bit[5], bit) Fmsubs

function clause decode (0b111011 :
(bit[5]) FRT :
(bit[5]) FRA :
(bit[5]) FRB :
(bit[5]) FRC :
0b11100 :
[Rc] as instr) =
  Fmsubs (FRT,FRA,FRB,FRC,Rc)

function clause execute (Fmsubs (FRT, FRA, FRB, FRC, Rc)) = ()

union ast member (bit[5], bit[5], bit[5], bit[5], bit) Fmsub

function clause decode (0b111111 :
(bit[5]) FRT :
(bit[5]) FRA :
(bit[5]) FRB :
(bit[5]) FRC :
0b11100 :
[Rc] as instr) =
  Fmsub (FRT,FRA,FRB,FRC,Rc)

function clause execute (Fmsub (FRT, FRA, FRB, FRC, Rc)) = ()

union ast member (bit[5], bit[5], bit[5], bit[5], bit) Fnmadds

function clause decode (0b111011 :
(bit[5]) FRT :
(bit[5]) FRA :
(bit[5]) FRB :
(bit[5]) FRC :
0b11111 :
[Rc] as instr) =
  Fnmadds (FRT,FRA,FRB,FRC,Rc)

function clause execute (Fnmadds (FRT, FRA, FRB, FRC, Rc)) = ()

union ast member (bit[5], bit[5], bit[5], bit[5], bit) Fnmadd

function clause decode (0b111111 :
(bit[5]) FRT :
(bit[5]) FRA :
(bit[5]) FRB :
(bit[5]) FRC :
0b11111 :
[Rc] as instr) =
  Fnmadd (FRT,FRA,FRB,FRC,Rc)

function clause execute (Fnmadd (FRT, FRA, FRB, FRC, Rc)) = ()

union ast member (bit[5], bit[5], bit[5], bit[5], bit) Fnmsubs

function clause decode (0b111011 :
(bit[5]) FRT :
(bit[5]) FRA :
(bit[5]) FRB :
(bit[5]) FRC :
0b11110 :
[Rc] as instr) =
  Fnmsubs (FRT,FRA,FRB,FRC,Rc)

function clause execute (Fnmsubs (FRT, FRA, FRB, FRC, Rc)) = ()

union ast member (bit[5], bit[5], bit[5], bit[5], bit) Fnmsub

function clause decode (0b111111 :
(bit[5]) FRT :
(bit[5]) FRA :
(bit[5]) FRB :
(bit[5]) FRC :
0b11110 :
[Rc] as instr) =
  Fnmsub (FRT,FRA,FRB,FRC,Rc)

function clause execute (Fnmsub (FRT, FRA, FRB, FRC, Rc)) = ()

union ast member (bit[5], bit[5], bit) Frsp

function clause decode (0b111111 :
(bit[5]) FRT :
(bit[5]) _ :
(bit[5]) FRB :
0b0000001100 :
[Rc] as instr) =
  Frsp (FRT,FRB,Rc)

function clause execute (Frsp (FRT, FRB, Rc)) = ()

union ast member (bit[5], bit[5], bit) Fctid

function clause decode (0b111111 :
(bit[5]) FRT :
(bit[5]) _ :
(bit[5]) FRB :
0b1100101110 :
[Rc] as instr) =
  Fctid (FRT,FRB,Rc)

function clause execute (Fctid (FRT, FRB, Rc)) = ()

union ast member (bit[5], bit[5], bit) Fctidz

function clause decode (0b111111 :
(bit[5]) FRT :
(bit[5]) _ :
(bit[5]) FRB :
0b1100101111 :
[Rc] as instr) =
  Fctidz (FRT,FRB,Rc)

function clause execute (Fctidz (FRT, FRB, Rc)) = ()

union ast member (bit[5], bit[5], bit) Fctidu

function clause decode (0b111111 :
(bit[5]) FRT :
(bit[5]) _ :
(bit[5]) FRB :
0b1110101110 :
[Rc] as instr) =
  Fctidu (FRT,FRB,Rc)

function clause execute (Fctidu (FRT, FRB, Rc)) = ()

union ast member (bit[5], bit[5], bit) Fctiduz

function clause decode (0b111111 :
(bit[5]) FRT :
(bit[5]) _ :
(bit[5]) FRB :
0b1110101111 :
[Rc] as instr) =
  Fctiduz (FRT,FRB,Rc)

function clause execute (Fctiduz (FRT, FRB, Rc)) = ()

union ast member (bit[5], bit[5], bit) Fctiw

function clause decode (0b111111 :
(bit[5]) FRT :
(bit[5]) _ :
(bit[5]) FRB :
0b0000001110 :
[Rc] as instr) =
  Fctiw (FRT,FRB,Rc)

function clause execute (Fctiw (FRT, FRB, Rc)) = ()

union ast member (bit[5], bit[5], bit) Fctiwz

function clause decode (0b111111 :
(bit[5]) FRT :
(bit[5]) _ :
(bit[5]) FRB :
0b0000001111 :
[Rc] as instr) =
  Fctiwz (FRT,FRB,Rc)

function clause execute (Fctiwz (FRT, FRB, Rc)) = ()

union ast member (bit[5], bit[5], bit) Fctiwu

function clause decode (0b111111 :
(bit[5]) FRT :
(bit[5]) _ :
(bit[5]) FRB :
0b0010001110 :
[Rc] as instr) =
  Fctiwu (FRT,FRB,Rc)

function clause execute (Fctiwu (FRT, FRB, Rc)) = ()

union ast member (bit[5], bit[5], bit) Fctiwuz

function clause decode (0b111111 :
(bit[5]) FRT :
(bit[5]) _ :
(bit[5]) FRB :
0b0010001111 :
[Rc] as instr) =
  Fctiwuz (FRT,FRB,Rc)

function clause execute (Fctiwuz (FRT, FRB, Rc)) = ()

union ast member (bit[5], bit[5], bit) Fcfid

function clause decode (0b111111 :
(bit[5]) FRT :
(bit[5]) _ :
(bit[5]) FRB :
0b1101001110 :
[Rc] as instr) =
  Fcfid (FRT,FRB,Rc)

function clause execute (Fcfid (FRT, FRB, Rc)) = ()

union ast member (bit[5], bit[5], bit) Fcfidu

function clause decode (0b111111 :
(bit[5]) FRT :
(bit[5]) _ :
(bit[5]) FRB :
0b1111001110 :
[Rc] as instr) =
  Fcfidu (FRT,FRB,Rc)

function clause execute (Fcfidu (FRT, FRB, Rc)) = ()

union ast member (bit[5], bit[5], bit) Fcfids

function clause decode (0b111011 :
(bit[5]) FRT :
(bit[5]) _ :
(bit[5]) FRB :
0b1101001110 :
[Rc] as instr) =
  Fcfids (FRT,FRB,Rc)

function clause execute (Fcfids (FRT, FRB, Rc)) = ()

union ast member (bit[5], bit[5], bit) Fcfidus

function clause decode (0b111011 :
(bit[5]) FRT :
(bit[5]) _ :
(bit[5]) FRB :
0b1111001110 :
[Rc] as instr) =
  Fcfidus (FRT,FRB,Rc)

function clause execute (Fcfidus (FRT, FRB, Rc)) = ()

union ast member (bit[5], bit[5], bit) Frin

function clause decode (0b111111 :
(bit[5]) FRT :
(bit[5]) _ :
(bit[5]) FRB :
0b0110001000 :
[Rc] as instr) =
  Frin (FRT,FRB,Rc)

function clause execute (Frin (FRT, FRB, Rc)) = ()

union ast member (bit[5], bit[5], bit) Frip

function clause decode (0b111111 :
(bit[5]) FRT :
(bit[5]) _ :
(bit[5]) FRB :
0b0111001000 :
[Rc] as instr) =
  Frip (FRT,FRB,Rc)

function clause execute (Frip (FRT, FRB, Rc)) = ()

union ast member (bit[5], bit[5], bit) Friz

function clause decode (0b111111 :
(bit[5]) FRT :
(bit[5]) _ :
(bit[5]) FRB :
0b0110101000 :
[Rc] as instr) =
  Friz (FRT,FRB,Rc)

function clause execute (Friz (FRT, FRB, Rc)) = ()

union ast member (bit[5], bit[5], bit) Frim

function clause decode (0b111111 :
(bit[5]) FRT :
(bit[5]) _ :
(bit[5]) FRB :
0b0111101000 :
[Rc] as instr) =
  Frim (FRT,FRB,Rc)

function clause execute (Frim (FRT, FRB, Rc)) = ()

union ast member (bit[3], bit[5], bit[5]) Fcmpu

function clause decode (0b111111 :
(bit[3]) BF :
(bit[2]) _ :
(bit[5]) FRA :
(bit[5]) FRB :
0b0000000000 :
(bit[1]) _ as instr) =
  Fcmpu (BF,FRA,FRB)

function clause execute (Fcmpu (BF, FRA, FRB)) = ()

union ast member (bit[3], bit[5], bit[5]) Fcmpo

function clause decode (0b111111 :
(bit[3]) BF :
(bit[2]) _ :
(bit[5]) FRA :
(bit[5]) FRB :
0b0000100000 :
(bit[1]) _ as instr) =
  Fcmpo (BF,FRA,FRB)

function clause execute (Fcmpo (BF, FRA, FRB)) = ()

union ast member (bit[5], bit[5], bit[5], bit[5], bit) Fsel

function clause decode (0b111111 :
(bit[5]) FRT :
(bit[5]) FRA :
(bit[5]) FRB :
(bit[5]) FRC :
0b10111 :
[Rc] as instr) =
  Fsel (FRT,FRA,FRB,FRC,Rc)

function clause execute (Fsel (FRT, FRA, FRB, FRC, Rc)) = ()

union ast member (bit[5], bit) Mffs

function clause decode (0b111111 :
(bit[5]) FRT :
(bit[5]) _ :
(bit[5]) _ :
0b1001000111 :
[Rc] as instr) =
  Mffs (FRT,Rc)

function clause execute (Mffs (FRT, Rc)) = ()

union ast member (bit[3], bit[3]) Mcrfs

function clause decode (0b111111 :
(bit[3]) BF :
(bit[2]) _ :
(bit[3]) BFA :
(bit[2]) _ :
(bit[5]) _ :
0b0001000000 :
(bit[1]) _ as instr) =
  Mcrfs (BF,BFA)

function clause execute (Mcrfs (BF, BFA)) = ()

union ast member (bit[3], bit, bit[4], bit) Mtfsfi

function clause decode (0b111111 :
(bit[3]) BF :
(bit[2]) _ :
(bit[4]) _ :
[W] :
(bit[4]) U :
(bit[1]) _ :
0b0010000110 :
[Rc] as instr) =
  Mtfsfi (BF,W,U,Rc)

function clause execute (Mtfsfi (BF, W, U, Rc)) = ()

union ast member (bit, bit[8], bit, bit[5], bit) Mtfsf

function clause decode (0b111111 :
[L] :
(bit[8]) FLM :
[W] :
(bit[5]) FRB :
0b1011000111 :
[Rc] as instr) =
  Mtfsf (L,FLM,W,FRB,Rc)

function clause execute (Mtfsf (L, FLM, W, FRB, Rc)) = ()

union ast member (bit[5], bit) Mtfsb0

function clause decode (0b111111 :
(bit[5]) BT :
(bit[5]) _ :
(bit[5]) _ :
0b0001000110 :
[Rc] as instr) =
  Mtfsb0 (BT,Rc)

function clause execute (Mtfsb0 (BT, Rc)) = ()

union ast member (bit[5], bit) Mtfsb1

function clause decode (0b111111 :
(bit[5]) BT :
(bit[5]) _ :
(bit[5]) _ :
0b0000100110 :
[Rc] as instr) =
  Mtfsb1 (BT,Rc)

function clause execute (Mtfsb1 (BT, Rc)) = ()

union ast member (bit[5], bit[5], bit[5], bit) Daddq

function clause decode (0b111111 :
(bit[5]) FRTp :
(bit[5]) FRAp :
(bit[5]) FRBp :
0b0000000010 :
[Rc] as instr) =
  Daddq (FRTp,FRAp,FRBp,Rc)

function clause execute (Daddq (FRTp, FRAp, FRBp, Rc)) = ()

union ast member (bit[5], bit[5], bit[5], bit) Dadd

function clause decode (0b111011 :
(bit[5]) FRT :
(bit[5]) FRA :
(bit[5]) FRB :
0b0000000010 :
[Rc] as instr) =
  Dadd (FRT,FRA,FRB,Rc)

function clause execute (Dadd (FRT, FRA, FRB, Rc)) = ()

union ast member (bit[5], bit[5], bit[5], bit) Dsubq

function clause decode (0b111111 :
(bit[5]) FRTp :
(bit[5]) FRAp :
(bit[5]) FRBp :
0b1000000010 :
[Rc] as instr) =
  Dsubq (FRTp,FRAp,FRBp,Rc)

function clause execute (Dsubq (FRTp, FRAp, FRBp, Rc)) = ()

union ast member (bit[5], bit[5], bit[5], bit) Dsub

function clause decode (0b111011 :
(bit[5]) FRT :
(bit[5]) FRA :
(bit[5]) FRB :
0b1000000010 :
[Rc] as instr) =
  Dsub (FRT,FRA,FRB,Rc)

function clause execute (Dsub (FRT, FRA, FRB, Rc)) = ()

union ast member (bit[5], bit[5], bit[5], bit) Dmulq

function clause decode (0b111111 :
(bit[5]) FRTp :
(bit[5]) FRAp :
(bit[5]) FRBp :
0b0000100010 :
[Rc] as instr) =
  Dmulq (FRTp,FRAp,FRBp,Rc)

function clause execute (Dmulq (FRTp, FRAp, FRBp, Rc)) = ()

union ast member (bit[5], bit[5], bit[5], bit) Dmul

function clause decode (0b111011 :
(bit[5]) FRT :
(bit[5]) FRA :
(bit[5]) FRB :
0b0000100010 :
[Rc] as instr) =
  Dmul (FRT,FRA,FRB,Rc)

function clause execute (Dmul (FRT, FRA, FRB, Rc)) = ()

union ast member (bit[5], bit[5], bit[5], bit) Ddivq

function clause decode (0b111111 :
(bit[5]) FRTp :
(bit[5]) FRAp :
(bit[5]) FRBp :
0b1000100010 :
[Rc] as instr) =
  Ddivq (FRTp,FRAp,FRBp,Rc)

function clause execute (Ddivq (FRTp, FRAp, FRBp, Rc)) = ()

union ast member (bit[5], bit[5], bit[5], bit) Ddiv

function clause decode (0b111011 :
(bit[5]) FRT :
(bit[5]) FRA :
(bit[5]) FRB :
0b1000100010 :
[Rc] as instr) =
  Ddiv (FRT,FRA,FRB,Rc)

function clause execute (Ddiv (FRT, FRA, FRB, Rc)) = ()

union ast member (bit[3], bit[5], bit[5]) Dcmpuq

function clause decode (0b111111 :
(bit[3]) BF :
(bit[2]) _ :
(bit[5]) FRAp :
(bit[5]) FRBp :
0b1010000010 :
(bit[1]) _ as instr) =
  Dcmpuq (BF,FRAp,FRBp)

function clause execute (Dcmpuq (BF, FRAp, FRBp)) = ()

union ast member (bit[3], bit[5], bit[5]) Dcmpu

function clause decode (0b111011 :
(bit[3]) BF :
(bit[2]) _ :
(bit[5]) FRA :
(bit[5]) FRB :
0b1010000010 :
(bit[1]) _ as instr) =
  Dcmpu (BF,FRA,FRB)

function clause execute (Dcmpu (BF, FRA, FRB)) = ()

union ast member (bit[3], bit[5], bit[5]) Dcmpoq

function clause decode (0b111111 :
(bit[3]) BF :
(bit[2]) _ :
(bit[5]) FRAp :
(bit[5]) FRBp :
0b0010000010 :
(bit[1]) _ as instr) =
  Dcmpoq (BF,FRAp,FRBp)

function clause execute (Dcmpoq (BF, FRAp, FRBp)) = ()

union ast member (bit[3], bit[5], bit[5]) Dcmpo

function clause decode (0b111011 :
(bit[3]) BF :
(bit[2]) _ :
(bit[5]) FRA :
(bit[5]) FRB :
0b0010000010 :
(bit[1]) _ as instr) =
  Dcmpo (BF,FRA,FRB)

function clause execute (Dcmpo (BF, FRA, FRB)) = ()

union ast member (bit[3], bit[5], bit[6]) Dtstdcq

function clause decode (0b111111 :
(bit[3]) BF :
(bit[2]) _ :
(bit[5]) FRAp :
(bit[6]) DCM :
0b011000010 :
(bit[1]) _ as instr) =
  Dtstdcq (BF,FRAp,DCM)

function clause execute (Dtstdcq (BF, FRAp, DCM)) = ()

union ast member (bit[3], bit[5], bit[6]) Dtstdc

function clause decode (0b111011 :
(bit[3]) BF :
(bit[2]) _ :
(bit[5]) FRA :
(bit[6]) DCM :
0b011000010 :
(bit[1]) _ as instr) =
  Dtstdc (BF,FRA,DCM)

function clause execute (Dtstdc (BF, FRA, DCM)) = ()

union ast member (bit[3], bit[5], bit[6]) Dtstdgq

function clause decode (0b111111 :
(bit[3]) BF :
(bit[2]) _ :
(bit[5]) FRAp :
(bit[6]) DGM :
0b011100010 :
(bit[1]) _ as instr) =
  Dtstdgq (BF,FRAp,DGM)

function clause execute (Dtstdgq (BF, FRAp, DGM)) = ()

union ast member (bit[3], bit[5], bit[6]) Dtstdg

function clause decode (0b111011 :
(bit[3]) BF :
(bit[2]) _ :
(bit[5]) FRA :
(bit[6]) DGM :
0b011100010 :
(bit[1]) _ as instr) =
  Dtstdg (BF,FRA,DGM)

function clause execute (Dtstdg (BF, FRA, DGM)) = ()

union ast member (bit[3], bit[5], bit[5]) Dtstexq

function clause decode (0b111111 :
(bit[3]) BF :
(bit[2]) _ :
(bit[5]) FRAp :
(bit[5]) FRBp :
0b0010100010 :
(bit[1]) _ as instr) =
  Dtstexq (BF,FRAp,FRBp)

function clause execute (Dtstexq (BF, FRAp, FRBp)) = ()

union ast member (bit[3], bit[5], bit[5]) Dtstex

function clause decode (0b111011 :
(bit[3]) BF :
(bit[2]) _ :
(bit[5]) FRA :
(bit[5]) FRB :
0b0010100010 :
(bit[1]) _ as instr) =
  Dtstex (BF,FRA,FRB)

function clause execute (Dtstex (BF, FRA, FRB)) = ()

union ast member (bit[3], bit[5], bit[5]) Dtstsfq

function clause decode (0b111111 :
(bit[3]) BF :
(bit[2]) _ :
(bit[5]) FRA :
(bit[5]) FRBp :
0b1010100010 :
(bit[1]) _ as instr) =
  Dtstsfq (BF,FRA,FRBp)

function clause execute (Dtstsfq (BF, FRA, FRBp)) = ()

union ast member (bit[3], bit[5], bit[5]) Dtstsf

function clause decode (0b111011 :
(bit[3]) BF :
(bit[2]) _ :
(bit[5]) FRA :
(bit[5]) FRB :
0b1010100010 :
(bit[1]) _ as instr) =
  Dtstsf (BF,FRA,FRB)

function clause execute (Dtstsf (BF, FRA, FRB)) = ()

union ast member (bit[5], bit[5], bit[5], bit[2], bit) Dquaiq

function clause decode (0b111111 :
(bit[5]) FRTp :
(bit[5]) TE :
(bit[5]) FRBp :
(bit[2]) RMC :
0b01000011 :
[Rc] as instr) =
  Dquaiq (FRTp,TE,FRBp,RMC,Rc)

function clause execute (Dquaiq (FRTp, TE, FRBp, RMC, Rc)) = ()

union ast member (bit[5], bit[5], bit[5], bit[2], bit) Dquai

function clause decode (0b111011 :
(bit[5]) FRT :
(bit[5]) TE :
(bit[5]) FRB :
(bit[2]) RMC :
0b01000011 :
[Rc] as instr) =
  Dquai (FRT,TE,FRB,RMC,Rc)

function clause execute (Dquai (FRT, TE, FRB, RMC, Rc)) = ()

union ast member (bit[5], bit[5], bit[5], bit[2], bit) Dquaq

function clause decode (0b111111 :
(bit[5]) FRTp :
(bit[5]) FRAp :
(bit[5]) FRBp :
(bit[2]) RMC :
0b00000011 :
[Rc] as instr) =
  Dquaq (FRTp,FRAp,FRBp,RMC,Rc)

function clause execute (Dquaq (FRTp, FRAp, FRBp, RMC, Rc)) = ()

union ast member (bit[5], bit[5], bit[5], bit[2], bit) Dqua

function clause decode (0b111011 :
(bit[5]) FRT :
(bit[5]) FRA :
(bit[5]) FRB :
(bit[2]) RMC :
0b00000011 :
[Rc] as instr) =
  Dqua (FRT,FRA,FRB,RMC,Rc)

function clause execute (Dqua (FRT, FRA, FRB, RMC, Rc)) = ()

union ast member (bit[5], bit[5], bit[5], bit[2], bit) Drrndq

function clause decode (0b111111 :
(bit[5]) FRTp :
(bit[5]) FRA :
(bit[5]) FRBp :
(bit[2]) RMC :
0b00100011 :
[Rc] as instr) =
  Drrndq (FRTp,FRA,FRBp,RMC,Rc)

function clause execute (Drrndq (FRTp, FRA, FRBp, RMC, Rc)) = ()

union ast member (bit[5], bit[5], bit[5], bit[2], bit) Drrnd

function clause decode (0b111011 :
(bit[5]) FRT :
(bit[5]) FRA :
(bit[5]) FRB :
(bit[2]) RMC :
0b00100011 :
[Rc] as instr) =
  Drrnd (FRT,FRA,FRB,RMC,Rc)

function clause execute (Drrnd (FRT, FRA, FRB, RMC, Rc)) = ()

union ast member (bit[5], bit, bit[5], bit[2], bit) Drintxq

function clause decode (0b111111 :
(bit[5]) FRTp :
(bit[4]) _ :
[R] :
(bit[5]) FRBp :
(bit[2]) RMC :
0b01100011 :
[Rc] as instr) =
  Drintxq (FRTp,R,FRBp,RMC,Rc)

function clause execute (Drintxq (FRTp, R, FRBp, RMC, Rc)) = ()

union ast member (bit[5], bit, bit[5], bit[2], bit) Drintx

function clause decode (0b111011 :
(bit[5]) FRT :
(bit[4]) _ :
[R] :
(bit[5]) FRB :
(bit[2]) RMC :
0b01100011 :
[Rc] as instr) =
  Drintx (FRT,R,FRB,RMC,Rc)

function clause execute (Drintx (FRT, R, FRB, RMC, Rc)) = ()

union ast member (bit[5], bit, bit[5], bit[2], bit) Drintnq

function clause decode (0b111111 :
(bit[5]) FRTp :
(bit[4]) _ :
[R] :
(bit[5]) FRBp :
(bit[2]) RMC :
0b11100011 :
[Rc] as instr) =
  Drintnq (FRTp,R,FRBp,RMC,Rc)

function clause execute (Drintnq (FRTp, R, FRBp, RMC, Rc)) = ()

union ast member (bit[5], bit, bit[5], bit[2], bit) Drintn

function clause decode (0b111011 :
(bit[5]) FRT :
(bit[4]) _ :
[R] :
(bit[5]) FRB :
(bit[2]) RMC :
0b11100011 :
[Rc] as instr) =
  Drintn (FRT,R,FRB,RMC,Rc)

function clause execute (Drintn (FRT, R, FRB, RMC, Rc)) = ()

union ast member (bit[5], bit[5], bit) Dctdp

function clause decode (0b111011 :
(bit[5]) FRT :
(bit[5]) _ :
(bit[5]) FRB :
0b0100000010 :
[Rc] as instr) =
  Dctdp (FRT,FRB,Rc)

function clause execute (Dctdp (FRT, FRB, Rc)) = ()

union ast member (bit[5], bit[5], bit) Dctqpq

function clause decode (0b111111 :
(bit[5]) FRTp :
(bit[5]) _ :
(bit[5]) FRB :
0b0100000010 :
[Rc] as instr) =
  Dctqpq (FRTp,FRB,Rc)

function clause execute (Dctqpq (FRTp, FRB, Rc)) = ()

union ast member (bit[5], bit[5], bit) Drsp

function clause decode (0b111011 :
(bit[5]) FRT :
(bit[5]) _ :
(bit[5]) FRB :
0b1100000010 :
[Rc] as instr) =
  Drsp (FRT,FRB,Rc)

function clause execute (Drsp (FRT, FRB, Rc)) = ()

union ast member (bit[5], bit[5], bit) Drdpq

function clause decode (0b111111 :
(bit[5]) FRTp :
(bit[5]) _ :
(bit[5]) FRBp :
0b1100000010 :
[Rc] as instr) =
  Drdpq (FRTp,FRBp,Rc)

function clause execute (Drdpq (FRTp, FRBp, Rc)) = ()

union ast member (bit[5], bit[5], bit) Dcffix

function clause decode (0b111011 :
(bit[5]) FRT :
(bit[5]) _ :
(bit[5]) FRB :
0b1100100010 :
[Rc] as instr) =
  Dcffix (FRT,FRB,Rc)

function clause execute (Dcffix (FRT, FRB, Rc)) = ()

union ast member (bit[5], bit[5], bit) Dcffixq

function clause decode (0b111111 :
(bit[5]) FRTp :
(bit[5]) _ :
(bit[5]) FRB :
0b1100100010 :
[Rc] as instr) =
  Dcffixq (FRTp,FRB,Rc)

function clause execute (Dcffixq (FRTp, FRB, Rc)) = ()

union ast member (bit[5], bit[5], bit) Dctfixq

function clause decode (0b111111 :
(bit[5]) FRT :
(bit[5]) _ :
(bit[5]) FRBp :
0b0100100010 :
[Rc] as instr) =
  Dctfixq (FRT,FRBp,Rc)

function clause execute (Dctfixq (FRT, FRBp, Rc)) = ()

union ast member (bit[5], bit[5], bit) Dctfix

function clause decode (0b111011 :
(bit[5]) FRT :
(bit[5]) _ :
(bit[5]) FRB :
0b0100100010 :
[Rc] as instr) =
  Dctfix (FRT,FRB,Rc)

function clause execute (Dctfix (FRT, FRB, Rc)) = ()

union ast member (bit[5], bit[2], bit[5], bit) Ddedpdq

function clause decode (0b111111 :
(bit[5]) FRTp :
(bit[2]) SP :
(bit[3]) _ :
(bit[5]) FRBp :
0b0101000010 :
[Rc] as instr) =
  Ddedpdq (FRTp,SP,FRBp,Rc)

function clause execute (Ddedpdq (FRTp, SP, FRBp, Rc)) = ()

union ast member (bit[5], bit[2], bit[5], bit) Ddedpd

function clause decode (0b111011 :
(bit[5]) FRT :
(bit[2]) SP :
(bit[3]) _ :
(bit[5]) FRB :
0b0101000010 :
[Rc] as instr) =
  Ddedpd (FRT,SP,FRB,Rc)

function clause execute (Ddedpd (FRT, SP, FRB, Rc)) = ()

union ast member (bit[5], bit, bit[5], bit) Denbcdq

function clause decode (0b111111 :
(bit[5]) FRTp :
[S] :
(bit[4]) _ :
(bit[5]) FRBp :
0b1101000010 :
[Rc] as instr) =
  Denbcdq (FRTp,S,FRBp,Rc)

function clause execute (Denbcdq (FRTp, S, FRBp, Rc)) = ()

union ast member (bit[5], bit, bit[5], bit) Denbcd

function clause decode (0b111011 :
(bit[5]) FRT :
[S] :
(bit[4]) _ :
(bit[5]) FRB :
0b1101000010 :
[Rc] as instr) =
  Denbcd (FRT,S,FRB,Rc)

function clause execute (Denbcd (FRT, S, FRB, Rc)) = ()

union ast member (bit[5], bit[5], bit) Dxexq

function clause decode (0b111111 :
(bit[5]) FRT :
(bit[5]) _ :
(bit[5]) FRBp :
0b0101100010 :
[Rc] as instr) =
  Dxexq (FRT,FRBp,Rc)

function clause execute (Dxexq (FRT, FRBp, Rc)) = ()

union ast member (bit[5], bit[5], bit) Dxex

function clause decode (0b111011 :
(bit[5]) FRT :
(bit[5]) _ :
(bit[5]) FRB :
0b0101100010 :
[Rc] as instr) =
  Dxex (FRT,FRB,Rc)

function clause execute (Dxex (FRT, FRB, Rc)) = ()

union ast member (bit[5], bit[5], bit[5], bit) Diexq

function clause decode (0b111111 :
(bit[5]) FRTp :
(bit[5]) FRA :
(bit[5]) FRBp :
0b1101100010 :
[Rc] as instr) =
  Diexq (FRTp,FRA,FRBp,Rc)

function clause execute (Diexq (FRTp, FRA, FRBp, Rc)) = ()

union ast member (bit[5], bit[5], bit[5], bit) Diex

function clause decode (0b111011 :
(bit[5]) FRT :
(bit[5]) FRA :
(bit[5]) FRB :
0b1101100010 :
[Rc] as instr) =
  Diex (FRT,FRA,FRB,Rc)

function clause execute (Diex (FRT, FRA, FRB, Rc)) = ()

union ast member (bit[5], bit[5], bit[6], bit) Dscliq

function clause decode (0b111111 :
(bit[5]) FRTp :
(bit[5]) FRAp :
(bit[6]) SH :
0b001000010 :
[Rc] as instr) =
  Dscliq (FRTp,FRAp,SH,Rc)

function clause execute (Dscliq (FRTp, FRAp, SH, Rc)) = ()

union ast member (bit[5], bit[5], bit[6], bit) Dscli

function clause decode (0b111011 :
(bit[5]) FRT :
(bit[5]) FRA :
(bit[6]) SH :
0b001000010 :
[Rc] as instr) =
  Dscli (FRT,FRA,SH,Rc)

function clause execute (Dscli (FRT, FRA, SH, Rc)) = ()

union ast member (bit[5], bit[5], bit[6], bit) Dscriq

function clause decode (0b111111 :
(bit[5]) FRTp :
(bit[5]) FRAp :
(bit[6]) SH :
0b001100010 :
[Rc] as instr) =
  Dscriq (FRTp,FRAp,SH,Rc)

function clause execute (Dscriq (FRTp, FRAp, SH, Rc)) = ()

union ast member (bit[5], bit[5], bit[6], bit) Dscri

function clause decode (0b111011 :
(bit[5]) FRT :
(bit[5]) FRA :
(bit[6]) SH :
0b001100010 :
[Rc] as instr) =
  Dscri (FRT,FRA,SH,Rc)

function clause execute (Dscri (FRT, FRA, SH, Rc)) = ()

union ast member (bit[5], bit[5], bit[5]) Lvebx

function clause decode (0b011111 :
(bit[5]) VRT :
(bit[5]) RA :
(bit[5]) RB :
0b0000000111 :
(bit[1]) _ as instr) =
  Lvebx (VRT,RA,RB)

function clause execute (Lvebx (VRT, RA, RB)) =
  {
    (bit[64]) b := 0;
    (bit[64]) EA := 0;
    if RA == 0 then b := 0 else b := GPR[RA];
    EA := b + GPR[RB];
    eb := EA[60 .. 63];
    VR[VRT] := undefined;
    if bigendianmode
    then (VR[VRT])[8 * eb..8 * eb + 7] := MEMr (EA,1)
    else (VR[VRT])[120 - 8 * eb..127 - 8 * eb] := MEMr (EA,1)
  }

union ast member (bit[5], bit[5], bit[5]) Lvehx

function clause decode (0b011111 :
(bit[5]) VRT :
(bit[5]) RA :
(bit[5]) RB :
0b0000100111 :
(bit[1]) _ as instr) =
  Lvehx (VRT,RA,RB)

function clause execute (Lvehx (VRT, RA, RB)) =
  {
    (bit[64]) b := 0;
    (bit[64]) EA := 0;
    if RA == 0 then b := 0 else b := GPR[RA];
    EA :=
      (b + GPR[RB] &
        0b1111111111111111111111111111111111111111111111111111111111111110);
    eb := EA[60 .. 63];
    VR[VRT] := undefined;
    if bigendianmode
    then (VR[VRT])[8 * eb..8 * eb + 15] := MEMr (EA,2)
    else (VR[VRT])[112 - 8 * eb..127 - 8 * eb] := MEMr (EA,2)
  }

union ast member (bit[5], bit[5], bit[5]) Lvewx

function clause decode (0b011111 :
(bit[5]) VRT :
(bit[5]) RA :
(bit[5]) RB :
0b0001000111 :
(bit[1]) _ as instr) =
  Lvewx (VRT,RA,RB)

function clause execute (Lvewx (VRT, RA, RB)) =
  {
    (bit[64]) b := 0;
    (bit[64]) EA := 0;
    if RA == 0 then b := 0 else b := GPR[RA];
    EA :=
      (b + GPR[RB] &
        0b1111111111111111111111111111111111111111111111111111111111111100);
    eb := EA[60 .. 63];
    VR[VRT] := undefined;
    if bigendianmode
    then (VR[VRT])[8 * eb..8 * eb + 31] := MEMr (EA,4)
    else (VR[VRT])[96 - 8 * eb..127 - 8 * eb] := MEMr (EA,4)
  }

union ast member (bit[5], bit[5], bit[5]) Lvx

function clause decode (0b011111 :
(bit[5]) VRT :
(bit[5]) RA :
(bit[5]) RB :
0b0001100111 :
(bit[1]) _ as instr) =
  Lvx (VRT,RA,RB)

function clause execute (Lvx (VRT, RA, RB)) =
  {
    (bit[64]) b := 0;
    (bit[64]) EA := 0;
    if RA == 0 then b := 0 else b := GPR[RA];
    EA := b + GPR[RB];
    VR[VRT] :=
      MEMr
        (EA & 0b1111111111111111111111111111111111111111111111111111111111110000,16)
  }

union ast member (bit[5], bit[5], bit[5]) Lvxl

function clause decode (0b011111 :
(bit[5]) VRT :
(bit[5]) RA :
(bit[5]) RB :
0b0101100111 :
(bit[1]) _ as instr) =
  Lvxl (VRT,RA,RB)

function clause execute (Lvxl (VRT, RA, RB)) =
  {
    (bit[64]) b := 0;
    (bit[64]) EA := 0;
    if RA == 0 then b := 0 else b := GPR[RA];
    EA := b + GPR[RB];
    VR[VRT] :=
      MEMr
        (EA & 0b1111111111111111111111111111111111111111111111111111111111110000,16);
    mark_as_not_likely_to_be_needed_again_anytime_soon (EA)
  }

union ast member (bit[5], bit[5], bit[5]) Stvebx

function clause decode (0b011111 :
(bit[5]) VRS :
(bit[5]) RA :
(bit[5]) RB :
0b0010000111 :
(bit[1]) _ as instr) =
  Stvebx (VRS,RA,RB)

function clause execute (Stvebx (VRS, RA, RB)) =
  {
    (bit[64]) b := 0;
    (bit[64]) EA := 0;
    if RA == 0 then b := 0 else b := GPR[RA];
    EA := b + GPR[RB];
    eb := EA[60 .. 63];
    if bigendianmode
    then MEMw(EA,1) := VRS[8 * eb .. 8 * eb + 7]
    else MEMw(EA,1) := VRS[120 - 8 * eb .. 127 - 8 * eb]
  }

union ast member (bit[5], bit[5], bit[5]) Stvehx

function clause decode (0b011111 :
(bit[5]) VRS :
(bit[5]) RA :
(bit[5]) RB :
0b0010100111 :
(bit[1]) _ as instr) =
  Stvehx (VRS,RA,RB)

function clause execute (Stvehx (VRS, RA, RB)) =
  {
    (bit[64]) b := 0;
    (bit[64]) EA := 0;
    if RA == 0 then b := 0 else b := GPR[RA];
    EA :=
      (b + GPR[RB] &
        0b1111111111111111111111111111111111111111111111111111111111111110);
    eb := EA[60 .. 63];
    if bigendianmode
    then MEMw(EA,2) := VRS[8 * eb .. 8 * eb + 15]
    else MEMw(EA,2) := VRS[112 - 8 * eb .. 127 - 8 * eb]
  }

union ast member (bit[5], bit[5], bit[5]) Stvewx

function clause decode (0b011111 :
(bit[5]) VRS :
(bit[5]) RA :
(bit[5]) RB :
0b0011000111 :
(bit[1]) _ as instr) =
  Stvewx (VRS,RA,RB)

function clause execute (Stvewx (VRS, RA, RB)) =
  {
    (bit[64]) b := 0;
    (bit[64]) EA := 0;
    if RA == 0 then b := 0 else b := GPR[RA];
    EA :=
      (b + GPR[RB] &
        0b1111111111111111111111111111111111111111111111111111111111111100);
    eb := EA[60 .. 63];
    if bigendianmode
    then MEMw(EA,4) := VRS[8 * eb .. 8 * eb + 31]
    else MEMw(EA,4) := VRS[96 - 8 * eb .. 127 - 8 * eb]
  }

union ast member (bit[5], bit[5], bit[5]) Stvx

function clause decode (0b011111 :
(bit[5]) VRS :
(bit[5]) RA :
(bit[5]) RB :
0b0011100111 :
(bit[1]) _ as instr) =
  Stvx (VRS,RA,RB)

function clause execute (Stvx (VRS, RA, RB)) =
  {
    (bit[64]) b := 0;
    (bit[64]) EA := 0;
    if RA == 0 then b := 0 else b := GPR[RA];
    EA := b + GPR[RB];
    MEMw(EA & 0b1111111111111111111111111111111111111111111111111111111111110000,16) :=
      VR[VRS]
  }

union ast member (bit[5], bit[5], bit[5]) Stvxl

function clause decode (0b011111 :
(bit[5]) VRS :
(bit[5]) RA :
(bit[5]) RB :
0b0111100111 :
(bit[1]) _ as instr) =
  Stvxl (VRS,RA,RB)

function clause execute (Stvxl (VRS, RA, RB)) =
  {
    (bit[64]) b := 0;
    (bit[64]) EA := 0;
    if RA == 0 then b := 0 else b := GPR[RA];
    EA := b + GPR[RB];
    MEMw(EA & 0b1111111111111111111111111111111111111111111111111111111111110000,16) :=
      VR[VRS];
    mark_as_not_likely_to_be_needed_again_anytime_soon (EA)
  }

union ast member (bit[5], bit[5], bit[5]) Lvsl

function clause decode (0b011111 :
(bit[5]) VRT :
(bit[5]) RA :
(bit[5]) RB :
0b0000000110 :
(bit[1]) _ as instr) =
  Lvsl (VRT,RA,RB)

function clause execute (Lvsl (VRT, RA, RB)) = ()

union ast member (bit[5], bit[5], bit[5]) Lvsr

function clause decode (0b011111 :
(bit[5]) VRT :
(bit[5]) RA :
(bit[5]) RB :
0b0000100110 :
(bit[1]) _ as instr) =
  Lvsr (VRT,RA,RB)

function clause execute (Lvsr (VRT, RA, RB)) = ()

union ast member (bit[5], bit[5], bit[5]) Vpkpx

function clause decode (0b000100 :
(bit[5]) VRT :
(bit[5]) VRA :
(bit[5]) VRB :
0b01100001110 as instr) =
  Vpkpx (VRT,VRA,VRB)

function clause execute (Vpkpx (VRT, VRA, VRB)) =
  foreach (i from 0 to 63 by 16 in inc)
  {
    (VR[VRT])[i] := (VR[VRA])[i * 2 + 7];
    (VR[VRT])[i + 1..i + 5] := (VR[VRA])[i * 2 + 8 .. i * 2 + 12];
    (VR[VRT])[i + 6..i + 10] := (VR[VRA])[i * 2 + 16 .. i * 2 + 20];
    (VR[VRT])[i + 11..i + 15] := (VR[VRA])[i * 2 + 24 .. i * 2 + 28];
    (VR[VRT])[i + 64] := (VR[VRB])[i * 2 + 7];
    (VR[VRT])[i + 65..i + 69] := (VR[VRB])[i * 2 + 8 .. i * 2 + 12];
    (VR[VRT])[i + 70..i + 74] := (VR[VRB])[i * 2 + 16 .. i * 2 + 20];
    (VR[VRT])[i + 75..i + 79] := (VR[VRB])[i * 2 + 24 .. i * 2 + 28]
  }

union ast member (bit[5], bit[5], bit[5]) Vpkshss

function clause decode (0b000100 :
(bit[5]) VRT :
(bit[5]) VRA :
(bit[5]) VRB :
0b00110001110 as instr) =
  Vpkshss (VRT,VRA,VRB)

function clause execute (Vpkshss (VRT, VRA, VRB)) =
  foreach (i from 0 to 63 by 8 in inc)
  {
    (VR[VRT])[i..i + 7] :=
      (Clamp (EXTS ((VR[VRA])[i * 2 .. i * 2 + 15]),0 - 128,127))[24 .. 31];
    (VR[VRT])[i + 64..i + 71] :=
      (Clamp (EXTS ((VR[VRB])[i * 2 .. i * 2 + 15]),0 - 128,127))[24 .. 31]
  }

union ast member (bit[5], bit[5], bit[5]) Vpkshus

function clause decode (0b000100 :
(bit[5]) VRT :
(bit[5]) VRA :
(bit[5]) VRB :
0b00100001110 as instr) =
  Vpkshus (VRT,VRA,VRB)

function clause execute (Vpkshus (VRT, VRA, VRB)) =
  foreach (i from 0 to 63 by 8 in inc)
  {
    (VR[VRT])[i..i + 7] :=
      (Clamp (EXTS ((VR[VRA])[i * 2 .. i * 2 + 15]),0,255))[24 .. 31];
    (VR[VRT])[i + 64..i + 71] :=
      (Clamp (EXTS ((VR[VRB])[i * 2 .. i * 2 + 15]),0,255))[24 .. 31]
  }

union ast member (bit[5], bit[5], bit[5]) Vpkswss

function clause decode (0b000100 :
(bit[5]) VRT :
(bit[5]) VRA :
(bit[5]) VRB :
0b00111001110 as instr) =
  Vpkswss (VRT,VRA,VRB)

function clause execute (Vpkswss (VRT, VRA, VRB)) =
  foreach (i from 0 to 63 by 16 in inc)
  {
    (VR[VRT])[i..i + 15] :=
      (Clamp
        (EXTS ((VR[VRA])[i * 2 .. i * 2 + 31]),0 - 0b1000000000000000,0b1000000000000000 -
          1))[16 .. 31];
    (VR[VRT])[i + 64..i + 79] :=
      (Clamp
        (EXTS ((VR[VRB])[i * 2 .. i * 2 + 31]),0 - 0b1000000000000000,0b1000000000000000 -
          1))[16 .. 31]
  }

union ast member (bit[5], bit[5], bit[5]) Vpkswus

function clause decode (0b000100 :
(bit[5]) VRT :
(bit[5]) VRA :
(bit[5]) VRB :
0b00101001110 as instr) =
  Vpkswus (VRT,VRA,VRB)

function clause execute (Vpkswus (VRT, VRA, VRB)) =
  foreach (i from 0 to 63 by 16 in inc)
  {
    (VR[VRT])[i..i + 15] :=
      (Clamp (EXTS ((VR[VRA])[i * 2 .. i * 2 + 31]),0,0b10000000000000000 - 1))[16 ..
        31];
    (VR[VRT])[i + 64..i + 79] :=
      (Clamp (EXTS ((VR[VRB])[i * 2 .. i * 2 + 31]),0,0b10000000000000000 - 1))[16 ..
        31]
  }

union ast member (bit[5], bit[5], bit[5]) Vpkuhum

function clause decode (0b000100 :
(bit[5]) VRT :
(bit[5]) VRA :
(bit[5]) VRB :
0b00000001110 as instr) =
  Vpkuhum (VRT,VRA,VRB)

function clause execute (Vpkuhum (VRT, VRA, VRB)) =
  foreach (i from 0 to 63 by 8 in inc)
  {
    (VR[VRT])[i..i + 7] := (VR[VRA])[i * 2 + 8 .. i * 2 + 15];
    (VR[VRT])[i + 64..i + 71] := (VR[VRB])[i * 2 + 8 .. i * 2 + 15]
  }

union ast member (bit[5], bit[5], bit[5]) Vpkuhus

function clause decode (0b000100 :
(bit[5]) VRT :
(bit[5]) VRA :
(bit[5]) VRB :
0b00010001110 as instr) =
  Vpkuhus (VRT,VRA,VRB)

function clause execute (Vpkuhus (VRT, VRA, VRB)) =
  foreach (i from 0 to 63 by 8 in inc)
  {
    (VR[VRT])[i..i + 7] :=
      (Clamp (EXTZ ((VR[VRA])[i * 2 .. i * 2 + 15]),0,255))[24 .. 31];
    (VR[VRT])[i + 64..i + 71] :=
      (Clamp (EXTZ ((VR[VRB])[i * 2 .. i * 2 + 15]),0,255))[24 .. 31]
  }

union ast member (bit[5], bit[5], bit[5]) Vpkuwum

function clause decode (0b000100 :
(bit[5]) VRT :
(bit[5]) VRA :
(bit[5]) VRB :
0b00001001110 as instr) =
  Vpkuwum (VRT,VRA,VRB)

function clause execute (Vpkuwum (VRT, VRA, VRB)) =
  foreach (i from 0 to 63 by 16 in inc)
  {
    (VR[VRT])[i..i + 15] := (VR[VRA])[i * 2 + 16 .. i * 2 + 31];
    (VR[VRT])[i + 64..i + 79] := (VR[VRB])[i * 2 + 16 .. i * 2 + 31]
  }

union ast member (bit[5], bit[5], bit[5]) Vpkuwus

function clause decode (0b000100 :
(bit[5]) VRT :
(bit[5]) VRA :
(bit[5]) VRB :
0b00011001110 as instr) =
  Vpkuwus (VRT,VRA,VRB)

function clause execute (Vpkuwus (VRT, VRA, VRB)) =
  foreach (i from 0 to 63 by 16 in inc)
  {
    (VR[VRT])[i..i + 15] :=
      (Clamp (EXTZ ((VR[VRA])[i * 2 .. i * 2 + 31]),0,0b10000000000000000 - 1))[16 ..
        31];
    (VR[VRT])[i + 64..i + 79] :=
      (Clamp (EXTZ ((VR[VRB])[i * 2 .. i * 2 + 31]),0,0b10000000000000000 - 1))[16 ..
        31]
  }

union ast member (bit[5], bit[5]) Vupkhpx

function clause decode (0b000100 :
(bit[5]) VRT :
(bit[5]) _ :
(bit[5]) VRB :
0b01101001110 as instr) =
  Vupkhpx (VRT,VRB)

function clause execute (Vupkhpx (VRT, VRB)) =
  foreach (i from 0 to 63 by 16 in inc)
  {
    (VR[VRT])[i * 2..i * 2 + 7] := EXTS ((VR[VRB])[i .. i]);
    (VR[VRT])[i * 2 + 8..i * 2 + 15] := EXTZ ((VR[VRB])[i + 1 .. i + 5]);
    (VR[VRT])[i * 2 + 16..i * 2 + 23] := EXTZ ((VR[VRB])[i + 6 .. i + 10]);
    (VR[VRT])[i * 2 + 24..i * 2 + 31] := EXTZ ((VR[VRB])[i + 11 .. i + 15])
  }

union ast member (bit[5], bit[5]) Vupkhsb

function clause decode (0b000100 :
(bit[5]) VRT :
(bit[5]) _ :
(bit[5]) VRB :
0b01000001110 as instr) =
  Vupkhsb (VRT,VRB)

function clause execute (Vupkhsb (VRT, VRB)) =
  foreach (i from 0 to 63 by 8 in inc)
  (VR[VRT])[i * 2..i * 2 + 15] := EXTS ((VR[VRB])[i .. i + 7])

union ast member (bit[5], bit[5]) Vupkhsh

function clause decode (0b000100 :
(bit[5]) VRT :
(bit[5]) _ :
(bit[5]) VRB :
0b01001001110 as instr) =
  Vupkhsh (VRT,VRB)

function clause execute (Vupkhsh (VRT, VRB)) =
  foreach (i from 0 to 63 by 16 in inc)
  (VR[VRT])[i * 2..i * 2 + 31] := EXTS ((VR[VRB])[i .. i + 15])

union ast member (bit[5], bit[5]) Vupklpx

function clause decode (0b000100 :
(bit[5]) VRT :
(bit[5]) _ :
(bit[5]) VRB :
0b01111001110 as instr) =
  Vupklpx (VRT,VRB)

function clause execute (Vupklpx (VRT, VRB)) =
  foreach (i from 0 to 63 by 16 in inc)
  {
    (VR[VRT])[i * 2..i * 2 + 7] := EXTS ((VR[VRB])[i + 64 .. i + 64]);
    (VR[VRT])[i * 2 + 8..i * 2 + 15] := EXTZ ((VR[VRB])[i + 65 .. i + 69]);
    (VR[VRT])[i * 2 + 16..i * 2 + 23] := EXTZ ((VR[VRB])[i + 70 .. i + 74]);
    (VR[VRT])[i * 2 + 24..i * 2 + 31] := EXTZ ((VR[VRB])[i + 75 .. i + 79])
  }

union ast member (bit[5], bit[5]) Vupklsb

function clause decode (0b000100 :
(bit[5]) VRT :
(bit[5]) _ :
(bit[5]) VRB :
0b01010001110 as instr) =
  Vupklsb (VRT,VRB)

function clause execute (Vupklsb (VRT, VRB)) =
  foreach (i from 0 to 63 by 8 in inc)
  (VR[VRT])[i * 2..i * 2 + 15] := EXTS ((VR[VRB])[i + 64 .. i + 71])

union ast member (bit[5], bit[5]) Vupklsh

function clause decode (0b000100 :
(bit[5]) VRT :
(bit[5]) _ :
(bit[5]) VRB :
0b01011001110 as instr) =
  Vupklsh (VRT,VRB)

function clause execute (Vupklsh (VRT, VRB)) =
  foreach (i from 0 to 63 by 16 in inc)
  (VR[VRT])[i * 2..i * 2 + 31] := EXTS ((VR[VRB])[i + 64 .. i + 79])

union ast member (bit[5], bit[5], bit[5]) Vmrghb

function clause decode (0b000100 :
(bit[5]) VRT :
(bit[5]) VRA :
(bit[5]) VRB :
0b00000001100 as instr) =
  Vmrghb (VRT,VRA,VRB)

function clause execute (Vmrghb (VRT, VRA, VRB)) =
  foreach (i from 0 to 63 by 8 in inc)
  {
    (VR[VRT])[i * 2..i * 2 + 7] := (VR[VRA])[i .. i + 7];
    (VR[VRT])[i * 2 + 8..i * 2 + 15] := (VR[VRB])[i .. i + 7]
  }

union ast member (bit[5], bit[5], bit[5]) Vmrghh

function clause decode (0b000100 :
(bit[5]) VRT :
(bit[5]) VRA :
(bit[5]) VRB :
0b00001001100 as instr) =
  Vmrghh (VRT,VRA,VRB)

function clause execute (Vmrghh (VRT, VRA, VRB)) =
  foreach (i from 0 to 63 by 16 in inc)
  {
    (VR[VRT])[i * 2..i * 2 + 15] := (VR[VRA])[i .. i + 15];
    (VR[VRT])[i * 2 + 16..i * 2 + 31] := (VR[VRB])[i .. i + 15]
  }

union ast member (bit[5], bit[5], bit[5]) Vmrghw

function clause decode (0b000100 :
(bit[5]) VRT :
(bit[5]) VRA :
(bit[5]) VRB :
0b00010001100 as instr) =
  Vmrghw (VRT,VRA,VRB)

function clause execute (Vmrghw (VRT, VRA, VRB)) =
  foreach (i from 0 to 63 by 32 in inc)
  {
    (VR[VRT])[i * 2..i * 2 + 31] := (VR[VRA])[i .. i + 31];
    (VR[VRT])[i * 2 + 32..i * 2 + 63] := (VR[VRB])[i .. i + 31]
  }

union ast member (bit[5], bit[5], bit[5]) Vmrglb

function clause decode (0b000100 :
(bit[5]) VRT :
(bit[5]) VRA :
(bit[5]) VRB :
0b00100001100 as instr) =
  Vmrglb (VRT,VRA,VRB)

function clause execute (Vmrglb (VRT, VRA, VRB)) =
  foreach (i from 0 to 63 by 8 in inc)
  {
    (VR[VRT])[i * 2..i * 2 + 7] := (VR[VRA])[i + 64 .. i + 71];
    (VR[VRT])[i * 2 + 8..i * 2 + 15] := (VR[VRB])[i + 64 .. i + 71]
  }

union ast member (bit[5], bit[5], bit[5]) Vmrglh

function clause decode (0b000100 :
(bit[5]) VRT :
(bit[5]) VRA :
(bit[5]) VRB :
0b00101001100 as instr) =
  Vmrglh (VRT,VRA,VRB)

function clause execute (Vmrglh (VRT, VRA, VRB)) =
  foreach (i from 0 to 63 by 16 in inc)
  {
    (VR[VRT])[i * 2..i * 2 + 15] := (VR[VRA])[i + 64 .. i + 79];
    (VR[VRT])[i * 2 + 16..i * 2 + 31] := (VR[VRB])[i + 64 .. i + 79]
  }

union ast member (bit[5], bit[5], bit[5]) Vmrglw

function clause decode (0b000100 :
(bit[5]) VRT :
(bit[5]) VRA :
(bit[5]) VRB :
0b00110001100 as instr) =
  Vmrglw (VRT,VRA,VRB)

function clause execute (Vmrglw (VRT, VRA, VRB)) =
  foreach (i from 0 to 63 by 32 in inc)
  {
    (VR[VRT])[i * 2..i * 2 + 31] := (VR[VRA])[i + 64 .. i + 95];
    (VR[VRT])[i * 2 + 32..i * 2 + 63] := (VR[VRB])[i + 64 .. i + 95]
  }

union ast member (bit[5], bit[4], bit[5]) Vspltb

function clause decode (0b000100 :
(bit[5]) VRT :
(bit[1]) _ :
(bit[4]) UIM :
(bit[5]) VRB :
0b01000001100 as instr) =
  Vspltb (VRT,UIM,VRB)

function clause execute (Vspltb (VRT, UIM, VRB)) =
  {
    b := UIM : 0b000;
    foreach (i from 0 to 127 by 8 in inc)
    (VR[VRT])[i..i + 7] := (VR[VRB])[b .. b + 7]
  }

union ast member (bit[5], bit[3], bit[5]) Vsplth

function clause decode (0b000100 :
(bit[5]) VRT :
(bit[2]) _ :
(bit[3]) UIM :
(bit[5]) VRB :
0b01001001100 as instr) =
  Vsplth (VRT,UIM,VRB)

function clause execute (Vsplth (VRT, UIM, VRB)) =
  {
    b := UIM : 0b0000;
    foreach (i from 0 to 127 by 16 in inc)
    (VR[VRT])[i..i + 15] := (VR[VRB])[b .. b + 15]
  }

union ast member (bit[5], bit[2], bit[5]) Vspltw

function clause decode (0b000100 :
(bit[5]) VRT :
(bit[3]) _ :
(bit[2]) UIM :
(bit[5]) VRB :
0b01010001100 as instr) =
  Vspltw (VRT,UIM,VRB)

function clause execute (Vspltw (VRT, UIM, VRB)) =
  {
    b := UIM : 0b00000;
    foreach (i from 0 to 127 by 32 in inc)
    (VR[VRT])[i..i + 31] := (VR[VRB])[b .. b + 31]
  }

union ast member (bit[5], bit[5]) Vspltisb

function clause decode (0b000100 :
(bit[5]) VRT :
(bit[5]) SIM :
(bit[5]) _ :
0b01100001100 as instr) =
  Vspltisb (VRT,SIM)

function clause execute (Vspltisb (VRT, SIM)) =
  foreach (i from 0 to 127 by 8 in inc)
  (VR[VRT])[i..i + 7] := EXTS_EXPLICIT (SIM,8)

union ast member (bit[5], bit[5]) Vspltish

function clause decode (0b000100 :
(bit[5]) VRT :
(bit[5]) SIM :
(bit[5]) _ :
0b01101001100 as instr) =
  Vspltish (VRT,SIM)

function clause execute (Vspltish (VRT, SIM)) =
  foreach (i from 0 to 127 by 16 in inc)
  (VR[VRT])[i..i + 15] := EXTS_EXPLICIT (SIM,16)

union ast member (bit[5], bit[5]) Vspltisw

function clause decode (0b000100 :
(bit[5]) VRT :
(bit[5]) SIM :
(bit[5]) _ :
0b01110001100 as instr) =
  Vspltisw (VRT,SIM)

function clause execute (Vspltisw (VRT, SIM)) =
  foreach (i from 0 to 127 by 32 in inc)
  (VR[VRT])[i..i + 31] := EXTS_EXPLICIT (SIM,32)

union ast member (bit[5], bit[5], bit[5], bit[5]) Vperm

function clause decode (0b000100 :
(bit[5]) VRT :
(bit[5]) VRA :
(bit[5]) VRB :
(bit[5]) VRC :
0b101011 as instr) =
  Vperm (VRT,VRA,VRB,VRC)

function clause execute (Vperm (VRT, VRA, VRB, VRC)) =
  {
    (bit[256]) temp := VR[VRA] : VR[VRB];
    foreach (i from 0 to 127 by 8 in inc)
    {
      b := (VR[VRC])[i + 3 .. i + 7] : 0b000;
      (VR[VRT])[i..i + 7] := temp[b .. b + 7]
    }
  }

union ast member (bit[5], bit[5], bit[5], bit[5]) Vsel

function clause decode (0b000100 :
(bit[5]) VRT :
(bit[5]) VRA :
(bit[5]) VRB :
(bit[5]) VRC :
0b101010 as instr) =
  Vsel (VRT,VRA,VRB,VRC)

function clause execute (Vsel (VRT, VRA, VRB, VRC)) = ()

union ast member (bit[5], bit[5], bit[5]) Vsl

function clause decode (0b000100 :
(bit[5]) VRT :
(bit[5]) VRA :
(bit[5]) VRB :
0b00111000100 as instr) =
  Vsl (VRT,VRA,VRB)

function clause execute (Vsl (VRT, VRA, VRB)) =
  {
    sh := (VR[VRB])[125 .. 127];
    t := 1;
    foreach (i from 0 to 127 by 8 in inc)
    t := (t & (VR[VRB])[i + 5 .. i + 7] == sh);
    if t == 1 then VR[VRT] := VR[VRA] << sh else VR[VRT] := undefined
  }

union ast member (bit[5], bit[5], bit[5], bit[4]) Vsldoi

function clause decode (0b000100 :
(bit[5]) VRT :
(bit[5]) VRA :
(bit[5]) VRB :
(bit[1]) _ :
(bit[4]) SHB :
0b101100 as instr) =
  Vsldoi (VRT,VRA,VRB,SHB)

function clause execute (Vsldoi (VRT, VRA, VRB, SHB)) =
  VR[VRT] := (VR[VRA] : VR[VRB])[8 * SHB .. 8 * SHB + 127]

union ast member (bit[5], bit[5], bit[5]) Vslo

function clause decode (0b000100 :
(bit[5]) VRT :
(bit[5]) VRA :
(bit[5]) VRB :
0b10000001100 as instr) =
  Vslo (VRT,VRA,VRB)

function clause execute (Vslo (VRT, VRA, VRB)) =
  {
    shb := (VR[VRB])[121 .. 124];
    VR[VRT] := VR[VRA] << (shb : 0b000)
  }

union ast member (bit[5], bit[5], bit[5]) Vsr

function clause decode (0b000100 :
(bit[5]) VRT :
(bit[5]) VRA :
(bit[5]) VRB :
0b01011000100 as instr) =
  Vsr (VRT,VRA,VRB)

function clause execute (Vsr (VRT, VRA, VRB)) =
  {
    sh := (VR[VRB])[125 .. 127];
    t := 1;
    foreach (i from 0 to 127 by 8 in inc)
    t := (t & (VR[VRB])[i + 5 .. i + 7] == sh);
    if t == 1 then VR[VRT] := VR[VRA] >> sh else VR[VRT] := undefined
  }

union ast member (bit[5], bit[5], bit[5]) Vsro

function clause decode (0b000100 :
(bit[5]) VRT :
(bit[5]) VRA :
(bit[5]) VRB :
0b10001001100 as instr) =
  Vsro (VRT,VRA,VRB)

function clause execute (Vsro (VRT, VRA, VRB)) =
  {
    shb := (VR[VRB])[121 .. 124];
    VR[VRT] := VR[VRA] >> (shb : 0b000)
  }

union ast member (bit[5], bit[5], bit[5]) Vaddcuw

function clause decode (0b000100 :
(bit[5]) VRT :
(bit[5]) VRA :
(bit[5]) VRB :
0b00110000000 as instr) =
  Vaddcuw (VRT,VRA,VRB)

function clause execute (Vaddcuw (VRT, VRA, VRB)) =
  foreach (i from 0 to 127 by 32 in inc)
  {
    aop := EXTZ ((VR[VRA])[i .. i + 31]);
    bop := EXTZ ((VR[VRB])[i .. i + 31]);
    (VR[VRT])[i..i + 31] := Chop (aop + bop >> 32,1)
  }

union ast member (bit[5], bit[5], bit[5]) Vaddsbs

function clause decode (0b000100 :
(bit[5]) VRT :
(bit[5]) VRA :
(bit[5]) VRB :
0b01100000000 as instr) =
  Vaddsbs (VRT,VRA,VRB)

function clause execute (Vaddsbs (VRT, VRA, VRB)) =
  foreach (i from 0 to 127 by 8 in inc)
  {
    aop := EXTS (VRA[i .. i + 7]);
    bop := EXTS (VRB[i .. i + 7]);
    (VR[VRT])[i..i + 7] := (Clamp (aop + bop,0 - 128,127))[24 .. 31]
  }

union ast member (bit[5], bit[5], bit[5]) Vaddshs

function clause decode (0b000100 :
(bit[5]) VRT :
(bit[5]) VRA :
(bit[5]) VRB :
0b01101000000 as instr) =
  Vaddshs (VRT,VRA,VRB)

function clause execute (Vaddshs (VRT, VRA, VRB)) =
  foreach (i from 0 to 127 by 16 in inc)
  {
    aop := EXTS ((VR[VRA])[i .. i + 15]);
    bop := EXTS ((VR[VRB])[i .. i + 15]);
    (VR[VRT])[i..i + 15] :=
      (Clamp (aop + bop,0 - 0b1000000000000000,0b1000000000000000 - 1))[16 .. 31]
  }

union ast member (bit[5], bit[5], bit[5]) Vaddsws

function clause decode (0b000100 :
(bit[5]) VRT :
(bit[5]) VRA :
(bit[5]) VRB :
0b01110000000 as instr) =
  Vaddsws (VRT,VRA,VRB)

function clause execute (Vaddsws (VRT, VRA, VRB)) =
  foreach (i from 0 to 127 by 32 in inc)
  {
    aop := EXTS ((VR[VRA])[i .. i + 31]);
    bop := EXTS ((VR[VRB])[i .. i + 31]);
    (VR[VRT])[i..i + 31] :=
      Clamp
        (aop + bop,0 - 0b10000000000000000000000000000000,0b10000000000000000000000000000000 -
          1)
  }

union ast member (bit[5], bit[5], bit[5]) Vaddubm

function clause decode (0b000100 :
(bit[5]) VRT :
(bit[5]) VRA :
(bit[5]) VRB :
0b00000000000 as instr) =
  Vaddubm (VRT,VRA,VRB)

function clause execute (Vaddubm (VRT, VRA, VRB)) =
  foreach (i from 0 to 127 by 8 in inc)
  {
    aop := EXTZ ((VR[VRA])[i .. i + 7]);
    bop := EXTZ ((VR[VRB])[i .. i + 7]);
    (VR[VRT])[i..i + 7] := Chop (aop + bop,8)
  }

union ast member (bit[5], bit[5], bit[5]) Vadduhm

function clause decode (0b000100 :
(bit[5]) VRT :
(bit[5]) VRA :
(bit[5]) VRB :
0b00001000000 as instr) =
  Vadduhm (VRT,VRA,VRB)

function clause execute (Vadduhm (VRT, VRA, VRB)) =
  foreach (i from 0 to 127 by 16 in inc)
  {
    aop := EXTZ ((VR[VRA])[i .. i + 15]);
    bop := EXTZ ((VR[VRB])[i .. i + 15]);
    (VR[VRT])[i..i + 15] := Chop (aop + bop,16)
  }

union ast member (bit[5], bit[5], bit[5]) Vadduwm

function clause decode (0b000100 :
(bit[5]) VRT :
(bit[5]) VRA :
(bit[5]) VRB :
0b00010000000 as instr) =
  Vadduwm (VRT,VRA,VRB)

function clause execute (Vadduwm (VRT, VRA, VRB)) =
  foreach (i from 0 to 127 by 32 in inc)
  {
    aop := EXTZ ((VR[VRA])[i .. i + 31]);
    bop := EXTZ ((VR[VRB])[i .. i + 31]);
    (VR[VRT])[i..i + 31] := Chop (aop + bop,32)
  }

union ast member (bit[5], bit[5], bit[5]) Vaddubs

function clause decode (0b000100 :
(bit[5]) VRT :
(bit[5]) VRA :
(bit[5]) VRB :
0b01000000000 as instr) =
  Vaddubs (VRT,VRA,VRB)

function clause execute (Vaddubs (VRT, VRA, VRB)) =
  foreach (i from 0 to 127 by 8 in inc)
  {
    aop := EXTZ ((VR[VRA])[i .. i + 7]);
    bop := EXTZ ((VR[VRB])[i .. i + 7]);
    (VR[VRT])[i..i + 7] := (Clamp (aop + bop,0,255))[24 .. 31]
  }

union ast member (bit[5], bit[5], bit[5]) Vadduhs

function clause decode (0b000100 :
(bit[5]) VRT :
(bit[5]) VRA :
(bit[5]) VRB :
0b01001000000 as instr) =
  Vadduhs (VRT,VRA,VRB)

function clause execute (Vadduhs (VRT, VRA, VRB)) =
  foreach (i from 0 to 127 by 16 in inc)
  {
    aop := EXTZ ((VR[VRA])[i .. i + 15]);
    bop := EXTZ ((VR[VRB])[i .. i + 15]);
    (VR[VRT])[i..i + 15] :=
      (Clamp (aop + bop,0,0b10000000000000000 - 1))[16 .. 31]
  }

union ast member (bit[5], bit[5], bit[5]) Vadduws

function clause decode (0b000100 :
(bit[5]) VRT :
(bit[5]) VRA :
(bit[5]) VRB :
0b01010000000 as instr) =
  Vadduws (VRT,VRA,VRB)

function clause execute (Vadduws (VRT, VRA, VRB)) =
  foreach (i from 0 to 127 by 32 in inc)
  {
    aop := EXTZ ((VR[VRA])[i .. i + 31]);
    bop := EXTZ ((VR[VRB])[i .. i + 31]);
    (VR[VRT])[i..i + 31] :=
      Clamp (aop + bop,0,0b100000000000000000000000000000000 - 1)
  }

union ast member (bit[5], bit[5], bit[5]) Vsubcuw

function clause decode (0b000100 :
(bit[5]) VRT :
(bit[5]) VRA :
(bit[5]) VRB :
0b10110000000 as instr) =
  Vsubcuw (VRT,VRA,VRB)

function clause execute (Vsubcuw (VRT, VRA, VRB)) =
  {
    (bit[32]) temp := 0;
    foreach (i from 0 to 127 by 32 in inc)
    {
      aop := (VR[VRA])[i .. i + 31];
      bop := (VR[VRB])[i .. i + 31];
      temp := (bit[32]) (EXTZ (aop) + EXTZ (~ (bop))) + 1 >> 32;
      (VR[VRT])[i..i + 31] := (temp & 0b00000000000000000000000000000001)
    }
  }

union ast member (bit[5], bit[5], bit[5]) Vsubsbs

function clause decode (0b000100 :
(bit[5]) VRT :
(bit[5]) VRA :
(bit[5]) VRB :
0b11100000000 as instr) =
  Vsubsbs (VRT,VRA,VRB)

function clause execute (Vsubsbs (VRT, VRA, VRB)) =
  foreach (i from 0 to 127 by 8 in inc)
  {
    aop := EXTS ((VR[VRA])[i .. i + 7]);
    bop := EXTS ((VR[VRB])[i .. i + 7]);
    (VR[VRT])[i..i + 7] :=
      (Clamp ((bit[32]) (aop + ~ (bop)) + 1,0 - 128,127))[24 .. 31]
  }

union ast member (bit[5], bit[5], bit[5]) Vsubshs

function clause decode (0b000100 :
(bit[5]) VRT :
(bit[5]) VRA :
(bit[5]) VRB :
0b11101000000 as instr) =
  Vsubshs (VRT,VRA,VRB)

function clause execute (Vsubshs (VRT, VRA, VRB)) =
  foreach (i from 0 to 127 by 16 in inc)
  {
    aop := EXTS ((VR[VRA])[i .. i + 15]);
    bop := EXTS ((VR[VRB])[i .. i + 15]);
    (VR[VRT])[i..i + 15] :=
      (Clamp
        ((bit[32]) (aop + ~ (bop)) + 1,0 - 0b1000000000000000,0b1000000000000000 -
          1))[16 .. 31]
  }

union ast member (bit[5], bit[5], bit[5]) Vsubsws

function clause decode (0b000100 :
(bit[5]) VRT :
(bit[5]) VRA :
(bit[5]) VRB :
0b11110000000 as instr) =
  Vsubsws (VRT,VRA,VRB)

function clause execute (Vsubsws (VRT, VRA, VRB)) =
  foreach (i from 0 to 127 by 32 in inc)
  {
    aop := EXTS ((VR[VRA])[i .. i + 31]);
    bop := EXTS ((VR[VRB])[i .. i + 31]);
    (VR[VRT])[i..i + 31] :=
      Clamp
        ((bit[32]) (aop + ~ (bop)) + 1,0 - 0b10000000000000000000000000000000,0b10000000000000000000000000000000 -
          1)
  }

union ast member (bit[5], bit[5], bit[5]) Vsububm

function clause decode (0b000100 :
(bit[5]) VRT :
(bit[5]) VRA :
(bit[5]) VRB :
0b10000000000 as instr) =
  Vsububm (VRT,VRA,VRB)

function clause execute (Vsububm (VRT, VRA, VRB)) =
  foreach (i from 0 to 127 by 8 in inc)
  {
    aop := EXTZ ((VR[VRA])[i .. i + 7]);
    bop := EXTZ ((VR[VRB])[i .. i + 7]);
    (VR[VRT])[i..i + 7] := Chop ((bit[32]) (aop + ~ (bop)) + 1,8)
  }

union ast member (bit[5], bit[5], bit[5]) Vsubuhm

function clause decode (0b000100 :
(bit[5]) VRT :
(bit[5]) VRA :
(bit[5]) VRB :
0b10001000000 as instr) =
  Vsubuhm (VRT,VRA,VRB)

function clause execute (Vsubuhm (VRT, VRA, VRB)) =
  foreach (i from 0 to 127 by 16 in inc)
  {
    aop := EXTZ ((VR[VRA])[i .. i + 15]);
    bop := EXTZ ((VR[VRB])[i .. i + 15]);
    (VR[VRT])[i..i + 16] := Chop ((bit[32]) (aop + ~ (bop)) + 1,16)
  }

union ast member (bit[5], bit[5], bit[5]) Vsubuwm

function clause decode (0b000100 :
(bit[5]) VRT :
(bit[5]) VRA :
(bit[5]) VRB :
0b10010000000 as instr) =
  Vsubuwm (VRT,VRA,VRB)

function clause execute (Vsubuwm (VRT, VRA, VRB)) =
  foreach (i from 0 to 127 by 32 in inc)
  {
    aop := EXTZ ((VR[VRA])[i .. i + 31]);
    bop := EXTZ ((VR[VRB])[i .. i + 31]);
    (VR[VRT])[i..i + 31] := Chop ((bit[64]) (aop + ~ (bop)) + 1,32)
  }

union ast member (bit[5], bit[5], bit[5]) Vsububs

function clause decode (0b000100 :
(bit[5]) VRT :
(bit[5]) VRA :
(bit[5]) VRB :
0b11000000000 as instr) =
  Vsububs (VRT,VRA,VRB)

function clause execute (Vsububs (VRT, VRA, VRB)) =
  foreach (i from 0 to 127 by 8 in inc)
  {
    aop := EXTZ ((VR[VRA])[i .. i + 7]);
    bop := EXTZ ((VR[VRB])[i .. i + 7]);
    (VR[VRT])[i..i + 7] :=
      (Clamp ((bit[32]) (aop + ~ (bop)) + 1,0,255))[24 .. 31]
  }

union ast member (bit[5], bit[5], bit[5]) Vsubuhs

function clause decode (0b000100 :
(bit[5]) VRT :
(bit[5]) VRA :
(bit[5]) VRB :
0b11001000000 as instr) =
  Vsubuhs (VRT,VRA,VRB)

function clause execute (Vsubuhs (VRT, VRA, VRB)) =
  foreach (i from 0 to 127 by 16 in inc)
  {
    aop := EXTZ ((VR[VRA])[i .. i + 15]);
    bop := EXTZ ((VR[VRB])[i .. i + 15]);
    (VR[VRT])[i..i + 15] :=
      (Clamp ((bit[32]) (aop + ~ (bop)) + 1,0,0b10000000000000000 - 1))[16 .. 31]
  }

union ast member (bit[5], bit[5], bit[5]) Vsubuws

function clause decode (0b000100 :
(bit[5]) VRT :
(bit[5]) VRA :
(bit[5]) VRB :
0b11010000000 as instr) =
  Vsubuws (VRT,VRA,VRB)

function clause execute (Vsubuws (VRT, VRA, VRB)) =
  foreach (i from 0 to 127 by 32 in inc)
  {
    aop := EXTZ ((VR[VRA])[i .. i + 31]);
    bop := EXTZ ((VR[VRB])[i .. i + 31]);
    (VR[VRT])[i..i + 31] :=
      Clamp
        ((bit[64]) (aop + ~ (bop)) + 1,0,0b100000000000000000000000000000000 - 1)
  }

union ast member (bit[5], bit[5], bit[5]) Vmulesb

function clause decode (0b000100 :
(bit[5]) VRT :
(bit[5]) VRA :
(bit[5]) VRB :
0b01100001000 as instr) =
  Vmulesb (VRT,VRA,VRB)

function clause execute (Vmulesb (VRT, VRA, VRB)) =
  foreach (i from 0 to 127 by 16 in inc)
  {
    prod := EXTS ((VR[VRA])[i .. i + 7]) * EXTS ((VR[VRB])[i .. i + 7]);
    (VR[VRT])[i..i + 15] := Chop (prod,16)
  }

union ast member (bit[5], bit[5], bit[5]) Vmulesh

function clause decode (0b000100 :
(bit[5]) VRT :
(bit[5]) VRA :
(bit[5]) VRB :
0b01101001000 as instr) =
  Vmulesh (VRT,VRA,VRB)

function clause execute (Vmulesh (VRT, VRA, VRB)) =
  foreach (i from 0 to 127 by 32 in inc)
  {
    prod := EXTS ((VR[VRA])[i .. i + 15]) * EXTS ((VR[VRB])[i .. i + 15]);
    (VR[VRT])[i..i + 31] := Chop (prod,32)
  }

union ast member (bit[5], bit[5], bit[5]) Vmuleub

function clause decode (0b000100 :
(bit[5]) VRT :
(bit[5]) VRA :
(bit[5]) VRB :
0b01000001000 as instr) =
  Vmuleub (VRT,VRA,VRB)

function clause execute (Vmuleub (VRT, VRA, VRB)) =
  foreach (i from 0 to 127 by 16 in inc)
  {
    prod := EXTZ ((VR[VRA])[i .. i + 7]) * EXTZ ((VR[VRB])[i .. i + 7]);
    (VR[VRT])[i..i + 15] := Chop (prod,16)
  }

union ast member (bit[5], bit[5], bit[5]) Vmuleuh

function clause decode (0b000100 :
(bit[5]) VRT :
(bit[5]) VRA :
(bit[5]) VRB :
0b01001001000 as instr) =
  Vmuleuh (VRT,VRA,VRB)

function clause execute (Vmuleuh (VRT, VRA, VRB)) =
  foreach (i from 0 to 127 by 32 in inc)
  {
    prod := EXTZ ((VR[VRA])[i .. i + 15]) * EXTZ ((VR[VRB])[i .. i + 15]);
    (VR[VRT])[i..i + 31] := Chop (prod,32)
  }

union ast member (bit[5], bit[5], bit[5]) Vmulosb

function clause decode (0b000100 :
(bit[5]) VRT :
(bit[5]) VRA :
(bit[5]) VRB :
0b00100001000 as instr) =
  Vmulosb (VRT,VRA,VRB)

function clause execute (Vmulosb (VRT, VRA, VRB)) =
  foreach (i from 0 to 127 by 16 in inc)
  {
    prod :=
      EXTS ((VR[VRA])[i + 8 .. i + 15]) * EXTS ((VR[VRB])[i + 8 .. i + 15]);
    (VR[VRT])[i..i + 15] := Chop (prod,16)
  }

union ast member (bit[5], bit[5], bit[5]) Vmulosh

function clause decode (0b000100 :
(bit[5]) VRT :
(bit[5]) VRA :
(bit[5]) VRB :
0b00101001000 as instr) =
  Vmulosh (VRT,VRA,VRB)

function clause execute (Vmulosh (VRT, VRA, VRB)) =
  foreach (i from 0 to 127 by 32 in inc)
  {
    prod :=
      EXTS ((VR[VRA])[i + 16 .. i + 31]) * EXTS ((VR[VRB])[i + 16 .. i + 31]);
    (VR[VRT])[i..i + 31] := Chop (prod,32)
  }

union ast member (bit[5], bit[5], bit[5]) Vmuloub

function clause decode (0b000100 :
(bit[5]) VRT :
(bit[5]) VRA :
(bit[5]) VRB :
0b00000001000 as instr) =
  Vmuloub (VRT,VRA,VRB)

function clause execute (Vmuloub (VRT, VRA, VRB)) =
  foreach (i from 0 to 127 by 16 in inc)
  {
    prod :=
      EXTZ ((VR[VRA])[i + 8 .. i + 15]) * EXTZ ((VR[VRB])[i + 8 .. i + 15]);
    (VR[VRT])[i..i + 15] := Chop (prod,16)
  }

union ast member (bit[5], bit[5], bit[5]) Vmulouh

function clause decode (0b000100 :
(bit[5]) VRT :
(bit[5]) VRA :
(bit[5]) VRB :
0b00001001000 as instr) =
  Vmulouh (VRT,VRA,VRB)

function clause execute (Vmulouh (VRT, VRA, VRB)) =
  foreach (i from 0 to 127 by 32 in inc)
  {
    prod :=
      EXTZ ((VR[VRA])[i + 16 .. i + 31]) * EXTZ ((VR[VRB])[i + 16 .. i + 31]);
    (VR[VRT])[i..i + 31] := Chop (prod,32)
  }

union ast member (bit[5], bit[5], bit[5], bit[5]) Vmhaddshs

function clause decode (0b000100 :
(bit[5]) VRT :
(bit[5]) VRA :
(bit[5]) VRB :
(bit[5]) VRC :
0b100000 as instr) =
  Vmhaddshs (VRT,VRA,VRB,VRC)

function clause execute (Vmhaddshs (VRT, VRA, VRB, VRC)) = ()

union ast member (bit[5], bit[5], bit[5], bit[5]) Vmhraddshs

function clause decode (0b000100 :
(bit[5]) VRT :
(bit[5]) VRA :
(bit[5]) VRB :
(bit[5]) VRC :
0b100001 as instr) =
  Vmhraddshs (VRT,VRA,VRB,VRC)

function clause execute (Vmhraddshs (VRT, VRA, VRB, VRC)) = ()

union ast member (bit[5], bit[5], bit[5], bit[5]) Vmladduhm

function clause decode (0b000100 :
(bit[5]) VRT :
(bit[5]) VRA :
(bit[5]) VRB :
(bit[5]) VRC :
0b100010 as instr) =
  Vmladduhm (VRT,VRA,VRB,VRC)

function clause execute (Vmladduhm (VRT, VRA, VRB, VRC)) =
  {
    (bit[16]) prod := 0;
    (bit[16]) sum := 0;
    foreach (i from 0 to 127 by 16 in inc)
    {
      prod := EXTZ ((VR[VRA])[i .. i + 15]) * EXTZ ((VR[VRB])[i .. i + 15]);
      sum := Chop (prod,16) + (VR[VRC])[i .. i + 15];
      (VR[VRT])[i..i + 15] := Chop (sum,16)
    }
  }

union ast member (bit[5], bit[5], bit[5], bit[5]) Vmsumubm

function clause decode (0b000100 :
(bit[5]) VRT :
(bit[5]) VRA :
(bit[5]) VRB :
(bit[5]) VRC :
0b100100 as instr) =
  Vmsumubm (VRT,VRA,VRB,VRC)

function clause execute (Vmsumubm (VRT, VRA, VRB, VRC)) =
  foreach (i from 0 to 127 by 32 in inc)
  {
    temp := EXTZ ((VR[VRC])[i .. i + 31]);
    foreach (j from 0 to 31 by 8 in inc)
    {
      prod :=
        EXTZ ((VR[VRA])[i + j .. i + j + 7]) *
          EXTZ ((VR[VRB])[i + j .. i + j + 7]);
      temp := temp + prod
    };
    (VR[VRT])[i..i + 31] := Chop (temp,32)
  }

union ast member (bit[5], bit[5], bit[5], bit[5]) Vmsummbm

function clause decode (0b000100 :
(bit[5]) VRT :
(bit[5]) VRA :
(bit[5]) VRB :
(bit[5]) VRC :
0b100101 as instr) =
  Vmsummbm (VRT,VRA,VRB,VRC)

function clause execute (Vmsummbm (VRT, VRA, VRB, VRC)) = ()

union ast member (bit[5], bit[5], bit[5], bit[5]) Vmsumshm

function clause decode (0b000100 :
(bit[5]) VRT :
(bit[5]) VRA :
(bit[5]) VRB :
(bit[5]) VRC :
0b101000 as instr) =
  Vmsumshm (VRT,VRA,VRB,VRC)

function clause execute (Vmsumshm (VRT, VRA, VRB, VRC)) = ()

union ast member (bit[5], bit[5], bit[5], bit[5]) Vmsumshs

function clause decode (0b000100 :
(bit[5]) VRT :
(bit[5]) VRA :
(bit[5]) VRB :
(bit[5]) VRC :
0b101001 as instr) =
  Vmsumshs (VRT,VRA,VRB,VRC)

function clause execute (Vmsumshs (VRT, VRA, VRB, VRC)) =
  foreach (i from 0 to 127 by 32 in inc)
  {
    temp := EXTS ((VR[VRC])[i .. i + 31]);
    foreach (j from 0 to 31 by 16 in inc)
    {
      prod :=
        EXTS ((VR[VRA])[i + j .. i + j + 15]) *
          EXTS ((VR[VRB])[i + j .. i + j + 15]);
      temp := temp + prod
    };
    (VR[VRT])[i..i + 31] :=
      Clamp
        (temp,0 - 0b10000000000000000000000000000000,0b10000000000000000000000000000000 -
          1)
  }

union ast member (bit[5], bit[5], bit[5], bit[5]) Vmsumuhm

function clause decode (0b000100 :
(bit[5]) VRT :
(bit[5]) VRA :
(bit[5]) VRB :
(bit[5]) VRC :
0b100110 as instr) =
  Vmsumuhm (VRT,VRA,VRB,VRC)

function clause execute (Vmsumuhm (VRT, VRA, VRB, VRC)) =
  foreach (i from 0 to 127 by 32 in inc)
  {
    temp := EXTZ ((VR[VRC])[i .. i + 31]);
    foreach (j from 0 to 31 by 16 in inc)
    {
      prod :=
        EXTZ ((VR[VRA])[i + j .. i + j + 15]) *
          EXTZ ((VR[VRB])[i + j .. i + j + 15]);
      temp := temp + prod
    };
    (VR[VRT])[i..i + 31] := Chop (temp,32)
  }

union ast member (bit[5], bit[5], bit[5], bit[5]) Vmsumuhs

function clause decode (0b000100 :
(bit[5]) VRT :
(bit[5]) VRA :
(bit[5]) VRB :
(bit[5]) VRC :
0b100111 as instr) =
  Vmsumuhs (VRT,VRA,VRB,VRC)

function clause execute (Vmsumuhs (VRT, VRA, VRB, VRC)) =
  foreach (i from 0 to 127 by 32 in inc)
  {
    temp := EXTZ ((VR[VRC])[i .. i + 31]);
    foreach (j from 0 to 31 by 16 in inc)
    {
      prod :=
        EXTZ ((VR[VRA])[i + j .. i + j + 15]) *
          EXTZ ((VR[VRB])[i + j .. i + j + 15]);
      temp := temp + prod
    };
    (VR[VRT])[i..i + 31] :=
      Clamp (temp,0,0b100000000000000000000000000000000 - 1)
  }

union ast member (bit[5], bit[5], bit[5]) Vsumsws

function clause decode (0b000100 :
(bit[5]) VRT :
(bit[5]) VRA :
(bit[5]) VRB :
0b11110001000 as instr) =
  Vsumsws (VRT,VRA,VRB)

function clause execute (Vsumsws (VRT, VRA, VRB)) =
  {
    temp := EXTS ((VR[VRB])[96 .. 127]);
    foreach (i from 0 to 127 by 32 in inc)
    temp := temp + EXTS ((VR[VRA])[i .. i + 31]);
    (VR[VRT])[0..31] := 0b00000000000000000000000000000000;
    (VR[VRT])[32..63] := 0b00000000000000000000000000000000;
    (VR[VRT])[64..95] := 0b00000000000000000000000000000000;
    (VR[VRT])[96..127] :=
      Clamp
        (temp,0 - 0b10000000000000000000000000000000,0b10000000000000000000000000000000 -
          1)
  }

union ast member (bit[5], bit[5], bit[5]) Vsum2sws

function clause decode (0b000100 :
(bit[5]) VRT :
(bit[5]) VRA :
(bit[5]) VRB :
0b11010001000 as instr) =
  Vsum2sws (VRT,VRA,VRB)

function clause execute (Vsum2sws (VRT, VRA, VRB)) =
  foreach (i from 0 to 127 by 64 in inc)
  {
    temp := EXTS ((VR[VRB])[i + 32 .. i + 63]);
    foreach (j from 0 to 63 by 32 in inc)
    temp := temp + EXTS ((VR[VRA])[i + j .. i + j + 31]);
    (VR[VRT])[i..i + 63] :=
      0b00000000000000000000000000000000 :
        Clamp
          (temp,0 - 0b10000000000000000000000000000000,0b10000000000000000000000000000000 -
            1)
  }

union ast member (bit[5], bit[5], bit[5]) Vsum4sbs

function clause decode (0b000100 :
(bit[5]) VRT :
(bit[5]) VRA :
(bit[5]) VRB :
0b11100001000 as instr) =
  Vsum4sbs (VRT,VRA,VRB)

function clause execute (Vsum4sbs (VRT, VRA, VRB)) =
  foreach (i from 0 to 127 by 32 in inc)
  {
    temp := EXTS ((VR[VRB])[i .. i + 31]);
    foreach (j from 0 to 31 by 8 in inc)
    temp := temp + EXTS ((VR[VRA])[i + j .. i + j + 7]);
    (VR[VRT])[i..i + 31] :=
      Clamp
        (temp,0 - 0b10000000000000000000000000000000,0b10000000000000000000000000000000 -
          1)
  }

union ast member (bit[5], bit[5], bit[5]) Vsum4shs

function clause decode (0b000100 :
(bit[5]) VRT :
(bit[5]) VRA :
(bit[5]) VRB :
0b11001001000 as instr) =
  Vsum4shs (VRT,VRA,VRB)

function clause execute (Vsum4shs (VRT, VRA, VRB)) =
  foreach (i from 0 to 127 by 32 in inc)
  {
    temp := EXTS ((VR[VRB])[i .. i + 31]);
    foreach (j from 0 to 31 by 16 in inc)
    temp := temp + EXTS ((VR[VRA])[i + j .. i + j + 15]);
    (VR[VRT])[i..i + 31] :=
      Clamp
        (temp,0 - 0b10000000000000000000000000000000,0b10000000000000000000000000000000 -
          1)
  }

union ast member (bit[5], bit[5], bit[5]) Vsum4ubs

function clause decode (0b000100 :
(bit[5]) VRT :
(bit[5]) VRA :
(bit[5]) VRB :
0b11000001000 as instr) =
  Vsum4ubs (VRT,VRA,VRB)

function clause execute (Vsum4ubs (VRT, VRA, VRB)) =
  foreach (i from 0 to 127 by 32 in inc)
  {
    temp := EXTZ ((VR[VRB])[i .. i + 31]);
    foreach (j from 0 to 31 by 8 in inc)
    temp := temp + EXTZ ((VR[VRA])[i + j .. i + j + 7]);
    (VR[VRT])[i..i + 31] :=
      Clamp (temp,0,0b100000000000000000000000000000000 - 1)
  }

union ast member (bit[5], bit[5], bit[5]) Vavgsb

function clause decode (0b000100 :
(bit[5]) VRT :
(bit[5]) VRA :
(bit[5]) VRB :
0b10100000010 as instr) =
  Vavgsb (VRT,VRA,VRB)

function clause execute (Vavgsb (VRT, VRA, VRB)) =
  foreach (i from 0 to 127 by 8 in inc)
  {
    aop := EXTS ((VR[VRA])[i .. i + 7]);
    bop := EXTS ((VR[VRB])[i .. i + 7]);
    (VR[VRT])[i..i + 7] := Chop ((bit[32]) (aop + bop) + 1 >> 1,8)
  }

union ast member (bit[5], bit[5], bit[5]) Vavgsh

function clause decode (0b000100 :
(bit[5]) VRT :
(bit[5]) VRA :
(bit[5]) VRB :
0b10101000010 as instr) =
  Vavgsh (VRT,VRA,VRB)

function clause execute (Vavgsh (VRT, VRA, VRB)) =
  foreach (i from 0 to 127 by 16 in inc)
  {
    aop := EXTS ((VR[VRA])[i .. i + 15]);
    bop := EXTS ((VR[VRB])[i .. i + 15]);
    (VR[VRT])[i..i + 15] := Chop ((bit[32]) (aop + bop) + 1 >> 1,16)
  }

union ast member (bit[5], bit[5], bit[5]) Vavgsw

function clause decode (0b000100 :
(bit[5]) VRT :
(bit[5]) VRA :
(bit[5]) VRB :
0b10110000010 as instr) =
  Vavgsw (VRT,VRA,VRB)

function clause execute (Vavgsw (VRT, VRA, VRB)) =
  foreach (i from 0 to 127 by 32 in inc)
  {
    aop := EXTS ((VR[VRA])[i .. i + 31]);
    bop := EXTS ((VR[VRB])[i .. i + 31]);
    (VR[VRT])[i..i + 31] := Chop ((bit[32]) (aop + bop) + 1 >> 1,32)
  }

union ast member (bit[5], bit[5], bit[5]) Vavgub

function clause decode (0b000100 :
(bit[5]) VRT :
(bit[5]) VRA :
(bit[5]) VRB :
0b10000000010 as instr) =
  Vavgub (VRT,VRA,VRB)

function clause execute (Vavgub (VRT, VRA, VRB)) = ()

union ast member (bit[5], bit[5], bit[5]) Vavguh

function clause decode (0b000100 :
(bit[5]) VRT :
(bit[5]) VRA :
(bit[5]) VRB :
0b10001000010 as instr) =
  Vavguh (VRT,VRA,VRB)

function clause execute (Vavguh (VRT, VRA, VRB)) =
  foreach (i from 0 to 127 by 16 in inc)
  {
    aop := EXTZ ((VR[VRA])[i .. i + 15]);
    bop := EXTZ ((VR[VRB])[i .. i + 15]);
    (VR[VRT])[i..i + 15] := Chop ((bit[32]) (aop + bop) + 1 >> 1,16)
  }

union ast member (bit[5], bit[5], bit[5]) Vavguw

function clause decode (0b000100 :
(bit[5]) VRT :
(bit[5]) VRA :
(bit[5]) VRB :
0b10010000010 as instr) =
  Vavguw (VRT,VRA,VRB)

function clause execute (Vavguw (VRT, VRA, VRB)) =
  foreach (i from 0 to 127 by 32 in inc)
  {
    aop := EXTZ ((VR[VRA])[i .. i + 31]);
    bop := EXTZ ((VR[VRB])[i .. i + 31]);
    (VR[VRT])[i..i + 31] := Chop ((bit[32]) (aop + bop) + 1 >> 1,32)
  }

union ast member (bit[5], bit[5], bit[5]) Vmaxsb

function clause decode (0b000100 :
(bit[5]) VRT :
(bit[5]) VRA :
(bit[5]) VRB :
0b00100000010 as instr) =
  Vmaxsb (VRT,VRA,VRB)

function clause execute (Vmaxsb (VRT, VRA, VRB)) = ()

union ast member (bit[5], bit[5], bit[5]) Vmaxsh

function clause decode (0b000100 :
(bit[5]) VRT :
(bit[5]) VRA :
(bit[5]) VRB :
0b00101000010 as instr) =
  Vmaxsh (VRT,VRA,VRB)

function clause execute (Vmaxsh (VRT, VRA, VRB)) = ()

union ast member (bit[5], bit[5], bit[5]) Vmaxsw

function clause decode (0b000100 :
(bit[5]) VRT :
(bit[5]) VRA :
(bit[5]) VRB :
0b00110000010 as instr) =
  Vmaxsw (VRT,VRA,VRB)

function clause execute (Vmaxsw (VRT, VRA, VRB)) = ()

union ast member (bit[5], bit[5], bit[5]) Vmaxub

function clause decode (0b000100 :
(bit[5]) VRT :
(bit[5]) VRA :
(bit[5]) VRB :
0b00000000010 as instr) =
  Vmaxub (VRT,VRA,VRB)

function clause execute (Vmaxub (VRT, VRA, VRB)) = ()

union ast member (bit[5], bit[5], bit[5]) Vmaxuh

function clause decode (0b000100 :
(bit[5]) VRT :
(bit[5]) VRA :
(bit[5]) VRB :
0b00001000010 as instr) =
  Vmaxuh (VRT,VRA,VRB)

function clause execute (Vmaxuh (VRT, VRA, VRB)) = ()

union ast member (bit[5], bit[5], bit[5]) Vmaxuw

function clause decode (0b000100 :
(bit[5]) VRT :
(bit[5]) VRA :
(bit[5]) VRB :
0b00010000010 as instr) =
  Vmaxuw (VRT,VRA,VRB)

function clause execute (Vmaxuw (VRT, VRA, VRB)) = ()

union ast member (bit[5], bit[5], bit[5]) Vminsb

function clause decode (0b000100 :
(bit[5]) VRT :
(bit[5]) VRA :
(bit[5]) VRB :
0b01100000010 as instr) =
  Vminsb (VRT,VRA,VRB)

function clause execute (Vminsb (VRT, VRA, VRB)) = ()

union ast member (bit[5], bit[5], bit[5]) Vminsh

function clause decode (0b000100 :
(bit[5]) VRT :
(bit[5]) VRA :
(bit[5]) VRB :
0b01101000010 as instr) =
  Vminsh (VRT,VRA,VRB)

function clause execute (Vminsh (VRT, VRA, VRB)) = ()

union ast member (bit[5], bit[5], bit[5]) Vminsw

function clause decode (0b000100 :
(bit[5]) VRT :
(bit[5]) VRA :
(bit[5]) VRB :
0b01110000010 as instr) =
  Vminsw (VRT,VRA,VRB)

function clause execute (Vminsw (VRT, VRA, VRB)) = ()

union ast member (bit[5], bit[5], bit[5]) Vminub

function clause decode (0b000100 :
(bit[5]) VRT :
(bit[5]) VRA :
(bit[5]) VRB :
0b01000000010 as instr) =
  Vminub (VRT,VRA,VRB)

function clause execute (Vminub (VRT, VRA, VRB)) = ()

union ast member (bit[5], bit[5], bit[5]) Vminuh

function clause decode (0b000100 :
(bit[5]) VRT :
(bit[5]) VRA :
(bit[5]) VRB :
0b01001000010 as instr) =
  Vminuh (VRT,VRA,VRB)

function clause execute (Vminuh (VRT, VRA, VRB)) = ()

union ast member (bit[5], bit[5], bit[5]) Vminuw

function clause decode (0b000100 :
(bit[5]) VRT :
(bit[5]) VRA :
(bit[5]) VRB :
0b01010000010 as instr) =
  Vminuw (VRT,VRA,VRB)

function clause execute (Vminuw (VRT, VRA, VRB)) = ()

union ast member (bit[5], bit[5], bit[5], bit) Vcmpequb

function clause decode (0b000100 :
(bit[5]) VRT :
(bit[5]) VRA :
(bit[5]) VRB :
[Rc] :
0b0000000110 as instr) =
  Vcmpequb (VRT,VRA,VRB,Rc)

function clause execute (Vcmpequb (VRT, VRA, VRB, Rc)) = ()

union ast member (bit[5], bit[5], bit[5], bit) Vcmpequh

function clause decode (0b000100 :
(bit[5]) VRT :
(bit[5]) VRA :
(bit[5]) VRB :
[Rc] :
0b0001000110 as instr) =
  Vcmpequh (VRT,VRA,VRB,Rc)

function clause execute (Vcmpequh (VRT, VRA, VRB, Rc)) = ()

union ast member (bit[5], bit[5], bit[5], bit) Vcmpequw

function clause decode (0b000100 :
(bit[5]) VRT :
(bit[5]) VRA :
(bit[5]) VRB :
[Rc] :
0b0010000110 as instr) =
  Vcmpequw (VRT,VRA,VRB,Rc)

function clause execute (Vcmpequw (VRT, VRA, VRB, Rc)) = ()

union ast member (bit[5], bit[5], bit[5], bit) Vcmpgtsb

function clause decode (0b000100 :
(bit[5]) VRT :
(bit[5]) VRA :
(bit[5]) VRB :
[Rc] :
0b1100000110 as instr) =
  Vcmpgtsb (VRT,VRA,VRB,Rc)

function clause execute (Vcmpgtsb (VRT, VRA, VRB, Rc)) = ()

union ast member (bit[5], bit[5], bit[5], bit) Vcmpgtsh

function clause decode (0b000100 :
(bit[5]) VRT :
(bit[5]) VRA :
(bit[5]) VRB :
[Rc] :
0b1101000110 as instr) =
  Vcmpgtsh (VRT,VRA,VRB,Rc)

function clause execute (Vcmpgtsh (VRT, VRA, VRB, Rc)) = ()

union ast member (bit[5], bit[5], bit[5], bit) Vcmpgtsw

function clause decode (0b000100 :
(bit[5]) VRT :
(bit[5]) VRA :
(bit[5]) VRB :
[Rc] :
0b1110000110 as instr) =
  Vcmpgtsw (VRT,VRA,VRB,Rc)

function clause execute (Vcmpgtsw (VRT, VRA, VRB, Rc)) = ()

union ast member (bit[5], bit[5], bit[5], bit) Vcmpgtub

function clause decode (0b000100 :
(bit[5]) VRT :
(bit[5]) VRA :
(bit[5]) VRB :
[Rc] :
0b1000000110 as instr) =
  Vcmpgtub (VRT,VRA,VRB,Rc)

function clause execute (Vcmpgtub (VRT, VRA, VRB, Rc)) = ()

union ast member (bit[5], bit[5], bit[5], bit) Vcmpgtuh

function clause decode (0b000100 :
(bit[5]) VRT :
(bit[5]) VRA :
(bit[5]) VRB :
[Rc] :
0b1001000110 as instr) =
  Vcmpgtuh (VRT,VRA,VRB,Rc)

function clause execute (Vcmpgtuh (VRT, VRA, VRB, Rc)) = ()

union ast member (bit[5], bit[5], bit[5], bit) Vcmpgtuw

function clause decode (0b000100 :
(bit[5]) VRT :
(bit[5]) VRA :
(bit[5]) VRB :
[Rc] :
0b1010000110 as instr) =
  Vcmpgtuw (VRT,VRA,VRB,Rc)

function clause execute (Vcmpgtuw (VRT, VRA, VRB, Rc)) = ()

union ast member (bit[5], bit[5], bit[5]) Vand

function clause decode (0b000100 :
(bit[5]) VRT :
(bit[5]) VRA :
(bit[5]) VRB :
0b10000000100 as instr) =
  Vand (VRT,VRA,VRB)

function clause execute (Vand (VRT, VRA, VRB)) = VR[VRT] := (VR[VRA] & VR[VRB])

union ast member (bit[5], bit[5], bit[5]) Vandc

function clause decode (0b000100 :
(bit[5]) VRT :
(bit[5]) VRA :
(bit[5]) VRB :
0b10001000100 as instr) =
  Vandc (VRT,VRA,VRB)

function clause execute (Vandc (VRT, VRA, VRB)) =
  VR[VRT] := (VR[VRA] & ~ (VR[VRB]))

union ast member (bit[5], bit[5], bit[5]) Vnor

function clause decode (0b000100 :
(bit[5]) VRT :
(bit[5]) VRA :
(bit[5]) VRB :
0b10100000100 as instr) =
  Vnor (VRT,VRA,VRB)

function clause execute (Vnor (VRT, VRA, VRB)) =
  VR[VRT] := ~ (VR[VRA] | VR[VRB])

union ast member (bit[5], bit[5], bit[5]) Vor

function clause decode (0b000100 :
(bit[5]) VRT :
(bit[5]) VRA :
(bit[5]) VRB :
0b10010000100 as instr) =
  Vor (VRT,VRA,VRB)

function clause execute (Vor (VRT, VRA, VRB)) = VR[VRT] := (VR[VRA] | VR[VRB])

union ast member (bit[5], bit[5], bit[5]) Vxor

function clause decode (0b000100 :
(bit[5]) VRT :
(bit[5]) VRA :
(bit[5]) VRB :
0b10011000100 as instr) =
  Vxor (VRT,VRA,VRB)

function clause execute (Vxor (VRT, VRA, VRB)) = VR[VRT] := VR[VRA] ^ VR[VRB]

union ast member (bit[5], bit[5], bit[5]) Vrlb

function clause decode (0b000100 :
(bit[5]) VRT :
(bit[5]) VRA :
(bit[5]) VRB :
0b00000000100 as instr) =
  Vrlb (VRT,VRA,VRB)

function clause execute (Vrlb (VRT, VRA, VRB)) =
  foreach (i from 0 to 127 by 8 in inc)
  {
    sh := (VR[VRB])[i + 5 .. i + 7];
    (VR[VRT])[i..i + 7] := (VR[VRA])[i .. i + 7] << sh
  }

union ast member (bit[5], bit[5], bit[5]) Vrlh

function clause decode (0b000100 :
(bit[5]) VRT :
(bit[5]) VRA :
(bit[5]) VRB :
0b00001000100 as instr) =
  Vrlh (VRT,VRA,VRB)

function clause execute (Vrlh (VRT, VRA, VRB)) =
  foreach (i from 0 to 127 by 16 in inc)
  {
    sh := (VR[VRB])[i + 12 .. i + 15];
    (VR[VRT])[i..i + 15] := (VR[VRA])[i .. i + 15] << sh
  }

union ast member (bit[5], bit[5], bit[5]) Vrlw

function clause decode (0b000100 :
(bit[5]) VRT :
(bit[5]) VRA :
(bit[5]) VRB :
0b00010000100 as instr) =
  Vrlw (VRT,VRA,VRB)

function clause execute (Vrlw (VRT, VRA, VRB)) =
  foreach (i from 0 to 127 by 32 in inc)
  {
    sh := (VR[VRB])[i + 27 .. i + 31];
    (VR[VRT])[i..i + 31] := (VR[VRA])[i .. i + 31] << sh
  }

union ast member (bit[5], bit[5], bit[5]) Vslb

function clause decode (0b000100 :
(bit[5]) VRT :
(bit[5]) VRA :
(bit[5]) VRB :
0b00100000100 as instr) =
  Vslb (VRT,VRA,VRB)

function clause execute (Vslb (VRT, VRA, VRB)) =
  foreach (i from 0 to 127 by 8 in inc)
  {
    sh := (VR[VRB])[i + 5 .. i + 7];
    (VR[VRT])[i..i + 7] := (VR[VRA])[i .. i + 7] << sh
  }

union ast member (bit[5], bit[5], bit[5]) Vslh

function clause decode (0b000100 :
(bit[5]) VRT :
(bit[5]) VRA :
(bit[5]) VRB :
0b00101000100 as instr) =
  Vslh (VRT,VRA,VRB)

function clause execute (Vslh (VRT, VRA, VRB)) =
  foreach (i from 0 to 127 by 16 in inc)
  {
    sh := (VR[VRB])[i + 12 .. i + 15];
    (VR[VRT])[i..i + 15] := (VR[VRA])[i .. i + 15] << sh
  }

union ast member (bit[5], bit[5], bit[5]) Vslw

function clause decode (0b000100 :
(bit[5]) VRT :
(bit[5]) VRA :
(bit[5]) VRB :
0b00110000100 as instr) =
  Vslw (VRT,VRA,VRB)

function clause execute (Vslw (VRT, VRA, VRB)) =
  foreach (i from 0 to 127 by 32 in inc)
  {
    sh := (VR[VRB])[i + 27 .. i + 31];
    (VR[VRT])[i..i + 31] := (VR[VRA])[i .. i + 31] << sh
  }

union ast member (bit[5], bit[5], bit[5]) Vsrb

function clause decode (0b000100 :
(bit[5]) VRT :
(bit[5]) VRA :
(bit[5]) VRB :
0b01000000100 as instr) =
  Vsrb (VRT,VRA,VRB)

function clause execute (Vsrb (VRT, VRA, VRB)) =
  foreach (i from 0 to 127 by 8 in inc)
  {
    sh := (VR[VRB])[i + 5 .. i + 7];
    (VR[VRT])[i..i + 7] := (VR[VRA])[i .. i + 7] >> sh
  }

union ast member (bit[5], bit[5], bit[5]) Vsrh

function clause decode (0b000100 :
(bit[5]) VRT :
(bit[5]) VRA :
(bit[5]) VRB :
0b01001000100 as instr) =
  Vsrh (VRT,VRA,VRB)

function clause execute (Vsrh (VRT, VRA, VRB)) =
  foreach (i from 0 to 127 by 16 in inc)
  {
    sh := (VR[VRB])[i + 12 .. i + 15];
    (VR[VRT])[i..i + 15] := (VR[VRA])[i .. i + 15] >> sh
  }

union ast member (bit[5], bit[5], bit[5]) Vsrw

function clause decode (0b000100 :
(bit[5]) VRT :
(bit[5]) VRA :
(bit[5]) VRB :
0b01010000100 as instr) =
  Vsrw (VRT,VRA,VRB)

function clause execute (Vsrw (VRT, VRA, VRB)) =
  foreach (i from 0 to 127 by 32 in inc)
  {
    sh := (VR[VRB])[i + 27 .. i + 31];
    (VR[VRT])[i..i + 31] := (VR[VRA])[i .. i + 31] >> sh
  }

union ast member (bit[5], bit[5], bit[5]) Vsrab

function clause decode (0b000100 :
(bit[5]) VRT :
(bit[5]) VRA :
(bit[5]) VRB :
0b01100000100 as instr) =
  Vsrab (VRT,VRA,VRB)

function clause execute (Vsrab (VRT, VRA, VRB)) = ()

union ast member (bit[5], bit[5], bit[5]) Vsrah

function clause decode (0b000100 :
(bit[5]) VRT :
(bit[5]) VRA :
(bit[5]) VRB :
0b01101000100 as instr) =
  Vsrah (VRT,VRA,VRB)

function clause execute (Vsrah (VRT, VRA, VRB)) = ()

union ast member (bit[5], bit[5], bit[5]) Vsraw

function clause decode (0b000100 :
(bit[5]) VRT :
(bit[5]) VRA :
(bit[5]) VRB :
0b01110000100 as instr) =
  Vsraw (VRT,VRA,VRB)

function clause execute (Vsraw (VRT, VRA, VRB)) = ()

union ast member (bit[5], bit[5], bit[5]) Vaddfp

function clause decode (0b000100 :
(bit[5]) VRT :
(bit[5]) VRA :
(bit[5]) VRB :
0b00000001010 as instr) =
  Vaddfp (VRT,VRA,VRB)

function clause execute (Vaddfp (VRT, VRA, VRB)) = ()

union ast member (bit[5], bit[5], bit[5]) Vsubfp

function clause decode (0b000100 :
(bit[5]) VRT :
(bit[5]) VRA :
(bit[5]) VRB :
0b00001001010 as instr) =
  Vsubfp (VRT,VRA,VRB)

function clause execute (Vsubfp (VRT, VRA, VRB)) = ()

union ast member (bit[5], bit[5], bit[5], bit[5]) Vmaddfp

function clause decode (0b000100 :
(bit[5]) VRT :
(bit[5]) VRA :
(bit[5]) VRB :
(bit[5]) VRC :
0b101110 as instr) =
  Vmaddfp (VRT,VRA,VRB,VRC)

function clause execute (Vmaddfp (VRT, VRA, VRB, VRC)) = ()

union ast member (bit[5], bit[5], bit[5], bit[5]) Vnmsubfp

function clause decode (0b000100 :
(bit[5]) VRT :
(bit[5]) VRA :
(bit[5]) VRB :
(bit[5]) VRC :
0b101111 as instr) =
  Vnmsubfp (VRT,VRA,VRB,VRC)

function clause execute (Vnmsubfp (VRT, VRA, VRB, VRC)) = ()

union ast member (bit[5], bit[5], bit[5]) Vmaxfp

function clause decode (0b000100 :
(bit[5]) VRT :
(bit[5]) VRA :
(bit[5]) VRB :
0b10000001010 as instr) =
  Vmaxfp (VRT,VRA,VRB)

function clause execute (Vmaxfp (VRT, VRA, VRB)) = ()

union ast member (bit[5], bit[5], bit[5]) Vminfp

function clause decode (0b000100 :
(bit[5]) VRT :
(bit[5]) VRA :
(bit[5]) VRB :
0b10001001010 as instr) =
  Vminfp (VRT,VRA,VRB)

function clause execute (Vminfp (VRT, VRA, VRB)) = ()

union ast member (bit[5], bit[5], bit[5]) Vctsxs

function clause decode (0b000100 :
(bit[5]) VRT :
(bit[5]) UIM :
(bit[5]) VRB :
0b01111001010 as instr) =
  Vctsxs (VRT,UIM,VRB)

function clause execute (Vctsxs (VRT, UIM, VRB)) =
  foreach (i from 0 to 127 by 32 in inc)
  (VR[VRT])[i..i + 31] := ConvertSPtoSXWsaturate ((VR[VRB])[i .. i + 31],UIM)

union ast member (bit[5], bit[5], bit[5]) Vctuxs

function clause decode (0b000100 :
(bit[5]) VRT :
(bit[5]) UIM :
(bit[5]) VRB :
0b01110001010 as instr) =
  Vctuxs (VRT,UIM,VRB)

function clause execute (Vctuxs (VRT, UIM, VRB)) =
  foreach (i from 0 to 127 by 32 in inc)
  (VR[VRT])[i..i + 31] := ConvertSPtoUXWsaturate ((VR[VRB])[i .. i + 31],UIM)

union ast member (bit[5], bit[5], bit[5]) Vcfsx

function clause decode (0b000100 :
(bit[5]) VRT :
(bit[5]) UIM :
(bit[5]) VRB :
0b01101001010 as instr) =
  Vcfsx (VRT,UIM,VRB)

function clause execute (Vcfsx (VRT, UIM, VRB)) = ()

union ast member (bit[5], bit[5], bit[5]) Vcfux

function clause decode (0b000100 :
(bit[5]) VRT :
(bit[5]) UIM :
(bit[5]) VRB :
0b01100001010 as instr) =
  Vcfux (VRT,UIM,VRB)

function clause execute (Vcfux (VRT, UIM, VRB)) = ()

union ast member (bit[5], bit[5]) Vrfim

function clause decode (0b000100 :
(bit[5]) VRT :
(bit[5]) _ :
(bit[5]) VRB :
0b01011001010 as instr) =
  Vrfim (VRT,VRB)

function clause execute (Vrfim (VRT, VRB)) =
  foreach (i from 0 to 127 by 32 in inc)
  (VR[VRT])[0..31] := RoundToSPIntFloor ((VR[VRB])[0 .. 31])

union ast member (bit[5], bit[5]) Vrfin

function clause decode (0b000100 :
(bit[5]) VRT :
(bit[5]) _ :
(bit[5]) VRB :
0b01000001010 as instr) =
  Vrfin (VRT,VRB)

function clause execute (Vrfin (VRT, VRB)) =
  foreach (i from 0 to 127 by 32 in inc)
  (VR[VRT])[0..31] := RoundToSPIntNear ((VR[VRB])[0 .. 31])

union ast member (bit[5], bit[5]) Vrfip

function clause decode (0b000100 :
(bit[5]) VRT :
(bit[5]) _ :
(bit[5]) VRB :
0b01010001010 as instr) =
  Vrfip (VRT,VRB)

function clause execute (Vrfip (VRT, VRB)) =
  foreach (i from 0 to 127 by 32 in inc)
  (VR[VRT])[0..31] := RoundToSPIntCeil ((VR[VRB])[0 .. 31])

union ast member (bit[5], bit[5]) Vrfiz

function clause decode (0b000100 :
(bit[5]) VRT :
(bit[5]) _ :
(bit[5]) VRB :
0b01001001010 as instr) =
  Vrfiz (VRT,VRB)

function clause execute (Vrfiz (VRT, VRB)) =
  foreach (i from 0 to 127 by 32 in inc)
  (VR[VRT])[0..31] := RoundToSPIntTrunc ((VR[VRB])[0 .. 31])

union ast member (bit[5], bit[5], bit[5], bit) Vcmpbfp

function clause decode (0b000100 :
(bit[5]) VRT :
(bit[5]) VRA :
(bit[5]) VRB :
[Rc] :
0b1111000110 as instr) =
  Vcmpbfp (VRT,VRA,VRB,Rc)

function clause execute (Vcmpbfp (VRT, VRA, VRB, Rc)) = ()

union ast member (bit[5], bit[5], bit[5], bit) Vcmpeqfp

function clause decode (0b000100 :
(bit[5]) VRT :
(bit[5]) VRA :
(bit[5]) VRB :
[Rc] :
0b0011000110 as instr) =
  Vcmpeqfp (VRT,VRA,VRB,Rc)

function clause execute (Vcmpeqfp (VRT, VRA, VRB, Rc)) = ()

union ast member (bit[5], bit[5], bit[5], bit) Vcmpgefp

function clause decode (0b000100 :
(bit[5]) VRT :
(bit[5]) VRA :
(bit[5]) VRB :
[Rc] :
0b0111000110 as instr) =
  Vcmpgefp (VRT,VRA,VRB,Rc)

function clause execute (Vcmpgefp (VRT, VRA, VRB, Rc)) = ()

union ast member (bit[5], bit[5], bit[5], bit) Vcmpgtfp

function clause decode (0b000100 :
(bit[5]) VRT :
(bit[5]) VRA :
(bit[5]) VRB :
[Rc] :
0b1011000110 as instr) =
  Vcmpgtfp (VRT,VRA,VRB,Rc)

function clause execute (Vcmpgtfp (VRT, VRA, VRB, Rc)) = ()

union ast member (bit[5], bit[5]) Vexptefp

function clause decode (0b000100 :
(bit[5]) VRT :
(bit[5]) _ :
(bit[5]) VRB :
0b00110001010 as instr) =
  Vexptefp (VRT,VRB)

function clause execute (Vexptefp (VRT, VRB)) =
  foreach (i from 0 to 127 by 32 in inc)
  (VR[VRT])[i..i + 31] := Power2EstimateSP ((VR[VRB])[i .. i + 31])

union ast member (bit[5], bit[5]) Vlogefp

function clause decode (0b000100 :
(bit[5]) VRT :
(bit[5]) _ :
(bit[5]) VRB :
0b00111001010 as instr) =
  Vlogefp (VRT,VRB)

function clause execute (Vlogefp (VRT, VRB)) =
  foreach (i from 0 to 127 by 32 in inc)
  (VR[VRT])[i..i + 31] := LogBase2EstimateSP ((VR[VRB])[i .. i + 31])

union ast member (bit[5], bit[5]) Vrefp

function clause decode (0b000100 :
(bit[5]) VRT :
(bit[5]) _ :
(bit[5]) VRB :
0b00100001010 as instr) =
  Vrefp (VRT,VRB)

function clause execute (Vrefp (VRT, VRB)) =
  foreach (i from 0 to 127 by 32 in inc)
  (VR[VRT])[i..i + 31] := ReciprocalEstimateSP ((VR[VRB])[i .. i + 31])

union ast member (bit[5], bit[5]) Vrsqrtefp

function clause decode (0b000100 :
(bit[5]) VRT :
(bit[5]) _ :
(bit[5]) VRB :
0b00101001010 as instr) =
  Vrsqrtefp (VRT,VRB)

function clause execute (Vrsqrtefp (VRT, VRB)) =
  foreach (i from 0 to 127 by 32 in inc)
  (VR[VRT])[i..i + 31] :=
    ReciprocalSquareRootEstimateSP ((VR[VRB])[i .. i + 31])

union ast member (bit[5]) Mtvscr

function clause decode (0b000100 :
(bit[10]) _ :
(bit[5]) VRB :
0b11001000100 as instr) =
  Mtvscr (VRB)

function clause execute (Mtvscr (VRB)) = VSCR := (VR[VRB])[96 .. 127]

union ast member (bit[5]) Mfvscr

function clause decode (0b000100 :
(bit[5]) VRT :
(bit[10]) _ :
0b11000000100 as instr) =
  Mfvscr (VRT)

function clause execute (Mfvscr (VRT)) =
  VR[VRT] :=
    0b000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :
      VSCR

union ast member (bit[5], bit[5], bit[5], bit) Lxsdx

function clause decode (0b011111 :
(bit[5]) T :
(bit[5]) RA :
(bit[5]) RB :
0b1001001100 :
[TX] as instr) =
  Lxsdx (T,RA,RB,TX)

function clause execute (Lxsdx (T, RA, RB, TX)) = ()

union ast member (bit[5], bit[5], bit[5], bit) Lxvd2x

function clause decode (0b011111 :
(bit[5]) T :
(bit[5]) RA :
(bit[5]) RB :
0b1101001100 :
[TX] as instr) =
  Lxvd2x (T,RA,RB,TX)

function clause execute (Lxvd2x (T, RA, RB, TX)) = ()

union ast member (bit[5], bit[5], bit[5], bit) Lxvdsx

function clause decode (0b011111 :
(bit[5]) T :
(bit[5]) RA :
(bit[5]) RB :
0b0101001100 :
[TX] as instr) =
  Lxvdsx (T,RA,RB,TX)

function clause execute (Lxvdsx (T, RA, RB, TX)) = ()

union ast member (bit[5], bit[5], bit[5], bit) Lxvw4x

function clause decode (0b011111 :
(bit[5]) T :
(bit[5]) RA :
(bit[5]) RB :
0b1100001100 :
[TX] as instr) =
  Lxvw4x (T,RA,RB,TX)

function clause execute (Lxvw4x (T, RA, RB, TX)) = ()

union ast member (bit[5], bit[5], bit[5], bit) Stxsdx

function clause decode (0b011111 :
(bit[5]) S :
(bit[5]) RA :
(bit[5]) RB :
0b1011001100 :
[SX] as instr) =
  Stxsdx (S,RA,RB,SX)

function clause execute (Stxsdx (S, RA, RB, SX)) = ()

union ast member (bit[5], bit[5], bit[5], bit) Stxvd2x

function clause decode (0b011111 :
(bit[5]) S :
(bit[5]) RA :
(bit[5]) RB :
0b1111001100 :
[SX] as instr) =
  Stxvd2x (S,RA,RB,SX)

function clause execute (Stxvd2x (S, RA, RB, SX)) = ()

union ast member (bit[5], bit[5], bit[5], bit) Stxvw4x

function clause decode (0b011111 :
(bit[5]) S :
(bit[5]) RA :
(bit[5]) RB :
0b1110001100 :
[SX] as instr) =
  Stxvw4x (S,RA,RB,SX)

function clause execute (Stxvw4x (S, RA, RB, SX)) = ()

union ast member (bit[5], bit[5], bit, bit) Xsabsdp

function clause decode (0b111100 :
(bit[5]) T :
(bit[5]) _ :
(bit[5]) B :
0b101011001 :
[BX] :
[TX] as instr) =
  Xsabsdp (T,B,BX,TX)

function clause execute (Xsabsdp (T, B, BX, TX)) = ()

union ast member (bit[5], bit[5], bit[5], bit, bit, bit) Xsadddp

function clause decode (0b111100 :
(bit[5]) T :
(bit[5]) A :
(bit[5]) B :
0b00100000 :
[AX] :
[BX] :
[TX] as instr) =
  Xsadddp (T,A,B,AX,BX,TX)

function clause execute (Xsadddp (T, A, B, AX, BX, TX)) = ()

union ast member (bit[3], bit[5], bit[5], bit, bit) Xscmpodp

function clause decode (0b111100 :
(bit[3]) BF :
(bit[2]) _ :
(bit[5]) A :
(bit[5]) B :
0b00101011 :
[AX] :
[BX] :
(bit[1]) _ as instr) =
  Xscmpodp (BF,A,B,AX,BX)

function clause execute (Xscmpodp (BF, A, B, AX, BX)) = ()

union ast member (bit[3], bit[5], bit[5], bit, bit) Xscmpudp

function clause decode (0b111100 :
(bit[3]) BF :
(bit[2]) _ :
(bit[5]) A :
(bit[5]) B :
0b00100011 :
[AX] :
[BX] :
(bit[1]) _ as instr) =
  Xscmpudp (BF,A,B,AX,BX)

function clause execute (Xscmpudp (BF, A, B, AX, BX)) = ()

union ast member (bit[5], bit[5], bit[5], bit, bit, bit) Xscpsgndp

function clause decode (0b111100 :
(bit[5]) T :
(bit[5]) A :
(bit[5]) B :
0b10110000 :
[AX] :
[BX] :
[TX] as instr) =
  Xscpsgndp (T,A,B,AX,BX,TX)

function clause execute (Xscpsgndp (T, A, B, AX, BX, TX)) = ()

union ast member (bit[5], bit[5], bit, bit) Xscvdpsp

function clause decode (0b111100 :
(bit[5]) T :
(bit[5]) _ :
(bit[5]) B :
0b100001001 :
[BX] :
[TX] as instr) =
  Xscvdpsp (T,B,BX,TX)

function clause execute (Xscvdpsp (T, B, BX, TX)) = ()

union ast member (bit[5], bit[5], bit, bit) Xscvdpsxds

function clause decode (0b111100 :
(bit[5]) T :
(bit[5]) _ :
(bit[5]) B :
0b101011000 :
[BX] :
[TX] as instr) =
  Xscvdpsxds (T,B,BX,TX)

function clause execute (Xscvdpsxds (T, B, BX, TX)) = ()

union ast member (bit[5], bit[5], bit, bit) Xscvdpsxws

function clause decode (0b111100 :
(bit[5]) T :
(bit[5]) _ :
(bit[5]) B :
0b001011000 :
[BX] :
[TX] as instr) =
  Xscvdpsxws (T,B,BX,TX)

function clause execute (Xscvdpsxws (T, B, BX, TX)) = ()

union ast member (bit[5], bit[5], bit, bit) Xscvdpuxds

function clause decode (0b111100 :
(bit[5]) T :
(bit[5]) _ :
(bit[5]) B :
0b101001000 :
[BX] :
[TX] as instr) =
  Xscvdpuxds (T,B,BX,TX)

function clause execute (Xscvdpuxds (T, B, BX, TX)) = ()

union ast member (bit[5], bit[5], bit, bit) Xscvdpuxws

function clause decode (0b111100 :
(bit[5]) T :
(bit[5]) _ :
(bit[5]) B :
0b001001000 :
[BX] :
[TX] as instr) =
  Xscvdpuxws (T,B,BX,TX)

function clause execute (Xscvdpuxws (T, B, BX, TX)) = ()

union ast member (bit[5], bit[5], bit, bit) Xscvspdp

function clause decode (0b111100 :
(bit[5]) T :
(bit[5]) _ :
(bit[5]) B :
0b101001001 :
[BX] :
[TX] as instr) =
  Xscvspdp (T,B,BX,TX)

function clause execute (Xscvspdp (T, B, BX, TX)) = ()

union ast member (bit[5], bit[5], bit, bit) Xscvsxddp

function clause decode (0b111100 :
(bit[5]) T :
(bit[5]) _ :
(bit[5]) B :
0b101111000 :
[BX] :
[TX] as instr) =
  Xscvsxddp (T,B,BX,TX)

function clause execute (Xscvsxddp (T, B, BX, TX)) = ()

union ast member (bit[5], bit[5], bit, bit) Xscvuxddp

function clause decode (0b111100 :
(bit[5]) T :
(bit[5]) _ :
(bit[5]) B :
0b101101000 :
[BX] :
[TX] as instr) =
  Xscvuxddp (T,B,BX,TX)

function clause execute (Xscvuxddp (T, B, BX, TX)) = ()

union ast member (bit[5], bit[5], bit[5], bit, bit, bit) Xsdivdp

function clause decode (0b111100 :
(bit[5]) T :
(bit[5]) A :
(bit[5]) B :
0b00111000 :
[AX] :
[BX] :
[TX] as instr) =
  Xsdivdp (T,A,B,AX,BX,TX)

function clause execute (Xsdivdp (T, A, B, AX, BX, TX)) = ()

union ast member (bit[5], bit[5], bit[5], bit, bit, bit) Xsmaddmdp

function clause decode (0b111100 :
(bit[5]) T :
(bit[5]) A :
(bit[5]) B :
0b00101001 :
[AX] :
[BX] :
[TX] as instr) =
  Xsmaddmdp (T,A,B,AX,BX,TX)

function clause execute (Xsmaddmdp (T, A, B, AX, BX, TX)) = ()

union ast member (bit[5], bit[5], bit[5], bit, bit, bit) Xsmaddadp

function clause decode (0b111100 :
(bit[5]) T :
(bit[5]) A :
(bit[5]) B :
0b00100001 :
[AX] :
[BX] :
[TX] as instr) =
  Xsmaddadp (T,A,B,AX,BX,TX)

function clause execute (Xsmaddadp (T, A, B, AX, BX, TX)) = ()

union ast member (bit[5], bit[5], bit[5], bit, bit, bit) Xsmaxdp

function clause decode (0b111100 :
(bit[5]) T :
(bit[5]) A :
(bit[5]) B :
0b10100000 :
[AX] :
[BX] :
[TX] as instr) =
  Xsmaxdp (T,A,B,AX,BX,TX)

function clause execute (Xsmaxdp (T, A, B, AX, BX, TX)) = ()

union ast member (bit[5], bit[5], bit[5], bit, bit, bit) Xsmindp

function clause decode (0b111100 :
(bit[5]) T :
(bit[5]) A :
(bit[5]) B :
0b10101000 :
[AX] :
[BX] :
[TX] as instr) =
  Xsmindp (T,A,B,AX,BX,TX)

function clause execute (Xsmindp (T, A, B, AX, BX, TX)) = ()

union ast member (bit[5], bit[5], bit[5], bit, bit, bit) Xsmsubmdp

function clause decode (0b111100 :
(bit[5]) T :
(bit[5]) A :
(bit[5]) B :
0b00111001 :
[AX] :
[BX] :
[TX] as instr) =
  Xsmsubmdp (T,A,B,AX,BX,TX)

function clause execute (Xsmsubmdp (T, A, B, AX, BX, TX)) = ()

union ast member (bit[5], bit[5], bit[5], bit, bit, bit) Xsmsubadp

function clause decode (0b111100 :
(bit[5]) T :
(bit[5]) A :
(bit[5]) B :
0b00110001 :
[AX] :
[BX] :
[TX] as instr) =
  Xsmsubadp (T,A,B,AX,BX,TX)

function clause execute (Xsmsubadp (T, A, B, AX, BX, TX)) = ()

union ast member (bit[5], bit[5], bit[5], bit, bit, bit) Xsmuldp

function clause decode (0b111100 :
(bit[5]) T :
(bit[5]) A :
(bit[5]) B :
0b00110000 :
[AX] :
[BX] :
[TX] as instr) =
  Xsmuldp (T,A,B,AX,BX,TX)

function clause execute (Xsmuldp (T, A, B, AX, BX, TX)) = ()

union ast member (bit[5], bit[5], bit, bit) Xsnabsdp

function clause decode (0b111100 :
(bit[5]) T :
(bit[5]) _ :
(bit[5]) B :
0b101101001 :
[BX] :
[TX] as instr) =
  Xsnabsdp (T,B,BX,TX)

function clause execute (Xsnabsdp (T, B, BX, TX)) = ()

union ast member (bit[5], bit[5], bit, bit) Xsnegdp

function clause decode (0b111100 :
(bit[5]) T :
(bit[5]) _ :
(bit[5]) B :
0b101111001 :
[BX] :
[TX] as instr) =
  Xsnegdp (T,B,BX,TX)

function clause execute (Xsnegdp (T, B, BX, TX)) = ()

union ast member (bit[5], bit[5], bit[5], bit, bit, bit) Xsnmaddmdp

function clause decode (0b111100 :
(bit[5]) T :
(bit[5]) A :
(bit[5]) B :
0b10101001 :
[AX] :
[BX] :
[TX] as instr) =
  Xsnmaddmdp (T,A,B,AX,BX,TX)

function clause execute (Xsnmaddmdp (T, A, B, AX, BX, TX)) = ()

union ast member (bit[5], bit[5], bit[5], bit, bit, bit) Xsnmaddadp

function clause decode (0b111100 :
(bit[5]) T :
(bit[5]) A :
(bit[5]) B :
0b10100001 :
[AX] :
[BX] :
[TX] as instr) =
  Xsnmaddadp (T,A,B,AX,BX,TX)

function clause execute (Xsnmaddadp (T, A, B, AX, BX, TX)) = ()

union ast member (bit[5], bit[5], bit[5], bit, bit, bit) Xsnmsubmdp

function clause decode (0b111100 :
(bit[5]) T :
(bit[5]) A :
(bit[5]) B :
0b10111001 :
[AX] :
[BX] :
[TX] as instr) =
  Xsnmsubmdp (T,A,B,AX,BX,TX)

function clause execute (Xsnmsubmdp (T, A, B, AX, BX, TX)) = ()

union ast member (bit[5], bit[5], bit[5], bit, bit, bit) Xsnmsubadp

function clause decode (0b111100 :
(bit[5]) T :
(bit[5]) A :
(bit[5]) B :
0b10110001 :
[AX] :
[BX] :
[TX] as instr) =
  Xsnmsubadp (T,A,B,AX,BX,TX)

function clause execute (Xsnmsubadp (T, A, B, AX, BX, TX)) = ()

union ast member (bit[5], bit[5], bit, bit) Xsrdpi

function clause decode (0b111100 :
(bit[5]) T :
(bit[5]) _ :
(bit[5]) B :
0b001001001 :
[BX] :
[TX] as instr) =
  Xsrdpi (T,B,BX,TX)

function clause execute (Xsrdpi (T, B, BX, TX)) = ()

union ast member (bit[5], bit[5], bit, bit) Xsrdpic

function clause decode (0b111100 :
(bit[5]) T :
(bit[5]) _ :
(bit[5]) B :
0b001101011 :
[BX] :
[TX] as instr) =
  Xsrdpic (T,B,BX,TX)

function clause execute (Xsrdpic (T, B, BX, TX)) = ()

union ast member (bit[5], bit[5], bit, bit) Xsrdpim

function clause decode (0b111100 :
(bit[5]) T :
(bit[5]) _ :
(bit[5]) B :
0b001111001 :
[BX] :
[TX] as instr) =
  Xsrdpim (T,B,BX,TX)

function clause execute (Xsrdpim (T, B, BX, TX)) = ()

union ast member (bit[5], bit[5], bit, bit) Xsrdpip

function clause decode (0b111100 :
(bit[5]) T :
(bit[5]) _ :
(bit[5]) B :
0b001101001 :
[BX] :
[TX] as instr) =
  Xsrdpip (T,B,BX,TX)

function clause execute (Xsrdpip (T, B, BX, TX)) = ()

union ast member (bit[5], bit[5], bit, bit) Xsrdpiz

function clause decode (0b111100 :
(bit[5]) T :
(bit[5]) _ :
(bit[5]) B :
0b001011001 :
[BX] :
[TX] as instr) =
  Xsrdpiz (T,B,BX,TX)

function clause execute (Xsrdpiz (T, B, BX, TX)) = ()

union ast member (bit[5], bit[5], bit, bit) Xsredp

function clause decode (0b111100 :
(bit[5]) T :
(bit[5]) _ :
(bit[5]) B :
0b001011010 :
[BX] :
[TX] as instr) =
  Xsredp (T,B,BX,TX)

function clause execute (Xsredp (T, B, BX, TX)) = ()

union ast member (bit[5], bit[5], bit, bit) Xsrsqrtedp

function clause decode (0b111100 :
(bit[5]) T :
(bit[5]) _ :
(bit[5]) B :
0b001001010 :
[BX] :
[TX] as instr) =
  Xsrsqrtedp (T,B,BX,TX)

function clause execute (Xsrsqrtedp (T, B, BX, TX)) = ()

union ast member (bit[5], bit[5], bit, bit) Xssqrtdp

function clause decode (0b111100 :
(bit[5]) T :
(bit[5]) _ :
(bit[5]) B :
0b001001011 :
[BX] :
[TX] as instr) =
  Xssqrtdp (T,B,BX,TX)

function clause execute (Xssqrtdp (T, B, BX, TX)) = ()

union ast member (bit[5], bit[5], bit[5], bit, bit, bit) Xssubdp

function clause decode (0b111100 :
(bit[5]) T :
(bit[5]) A :
(bit[5]) B :
0b00101000 :
[AX] :
[BX] :
[TX] as instr) =
  Xssubdp (T,A,B,AX,BX,TX)

function clause execute (Xssubdp (T, A, B, AX, BX, TX)) = ()

union ast member (bit[3], bit[5], bit[5], bit, bit) Xstdivdp

function clause decode (0b111100 :
(bit[3]) BF :
(bit[2]) _ :
(bit[5]) A :
(bit[5]) B :
0b00111101 :
[AX] :
[BX] :
(bit[1]) _ as instr) =
  Xstdivdp (BF,A,B,AX,BX)

function clause execute (Xstdivdp (BF, A, B, AX, BX)) = ()

union ast member (bit[3], bit[5], bit) Xstsqrtdp

function clause decode (0b111100 :
(bit[3]) BF :
(bit[2]) _ :
(bit[5]) _ :
(bit[5]) B :
0b001101010 :
[BX] :
(bit[1]) _ as instr) =
  Xstsqrtdp (BF,B,BX)

function clause execute (Xstsqrtdp (BF, B, BX)) = ()

union ast member (bit[5], bit[5], bit, bit) Xvabsdp

function clause decode (0b111100 :
(bit[5]) T :
(bit[5]) _ :
(bit[5]) B :
0b111011001 :
[BX] :
[TX] as instr) =
  Xvabsdp (T,B,BX,TX)

function clause execute (Xvabsdp (T, B, BX, TX)) = ()

union ast member (bit[5], bit[5], bit, bit) Xvabssp

function clause decode (0b111100 :
(bit[5]) T :
(bit[5]) _ :
(bit[5]) B :
0b110011001 :
[BX] :
[TX] as instr) =
  Xvabssp (T,B,BX,TX)

function clause execute (Xvabssp (T, B, BX, TX)) = ()

union ast member (bit[5], bit[5], bit[5], bit, bit, bit) Xvadddp

function clause decode (0b111100 :
(bit[5]) T :
(bit[5]) A :
(bit[5]) B :
0b01100000 :
[AX] :
[BX] :
[TX] as instr) =
  Xvadddp (T,A,B,AX,BX,TX)

function clause execute (Xvadddp (T, A, B, AX, BX, TX)) = ()

union ast member (bit[5], bit[5], bit[5], bit, bit, bit) Xvaddsp

function clause decode (0b111100 :
(bit[5]) T :
(bit[5]) A :
(bit[5]) B :
0b01000000 :
[AX] :
[BX] :
[TX] as instr) =
  Xvaddsp (T,A,B,AX,BX,TX)

function clause execute (Xvaddsp (T, A, B, AX, BX, TX)) = ()

union ast member (bit[5], bit[5], bit[5], bit, bit, bit, bit) Xvcmpeqdp

function clause decode (0b111100 :
(bit[5]) T :
(bit[5]) A :
(bit[5]) B :
[Rc] :
0b1100011 :
[AX] :
[BX] :
[TX] as instr) =
  Xvcmpeqdp (T,A,B,Rc,AX,BX,TX)

function clause execute (Xvcmpeqdp (T, A, B, Rc, AX, BX, TX)) = ()

union ast member (bit[5], bit[5], bit[5], bit, bit, bit, bit) Xvcmpeqsp

function clause decode (0b111100 :
(bit[5]) T :
(bit[5]) A :
(bit[5]) B :
[Rc] :
0b1000011 :
[AX] :
[BX] :
[TX] as instr) =
  Xvcmpeqsp (T,A,B,Rc,AX,BX,TX)

function clause execute (Xvcmpeqsp (T, A, B, Rc, AX, BX, TX)) = ()

union ast member (bit[5], bit[5], bit[5], bit, bit, bit, bit) Xvcmpgedp

function clause decode (0b111100 :
(bit[5]) T :
(bit[5]) A :
(bit[5]) B :
[Rc] :
0b1110011 :
[AX] :
[BX] :
[TX] as instr) =
  Xvcmpgedp (T,A,B,Rc,AX,BX,TX)

function clause execute (Xvcmpgedp (T, A, B, Rc, AX, BX, TX)) = ()

union ast member (bit[5], bit[5], bit[5], bit, bit, bit, bit) Xvcmpgesp

function clause decode (0b111100 :
(bit[5]) T :
(bit[5]) A :
(bit[5]) B :
[Rc] :
0b1010011 :
[AX] :
[BX] :
[TX] as instr) =
  Xvcmpgesp (T,A,B,Rc,AX,BX,TX)

function clause execute (Xvcmpgesp (T, A, B, Rc, AX, BX, TX)) = ()

union ast member (bit[5], bit[5], bit[5], bit, bit, bit, bit) Xvcmpgtdp

function clause decode (0b111100 :
(bit[5]) T :
(bit[5]) A :
(bit[5]) B :
[Rc] :
0b1101011 :
[AX] :
[BX] :
[TX] as instr) =
  Xvcmpgtdp (T,A,B,Rc,AX,BX,TX)

function clause execute (Xvcmpgtdp (T, A, B, Rc, AX, BX, TX)) = ()

union ast member (bit[5], bit[5], bit[5], bit, bit, bit, bit) Xvcmpgtsp

function clause decode (0b111100 :
(bit[5]) T :
(bit[5]) A :
(bit[5]) B :
[Rc] :
0b1001011 :
[AX] :
[BX] :
[TX] as instr) =
  Xvcmpgtsp (T,A,B,Rc,AX,BX,TX)

function clause execute (Xvcmpgtsp (T, A, B, Rc, AX, BX, TX)) = ()

union ast member (bit[5], bit[5], bit[5], bit, bit, bit) Xvcpsgndp

function clause decode (0b111100 :
(bit[5]) T :
(bit[5]) A :
(bit[5]) B :
0b11110000 :
[AX] :
[BX] :
[TX] as instr) =
  Xvcpsgndp (T,A,B,AX,BX,TX)

function clause execute (Xvcpsgndp (T, A, B, AX, BX, TX)) = ()

union ast member (bit[5], bit[5], bit[5], bit, bit, bit) Xvcpsgnsp

function clause decode (0b111100 :
(bit[5]) T :
(bit[5]) A :
(bit[5]) B :
0b11010000 :
[AX] :
[BX] :
[TX] as instr) =
  Xvcpsgnsp (T,A,B,AX,BX,TX)

function clause execute (Xvcpsgnsp (T, A, B, AX, BX, TX)) = ()

union ast member (bit[5], bit[5], bit, bit) Xvcvdpsp

function clause decode (0b111100 :
(bit[5]) T :
(bit[5]) _ :
(bit[5]) B :
0b110001001 :
[BX] :
[TX] as instr) =
  Xvcvdpsp (T,B,BX,TX)

function clause execute (Xvcvdpsp (T, B, BX, TX)) = ()

union ast member (bit[5], bit[5], bit, bit) Xvcvdpsxds

function clause decode (0b111100 :
(bit[5]) T :
(bit[5]) _ :
(bit[5]) B :
0b111011000 :
[BX] :
[TX] as instr) =
  Xvcvdpsxds (T,B,BX,TX)

function clause execute (Xvcvdpsxds (T, B, BX, TX)) = ()

union ast member (bit[5], bit[5], bit, bit) Xvcvdpsxws

function clause decode (0b111100 :
(bit[5]) T :
(bit[5]) _ :
(bit[5]) B :
0b011011000 :
[BX] :
[TX] as instr) =
  Xvcvdpsxws (T,B,BX,TX)

function clause execute (Xvcvdpsxws (T, B, BX, TX)) = ()

union ast member (bit[5], bit[5], bit, bit) Xvcvdpuxds

function clause decode (0b111100 :
(bit[5]) T :
(bit[5]) _ :
(bit[5]) B :
0b111001000 :
[BX] :
[TX] as instr) =
  Xvcvdpuxds (T,B,BX,TX)

function clause execute (Xvcvdpuxds (T, B, BX, TX)) = ()

union ast member (bit[5], bit[5], bit, bit) Xvcvdpuxws

function clause decode (0b111100 :
(bit[5]) T :
(bit[5]) _ :
(bit[5]) B :
0b011001000 :
[BX] :
[TX] as instr) =
  Xvcvdpuxws (T,B,BX,TX)

function clause execute (Xvcvdpuxws (T, B, BX, TX)) = ()

union ast member (bit[5], bit[5], bit, bit) Xvcvspdp

function clause decode (0b111100 :
(bit[5]) T :
(bit[5]) _ :
(bit[5]) B :
0b111001001 :
[BX] :
[TX] as instr) =
  Xvcvspdp (T,B,BX,TX)

function clause execute (Xvcvspdp (T, B, BX, TX)) = ()

union ast member (bit[5], bit[5], bit, bit) Xvcvspsxds

function clause decode (0b111100 :
(bit[5]) T :
(bit[5]) _ :
(bit[5]) B :
0b110011000 :
[BX] :
[TX] as instr) =
  Xvcvspsxds (T,B,BX,TX)

function clause execute (Xvcvspsxds (T, B, BX, TX)) = ()

union ast member (bit[5], bit[5], bit, bit) Xvcvspsxws

function clause decode (0b111100 :
(bit[5]) T :
(bit[5]) _ :
(bit[5]) B :
0b010011000 :
[BX] :
[TX] as instr) =
  Xvcvspsxws (T,B,BX,TX)

function clause execute (Xvcvspsxws (T, B, BX, TX)) = ()

union ast member (bit[5], bit[5], bit, bit) Xvcvspuxds

function clause decode (0b111100 :
(bit[5]) T :
(bit[5]) _ :
(bit[5]) B :
0b110001000 :
[BX] :
[TX] as instr) =
  Xvcvspuxds (T,B,BX,TX)

function clause execute (Xvcvspuxds (T, B, BX, TX)) = ()

union ast member (bit[5], bit[5], bit, bit) Xvcvspuxws

function clause decode (0b111100 :
(bit[5]) T :
(bit[5]) _ :
(bit[5]) B :
0b010001000 :
[BX] :
[TX] as instr) =
  Xvcvspuxws (T,B,BX,TX)

function clause execute (Xvcvspuxws (T, B, BX, TX)) = ()

union ast member (bit[5], bit[5], bit, bit) Xvcvsxddp

function clause decode (0b111100 :
(bit[5]) T :
(bit[5]) _ :
(bit[5]) B :
0b111111000 :
[BX] :
[TX] as instr) =
  Xvcvsxddp (T,B,BX,TX)

function clause execute (Xvcvsxddp (T, B, BX, TX)) = ()

union ast member (bit[5], bit[5], bit, bit) Xvcvsxdsp

function clause decode (0b111100 :
(bit[5]) T :
(bit[5]) _ :
(bit[5]) B :
0b110111000 :
[BX] :
[TX] as instr) =
  Xvcvsxdsp (T,B,BX,TX)

function clause execute (Xvcvsxdsp (T, B, BX, TX)) = ()

union ast member (bit[5], bit[5], bit, bit) Xvcvsxwdp

function clause decode (0b111100 :
(bit[5]) T :
(bit[5]) _ :
(bit[5]) B :
0b011111000 :
[BX] :
[TX] as instr) =
  Xvcvsxwdp (T,B,BX,TX)

function clause execute (Xvcvsxwdp (T, B, BX, TX)) = ()

union ast member (bit[5], bit[5], bit, bit) Xvcvsxwsp

function clause decode (0b111100 :
(bit[5]) T :
(bit[5]) _ :
(bit[5]) B :
0b010111000 :
[BX] :
[TX] as instr) =
  Xvcvsxwsp (T,B,BX,TX)

function clause execute (Xvcvsxwsp (T, B, BX, TX)) = ()

union ast member (bit[5], bit[5], bit, bit) Xvcvuxddp

function clause decode (0b111100 :
(bit[5]) T :
(bit[5]) _ :
(bit[5]) B :
0b111101000 :
[BX] :
[TX] as instr) =
  Xvcvuxddp (T,B,BX,TX)

function clause execute (Xvcvuxddp (T, B, BX, TX)) = ()

union ast member (bit[5], bit[5], bit, bit) Xvcvuxdsp

function clause decode (0b111100 :
(bit[5]) T :
(bit[5]) _ :
(bit[5]) B :
0b110101000 :
[BX] :
[TX] as instr) =
  Xvcvuxdsp (T,B,BX,TX)

function clause execute (Xvcvuxdsp (T, B, BX, TX)) = ()

union ast member (bit[5], bit[5], bit, bit) Xvcvuxwdp

function clause decode (0b111100 :
(bit[5]) T :
(bit[5]) _ :
(bit[5]) B :
0b011101000 :
[BX] :
[TX] as instr) =
  Xvcvuxwdp (T,B,BX,TX)

function clause execute (Xvcvuxwdp (T, B, BX, TX)) = ()

union ast member (bit[5], bit[5], bit, bit) Xvcvuxwsp

function clause decode (0b111100 :
(bit[5]) T :
(bit[5]) _ :
(bit[5]) B :
0b010101000 :
[BX] :
[TX] as instr) =
  Xvcvuxwsp (T,B,BX,TX)

function clause execute (Xvcvuxwsp (T, B, BX, TX)) = ()

union ast member (bit[5], bit[5], bit[5], bit, bit, bit) Xvdivdp

function clause decode (0b111100 :
(bit[5]) T :
(bit[5]) A :
(bit[5]) B :
0b01111000 :
[AX] :
[BX] :
[TX] as instr) =
  Xvdivdp (T,A,B,AX,BX,TX)

function clause execute (Xvdivdp (T, A, B, AX, BX, TX)) = ()

union ast member (bit[5], bit[5], bit[5], bit, bit, bit) Xvdivsp

function clause decode (0b111100 :
(bit[5]) T :
(bit[5]) A :
(bit[5]) B :
0b01011000 :
[AX] :
[BX] :
[TX] as instr) =
  Xvdivsp (T,A,B,AX,BX,TX)

function clause execute (Xvdivsp (T, A, B, AX, BX, TX)) = ()

union ast member (bit[5], bit[5], bit[5], bit, bit, bit) Xvmaddmdp

function clause decode (0b111100 :
(bit[5]) T :
(bit[5]) A :
(bit[5]) B :
0b01101001 :
[AX] :
[BX] :
[TX] as instr) =
  Xvmaddmdp (T,A,B,AX,BX,TX)

function clause execute (Xvmaddmdp (T, A, B, AX, BX, TX)) = ()

union ast member (bit[5], bit[5], bit[5], bit, bit, bit) Xvmaddadp

function clause decode (0b111100 :
(bit[5]) T :
(bit[5]) A :
(bit[5]) B :
0b01100001 :
[AX] :
[BX] :
[TX] as instr) =
  Xvmaddadp (T,A,B,AX,BX,TX)

function clause execute (Xvmaddadp (T, A, B, AX, BX, TX)) = ()

union ast member (bit[5], bit[5], bit[5], bit, bit, bit) Xvmaddmsp

function clause decode (0b111100 :
(bit[5]) T :
(bit[5]) A :
(bit[5]) B :
0b01001001 :
[AX] :
[BX] :
[TX] as instr) =
  Xvmaddmsp (T,A,B,AX,BX,TX)

function clause execute (Xvmaddmsp (T, A, B, AX, BX, TX)) = ()

union ast member (bit[5], bit[5], bit[5], bit, bit, bit) Xvmaddasp

function clause decode (0b111100 :
(bit[5]) T :
(bit[5]) A :
(bit[5]) B :
0b01000001 :
[AX] :
[BX] :
[TX] as instr) =
  Xvmaddasp (T,A,B,AX,BX,TX)

function clause execute (Xvmaddasp (T, A, B, AX, BX, TX)) = ()

union ast member (bit[5], bit[5], bit[5], bit, bit, bit) Xvmaxdp

function clause decode (0b111100 :
(bit[5]) T :
(bit[5]) A :
(bit[5]) B :
0b11100000 :
[AX] :
[BX] :
[TX] as instr) =
  Xvmaxdp (T,A,B,AX,BX,TX)

function clause execute (Xvmaxdp (T, A, B, AX, BX, TX)) = ()

union ast member (bit[5], bit[5], bit[5], bit, bit, bit) Xvmaxsp

function clause decode (0b111100 :
(bit[5]) T :
(bit[5]) A :
(bit[5]) B :
0b11000000 :
[AX] :
[BX] :
[TX] as instr) =
  Xvmaxsp (T,A,B,AX,BX,TX)

function clause execute (Xvmaxsp (T, A, B, AX, BX, TX)) = ()

union ast member (bit[5], bit[5], bit[5], bit, bit, bit) Xvmindp

function clause decode (0b111100 :
(bit[5]) T :
(bit[5]) A :
(bit[5]) B :
0b11101000 :
[AX] :
[BX] :
[TX] as instr) =
  Xvmindp (T,A,B,AX,BX,TX)

function clause execute (Xvmindp (T, A, B, AX, BX, TX)) = ()

union ast member (bit[5], bit[5], bit[5], bit, bit, bit) Xvminsp

function clause decode (0b111100 :
(bit[5]) T :
(bit[5]) A :
(bit[5]) B :
0b11001000 :
[AX] :
[BX] :
[TX] as instr) =
  Xvminsp (T,A,B,AX,BX,TX)

function clause execute (Xvminsp (T, A, B, AX, BX, TX)) = ()

union ast member (bit[5], bit[5], bit[5], bit, bit, bit) Xvmsubmdp

function clause decode (0b111100 :
(bit[5]) T :
(bit[5]) A :
(bit[5]) B :
0b01111001 :
[AX] :
[BX] :
[TX] as instr) =
  Xvmsubmdp (T,A,B,AX,BX,TX)

function clause execute (Xvmsubmdp (T, A, B, AX, BX, TX)) = ()

union ast member (bit[5], bit[5], bit[5], bit, bit, bit) Xvmsubadp

function clause decode (0b111100 :
(bit[5]) T :
(bit[5]) A :
(bit[5]) B :
0b01110001 :
[AX] :
[BX] :
[TX] as instr) =
  Xvmsubadp (T,A,B,AX,BX,TX)

function clause execute (Xvmsubadp (T, A, B, AX, BX, TX)) = ()

union ast member (bit[5], bit[5], bit[5], bit, bit, bit) Xvmsubmsp

function clause decode (0b111100 :
(bit[5]) T :
(bit[5]) A :
(bit[5]) B :
0b01011001 :
[AX] :
[BX] :
[TX] as instr) =
  Xvmsubmsp (T,A,B,AX,BX,TX)

function clause execute (Xvmsubmsp (T, A, B, AX, BX, TX)) = ()

union ast member (bit[5], bit[5], bit[5], bit, bit, bit) Xvmsubasp

function clause decode (0b111100 :
(bit[5]) T :
(bit[5]) A :
(bit[5]) B :
0b01010001 :
[AX] :
[BX] :
[TX] as instr) =
  Xvmsubasp (T,A,B,AX,BX,TX)

function clause execute (Xvmsubasp (T, A, B, AX, BX, TX)) = ()

union ast member (bit[5], bit[5], bit[5], bit, bit, bit) Xvmuldp

function clause decode (0b111100 :
(bit[5]) T :
(bit[5]) A :
(bit[5]) B :
0b01110000 :
[AX] :
[BX] :
[TX] as instr) =
  Xvmuldp (T,A,B,AX,BX,TX)

function clause execute (Xvmuldp (T, A, B, AX, BX, TX)) = ()

union ast member (bit[5], bit[5], bit[5], bit, bit, bit) Xvmulsp

function clause decode (0b111100 :
(bit[5]) T :
(bit[5]) A :
(bit[5]) B :
0b01010000 :
[AX] :
[BX] :
[TX] as instr) =
  Xvmulsp (T,A,B,AX,BX,TX)

function clause execute (Xvmulsp (T, A, B, AX, BX, TX)) = ()

union ast member (bit[5], bit[5], bit, bit) Xvnabsdp

function clause decode (0b111100 :
(bit[5]) T :
(bit[5]) _ :
(bit[5]) B :
0b111101001 :
[BX] :
[TX] as instr) =
  Xvnabsdp (T,B,BX,TX)

function clause execute (Xvnabsdp (T, B, BX, TX)) = ()

union ast member (bit[5], bit[5], bit, bit) Xvnabssp

function clause decode (0b111100 :
(bit[5]) T :
(bit[5]) _ :
(bit[5]) B :
0b110101001 :
[BX] :
[TX] as instr) =
  Xvnabssp (T,B,BX,TX)

function clause execute (Xvnabssp (T, B, BX, TX)) = ()

union ast member (bit[5], bit[5], bit, bit) Xvnegdp

function clause decode (0b111100 :
(bit[5]) T :
(bit[5]) _ :
(bit[5]) B :
0b111111001 :
[BX] :
[TX] as instr) =
  Xvnegdp (T,B,BX,TX)

function clause execute (Xvnegdp (T, B, BX, TX)) = ()

union ast member (bit[5], bit[5], bit, bit) Xvnegsp

function clause decode (0b111100 :
(bit[5]) T :
(bit[5]) _ :
(bit[5]) B :
0b110111001 :
[BX] :
[TX] as instr) =
  Xvnegsp (T,B,BX,TX)

function clause execute (Xvnegsp (T, B, BX, TX)) = ()

union ast member (bit[5], bit[5], bit[5], bit, bit, bit) Xvnmaddmdp

function clause decode (0b111100 :
(bit[5]) T :
(bit[5]) A :
(bit[5]) B :
0b11101001 :
[AX] :
[BX] :
[TX] as instr) =
  Xvnmaddmdp (T,A,B,AX,BX,TX)

function clause execute (Xvnmaddmdp (T, A, B, AX, BX, TX)) = ()

union ast member (bit[5], bit[5], bit[5], bit, bit, bit) Xvnmaddadp

function clause decode (0b111100 :
(bit[5]) T :
(bit[5]) A :
(bit[5]) B :
0b11100001 :
[AX] :
[BX] :
[TX] as instr) =
  Xvnmaddadp (T,A,B,AX,BX,TX)

function clause execute (Xvnmaddadp (T, A, B, AX, BX, TX)) = ()

union ast member (bit[5], bit[5], bit[5], bit, bit, bit) Xvnmaddmsp

function clause decode (0b111100 :
(bit[5]) T :
(bit[5]) A :
(bit[5]) B :
0b11001001 :
[AX] :
[BX] :
[TX] as instr) =
  Xvnmaddmsp (T,A,B,AX,BX,TX)

function clause execute (Xvnmaddmsp (T, A, B, AX, BX, TX)) = ()

union ast member (bit[5], bit[5], bit[5], bit, bit, bit) Xvnmaddasp

function clause decode (0b111100 :
(bit[5]) T :
(bit[5]) A :
(bit[5]) B :
0b11000001 :
[AX] :
[BX] :
[TX] as instr) =
  Xvnmaddasp (T,A,B,AX,BX,TX)

function clause execute (Xvnmaddasp (T, A, B, AX, BX, TX)) = ()

union ast member (bit[5], bit[5], bit[5], bit, bit, bit) Xvnmsubmdp

function clause decode (0b111100 :
(bit[5]) T :
(bit[5]) A :
(bit[5]) B :
0b11111001 :
[AX] :
[BX] :
[TX] as instr) =
  Xvnmsubmdp (T,A,B,AX,BX,TX)

function clause execute (Xvnmsubmdp (T, A, B, AX, BX, TX)) = ()

union ast member (bit[5], bit[5], bit[5], bit, bit, bit) Xvnmsubadp

function clause decode (0b111100 :
(bit[5]) T :
(bit[5]) A :
(bit[5]) B :
0b11110001 :
[AX] :
[BX] :
[TX] as instr) =
  Xvnmsubadp (T,A,B,AX,BX,TX)

function clause execute (Xvnmsubadp (T, A, B, AX, BX, TX)) = ()

union ast member (bit[5], bit[5], bit[5], bit, bit, bit) Xvnmsubmsp

function clause decode (0b111100 :
(bit[5]) T :
(bit[5]) A :
(bit[5]) B :
0b11011001 :
[AX] :
[BX] :
[TX] as instr) =
  Xvnmsubmsp (T,A,B,AX,BX,TX)

function clause execute (Xvnmsubmsp (T, A, B, AX, BX, TX)) = ()

union ast member (bit[5], bit[5], bit[5], bit, bit, bit) Xvnmsubasp

function clause decode (0b111100 :
(bit[5]) T :
(bit[5]) A :
(bit[5]) B :
0b11010001 :
[AX] :
[BX] :
[TX] as instr) =
  Xvnmsubasp (T,A,B,AX,BX,TX)

function clause execute (Xvnmsubasp (T, A, B, AX, BX, TX)) = ()

union ast member (bit[5], bit[5], bit, bit) Xvrdpi

function clause decode (0b111100 :
(bit[5]) T :
(bit[5]) _ :
(bit[5]) B :
0b011001001 :
[BX] :
[TX] as instr) =
  Xvrdpi (T,B,BX,TX)

function clause execute (Xvrdpi (T, B, BX, TX)) = ()

union ast member (bit[5], bit[5], bit, bit) Xvrdpic

function clause decode (0b111100 :
(bit[5]) T :
(bit[5]) _ :
(bit[5]) B :
0b011101011 :
[BX] :
[TX] as instr) =
  Xvrdpic (T,B,BX,TX)

function clause execute (Xvrdpic (T, B, BX, TX)) = ()

union ast member (bit[5], bit[5], bit, bit) Xvrdpim

function clause decode (0b111100 :
(bit[5]) T :
(bit[5]) _ :
(bit[5]) B :
0b011111001 :
[BX] :
[TX] as instr) =
  Xvrdpim (T,B,BX,TX)

function clause execute (Xvrdpim (T, B, BX, TX)) = ()

union ast member (bit[5], bit[5], bit, bit) Xvrdpip

function clause decode (0b111100 :
(bit[5]) T :
(bit[5]) _ :
(bit[5]) B :
0b011101001 :
[BX] :
[TX] as instr) =
  Xvrdpip (T,B,BX,TX)

function clause execute (Xvrdpip (T, B, BX, TX)) = ()

union ast member (bit[5], bit[5], bit, bit) Xvrdpiz

function clause decode (0b111100 :
(bit[5]) T :
(bit[5]) _ :
(bit[5]) B :
0b011011001 :
[BX] :
[TX] as instr) =
  Xvrdpiz (T,B,BX,TX)

function clause execute (Xvrdpiz (T, B, BX, TX)) = ()

union ast member (bit[5], bit[5], bit, bit) Xvredp

function clause decode (0b111100 :
(bit[5]) T :
(bit[5]) _ :
(bit[5]) B :
0b011011010 :
[BX] :
[TX] as instr) =
  Xvredp (T,B,BX,TX)

function clause execute (Xvredp (T, B, BX, TX)) = ()

union ast member (bit[5], bit[5], bit, bit) Xvresp

function clause decode (0b111100 :
(bit[5]) T :
(bit[5]) _ :
(bit[5]) B :
0b010011010 :
[BX] :
[TX] as instr) =
  Xvresp (T,B,BX,TX)

function clause execute (Xvresp (T, B, BX, TX)) = ()

union ast member (bit[5], bit[5], bit, bit) Xvrspi

function clause decode (0b111100 :
(bit[5]) T :
(bit[5]) _ :
(bit[5]) B :
0b010001001 :
[BX] :
[TX] as instr) =
  Xvrspi (T,B,BX,TX)

function clause execute (Xvrspi (T, B, BX, TX)) = ()

union ast member (bit[5], bit[5], bit, bit) Xvrspic

function clause decode (0b111100 :
(bit[5]) T :
(bit[5]) _ :
(bit[5]) B :
0b010101011 :
[BX] :
[TX] as instr) =
  Xvrspic (T,B,BX,TX)

function clause execute (Xvrspic (T, B, BX, TX)) = ()

union ast member (bit[5], bit[5], bit, bit) Xvrspim

function clause decode (0b111100 :
(bit[5]) T :
(bit[5]) _ :
(bit[5]) B :
0b010111001 :
[BX] :
[TX] as instr) =
  Xvrspim (T,B,BX,TX)

function clause execute (Xvrspim (T, B, BX, TX)) = ()

union ast member (bit[5], bit[5], bit, bit) Xvrspip

function clause decode (0b111100 :
(bit[5]) T :
(bit[5]) _ :
(bit[5]) B :
0b010101001 :
[BX] :
[TX] as instr) =
  Xvrspip (T,B,BX,TX)

function clause execute (Xvrspip (T, B, BX, TX)) = ()

union ast member (bit[5], bit[5], bit, bit) Xvrspiz

function clause decode (0b111100 :
(bit[5]) T :
(bit[5]) _ :
(bit[5]) B :
0b010011001 :
[BX] :
[TX] as instr) =
  Xvrspiz (T,B,BX,TX)

function clause execute (Xvrspiz (T, B, BX, TX)) = ()

union ast member (bit[5], bit[5], bit, bit) Xvrsqrtedp

function clause decode (0b111100 :
(bit[5]) T :
(bit[5]) _ :
(bit[5]) B :
0b011001010 :
[BX] :
[TX] as instr) =
  Xvrsqrtedp (T,B,BX,TX)

function clause execute (Xvrsqrtedp (T, B, BX, TX)) = ()

union ast member (bit[5], bit[5], bit, bit) Xvrsqrtesp

function clause decode (0b111100 :
(bit[5]) T :
(bit[5]) _ :
(bit[5]) B :
0b010001010 :
[BX] :
[TX] as instr) =
  Xvrsqrtesp (T,B,BX,TX)

function clause execute (Xvrsqrtesp (T, B, BX, TX)) = ()

union ast member (bit[5], bit[5], bit, bit) Xvsqrtdp

function clause decode (0b111100 :
(bit[5]) T :
(bit[5]) _ :
(bit[5]) B :
0b011001011 :
[BX] :
[TX] as instr) =
  Xvsqrtdp (T,B,BX,TX)

function clause execute (Xvsqrtdp (T, B, BX, TX)) = ()

union ast member (bit[5], bit[5], bit, bit) Xvsqrtsp

function clause decode (0b111100 :
(bit[5]) T :
(bit[5]) _ :
(bit[5]) B :
0b010001011 :
[BX] :
[TX] as instr) =
  Xvsqrtsp (T,B,BX,TX)

function clause execute (Xvsqrtsp (T, B, BX, TX)) = ()

union ast member (bit[5], bit[5], bit[5], bit, bit, bit) Xvsubdp

function clause decode (0b111100 :
(bit[5]) T :
(bit[5]) A :
(bit[5]) B :
0b01101000 :
[AX] :
[BX] :
[TX] as instr) =
  Xvsubdp (T,A,B,AX,BX,TX)

function clause execute (Xvsubdp (T, A, B, AX, BX, TX)) = ()

union ast member (bit[5], bit[5], bit[5], bit, bit, bit) Xvsubsp

function clause decode (0b111100 :
(bit[5]) T :
(bit[5]) A :
(bit[5]) B :
0b01001000 :
[AX] :
[BX] :
[TX] as instr) =
  Xvsubsp (T,A,B,AX,BX,TX)

function clause execute (Xvsubsp (T, A, B, AX, BX, TX)) = ()

union ast member (bit[3], bit[5], bit[5], bit, bit) Xvtdivdp

function clause decode (0b111100 :
(bit[3]) BF :
(bit[2]) _ :
(bit[5]) A :
(bit[5]) B :
0b01111101 :
[AX] :
[BX] :
(bit[1]) _ as instr) =
  Xvtdivdp (BF,A,B,AX,BX)

function clause execute (Xvtdivdp (BF, A, B, AX, BX)) = ()

union ast member (bit[3], bit[5], bit[5], bit, bit) Xvtdivsp

function clause decode (0b111100 :
(bit[3]) BF :
(bit[2]) _ :
(bit[5]) A :
(bit[5]) B :
0b01011101 :
[AX] :
[BX] :
(bit[1]) _ as instr) =
  Xvtdivsp (BF,A,B,AX,BX)

function clause execute (Xvtdivsp (BF, A, B, AX, BX)) = ()

union ast member (bit[3], bit[5], bit) Xvtsqrtdp

function clause decode (0b111100 :
(bit[3]) BF :
(bit[2]) _ :
(bit[5]) _ :
(bit[5]) B :
0b011101010 :
[BX] :
(bit[1]) _ as instr) =
  Xvtsqrtdp (BF,B,BX)

function clause execute (Xvtsqrtdp (BF, B, BX)) = ()

union ast member (bit[3], bit[5], bit) Xvtsqrtsp

function clause decode (0b111100 :
(bit[3]) BF :
(bit[2]) _ :
(bit[5]) _ :
(bit[5]) B :
0b010101010 :
[BX] :
(bit[1]) _ as instr) =
  Xvtsqrtsp (BF,B,BX)

function clause execute (Xvtsqrtsp (BF, B, BX)) = ()

union ast member (bit[5], bit[5], bit[5], bit, bit, bit) Xxland

function clause decode (0b111100 :
(bit[5]) T :
(bit[5]) A :
(bit[5]) B :
0b10000010 :
[AX] :
[BX] :
[TX] as instr) =
  Xxland (T,A,B,AX,BX,TX)

function clause execute (Xxland (T, A, B, AX, BX, TX)) = ()

union ast member (bit[5], bit[5], bit[5], bit, bit, bit) Xxlandc

function clause decode (0b111100 :
(bit[5]) T :
(bit[5]) A :
(bit[5]) B :
0b10001010 :
[AX] :
[BX] :
[TX] as instr) =
  Xxlandc (T,A,B,AX,BX,TX)

function clause execute (Xxlandc (T, A, B, AX, BX, TX)) = ()

union ast member (bit[5], bit[5], bit[5], bit, bit, bit) Xxlnor

function clause decode (0b111100 :
(bit[5]) T :
(bit[5]) A :
(bit[5]) B :
0b10100010 :
[AX] :
[BX] :
[TX] as instr) =
  Xxlnor (T,A,B,AX,BX,TX)

function clause execute (Xxlnor (T, A, B, AX, BX, TX)) = ()

union ast member (bit[5], bit[5], bit[5], bit, bit, bit) Xxlor

function clause decode (0b111100 :
(bit[5]) T :
(bit[5]) A :
(bit[5]) B :
0b10010010 :
[AX] :
[BX] :
[TX] as instr) =
  Xxlor (T,A,B,AX,BX,TX)

function clause execute (Xxlor (T, A, B, AX, BX, TX)) = ()

union ast member (bit[5], bit[5], bit[5], bit, bit, bit) Xxlxor

function clause decode (0b111100 :
(bit[5]) T :
(bit[5]) A :
(bit[5]) B :
0b10011010 :
[AX] :
[BX] :
[TX] as instr) =
  Xxlxor (T,A,B,AX,BX,TX)

function clause execute (Xxlxor (T, A, B, AX, BX, TX)) = ()

union ast member (bit[5], bit[5], bit[5], bit, bit, bit) Xxmrghw

function clause decode (0b111100 :
(bit[5]) T :
(bit[5]) A :
(bit[5]) B :
0b00010010 :
[AX] :
[BX] :
[TX] as instr) =
  Xxmrghw (T,A,B,AX,BX,TX)

function clause execute (Xxmrghw (T, A, B, AX, BX, TX)) = ()

union ast member (bit[5], bit[5], bit[5], bit, bit, bit) Xxmrglw

function clause decode (0b111100 :
(bit[5]) T :
(bit[5]) A :
(bit[5]) B :
0b00110010 :
[AX] :
[BX] :
[TX] as instr) =
  Xxmrglw (T,A,B,AX,BX,TX)

function clause execute (Xxmrglw (T, A, B, AX, BX, TX)) = ()

union ast member (bit[5], bit[5], bit[5], bit[2], bit, bit, bit) Xxpermdi

function clause decode (0b111100 :
(bit[5]) T :
(bit[5]) A :
(bit[5]) B :
0b0 :
(bit[2]) DM :
0b01010 :
[AX] :
[BX] :
[TX] as instr) =
  Xxpermdi (T,A,B,DM,AX,BX,TX)

function clause execute (Xxpermdi (T, A, B, DM, AX, BX, TX)) = ()

union ast member (bit[5], bit[5], bit[5], bit[5], bit, bit, bit, bit) Xxsel

function clause decode (0b111100 :
(bit[5]) T :
(bit[5]) A :
(bit[5]) B :
(bit[5]) C :
0b11 :
[CX] :
[AX] :
[BX] :
[TX] as instr) =
  Xxsel (T,A,B,C,CX,AX,BX,TX)

function clause execute (Xxsel (T, A, B, C, CX, AX, BX, TX)) = ()

union ast member (bit[5], bit[5], bit[5], bit[2], bit, bit, bit) Xxsldwi

function clause decode (0b111100 :
(bit[5]) T :
(bit[5]) A :
(bit[5]) B :
0b0 :
(bit[2]) SHW :
0b00010 :
[AX] :
[BX] :
[TX] as instr) =
  Xxsldwi (T,A,B,SHW,AX,BX,TX)

function clause execute (Xxsldwi (T, A, B, SHW, AX, BX, TX)) = ()

union ast member (bit[5], bit[2], bit[5], bit, bit) Xxspltw

function clause decode (0b111100 :
(bit[5]) T :
(bit[3]) _ :
(bit[2]) UIM :
(bit[5]) B :
0b010100100 :
[BX] :
[TX] as instr) =
  Xxspltw (T,UIM,B,BX,TX)

function clause execute (Xxspltw (T, UIM, B, BX, TX)) = ()

union ast member (bit[5], bit[5], bit[5], bit) Dlmzb

function clause decode (0b011111 :
(bit[5]) RS :
(bit[5]) RA :
(bit[5]) RB :
0b0001001110 :
[Rc] as instr) =
  Dlmzb (RS,RA,RB,Rc)

function clause execute (Dlmzb (RS, RA, RB, Rc)) = ()

union ast member (bit[5], bit[5], bit[5], bit, bit) Macchw

function clause decode (0b000100 :
(bit[5]) RT :
(bit[5]) RA :
(bit[5]) RB :
[OE] :
0b010101100 :
[Rc] as instr) =
  Macchw (RT,RA,RB,OE,Rc)

function clause execute (Macchw (RT, RA, RB, OE, Rc)) = ()

union ast member (bit[5], bit[5], bit[5], bit, bit) Macchws

function clause decode (0b000100 :
(bit[5]) RT :
(bit[5]) RA :
(bit[5]) RB :
[OE] :
0b011101100 :
[Rc] as instr) =
  Macchws (RT,RA,RB,OE,Rc)

function clause execute (Macchws (RT, RA, RB, OE, Rc)) = ()

union ast member (bit[5], bit[5], bit[5], bit, bit) Macchwu

function clause decode (0b000100 :
(bit[5]) RT :
(bit[5]) RA :
(bit[5]) RB :
[OE] :
0b010001100 :
[Rc] as instr) =
  Macchwu (RT,RA,RB,OE,Rc)

function clause execute (Macchwu (RT, RA, RB, OE, Rc)) = ()

union ast member (bit[5], bit[5], bit[5], bit, bit) Macchwsu

function clause decode (0b000100 :
(bit[5]) RT :
(bit[5]) RA :
(bit[5]) RB :
[OE] :
0b011001100 :
[Rc] as instr) =
  Macchwsu (RT,RA,RB,OE,Rc)

function clause execute (Macchwsu (RT, RA, RB, OE, Rc)) = ()

union ast member (bit[5], bit[5], bit[5], bit, bit) Machhw

function clause decode (0b000100 :
(bit[5]) RT :
(bit[5]) RA :
(bit[5]) RB :
[OE] :
0b000101100 :
[Rc] as instr) =
  Machhw (RT,RA,RB,OE,Rc)

function clause execute (Machhw (RT, RA, RB, OE, Rc)) = ()

union ast member (bit[5], bit[5], bit[5], bit, bit) Machhws

function clause decode (0b000100 :
(bit[5]) RT :
(bit[5]) RA :
(bit[5]) RB :
[OE] :
0b001101100 :
[Rc] as instr) =
  Machhws (RT,RA,RB,OE,Rc)

function clause execute (Machhws (RT, RA, RB, OE, Rc)) = ()

union ast member (bit[5], bit[5], bit[5], bit, bit) Machhwu

function clause decode (0b000100 :
(bit[5]) RT :
(bit[5]) RA :
(bit[5]) RB :
[OE] :
0b000001100 :
[Rc] as instr) =
  Machhwu (RT,RA,RB,OE,Rc)

function clause execute (Machhwu (RT, RA, RB, OE, Rc)) = ()

union ast member (bit[5], bit[5], bit[5], bit, bit) Machhwsu

function clause decode (0b000100 :
(bit[5]) RT :
(bit[5]) RA :
(bit[5]) RB :
[OE] :
0b001001100 :
[Rc] as instr) =
  Machhwsu (RT,RA,RB,OE,Rc)

function clause execute (Machhwsu (RT, RA, RB, OE, Rc)) = ()

union ast member (bit[5], bit[5], bit[5], bit, bit) Maclhw

function clause decode (0b000100 :
(bit[5]) RT :
(bit[5]) RA :
(bit[5]) RB :
[OE] :
0b110101100 :
[Rc] as instr) =
  Maclhw (RT,RA,RB,OE,Rc)

function clause execute (Maclhw (RT, RA, RB, OE, Rc)) = ()

union ast member (bit[5], bit[5], bit[5], bit, bit) Maclhws

function clause decode (0b000100 :
(bit[5]) RT :
(bit[5]) RA :
(bit[5]) RB :
[OE] :
0b111101100 :
[Rc] as instr) =
  Maclhws (RT,RA,RB,OE,Rc)

function clause execute (Maclhws (RT, RA, RB, OE, Rc)) = ()

union ast member (bit[5], bit[5], bit[5], bit, bit) Maclhwu

function clause decode (0b000100 :
(bit[5]) RT :
(bit[5]) RA :
(bit[5]) RB :
[OE] :
0b110001100 :
[Rc] as instr) =
  Maclhwu (RT,RA,RB,OE,Rc)

function clause execute (Maclhwu (RT, RA, RB, OE, Rc)) = ()

union ast member (bit[5], bit[5], bit[5], bit, bit) Maclhwsu

function clause decode (0b000100 :
(bit[5]) RT :
(bit[5]) RA :
(bit[5]) RB :
[OE] :
0b111001100 :
[Rc] as instr) =
  Maclhwsu (RT,RA,RB,OE,Rc)

function clause execute (Maclhwsu (RT, RA, RB, OE, Rc)) = ()

union ast member (bit[5], bit[5], bit[5], bit) Mulchw

function clause decode (0b000100 :
(bit[5]) RT :
(bit[5]) RA :
(bit[5]) RB :
0b0010101000 :
[Rc] as instr) =
  Mulchw (RT,RA,RB,Rc)

function clause execute (Mulchw (RT, RA, RB, Rc)) = ()

union ast member (bit[5], bit[5], bit[5], bit) Mulchwu

function clause decode (0b000100 :
(bit[5]) RT :
(bit[5]) RA :
(bit[5]) RB :
0b0010001000 :
[Rc] as instr) =
  Mulchwu (RT,RA,RB,Rc)

function clause execute (Mulchwu (RT, RA, RB, Rc)) = ()

union ast member (bit[5], bit[5], bit[5], bit) Mulhhw

function clause decode (0b000100 :
(bit[5]) RT :
(bit[5]) RA :
(bit[5]) RB :
0b0000101000 :
[Rc] as instr) =
  Mulhhw (RT,RA,RB,Rc)

function clause execute (Mulhhw (RT, RA, RB, Rc)) = ()

union ast member (bit[5], bit[5], bit[5], bit) Mulhhwu

function clause decode (0b000100 :
(bit[5]) RT :
(bit[5]) RA :
(bit[5]) RB :
0b0000001000 :
[Rc] as instr) =
  Mulhhwu (RT,RA,RB,Rc)

function clause execute (Mulhhwu (RT, RA, RB, Rc)) = ()

union ast member (bit[5], bit[5], bit[5], bit) Mullhw

function clause decode (0b000100 :
(bit[5]) RT :
(bit[5]) RA :
(bit[5]) RB :
0b0110101000 :
[Rc] as instr) =
  Mullhw (RT,RA,RB,Rc)

function clause execute (Mullhw (RT, RA, RB, Rc)) = ()

union ast member (bit[5], bit[5], bit[5], bit) Mullhwu

function clause decode (0b000100 :
(bit[5]) RT :
(bit[5]) RA :
(bit[5]) RB :
0b0110001000 :
[Rc] as instr) =
  Mullhwu (RT,RA,RB,Rc)

function clause execute (Mullhwu (RT, RA, RB, Rc)) = ()

union ast member (bit[5], bit[5], bit[5], bit, bit) Nmacchw

function clause decode (0b000100 :
(bit[5]) RT :
(bit[5]) RA :
(bit[5]) RB :
[OE] :
0b010101110 :
[Rc] as instr) =
  Nmacchw (RT,RA,RB,OE,Rc)

function clause execute (Nmacchw (RT, RA, RB, OE, Rc)) = ()

union ast member (bit[5], bit[5], bit[5], bit, bit) Nmacchws

function clause decode (0b000100 :
(bit[5]) RT :
(bit[5]) RA :
(bit[5]) RB :
[OE] :
0b011101110 :
[Rc] as instr) =
  Nmacchws (RT,RA,RB,OE,Rc)

function clause execute (Nmacchws (RT, RA, RB, OE, Rc)) = ()

union ast member (bit[5], bit[5], bit[5], bit, bit) Nmachhw

function clause decode (0b000100 :
(bit[5]) RT :
(bit[5]) RA :
(bit[5]) RB :
[OE] :
0b000101110 :
[Rc] as instr) =
  Nmachhw (RT,RA,RB,OE,Rc)

function clause execute (Nmachhw (RT, RA, RB, OE, Rc)) = ()

union ast member (bit[5], bit[5], bit[5], bit, bit) Nmachhws

function clause decode (0b000100 :
(bit[5]) RT :
(bit[5]) RA :
(bit[5]) RB :
[OE] :
0b001101110 :
[Rc] as instr) =
  Nmachhws (RT,RA,RB,OE,Rc)

function clause execute (Nmachhws (RT, RA, RB, OE, Rc)) = ()

union ast member (bit[5], bit[5], bit[5], bit, bit) Nmaclhw

function clause decode (0b000100 :
(bit[5]) RT :
(bit[5]) RA :
(bit[5]) RB :
[OE] :
0b110101110 :
[Rc] as instr) =
  Nmaclhw (RT,RA,RB,OE,Rc)

function clause execute (Nmaclhw (RT, RA, RB, OE, Rc)) = ()

union ast member (bit[5], bit[5], bit[5], bit, bit) Nmaclhws

function clause decode (0b000100 :
(bit[5]) RT :
(bit[5]) RA :
(bit[5]) RB :
[OE] :
0b111101110 :
[Rc] as instr) =
  Nmaclhws (RT,RA,RB,OE,Rc)

function clause execute (Nmaclhws (RT, RA, RB, OE, Rc)) = ()

union ast member (bit[5], bit[5]) Icbi

function clause decode (0b011111 :
(bit[5]) _ :
(bit[5]) RA :
(bit[5]) RB :
0b1111010110 :
(bit[1]) _ as instr) =
  Icbi (RA,RB)

function clause execute (Icbi (RA, RB)) = ()

union ast member (bit[4], bit[5], bit[5]) Icbt

function clause decode (0b011111 :
(bit[1]) _ :
(bit[4]) CT :
(bit[5]) RA :
(bit[5]) RB :
0b0000010110 :
(bit[1]) _ as instr) =
  Icbt (CT,RA,RB)

function clause execute (Icbt (CT, RA, RB)) = ()

union ast member (bit[5], bit[5]) Dcba

function clause decode (0b011111 :
(bit[5]) _ :
(bit[5]) RA :
(bit[5]) RB :
0b1011110110 :
(bit[1]) _ as instr) =
  Dcba (RA,RB)

function clause execute (Dcba (RA, RB)) = ()

union ast member (bit[5], bit[5], bit[5]) Dcbt

function clause decode (0b011111 :
(bit[5]) TH :
(bit[5]) RA :
(bit[5]) RB :
0b0100010110 :
(bit[1]) _ as instr) =
  Dcbt (TH,RA,RB)

function clause execute (Dcbt (TH, RA, RB)) = ()

union ast member (bit[5], bit[5], bit[5]) Dcbtst

function clause decode (0b011111 :
(bit[5]) TH :
(bit[5]) RA :
(bit[5]) RB :
0b0011110110 :
(bit[1]) _ as instr) =
  Dcbtst (TH,RA,RB)

function clause execute (Dcbtst (TH, RA, RB)) = ()

union ast member (bit[5], bit[5]) Dcbz

function clause decode (0b011111 :
(bit[5]) _ :
(bit[5]) RA :
(bit[5]) RB :
0b1111110110 :
(bit[1]) _ as instr) =
  Dcbz (RA,RB)

function clause execute (Dcbz (RA, RB)) = ()

union ast member (bit[5], bit[5]) Dcbst

function clause decode (0b011111 :
(bit[5]) _ :
(bit[5]) RA :
(bit[5]) RB :
0b0000110110 :
(bit[1]) _ as instr) =
  Dcbst (RA,RB)

function clause execute (Dcbst (RA, RB)) = ()

union ast member (bit[2], bit[5], bit[5]) Dcbf

function clause decode (0b011111 :
(bit[3]) _ :
(bit[2]) L :
(bit[5]) RA :
(bit[5]) RB :
0b0001010110 :
(bit[1]) _ as instr) =
  Dcbf (L,RA,RB)

function clause execute (Dcbf (L, RA, RB)) = ()

union ast member Isync

function clause decode (0b010011 :
(bit[5]) _ :
(bit[5]) _ :
(bit[5]) _ :
0b0010010110 :
(bit[1]) _ as instr) =
  Isync ()

function clause execute Isync = I_Sync (())

union ast member (bit[5], bit[5], bit[5], bit) Lbarx

function clause decode (0b011111 :
(bit[5]) RT :
(bit[5]) RA :
(bit[5]) RB :
0b0000110100 :
[EH] as instr) =
  Lbarx (RT,RA,RB,EH)

function clause execute (Lbarx (RT, RA, RB, EH)) =
  {
    (bit[64]) b := 0;
    (bit[64]) EA := 0;
    if RA == 0 then b := 0 else b := GPR[RA];
    EA := b + GPR[RB];
    GPR[RT] :=
      0b00000000000000000000000000000000000000000000000000000000 :
        MEMr_reserve (EA,1)
  }

union ast member (bit[5], bit[5], bit[5], bit) Lharx

function clause decode (0b011111 :
(bit[5]) RT :
(bit[5]) RA :
(bit[5]) RB :
0b0001110100 :
[EH] as instr) =
  Lharx (RT,RA,RB,EH)

function clause execute (Lharx (RT, RA, RB, EH)) =
  {
    (bit[64]) b := 0;
    (bit[64]) EA := 0;
    if RA == 0 then b := 0 else b := GPR[RA];
    EA := b + GPR[RB];
    GPR[RT] :=
      0b000000000000000000000000000000000000000000000000 : MEMr_reserve (EA,2)
  }

union ast member (bit[5], bit[5], bit[5], bit) Lwarx

function clause decode (0b011111 :
(bit[5]) RT :
(bit[5]) RA :
(bit[5]) RB :
0b0000010100 :
[EH] as instr) =
  Lwarx (RT,RA,RB,EH)

function clause execute (Lwarx (RT, RA, RB, EH)) =
  {
    (bit[64]) b := 0;
    (bit[64]) EA := 0;
    if RA == 0 then b := 0 else b := GPR[RA];
    EA := b + GPR[RB];
    GPR[RT] := 0b00000000000000000000000000000000 : MEMr_reserve (EA,4)
  }

union ast member (bit[5], bit[5], bit[5]) Stbcx

function clause decode (0b011111 :
(bit[5]) RS :
(bit[5]) RA :
(bit[5]) RB :
0b1010110110 :
0b1 as instr) =
  Stbcx (RS,RA,RB)

function clause execute (Stbcx (RS, RA, RB)) = ()

union ast member (bit[5], bit[5], bit[5]) Sthcx

function clause decode (0b011111 :
(bit[5]) RS :
(bit[5]) RA :
(bit[5]) RB :
0b1011010110 :
0b1 as instr) =
  Sthcx (RS,RA,RB)

function clause execute (Sthcx (RS, RA, RB)) = ()

union ast member (bit[5], bit[5], bit[5]) Stwcx

function clause decode (0b011111 :
(bit[5]) RS :
(bit[5]) RA :
(bit[5]) RB :
0b0010010110 :
0b1 as instr) =
  Stwcx (RS,RA,RB)

function clause execute (Stwcx (RS, RA, RB)) = ()

union ast member (bit[5], bit[5], bit[5], bit) Ldarx

function clause decode (0b011111 :
(bit[5]) RT :
(bit[5]) RA :
(bit[5]) RB :
0b0001010100 :
[EH] as instr) =
  Ldarx (RT,RA,RB,EH)

function clause execute (Ldarx (RT, RA, RB, EH)) =
  {
    (bit[64]) b := 0;
    (bit[64]) EA := 0;
    if RA == 0 then b := 0 else b := GPR[RA];
    EA := b + GPR[RB];
    GPR[RT] := MEMr_reserve (EA,8)
  }

union ast member (bit[5], bit[5], bit[5]) Stdcx

function clause decode (0b011111 :
(bit[5]) RS :
(bit[5]) RA :
(bit[5]) RB :
0b0011010110 :
0b1 as instr) =
  Stdcx (RS,RA,RB)

function clause execute (Stdcx (RS, RA, RB)) = ()

union ast member (bit[2]) Sync

function clause decode (0b011111 :
(bit[3]) _ :
(bit[2]) L :
(bit[5]) _ :
(bit[5]) _ :
0b1001010110 :
(bit[1]) _ as instr) =
  Sync (L)

function clause execute (Sync (L)) =
  switch L { case 0b00 -> { H_Sync (()) } case 0b01 -> { LW_Sync (()) } }

union ast member Eieio

function clause decode (0b011111 :
(bit[5]) _ :
(bit[5]) _ :
(bit[5]) _ :
0b1101010110 :
(bit[1]) _ as instr) =
  Eieio ()

function clause execute Eieio = EIEIO_Sync (())

union ast member (bit[5]) Mbar

function clause decode (0b011111 :
(bit[5]) MO :
(bit[5]) _ :
(bit[5]) _ :
0b1101010110 :
(bit[1]) _ as instr) =
  Mbar (MO)

function clause execute (Mbar (MO)) = ()

union ast member (bit[2]) Wait

function clause decode (0b011111 :
(bit[3]) _ :
(bit[2]) WC :
(bit[5]) _ :
(bit[5]) _ :
0b0000111110 :
(bit[1]) _ as instr) =
  Wait (WC)

function clause execute (Wait (WC)) = ()


typedef decode_failure = enumerate { no_matching_pattern; unsupported_instruction; illegal_instruction } 

function clause decode _ = exit no_matching_pattern

end decode
end execute
end ast

val ast -> ast effect pure supported_instructions
function ast supported_instructions ((ast) instr) = {
  switch instr {
    case (Mbar(_)) -> exit unsupported_instruction
    case (Sync(0b10)) -> exit unsupported_instruction
    case (Sync(0b11)) -> exit unsupported_instruction
    case _ -> instr
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
        case (Lfsu(FRT,RA,D)) -> (RA == 0)
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
        case (Stfdpx(FRSp,RA,RB)) -> (FRSp mod 2 == 1)
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

val ast -> ast effect pure illegal_instructions
function ast illegal_instructions ((ast) instr) =
  if (illegal_instructions_pred ((ast) instr))
  then exit illegal_instruction else instr

(* fetch-decode-execute *)
function unit fde () = {
  NIA := CIA + 4;
  instr := decode(MEMr(CIA, 4));
  instr := supported_instructions(instr);
  execute(instr);
  CIA := NIA;
}
