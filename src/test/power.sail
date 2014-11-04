val extern forall Nat 'm, Nat 'n. (implicit<'m>,bit['n]) -> bit['m] effect pure EXTS

(* XXX binary coded decimal *)
function forall Type 'a . 'a DEC_TO_BCD ( x ) = x
function forall Type 'a . 'a BCD_TO_DEC ( x ) = x
(* XXX carry out *)
function bit carry_out ( x ) = bitzero
(* XXX Storage control *)
function forall Type 'a . 'a real_addr ( x ) = x
(* XXX For stvxl and lvxl - what does that do? *)
function forall Type 'a . unit mark_as_not_likely_to_be_needed_again_anytime_soon ( x ) = ()

(* XXX *)
val extern forall Nat 'k, Nat 'r,
  0 <= 'k, 'k <= 64, 'r + 'k = 64.
  (bit[64], [|'k|]) -> [|0:'r|] effect pure countLeadingZeroes

function forall Nat 'n, Nat 'm .
  bit['m] EXTS_EXPLICIT((bit['n]) v, ([|'m|]) m) =
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

function (bit[64]) ROTL(v, n) = v[n .. 63] : v[0 .. (n-1)]

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

register (bit[64]) SPRG4
register (bit[64]) SPRG5
register (bit[64]) SPRG6
register (bit[64]) SPRG7

(* XXX bogus, length should be 1024 with many more values - cf. mfspr
  definition - eg. SPRG4 to SPRG7 are at offsets 260 to 263, VRSAVE is 256,
  etc. *)
let (vector <0, 10, inc, (register<(bit[64])>) >) SPR =
  [ undefined, XER, undefined, undefined,
    undefined, undefined, undefined, undefined,
    LR, CTR
  ]

(* XXX DCR is implementation-dependent; also, some DCR are only 32 bits
 instead of 64, and mtdcrux/mfdcrux do special tricks in that case, not
 shown in pseudo-code. We just define two dummy DCR here, using sparse
 vector definition. *)
register (vector <0, 64, inc, bit>) DCR0
register (vector <0, 64, inc, bit>) DCR1
let (vector <0, 2** 64, inc, (register<(vector<0, 64, inc, bit>)>) >) DCR =
  [ 0=DCR0, 1=DCR1 ]

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


(* XXX *)
val extern bit[32] -> bit[64] effect pure DOUBLE
val extern bit[64] -> bit[32] effect pure SINGLE

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
val extern forall Nat 'n, Nat 'm. bit['n] -> bit['m] effect pure EXTZ

(* Chop has a very weird definition where the resulting size depends of
   context, but in practice it is used with the following definition everywhere,
   except in vaddcuw which probably needs to be patched accordingly. *)
val forall Nat 'n, Nat 'm, 'm <= 'n. (bit['n], [|'m|]) -> bit['m] effect pure Chop
function forall Nat 'm. (bit['m]) Chop(x, y) = x[0..y]

val forall Nat 'n, Nat 'm, Nat 'k, 'n <= 0, 0 <= 'm.
  (implicit<'k>, int, [|'n|], [|'m|]) -> bit['k] effect { wreg } Clamp

function forall Nat 'n, Nat 'm, Nat 'k, 'n <= 0, 0 <= 'm. (bit['k])
Clamp((int) x, ([|'n|]) y, ([|'m|]) z) = {
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


(* XXX effect for trap? *)
val extern unit -> unit effect pure trap

register (bit[1]) mode64bit
register (bool) bigendianmode

val bit[64] -> unit effect {rreg,wreg} set_overflow_cr0 
function (unit) set_overflow_cr0(target_register) = {
  (if mode64bit
   then m := 0
   else m := 32);
  (if target_register[m..63] < 0
  then c := 0b100
  else if target_register[m..63] > 0 
  then c := 0b010
  else c := 0b001);
  CR.CR0 := c:[XER.SO]
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
    if ~ (BO[2]) then CTR := CTR - 1 else ();
    ctr_ok := (BO[2] | (CTR[M .. 63] != 0) ^ BO[3]);
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
    if ~ (BO[2]) then CTR := CTR - 1 else ();
    ctr_ok := (BO[2] | (CTR[M .. 63] != 0) ^ BO[3]);
    cond_ok := (BO[0] | CR[BI + 32] ^ ~ (BO[1]));
    if ctr_ok & cond_ok then NIA := LR[0 .. 61] : 0b00 else ();
    if LK then LR := CIA + 4 else ()
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
    if RA == 0 then b := 0 else b := GPR[RA];
    EA := b + EXTS (D);
    GPR[RT] := 0b00000000000000000000000000000000 : MEMr (EA,4)
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
    if RA == 0 then b := 0 else b := GPR[RA];
    EA := b + EXTS (DS : 0b00);
    GPR[RT] := MEMr (EA,8)
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
    if RA == 0 then b := 0 else b := GPR[RA];
    EA := b + EXTS (D);
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
    EA := GPR[RA] + EXTS (D);
    MEMw(EA,4) := (GPR[RS])[32 .. 63];
    GPR[RA] := EA
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
    if RA == 0 then b := 0 else b := GPR[RA];
    EA := b + EXTS (DS : 0b00);
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
    EA := GPR[RA] + EXTS (DS : 0b00);
    MEMw(EA,8) := GPR[RS];
    GPR[RA] := EA
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
    (range<0, 32> ) r := 0;
    r := RT - 1;
    (range<0, 32> ) size := if NB == 0 then 32 else NB;
    (bit[256]) membuffer := MEMr (EA,size);
    j := 0;
    i := 32;
    foreach (n from (if NB == 0 then 32 else NB) to 1 by 1 in dec)
    {
      if i == 32
      then {
        r := (range<0, 32> ) (r + 1) mod 32;
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
  {
    (bit[64]) temp := ~ (GPR[RA]) + GPR[RB] + 1;
    GPR[RT] := temp;
    if Rc then set_overflow_cr0 (temp) else ()
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
  {
    (bit[64]) temp := ~ (GPR[RA]) + 1;
    GPR[RT] := temp;
    if Rc then set_overflow_cr0 (temp) else ()
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
  {
    (bit[64]) temp := (GPR[RA])[32 .. 63] * (GPR[RB])[32 .. 63];
    GPR[RT] := temp;
    if Rc then set_overflow_cr0 (temp) else ()
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

union ast member (bit[5], bit[5], bit[5], bit) Or

function clause decode (0b011111 :
(bit[5]) RS :
(bit[5]) RA :
(bit[5]) RB :
0b0110111100 :
[Rc] as instr) =
  Or (RS,RA,RB,Rc)

function clause execute (Or (RS, RA, RB, Rc)) = GPR[RA] := (GPR[RS] | GPR[RB])

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
    (GPR[RA])[32..63] := (GPR[RS])[32 .. 63];
    (GPR[RA])[0..31] := s ^^ 32
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
    GPR[RA] := (r & m)
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
    then trap ()
    else if length (SPR[n]) == 64
    then SPR[n] := GPR[RS]
    else SPR[n] := (GPR[RS])[32 .. 63]
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

union ast member (bit[5], bit[5], bit[16]) Lfd

function clause decode (0b110010 :
(bit[5]) FRT :
(bit[5]) RA :
(bit[16]) D as instr) =
  Lfd (FRT,RA,D)

function clause execute (Lfd (FRT, RA, D)) =
  {
    (bit[64]) b := 0;
    if RA == 0 then b := 0 else b := GPR[RA];
    EA := b + EXTS (D);
    FPR[FRT] := MEMr (EA,8)
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
    if RA == 0 then b := 0 else b := GPR[RA];
    EA := b + EXTS (D);
    MEMw(EA,8) := FPR[FRS]
  }

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
    if RA == 0 then b := 0 else b := GPR[RA];
    EA := b + GPR[RB];
    VR[VRT] :=
      MEMr
        (EA & 0b1111111111111111111111111111111111111111111111111111111111110000,16)
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
    if RA == 0 then b := 0 else b := GPR[RA];
    EA := b + GPR[RB];
    MEMw(EA & 0b1111111111111111111111111111111111111111111111111111111111110000,16) :=
      VR[VRS]
  }

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

union ast member (bit[5]) Mbar

function clause decode (0b011111 :
(bit[5]) MO :
(bit[5]) _ :
(bit[5]) _ :
0b1101010110 :
(bit[1]) _ as instr) =
  Mbar (MO)

function clause execute (Mbar (MO)) = ()


typedef decode_failure = enumerate { no_matching_pattern; unsupported_instruction } 

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

(* fetch-decode-execute *)
function unit fde () = {
  NIA := CIA + 4;
  instr := decode(MEMr(CIA, 4));
  instr := supported_instructions(instr);
  execute(instr);
  CIA := NIA;
}
