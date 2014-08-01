val extern forall Nat 'n. bit['n] -> bit[64] effect pure EXTS

(* XXX binary coded decimal *)
function forall Type 'a . 'a DEC_TO_BCD ( x ) = x
function forall Type 'a . 'a BCD_TO_DEC ( x ) = x
(* XXX carry out *)
function bit carry_out ( x ) = bitzero
(* XXX length *)
function nat length ( x ) = 64
(* XXX Storage control *)
function forall Type 'a . 'a real_addr ( x ) = x

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
  (bit[64]) mask := 0;
  if(start > stop) then {
    mask[start .. 63] := bitone ^^ (64 - start);
    mask[0 .. stop] := bitone ^^ (stop + 1);
  } else {
    mask[start .. stop ] := bitone ^^ (stop - start + 1);
  };
  mask;
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

val forall Nat 'n, Nat 'm, 'n <= 0, 0 <= 'm.
  (nat, [|'n|], [|'m|]) -> [|'n:'m|] effect { wreg } Clamp

function forall Nat 'n, Nat 'm, 'n <= 0, 0 <= 'm. ([|'n:'m|])
Clamp((nat) x, ([|'n|]) y, ([|'m|]) z) = {
  ([|'n:'m|]) result := 0;
  if (x<y) then {
    result := y;
    VSCR.SAT := bitone;
  } else if (x > z) then {
    result := z;
    VSCR.SAT := bitone;
  } else {
    result := x;
  };
  result;
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


val extern forall Nat 'n. ( nat , [|'n|] , bit[8*'n]) -> unit effect { wmem } MEMw
val extern forall Nat 'n. ( nat , [|'n|] ) -> (bit[8 * 'n]) effect { rmem } MEMr

(* XXX effect for trap? *)
val extern unit -> unit effect pure trap

register (bool) mode64bit

scattered function unit execute
scattered typedef ast = const union

val bit[32] -> ast effect pure decode

scattered function ast decode

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
    if ~ (BO[2]) then CTR := CTR - 1;
    ctr_ok := (BO[2] | (CTR[M .. 63] != 0) ^ BO[3]);
    cond_ok := (BO[0] | CR[BI + 32] ^ ~ (BO[1]));
    if ctr_ok & cond_ok then NIA := LR[0 .. 61] : 0b00;
    if LK then LR := CIA + 4
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

union ast member (bit[5], bit[5], bit[16]) Addi

function clause decode (0b001110 :
(bit[5]) RT :
(bit[5]) RA :
(bit[16]) SI as instr) =
  Addi (RT,RA,SI)

function clause execute (Addi (RT, RA, SI)) =
  if RA == 0 then GPR[RT] := EXTS (SI) else GPR[RT] := GPR[RA] + EXTS (SI)

union ast member (bit[5], bit[5], bit[5], bit) Or

function clause decode (0b011111 :
(bit[5]) RS :
(bit[5]) RA :
(bit[5]) RB :
0b0110111100 :
[Rc] as instr) =
  Or (RS,RA,RB,Rc)

function clause execute (Or (RS, RA, RB, Rc)) = GPR[RA] := (GPR[RS] | GPR[RB])


end decode
end execute
end ast


register ast instr (* monitor decoded instructions *)

(* fetch-decode-execute *)
function unit fde () = {
  NIA := CIA + 4;
  instr := decode(MEMr(CIA, 4));
  execute(instr);
  CIA := NIA;
}
