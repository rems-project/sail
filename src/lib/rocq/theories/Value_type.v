Require Extraction.

Set Extraction KeepSingleton.
Set Extraction Output Directory ".".

From Stdlib Require Import Bool.
From Stdlib Require Import String.
From Stdlib Require Import ZArith.
From Stdlib Require Import QArith.

From Stdlib Require ExtrOcamlBasic.
From Stdlib Require ExtrOcamlNatBigInt.
From Stdlib Require ExtrOcamlNativeString.
From Stdlib Require ExtrOcamlZBigInt.

Require Import Bit.
Require Import Ast.

Module Primops.
  Definition gt_int (v1 : value) (v2 : value) : option value :=
    match (v1, v2) with
    | (V_int v1, V_int v2) => Some (V_bool (Z.gtb v1 v2))
    | _ => None
    end.

  Definition lt_int (v1 : value) (v2 : value) : option value :=
    match (v1, v2) with
    | (V_int v1, V_int v2) => Some (V_bool (Z.ltb v1 v2))
    | _ => None
    end.

  Definition add_int (v1 : value) (v2 : value) : option value :=
    match (v1, v2) with
    | (V_int v1, V_int v2) => Some (V_int (Z.add v1 v2))
    | _ => None
    end.

  Definition sub_int (v1 : value) (v2 : value) : option value :=
    match (v1, v2) with
    | (V_int v1, V_int v2) => Some (V_int (Z.sub v1 v2))
    | _ => None
    end.

  Definition zero_extend (bits : value) (n : value) : option value :=
    match (bits, n) with
    | (V_bitvector bitlist, V_int n) =>
      let len := List.length bitlist in
      if Z.ltb n (Z.of_nat len) then
        None
      else
        let extend := Nat.sub (Z.to_nat n) len in
        Some (V_bitvector (List.repeat B0 extend ++ bitlist))
    | _ => None
    end.
End Primops.
