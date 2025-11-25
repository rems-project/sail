Require Extraction.

From Stdlib Require Import String.
From Stdlib Require Import ZArith.

From Stdlib Require ExtrOcamlBasic.
From Stdlib Require ExtrOcamlNatBigInt.
From Stdlib Require ExtrOcamlNativeString.
From Stdlib Require ExtrOcamlZBigInt.

Set Extraction KeepSingleton.
Set Extraction Output Directory ".".

From Stdlib Require Import Bool.

Parameter rational : Set.

Extract Inlined Constant rational => "Rational.t".

Inductive bit : Set :=
| B0 : bit
| B1 : bit.

Inductive value : Set :=
| V_bitvector : list bit -> value
| V_vector : list value -> value
| V_list : list value -> value
| V_int : Z -> value
| V_real : rational -> value
| V_bool : bool -> value
| V_tuple : list value -> value
| V_unit : value
| V_string : string -> value
| V_ref : string -> value
| V_member : string -> value
| V_ctor : string -> list value -> value
| V_record : list (string * value) -> value
| V_attempted_read : string -> value.

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
        let extend := (Z.to_nat n) - len in
        Some (V_bitvector (List.repeat B0 extend ++ bitlist))
    | _ => None
    end.
End Primops.
