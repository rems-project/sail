Require Extraction.

From Stdlib Require ExtrOcamlBasic.

Set Extraction KeepSingleton.
Set Extraction Output Directory ".".

From Stdlib Require Import Bool.

Parameter num : Set.

Extract Inlined Constant num => "Nat_big_num.num".

Parameter rational : Set.

Extract Inlined Constant rational => "Rational.t".

Parameter string : Set.

Extract Inlined Constant string => "string".

Parameter eq_string : string -> string -> bool.

Extract Inlined Constant eq_string => "String.equal".

Axiom eq_string_refl : forall x, Is_true (eq_string x x).
Axiom eq_string_sym : forall x y, Is_true (eq_string x y) -> Is_true (eq_string y x).
Axiom eq_string_trans : forall x y z, Is_true (eq_string x y) -> Is_true (eq_string y z) -> Is_true (eq_string x z).

Parameter lt_string : string -> string -> bool.

Extract Inlined Constant lt_string => "(fun s1 s2 -> String.compare s1 s2 < 0)".

Axiom lt_string_trans : forall x y z, Is_true (lt_string x y) -> Is_true (lt_string y z) -> Is_true (lt_string x z).
Axiom lt_string_not_eq_string: forall x y, Is_true (lt_string x y) -> ~ Is_true (eq_string x y).

Axiom lt_string_as_gt : forall x y, ~ Is_true (lt_string x y) -> ~ Is_true (eq_string x y) -> Is_true (lt_string y x).

Inductive bit : Set :=
| B0 : bit
| B1 : bit.

Inductive value : Set :=
| V_vector : list value -> value
| V_list : list value -> value
| V_int : num -> value
| V_real : rational -> value
| V_bool : bool -> value
| V_bit : bit -> value
| V_tuple : list value -> value
| V_unit : value
| V_string : string -> value
| V_ref : string -> value
| V_member : string -> value
| V_ctor : string -> list value -> value
| V_record : list (string * value) -> value
| V_attempted_read : string -> value.
