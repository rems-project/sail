Require Extraction.

From Stdlib Require ExtrOcamlBasic.

Set Extraction KeepSingleton.
Set Extraction Output Directory ".".

Parameter num : Set.

Extract Inlined Constant num => "Nat_big_num.num".

Parameter rational : Set.

Extract Inlined Constant rational => "Rational.t".

Parameter string : Set.

Extract Inlined Constant string => "string".

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
