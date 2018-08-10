Require Import Sail2_values.

Definition string_sub (s : string) (start : Z) (len : Z) : string :=
  String.substring (Z.to_nat start) (Z.to_nat len) s.

Definition string_startswith s expected :=
  let prefix := String.substring 0 (String.length expected) s in
  generic_eq prefix expected.

Definition string_drop s n :=
  let n := Z.to_nat n in
  String.substring n (String.length s - n) s.

Definition string_length s := Z.of_nat (String.length s).

Definition string_append := String.append.