Require Import Sail2_values.

Definition string_sub (s : string) (start : Z) (len : Z) : string :=
  String.substring (Z.to_nat start) (Z.to_nat len) s.

Definition string_startswith s expected :=
  let prefix := String.substring 0 (String.length expected) s in
  generic_eq prefix expected.

Definition string_drop s (n : {n : Z & ArithFact (n >= 0)}) :=
  let n := Z.to_nat (projT1 n) in
  String.substring n (String.length s - n) s.

Definition string_length s : {n : Z & ArithFact (n >= 0)} :=
 build_ex (Z.of_nat (String.length s)).

Definition string_append := String.append.

(* TODO: maybe_int_of_prefix, maybe_int_of_string *)

Fixpoint n_leading_spaces (s:string) : nat :=
  match s with
  | EmptyString => 0
  | String " " t => S (n_leading_spaces t)
  | _ => 0
  end.

Definition opt_spc_matches_prefix s : option (unit * {n : Z & ArithFact (n >= 0)}) :=
  Some (tt, build_ex (Z.of_nat (n_leading_spaces s))).

Definition spc_matches_prefix s : option (unit * {n : Z & ArithFact (n >= 0)}) :=
  match n_leading_spaces s with
  | O => None
  | S n => Some (tt, build_ex (Z.of_nat (S n)))
  end.