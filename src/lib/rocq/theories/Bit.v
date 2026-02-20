Require Extraction.

Set Extraction KeepSingleton.
Set Extraction Output Directory ".".

Inductive bit : Set :=
| B0 : bit
| B1 : bit.

Definition bit_eqb (lhs rhs : bit) : bool :=
  match (lhs, rhs) with
  | (B0, B0) => true
  | (B1, B1) => true
  | _ => false
  end.

Lemma bit_eqb_refl : forall b, bit_eqb b b = true.
Proof.
  destruct b; reflexivity.
Qed.
