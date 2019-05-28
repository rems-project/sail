Require Export Rbase.
Require Import Reals.
Require Export ROrderedType.
Require Import Sail2_values.

(* "Decidable" in a classical sense... *)
Instance Decidable_eq_real : forall (x y : R), Decidable (x = y) :=
  Decidable_eq_from_dec Req_dec.

Definition realFromFrac (num denom : Z) : R := Rdiv (IZR num) (IZR denom).

Definition neg_real := Ropp.
Definition mult_real := Rmult.
Definition sub_real := Rminus.
Definition add_real := Rplus.
Definition div_real := Rdiv.
Definition sqrt_real := sqrt.
Definition abs_real := Rabs.

(* Use flocq definitions, but without making the whole library a dependency. *)
Definition round_down (x : R) := (up x - 1)%Z.
Definition round_up (x : R) := (- round_down (- x))%Z.

Definition to_real := IZR.

Definition eq_real := Reqb.
Definition gteq_real (x y : R) : bool := if Rge_dec x y then true else false.
Definition lteq_real (x y : R) : bool := if Rle_dec x y then true else false.
Definition gt_real (x y : R) : bool := if Rgt_dec x y then true else false.
Definition lt_real (x y : R) : bool := if Rlt_dec x y then true else false.

(* Export select definitions from outside of Rbase *)
Definition pow_real := powerRZ.

Definition print_real (_ : string) (_ : R) : unit := tt.
Definition prerr_real (_ : string) (_ : R) : unit := tt.
