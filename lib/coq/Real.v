Require Export Rbase.
Require Import Reals.
Require Export ROrderedType.
Require Import Sail.Values.
Local Open Scope Z.

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




Lemma IZRdiv m n :
  0 < m -> 0 < n ->
  (IZR (m / n) <= IZR m / IZR n)%R.
intros.
apply Rmult_le_reg_l with (r := IZR n).
auto using IZR_lt.
unfold Rdiv.
rewrite <- Rmult_assoc.
rewrite Rinv_r_simpl_m.
rewrite <- mult_IZR.
apply IZR_le.
apply Z.mul_div_le.
assumption.
discrR.
omega.
Qed.

(* One annoying use of reals in the ARM spec I've been looking at. *)
Lemma round_up_div m n :
  0 < m -> 0 < n ->
  round_up (div_real (to_real m) (to_real n)) = (m + n - 1) / n.
intros.
unfold round_up, round_down, div_real, to_real.
apply Z.eq_opp_l.
apply Z.sub_move_r.
symmetry.
apply up_tech.

rewrite Ropp_Ropp_IZR.
apply Ropp_le_contravar.
apply Rmult_le_reg_l with (r := IZR n).
auto using IZR_lt.
unfold Rdiv.
rewrite <- Rmult_assoc.
rewrite Rinv_r_simpl_m.
rewrite <- mult_IZR.
apply IZR_le.
assert (diveq : n*((m+n-1)/n) = (m+n-1) - (m+n-1) mod n).
apply Zplus_minus_eq.
rewrite (Z.add_comm ((m+n-1) mod n)).
apply Z.div_mod.
omega.
rewrite diveq.
assert (modmax : (m+n-1) mod n < n).
specialize (Z.mod_pos_bound (m+n-1) n). intuition.
omega.

discrR; omega.

rewrite <- Z.opp_sub_distr.
rewrite Ropp_Ropp_IZR.
apply Ropp_lt_contravar.
apply Rmult_lt_reg_l with (r := IZR n).
auto using IZR_lt.
unfold Rdiv.
rewrite <- Rmult_assoc.
rewrite Rinv_r_simpl_m.
2: { discrR. omega. }
rewrite <- mult_IZR.
apply IZR_lt.
rewrite Z.mul_sub_distr_l.
apply Z.le_lt_trans with (m := m+n-1-n*1).
apply Z.sub_le_mono_r.
apply Z.mul_div_le.
assumption.
omega.
Qed.
