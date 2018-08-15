Require Import Coq.Arith.Peano_dec.
Require Import Coq.Logic.Eqdep Coq.Logic.Eqdep_dec Coq.Program.Equality.

(** * Equalities on dependent types *)

Theorem eq_rect_nat_double : forall T (a b c : nat) x ab bc,
  eq_rect b T (eq_rect a T x b ab) c bc = eq_rect a T x c (eq_trans ab bc).
Proof.
  intros.
  destruct ab.
  destruct bc.
  rewrite (UIP_dec eq_nat_dec (eq_trans eq_refl eq_refl) eq_refl).
  simpl.
  auto.
Qed.

Hint Rewrite eq_rect_nat_double.
Hint Rewrite <- (eq_rect_eq_dec eq_nat_dec).

Ltac generalize_proof :=
    match goal with
    | [ |- context[eq_rect _ _ _ _ ?H ] ] => generalize H
    end.

Ltac eq_rect_simpl :=
  unfold eq_rec_r, eq_rec;
  repeat rewrite eq_rect_nat_double;
  repeat rewrite <- (eq_rect_eq_dec eq_nat_dec).

Ltac destruct_existT :=
  repeat match goal with
           | [H: existT _ _ _ = existT _ _ _ |- _] =>
             (apply Eqdep.EqdepTheory.inj_pair2 in H; subst)
         end.

Lemma eq_rect_word_offset_helper : forall a b c,
  a = b -> c + a = c + b.
Proof.
  intros; congruence.
Qed.

Lemma eq_rect_word_mult_helper : forall a b c,
  a = b -> a * c = b * c.
Proof.
  intros; congruence.
Qed.

Lemma existT_eq_rect:
  forall (X: Type) (P: X -> Type) (x1 x2: X) (H1: P x1) (Hx: x1 = x2),
    existT P x2 (eq_rect x1 P H1 x2 Hx) =
    existT P x1 H1.
Proof.
  intros; subst; reflexivity.
Qed.

Lemma existT_eq_rect_eq:
  forall (X: Type) (P: X -> Type) (x1 x2: X)
         (H1: P x1) (H2: P x2) (Hx: x1 = x2),
    H2 = eq_rect _ P H1 _ Hx ->
    existT P x1 H1 = existT P x2 H2.
Proof.
  intros; subst; reflexivity.
Qed.

Lemma eq_rect_existT_eq:
  forall (X: Type) (P: X -> Type) (x1 x2: X)
         (H1: P x1) (H2: P x2) (Hx: x1 = x2)
         (Hex: existT P x1 H1 = existT P x2 H2),
    H2 = eq_rect _ P H1 _ Hx.
Proof.
  intros; subst.
  subst; destruct_existT.
  reflexivity.
Qed.

