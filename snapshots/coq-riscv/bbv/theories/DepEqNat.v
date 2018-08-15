
(* This file defines nat_cast, an alternative to eq_rect which works only for type nat instead
   of any type A.
   The motivation behind nat_cast is that it only matches on proofs in contradictory cases,
   so functions using nat_cast can always be run inside Coq using cbv, whereas function using
   eq_rect cannot. *)

Arguments id {A} x.

(* Transport equality, only matching on eq_refl in contradictory cases, to make sure
   terms using this function reduce *)
Fixpoint nat_cast (P : nat -> Type) {n m} : n = m -> P n -> P m.
  refine match n, m return n = m -> P n -> P m with
         | O, O => fun _ => id
         | S n, S m => fun pf => @nat_cast (fun n => P (S n)) n m (f_equal pred pf)
         | _, _ => fun pf => match _ pf : False with end
         end;
    clear; abstract congruence.
Defined. (* thx Jason *)

Lemma nat_cast_eq_rect: forall (P : nat -> Type),
  forall (n m : nat)  (e: n = m) (pn: P n),
  nat_cast P e pn = eq_rect n P pn m e.
Proof.
  destruct e.
  revert dependent P; induction n; simpl; intros.
  - reflexivity.
  - rewrite IHn. reflexivity.
Qed. (* thx Clement *)

Lemma nat_cast_proof_irrel: forall (P : nat -> Type),
  forall (n m : nat)  (e1 e2: n = m) (pn: P n),
  nat_cast P e1 pn = nat_cast P e2 pn.
Proof.
  destruct e1.
  revert dependent P; induction n; simpl; intros.
  - reflexivity.
  - erewrite IHn. reflexivity.
Qed.

Lemma nat_cast_same: forall (P: nat -> Type) (s: nat) (n: P s),
  nat_cast P eq_refl n = n.
Proof.
  intros. rewrite nat_cast_eq_rect. reflexivity.
Qed.

Lemma nat_cast_fuse: forall (P: nat -> Type) (n1 n2 n3: nat) (e12: n1 = n2) (e23: n2 = n3) (x: P n1),
  nat_cast P e23 (nat_cast P e12 x) = nat_cast P (eq_trans e12 e23) x.
Proof.
  destruct e12.
  destruct e23.
  intros.
  rewrite nat_cast_same.
  reflexivity.
Qed.

Lemma nat_cast_cast ni no (pf: ni = no) (P: nat -> Type) (x : P ni):
  nat_cast P pf x = match pf in _ = Y return P Y with
                    | eq_refl => x
                    end.
Proof.
  destruct pf.
  rewrite nat_cast_same.
  auto.
Qed.
 