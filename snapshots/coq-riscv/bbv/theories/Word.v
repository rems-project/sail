(** Fixed precision machine words *)

Require Import Coq.Arith.Arith Coq.Arith.Div2 Coq.NArith.NArith Coq.Bool.Bool Coq.omega.Omega.
Require Import Coq.Logic.Eqdep_dec Coq.Logic.EqdepFacts.
Require Import Coq.Program.Tactics Coq.Program.Equality.
Require Import Coq.setoid_ring.Ring.
Require Import Coq.setoid_ring.Ring_polynom.
Require Import bbv.Nomega.
Require Export bbv.ZLib bbv.NatLib bbv.NLib.
Require Export bbv.DepEq bbv.DepEqNat.

Require Import Coq.micromega.Lia.
(* for nia (integer arithmetic with multiplications that omega cannot solve *)

Set Implicit Arguments.

(*! Definitions *)

(** * [word] *)

Inductive word : nat -> Set :=
| WO : word O
| WS : bool -> forall n, word n -> word (S n).

Delimit Scope word_scope with word.
Bind Scope word_scope with word.

(* This scope will be closed at the end of the file. *)
(* Coq trunk seems to inherit open scopes across imports? *)
Open Scope word_scope.

(** * Conversion to and from [nat] (or [N]), zero and one *)

Fixpoint wordToNat sz (w : word sz) : nat :=
  match w with
    | WO => O
    | WS false w' => (wordToNat w') * 2
    | WS true w' => S (wordToNat w' * 2)
  end.

Fixpoint wordToNat' sz (w : word sz) : nat :=
  match w with
    | WO => O
    | WS false w' => 2 * wordToNat w'
    | WS true w' => S (2 * wordToNat w')
  end.

Fixpoint natToWord (sz n : nat) : word sz :=
  match sz with
    | O => WO
    | S sz' => WS (mod2 n) (natToWord sz' (div2 n))
  end.

Fixpoint wordToN sz (w : word sz) : N :=
  match w with
    | WO => 0
    | WS false w' => 2 * wordToN w'
    | WS true w' => N.succ (2 * wordToN w')
  end%N.

Definition wzero sz := natToWord sz 0.

Fixpoint wzero' (sz : nat) : word sz :=
  match sz with
    | O => WO
    | S sz' => WS false (wzero' sz')
  end.

Fixpoint posToWord (sz : nat) (p : positive) {struct p} : word sz :=
  match sz with
    | O => WO
    | S sz' =>
      match p with
        | xI p' => WS true (posToWord sz' p')
        | xO p' => WS false (posToWord sz' p')
        | xH => WS true (wzero' sz')
      end
  end.

Definition NToWord (sz : nat) (n : N) : word sz :=
  match n with
    | N0 => wzero' sz
    | Npos p => posToWord sz p
  end.

Definition wone sz := natToWord sz 1.

Fixpoint wones (sz : nat) : word sz :=
  match sz with
    | O => WO
    | S sz' => WS true (wones sz')
  end.

(** * MSB, LSB, head, and tail *)

Fixpoint wmsb sz (w : word sz) (a : bool) : bool :=
  match w with
    | WO => a
    | WS b x => wmsb x b
  end.

Definition wlsb sz (w: word (S sz)) :=
  match w with
  | WO => idProp
  | WS b _ => b
  end.

Definition whd sz (w : word (S sz)) : bool :=
  match w in word sz' return match sz' with
                               | O => unit
                               | S _ => bool
                             end with
    | WO => tt
    | WS b _ => b
  end.

Definition wtl sz (w : word (S sz)) : word sz :=
  match w in word sz' return match sz' with
                               | O => unit
                               | S sz'' => word sz''
                             end with
    | WO => tt
    | WS _ w' => w'
  end.

Fixpoint rep_bit (n : nat) (b : word 1) : word n :=
  match n as n0 return (word n0) with
  | 0 => WO
  | S n0 => WS (whd b) (rep_bit n0 b)
  end.

(** * Shattering (to define [weq]) and decidable equality **)

Lemma shatter_word : forall n (a : word n),
  match n return word n -> Prop with
    | O => fun a => a = WO
    | S _ => fun a => a = WS (whd a) (wtl a)
  end a.
  destruct a; eauto.
Qed.

Lemma shatter_word_S : forall n (a : word (S n)),
  exists b, exists c, a = WS b c.
Proof.
  intros n a; repeat eexists; apply (shatter_word a).
Qed.
Lemma shatter_word_0 : forall a : word 0,
  a = WO.
Proof.
  intros a; apply (shatter_word a).
Qed.

Hint Resolve shatter_word_0.

Definition weq : forall sz (x y : word sz), {x = y} + {x <> y}.
  refine (fix weq sz (x : word sz) : forall y : word sz, {x = y} + {x <> y} :=
    match x in word sz return forall y : word sz, {x = y} + {x <> y} with
      | WO => fun _ => left _ _
      | WS b x' => fun y => if bool_dec b (whd y)
        then if weq _ x' (wtl y) then left _ _ else right _ _
        else right _ _
    end); clear weq.

  abstract (symmetry; apply shatter_word_0).

  abstract (subst; symmetry; apply (shatter_word (n:=S _) _)).

  let y' := y in (* kludge around warning of mechanically generated names not playing well with [abstract] *)
  abstract (rewrite (shatter_word y'); simpl; intro H; injection H; intros;
    eauto using inj_pair2_eq_dec, eq_nat_dec).

  let y' := y in (* kludge around warning of mechanically generated names not playing well with [abstract] *)
  abstract (rewrite (shatter_word y'); simpl; intro H; injection H; auto).
Defined.

Fixpoint weqb sz (x : word sz) : word sz -> bool :=
  match x in word sz return word sz -> bool with
    | WO => fun _ => true
    | WS b x' => fun y =>
      if eqb b (whd y)
      then if @weqb _ x' (wtl y) then true else false
      else false
  end.

(** * Combining and splitting *)

Fixpoint combine (sz1 : nat) (w : word sz1) : forall sz2, word sz2 -> word (sz1 + sz2) :=
  match w in word sz1 return forall sz2, word sz2 -> word (sz1 + sz2) with
    | WO => fun _ w' => w'
    | WS b w' => fun _ w'' => WS b (combine w' w'')
  end.

Fixpoint split1 (sz1 sz2 : nat) : word (sz1 + sz2) -> word sz1 :=
  match sz1 with
    | O => fun _ => WO
    | S sz1' => fun w => WS (whd w) (split1 sz1' sz2 (wtl w))
  end.

Fixpoint split2 (sz1 sz2 : nat) : word (sz1 + sz2) -> word sz2 :=
  match sz1 with
    | O => fun w => w
    | S sz1' => fun w => split2 sz1' sz2 (wtl w)
  end.

(** * Extension operators *)

Definition sext (sz : nat) (w : word sz) (sz' : nat) : word (sz + sz') :=
  if wmsb w false then
    combine w (wones sz')
  else
    combine w (wzero sz').

Definition zext (sz : nat) (w : word sz) (sz' : nat) : word (sz + sz') :=
  combine w (wzero sz').

(** * Arithmetic *)

Definition wneg sz (x : word sz) : word sz :=
  NToWord sz (Npow2 sz - wordToN x).

Definition wordBin (f : N -> N -> N) sz (x y : word sz) : word sz :=
  NToWord sz (f (wordToN x) (wordToN y)).

Definition wplus := wordBin Nplus.
Definition wmult := wordBin Nmult.
Definition wdiv := wordBin N.div.
Definition wmod := wordBin Nmod.
Definition wmult' sz (x y : word sz) : word sz :=
  split2 sz sz (NToWord (sz + sz) (Nmult (wordToN x) (wordToN y))).
Definition wminus sz (x y : word sz) : word sz := wplus x (wneg y).
Definition wnegN sz (x : word sz) : word sz :=
  natToWord sz (pow2 sz - wordToNat x).

Definition wordBinN (f : nat -> nat -> nat) sz (x y : word sz) : word sz :=
  natToWord sz (f (wordToNat x) (wordToNat y)).

Definition wplusN := wordBinN plus.

Definition wmultN := wordBinN mult.
Definition wmultN' sz (x y : word sz) : word sz :=
  split2 sz sz (natToWord (sz + sz) (mult (wordToNat x) (wordToNat y))).

Definition wminusN sz (x y : word sz) : word sz := wplusN x (wnegN y).

Notation "w ~ 1" := (WS true w)
 (at level 7, left associativity, format "w '~' '1'") : word_scope.
Notation "w ~ 0" := (WS false w)
 (at level 7, left associativity, format "w '~' '0'") : word_scope.

Notation "^~" := wneg.
Notation "l ^+ r" := (@wplus _ l%word r%word) (at level 50, left associativity).
Notation "l ^* r" := (@wmult _ l%word r%word) (at level 40, left associativity).
Notation "l ^- r" := (@wminus _ l%word r%word) (at level 50, left associativity).
Notation "l ^/ r" := (@wdiv _ l%word r%word) (at level 50, left associativity).
Notation "l ^% r" := (@wmod _ l%word r%word) (at level 50, left associativity).

(** * Bitwise operators *)

Fixpoint wnot sz (w : word sz) : word sz :=
  match w with
    | WO => WO
    | WS b w' => WS (negb b) (wnot w')
  end.

Fixpoint bitwp (f : bool -> bool -> bool) sz (w1 : word sz) : word sz -> word sz :=
  match w1 with
    | WO => fun _ => WO
    | WS b w1' => fun w2 => WS (f b (whd w2)) (bitwp f w1' (wtl w2))
  end.

Definition wnot' sz := bitwp xorb (wones sz).

Definition wor := bitwp orb.
Definition wand := bitwp andb.
Definition wxor := bitwp xorb.

Notation "l ^| r" := (@wor _ l%word r%word) (at level 50, left associativity).
Notation "l ^& r" := (@wand _ l%word r%word) (at level 40, left associativity).

(** * Conversion to and from [Z] *)

Definition wordToZ sz (w : word sz) : Z :=
  if wmsb w false then
    (** Negative **)
    match wordToN (wneg w) with
    | N0 => 0%Z
    | Npos x => Zneg x
    end
  else
    (** Positive **)
    match wordToN w with
    | N0 => 0%Z
    | Npos x => Zpos x
    end.

Definition uwordToZ sz (w : word sz) : Z := Z.of_N (wordToN w).

Definition ZToWord (sz : nat) (z : Z) : word sz :=
  match z with
  | Z0 => wzero' sz
  | Zpos x => posToWord sz x
  | Zneg x => wneg (posToWord sz x)
  end.

(** * Arithmetic by [Z] *)

Definition wordBinZ (f : Z -> Z -> Z) sz (x y : word sz) : word sz :=
  ZToWord sz (f (wordToZ x) (wordToZ y)).

Definition wplusZ := wordBinZ Z.add.
Definition wminusZ := wordBinZ Z.sub.
Definition wmultZ := wordBinZ Z.mul.
Definition wmultZsu sz (x y : word sz) :=
  ZToWord sz (Z.mul (wordToZ x) (Z.of_N (wordToN y))).
Definition wdivZ := wordBinZ Z.quot.
Definition wdivZsu sz (x y : word sz) :=
  ZToWord sz (Z.div (wordToZ x) (Z.of_N (wordToN y))).
Definition wremZ := wordBinZ Z.rem.
Definition wremZsu sz (x y : word sz) :=
  ZToWord sz (Z.modulo (wordToZ x) (Z.of_N (wordToN y))).

(** * Comparison predicates and deciders *)

Definition wlt sz (l r : word sz) : Prop :=
  N.lt (wordToN l) (wordToN r).
Definition wslt sz (l r : word sz) : Prop :=
  Z.lt (wordToZ l) (wordToZ r).

Notation "w1 > w2" := (@wlt _ w2%word w1%word) : word_scope.
Notation "w1 >= w2" := (~(@wlt _ w1%word w2%word)) : word_scope.
Notation "w1 < w2" := (@wlt _ w1%word w2%word) : word_scope.
Notation "w1 <= w2" := (~(@wlt _ w2%word w1%word)) : word_scope.

Notation "w1 '>s' w2" := (@wslt _ w2%word w1%word) (at level 70, w2 at next level) : word_scope.
Notation "w1 '>s=' w2" := (~(@wslt _ w1%word w2%word)) (at level 70, w2 at next level) : word_scope.
Notation "w1 '<s' w2" := (@wslt _ w1%word w2%word) (at level 70, w2 at next level) : word_scope.
Notation "w1 '<s=' w2" := (~(@wslt _ w2%word w1%word)) (at level 70, w2 at next level) : word_scope.

Definition wlt_dec : forall sz (l r : word sz), {l < r} + {l >= r}.
  refine (fun sz l r =>
    match N.compare (wordToN l) (wordToN r) as k return N.compare (wordToN l) (wordToN r) = k -> _ with
      | Lt => fun pf => left _ _
      | _ => fun pf => right _ _
    end (refl_equal _));
  abstract congruence.
Defined.

Definition wslt_dec : forall sz (l r : word sz), {l <s r} + {l >s= r}.
  refine (fun sz l r =>
    match Z.compare (wordToZ l) (wordToZ r) as c return Z.compare (wordToZ l) (wordToZ r) = c -> _ with
      | Lt => fun pf => left _ _
      | _ => fun pf => right _ _
    end (refl_equal _));
  abstract congruence.
Defined.

Definition wltb{sz: nat}(l r: word sz): bool := BinNat.N.ltb (wordToN l) (wordToN r).

Definition wsltb{sz: nat}(l r: word sz): bool := Z.ltb (wordToZ l) (wordToZ r).

Notation "$ n" := (natToWord _ n) (at level 0).
Notation "# n" := (wordToNat n) (at level 0).

(** * Bit shifting *)

Fact sz_minus_nshift : forall sz nshift, (nshift < sz)%nat -> sz = sz - nshift + nshift.
Proof.
  intros; omega.
Qed.

Fact nshift_plus_nkeep : forall sz nshift, (nshift < sz)%nat -> nshift + (sz - nshift) = sz.
Proof.
  intros; omega.
Qed.

Definition wlshift (sz : nat) (w : word sz) (n : nat) : word sz.
  refine (split1 sz n _).
  rewrite plus_comm.
  exact (combine (wzero n) w).
Defined.

Definition wrshift (sz : nat) (w : word sz) (n : nat) : word sz.
  refine (split2 n sz _).
  rewrite plus_comm.
  exact (combine w (wzero n)).
Defined.

Definition wrshifta (sz : nat) (w : word sz) (n : nat) : word sz.
  refine (split2 n sz _).
  rewrite plus_comm.
  exact (sext w _).
Defined.

(* Redefine shifts so that they do not use eq_rect, which matches on add_comm,
   which is an opaque proof, which makes cbv blow up.
   If you ever want to reduce terms inside Coq with cbv, you should use the
   shifts below!  *)

Definition wlshift' {sz : nat} (w : word sz) (n : nat) : word sz.
  refine (split1 sz n (nat_cast _ _ _)).
  apply PeanoNat.Nat.add_comm.
  exact (combine (wzero n) w).
Defined.

Definition wrshift' {sz : nat} (w : word sz) (n : nat) : word sz.
  refine (split2 n sz (nat_cast _ _ _)).
  apply PeanoNat.Nat.add_comm.
  exact (combine w (wzero n)).
Defined.

Definition wrshifta' {sz : nat} (w : word sz) (n : nat) : word sz.
  refine (split2 n sz (nat_cast _ _ _)).
  apply PeanoNat.Nat.add_comm.
  exact (sext w _).
Defined.

Definition extz {sz} (w: word sz) (n: nat) := combine (wzero n) w.

Fixpoint wpow2 sz: word (S sz) :=
  match sz with
  | O => WO~1
  | S sz' => (wpow2 sz')~0
  end.

Notation "l ^<< r" := (@wlshift _ _ l%word r%word) (at level 35).
Notation "l ^>> r" := (@wrshift _ _ l%word r%word) (at level 35).

(** * Setting an individual bit *)

Definition wbit sz sz' (n : word sz') := natToWord sz (pow2 (wordToNat n)).


(*! Facts *)

Hint Rewrite div2_double div2_S_double: div2.
Local Hint Resolve mod2_S_double mod2_double.

Theorem eq_rect_word_offset : forall n n' offset w Heq,
  eq_rect n (fun n => word (offset + n)) w n' Heq =
  eq_rect (offset + n) (fun n => word n) w (offset + n') (eq_rect_word_offset_helper _ _ _ Heq).
Proof.
  intros.
  destruct Heq.
  rewrite (UIP_dec eq_nat_dec (eq_rect_word_offset_helper _ _ offset eq_refl) eq_refl).
  reflexivity.
Qed.

Theorem eq_rect_word_mult : forall n n' scale w Heq,
  eq_rect n (fun n => word (n * scale)) w n' Heq =
  eq_rect (n * scale) (fun n => word n) w (n' * scale) (eq_rect_word_mult_helper _ _ _ Heq).
Proof.
  intros.
  destruct Heq.
  rewrite (UIP_dec eq_nat_dec (eq_rect_word_mult_helper _ _ scale eq_refl) eq_refl).
  reflexivity.
Qed.

Theorem eq_rect_word_match : forall n n' (w : word n) (H : n = n'),
  match H in (_ = N) return (word N) with
  | eq_refl => w
  end = eq_rect n (fun n => word n) w n' H.
Proof.
  intros.
  destruct H.
  rewrite <- (eq_rect_eq_dec eq_nat_dec).
  reflexivity.
Qed.

Theorem whd_match : forall n n' (w : word (S n)) (Heq : S n = S n'),
  whd w = whd (match Heq in (_ = N) return (word N) with
               | eq_refl => w
               end).
Proof.
  intros.
  rewrite eq_rect_word_match.
  generalize dependent w.
  remember Heq as Heq'. clear HeqHeq'.
  generalize dependent Heq'.
  replace (n') with (n) by omega.
  intros. rewrite <- (eq_rect_eq_dec eq_nat_dec). reflexivity.
Qed.

Theorem wtl_match : forall n n' (w : word (S n)) (Heq : S n = S n') (Heq' : n = n'),
  (match Heq' in (_ = N) return (word N) with
   | eq_refl => wtl w
   end) = wtl (match Heq in (_ = N) return (word N) with
               | eq_refl => w
               end).
Proof.
  intros.
  repeat match goal with
           | [ |- context[match ?pf with refl_equal => _ end] ] => generalize pf
         end.
  generalize dependent w; clear.
  intros.
  generalize Heq Heq'.
  subst.
  intros.
  rewrite (UIP_dec eq_nat_dec Heq' (refl_equal _)).
  rewrite (UIP_dec eq_nat_dec Heq0 (refl_equal _)).
  reflexivity.
Qed.

Theorem word0: forall (w : word 0), w = WO.
Proof.
  firstorder.
Qed.

Theorem wordToNat_wordToNat' : forall sz (w : word sz),
  wordToNat w = wordToNat' w.
Proof.
  induction w. auto. unfold wordToNat. simpl. rewrite mult_comm. reflexivity.
Qed.

Theorem natToWord_wordToNat : forall sz w, natToWord sz (wordToNat w) = w.
  induction w as [|b]; rewrite wordToNat_wordToNat'; intuition; f_equal; unfold natToWord, wordToNat'; fold natToWord; fold wordToNat';
    destruct b; f_equal; autorewrite with div2; intuition.
Qed.

Theorem roundTrip_0 : forall sz, wordToNat (natToWord sz 0) = 0.
  induction sz; simpl; intuition.
Qed.

Hint Rewrite roundTrip_0 : wordToNat.

Lemma wordToNat_natToWord' : forall sz w, exists k, wordToNat (natToWord sz w) + k * pow2 sz = w.
  induction sz as [|sz IHsz]; simpl; intro w; intuition; repeat rewrite untimes2.

  exists w; intuition.

  case_eq (mod2 w); intro Hmw.

  specialize (IHsz (div2 w)); firstorder.
  rewrite wordToNat_wordToNat' in *.
  let x' := match goal with H : _ + ?x * _ = _ |- _ => x end in
  rename x' into x. (* force non-auto-generated name *)
  exists x; intuition.
  rewrite mult_assoc.
  rewrite (mult_comm x 2).
  rewrite mult_comm. simpl mult at 1.
  rewrite (plus_Sn_m (2 * wordToNat' (natToWord sz (div2 w)))).
  rewrite <- mult_assoc.
  rewrite <- mult_plus_distr_l.
  rewrite H; clear H.
  symmetry; apply div2_odd; auto.

  specialize (IHsz (div2 w)); firstorder.
  let x' := match goal with H : _ + ?x * _ = _ |- _ => x end in
  rename x' into x. (* force non-auto-generated name *)
  exists x; intuition.
  rewrite mult_assoc.
  rewrite (mult_comm x 2).
  rewrite <- mult_assoc.
  rewrite mult_comm.
  rewrite <- mult_plus_distr_l.
  match goal with H : _ |- _ => rewrite H; clear H end.
  symmetry; apply div2_even; auto.
Qed.

Theorem wordToNat_natToWord:
  forall sz w, exists k, wordToNat (natToWord sz w) = w - k * pow2 sz /\ (k * pow2 sz <= w)%nat.
Proof.
  intros sz w; destruct (wordToNat_natToWord' sz w) as [k]; exists k; intuition.
Qed.

Lemma wordToNat_natToWord_2: forall sz w : nat,
    (w < pow2 sz)%nat -> wordToNat (natToWord sz w) = w.
Proof.
  intros.
  pose proof (wordToNat_natToWord sz w).
  destruct H0; destruct H0.
  rewrite H0 in *; clear H0.
  destruct x; try omega.
  exfalso; simpl in H1.

  pose proof (Lt.le_lt_trans _ _ _ H1 H).
  pose proof (Plus.le_plus_l (pow2 sz) (x * pow2 sz)).
  pose proof (Lt.le_lt_trans _ _ _ H2 H0).
  omega.
Qed.

Lemma natToWord_times2: forall sz x,
  ((natToWord sz x)~0)%word = natToWord (S sz) (2 * x).
Proof.
  intros. unfold natToWord. fold natToWord. f_equal.
  - symmetry. apply mod2_double.
  - rewrite div2_double. reflexivity.
Qed.

Theorem WS_neq : forall b1 b2 sz (w1 w2 : word sz),
  (b1 <> b2 \/ w1 <> w2)
  -> WS b1 w1 <> WS b2 w2.
  intros b1 b2 sz w1 w2 ? H0; intuition.
  apply (f_equal (@whd _)) in H0; tauto.
  apply (f_equal (@wtl _)) in H0; tauto.
Qed.

Theorem weqb_true_iff : forall sz x y,
  @weqb sz x y = true <-> x = y.
Proof.
  induction x as [|b ? x IHx]; simpl; intros y.
  { split; auto. }
  { rewrite (shatter_word y) in *. simpl in *.
    case_eq (eqb b (whd y)); intros H.
    case_eq (weqb x (wtl y)); intros H0.
    split; auto; intros. rewrite eqb_true_iff in H. f_equal; eauto. eapply IHx; eauto.
    split; intros H1; try congruence. inversion H1; clear H1; subst.
    eapply inj_pair2_eq_dec in H4. eapply IHx in H4. congruence.
    eapply Peano_dec.eq_nat_dec.
    split; intros; try congruence.
    inversion H0. apply eqb_false_iff in H. congruence. }
Qed.

Ltac shatterer := simpl; intuition;
  match goal with
    | [ w : _ |- _ ] => rewrite (shatter_word w); simpl
  end; f_equal; auto.

Theorem combine_split : forall sz1 sz2 (w : word (sz1 + sz2)),
  combine (split1 sz1 sz2 w) (split2 sz1 sz2 w) = w.
  induction sz1; shatterer.
Qed.

Theorem split1_combine : forall sz1 sz2 (w : word sz1) (z : word sz2),
  split1 sz1 sz2 (combine w z) = w.
  induction sz1; shatterer.
Qed.

Theorem split2_combine : forall sz1 sz2 (w : word sz1) (z : word sz2),
  split2 sz1 sz2 (combine w z) = z.
  induction sz1; shatterer.
Qed.

Hint Rewrite combine_split.
Hint Rewrite split1_combine.
Hint Rewrite split2_combine.

Theorem combine_assoc : forall n1 (w1 : word n1) n2 n3 (w2 : word n2) (w3 : word n3) Heq,
  combine (combine w1 w2) w3
  = match Heq in _ = N return word N with
      | refl_equal => combine w1 (combine w2 w3)
    end.
  induction w1 as [|?? w1 IHw1]; simpl; intros n2 n3 w2 w3 Heq; intuition.

  rewrite (UIP_dec eq_nat_dec Heq (refl_equal _)); reflexivity.

  rewrite (IHw1 _ _ _ _ (plus_assoc _ _ _)); clear IHw1.
  repeat match goal with
           | [ |- context[match ?pf with refl_equal => _ end] ] => generalize pf
         end.
  generalize dependent (combine w1 (combine w2 w3)).
  rewrite plus_assoc; intros w Heq0 e.
  rewrite (UIP_dec eq_nat_dec e (refl_equal _)).
  rewrite (UIP_dec eq_nat_dec Heq0 (refl_equal _)).
  reflexivity.
Qed.

Theorem split1_iter : forall n1 n2 n3 Heq w,
  split1 n1 n2 (split1 (n1 + n2) n3 w)
  = split1 n1 (n2 + n3) (match Heq in _ = N return word N with
                           | refl_equal => w
                         end).
Proof.
  induction n1; simpl; intuition.

  f_equal.
  apply whd_match.
  assert (n1 + n2 + n3 = n1 + (n2 + n3)) as Heq' by omega.
  rewrite IHn1 with (Heq:=Heq').
  f_equal.
  apply wtl_match.
Qed.

Theorem split2_iter : forall n1 n2 n3 Heq w,
  split2 n2 n3 (split2 n1 (n2 + n3) w)
  = split2 (n1 + n2) n3 (match Heq in _ = N return word N with
                           | refl_equal => w
                         end).
  induction n1 as [|n1 IHn1]; simpl; intros n2 n3 Heq w; intuition.

  rewrite (UIP_dec eq_nat_dec Heq (refl_equal _)); reflexivity.

  rewrite (IHn1 _ _ (plus_assoc _ _ _)).
  f_equal.
  apply wtl_match.
Qed.

Theorem split1_split2 : forall n1 n2 n3 Heq w,
  split1 n2 n3 (split2 n1 (n2 + n3) w) =
  split2 n1 n2 (split1 (n1 + n2) n3 (match Heq in _ = N return word N with
                                     | refl_equal => w
                                     end)).
Proof.
  induction n1; simpl; intros.

  rewrite (UIP_dec eq_nat_dec Heq (refl_equal _)).
  reflexivity.

  rewrite (shatter_word w).
  simpl.
  assert (n1 + (n2 + n3) = n1 + n2 + n3) as Heq' by omega.
  rewrite <- wtl_match with (Heq':=Heq').
  rewrite <- IHn1.
  f_equal.
Qed.

Theorem split2_split1 : forall n1 n2 n3 Heq w,
  split2 n1 n2 (split1 (n1+n2) n3 w) =
  split1 n2 n3 (split2 n1 (n2+n3) (match Heq in _ = N return word N with
                                     | refl_equal => w
                                     end)).
Proof.
  induction n1; simpl; intros.

  rewrite (UIP_dec eq_nat_dec Heq (refl_equal _)).
  reflexivity.

  rewrite (shatter_word w).
  simpl.
  assert (n1 + n2 + n3 = n1 + (n2 + n3)) as Heq' by omega.
  rewrite <- wtl_match with (Heq':=Heq').
  rewrite <- IHn1.
  f_equal.
Qed.

Theorem combine_0_n : forall sz2 (w: word 0) (v: word sz2),
  combine w v = v.
Proof.
  intros.
  replace w with WO.
  auto.
  rewrite word0; auto.
Qed.

Lemma WS_eq_rect : forall b n (w: word n) n' H H',
  eq_rect _ word (@WS b n w) _ H = @WS b n' (eq_rect _ word w _ H').
Proof.
  destruct n; intros; subst;
    eq_rect_simpl; auto.
Qed.

Theorem combine_eq_rect2 : forall sz n n'
  (H: n = n') H'
  (a: word sz) (b: word n),
  combine a b =
    eq_rect _ word (combine a (eq_rect _ word b _ H)) _ H'.
Proof.
  induction a; simpl; intros.
  eq_rect_simpl; auto.
  erewrite WS_eq_rect.
  erewrite IHa.
  auto.

  Grab Existential Variables.
  omega.
Qed.

Theorem combine_n_0 : forall sz1 (w : word sz1) (v : word 0),
  combine w v = eq_rect _ word w _ (plus_n_O sz1).
Proof.
  induction w; intros.
  - replace v with WO; auto.
  - simpl; rewrite IHw.
    erewrite WS_eq_rect.
    reflexivity.
Qed.

Lemma whd_eq_rect : forall n w Heq,
  whd (eq_rect (S n) word w (S (n + 0)) Heq) =
  whd w.
Proof.
  intros.
  generalize Heq.
  replace (n + 0) with n by omega.
  intros.
  f_equal.
  eq_rect_simpl.
  reflexivity.
Qed.

Lemma wtl_eq_rect : forall n w Heq Heq',
  wtl (eq_rect (S n) word w (S (n + 0)) Heq) =
  eq_rect n word (wtl w) (n + 0) Heq'.
Proof.
  intros.
  generalize dependent Heq.
  rewrite <- Heq'; simpl; intros.
  rewrite <- (eq_rect_eq_dec eq_nat_dec).
  reflexivity.
Qed.

Lemma whd_eq_rect_mul : forall n w Heq,
  whd (eq_rect (S n) word w (S (n * 1)) Heq) =
  whd w.
Proof.
  intros.
  generalize Heq.
  replace (n * 1) with n by auto.
  intros.
  eq_rect_simpl.
  reflexivity.
Qed.

Lemma wtl_eq_rect_mul : forall n w b Heq Heq',
  wtl (eq_rect (S n) word (WS b w) (S (n * 1)) Heq) =
  eq_rect _ word w _ Heq'.
Proof.
  intros.
  generalize Heq.
  rewrite <- Heq'.
  intros. eq_rect_simpl.
  reflexivity.
Qed.

Theorem split1_0 : forall n w Heq,
  split1 n 0 (eq_rect _ word w _ Heq) = w.
Proof.
  intros.
  induction n; intros.
  shatterer.
  simpl.
  erewrite wtl_eq_rect.
  rewrite IHn.
  rewrite whd_eq_rect.
  simpl.
  shatterer.

  Grab Existential Variables.
  omega.
Qed.

Theorem split2_0 : forall n w Heq,
  split2 0 n (eq_rect _ word w _ Heq) = w.
Proof.
  intros.
  simpl.
  eq_rect_simpl.
  reflexivity.
Qed.

Theorem combine_end : forall n1 n2 n3 Heq w,
  combine (split1 n2 n3 (split2 n1 (n2 + n3) w))
  (split2 (n1 + n2) n3 (match Heq in _ = N return word N with
                          | refl_equal => w
                        end))
  = split2 n1 (n2 + n3) w.
  induction n1 as [|n1 IHn1]; simpl; intros n2 n3 Heq w.

  rewrite (UIP_dec eq_nat_dec Heq (refl_equal _)).
  apply combine_split.

  rewrite (shatter_word w) in *.
  simpl.
  eapply trans_eq; [ | apply IHn1 with (Heq := plus_assoc _ _ _) ]; clear IHn1.
  repeat f_equal.
  repeat match goal with
           | [ |- context[match ?pf with refl_equal => _ end] ] => generalize pf
         end.
  simpl.
  generalize dependent w.
  rewrite plus_assoc.
  intros.
  rewrite (UIP_dec eq_nat_dec e (refl_equal _)).
  rewrite (UIP_dec eq_nat_dec Heq0 (refl_equal _)).
  reflexivity.
Qed.

Theorem eq_rect_combine : forall n1 n2 n2' (w1 : word n1) (w2 : word n2') Heq,
  eq_rect (n1 + n2') (fun n => word n)
    (combine w1 w2) (n1 + n2) Heq =
  combine w1 (eq_rect n2' (fun n => word n) w2 n2 (plus_reg_l _ _ _ Heq)).
Proof.
  intros.
  generalize (plus_reg_l n2' n2 n1 Heq); intros.
  generalize dependent Heq.
  generalize dependent w2.
  rewrite e; intros.
  repeat rewrite <- (eq_rect_eq_dec eq_nat_dec).
  reflexivity.
Qed.

Lemma eq_rect_combine_assoc' : forall a b c H wa wb wc,
  eq_rect (a + (b + c)) word (combine wa (combine wb wc)) _ H = combine (combine wa wb) wc.
Proof.
  intros.
  erewrite combine_assoc, eq_rect_word_match.
  reflexivity.
Qed.

Lemma eq_rect_split2_helper : forall a b c,
  a = b -> c + a = c + b.
Proof.
  intros; omega.
Qed.

Theorem eq_rect_split2 : forall n1 n2 n2' (w : word (n1 + n2')) Heq,
  eq_rect n2' (fun n => word n)
    (split2 n1 n2' w) n2 Heq =
  split2 n1 n2 (eq_rect (n1+n2') (fun n => word n) w (n1+n2) (eq_rect_split2_helper _ Heq)).
Proof.
  intros.
  generalize (eq_rect_split2_helper n1 Heq); intros.
  generalize dependent Heq.
  generalize dependent w.
  assert (n2' = n2) as H' by omega.
  generalize dependent e.
  rewrite H'; intros.
  repeat rewrite <- (eq_rect_eq_dec eq_nat_dec).
  reflexivity.
Qed.

Theorem eq_rect_split2_eq2 : forall n1 n2 n2' (w : word (n1 + n2)) Heq Heq2,
  eq_rect n2 (fun n => word n)
    (split2 n1 n2 w) n2' Heq =
  split2 n1 n2' (eq_rect (n1+n2) (fun n => word n) w (n1+n2') Heq2).
Proof.
  intros.
  assert (H' := Heq).
  generalize dependent w.
  generalize dependent Heq.
  generalize dependent Heq2.
  rewrite H'; intros.
  repeat rewrite <- (eq_rect_eq_dec eq_nat_dec).
  reflexivity.
Qed.

Theorem eq_rect_split2_eq1 : forall n1 n1' n2 (w: word (n1 + n2)) Heq,
     split2 n1 n2 w = split2 n1' n2
        (eq_rect (n1 + n2) (fun y : nat => word y) w
     (n1' + n2) Heq).
Proof.
  intros.
  assert (n1 = n1') as H' by omega.
  generalize dependent w.
  generalize dependent Heq.
  rewrite H'; intros.
  rewrite <- (eq_rect_eq_dec eq_nat_dec).
  reflexivity.
Qed.

Theorem combine_split_eq_rect2 : forall n1 n2 n2' (w : word (n1 + n2)) Heq,
  combine (split1 n1 n2 w)
          (eq_rect n2 (fun n => word n) (split2 n1 n2 w)
                   n2' Heq) =
  eq_rect (n1 + n2) (fun n => word n) w
          (n1 + n2') (eq_rect_split2_helper _ Heq).
Proof.
  intros.
  assert (n2 = n2') by omega.
  generalize dependent Heq.
  generalize dependent w.
  rewrite <- H; intros.
  repeat rewrite <- (eq_rect_eq_dec eq_nat_dec).
  apply combine_split.
Qed.

Lemma eq_rect_split1_helper : forall a b c,
  a = b -> a + c = b + c.
Proof.
  intros; omega.
Qed.

Lemma eq_rect_split1_eq2_helper : forall a b c,
  a = b -> c + a = c + b.
Proof.
  intros; omega.
Qed.

Theorem eq_rect_split1 : forall n1 n1' n2 (w : word (n1' + n2)) Heq,
  eq_rect n1' (fun n => word n)
    (split1 n1' n2 w) n1 Heq =
  split1 n1 n2 (eq_rect (n1'+n2) (fun n => word n) w (n1+n2) (eq_rect_split1_helper _ Heq)).
Proof.
  intros.
  generalize (eq_rect_split1_helper n2 Heq); intros.
  generalize dependent Heq.
  generalize dependent w.
  assert (n1' = n1) as H' by omega.
  generalize dependent e.
  rewrite H'; intros.
  repeat rewrite <- (eq_rect_eq_dec eq_nat_dec).
  reflexivity.
Qed.

Theorem eq_rect_split1_eq1 : forall n1 n1' n2 (w : word (n1 + n2)) Heq Heq1,
  eq_rect n1 (fun n => word n)
    (split1 n1 n2 w) n1' Heq =
  split1 n1' n2 (eq_rect (n1+n2) (fun n => word n) w (n1'+n2) Heq1).
Proof.
  intros.
  generalize dependent w.
  generalize dependent Heq1.
  rewrite Heq; intros.
  repeat rewrite <- (eq_rect_eq_dec eq_nat_dec).
  reflexivity.
Qed.

Lemma split1_eq_rect_eq1_helper : forall a b c, b = a -> a + c = b + c.
Proof. intros. subst. reflexivity. Qed.

Theorem split1_eq_rect_eq1 : forall a a' b H w,
  split1 a b w = eq_rect _ word (split1 a' b
    (eq_rect _ word w _ (split1_eq_rect_eq1_helper b H))) _ H.
Proof.
  intros a a' b H.
  subst a'; intros; eq_rect_simpl; auto.
Qed.

Theorem eq_rect_split1_eq2 : forall n1 n2 n2' (w: word (n1 + n2)) Heq,
     split1 n1 n2 w = split1 n1 n2'
        (eq_rect (n1 + n2) (fun y : nat => word y) w
     (n1 + n2') Heq).
Proof.
  intros.
  assert (n2 = n2') as H' by omega.
  generalize dependent w.
  generalize dependent Heq.
  rewrite H'; intros.
  rewrite <- (eq_rect_eq_dec eq_nat_dec).
  reflexivity.
Qed.

Fact eq_rect_combine_dist_helper1 : forall a b c d, b * c = d -> (a + b) * c = a * c + d.
Proof. intros; subst. apply Nat.mul_add_distr_r. Qed.

Fact eq_rect_combine_dist_helper2 : forall a b c d, b * c = d -> a * c + d = (a + b) * c.
Proof. intros; subst. symmetry; apply Nat.mul_add_distr_r. Qed.

Theorem eq_rect_combine_dist : forall a b c d (w : word ((a + b) * c)) (H : b * c = d),
  b * c = d ->
  let H1 := (eq_rect_combine_dist_helper1 a b c H) in
  let H2 := (eq_rect_combine_dist_helper2 a b c H) in
  let w' := eq_rec ((a + b) * c) word w _ H1 in
  w = eq_rec _ word (combine (split1 (a * c) d w') (split2 (a * c) d w')) _ H2.
Proof.
  intros.
  subst d.
  rewrite combine_split.
  eq_rect_simpl.
  generalize dependent w.
  generalize dependent H2.
  rewrite H1.
  intros.
  eq_rect_simpl; auto.
Qed.

Lemma wzero_dist : forall a b c H,
  wzero ((a + b) * c) = eq_rect _ word (wzero (a * c + b * c)) _ H.
Proof.
  intros a b c H.
  rewrite H.
  reflexivity.
Qed.

Lemma wzero_rev : forall (a b : nat) H,
   wzero (a + b) = eq_rect _ word (wzero (b + a)) _ H.
Proof. intros a b H. rewrite H. auto. Qed.

Lemma split1_zero : forall sz1 sz2, split1 sz1 sz2 (natToWord _ O) = natToWord _ O.
Proof.
  induction sz1; auto; simpl; intros.
  f_equal. eauto.
Qed.

Lemma split2_zero : forall sz1 sz2, split2 sz1 sz2 (natToWord _ O) = natToWord _ O.
Proof.
  induction sz1; auto.
Qed.

Theorem combine_inj : forall sz1 sz2 a b c d,
  @combine sz1 a sz2 b = @combine sz1 c sz2 d -> a = c /\ b = d.
Proof.
  induction sz1; simpl; intros.
  - rewrite (word0 a) in *.
    rewrite (word0 c) in *.
    simpl in *.
    intuition.
  - rewrite (shatter_word a) in *.
    rewrite (shatter_word c) in *.
    simpl in *.
    inversion H.
    apply (inj_pair2_eq_dec _ eq_nat_dec) in H2.
    destruct (IHsz1 _ _ _ _ _ H2).
    intuition.
    f_equal; auto.
Qed.

Theorem combine_wzero : forall sz1 sz2, combine (wzero sz1) (wzero sz2) = wzero (sz1 + sz2).
Proof.
  induction sz1; auto.
  unfold wzero in *.
  intros; simpl; f_equal; auto.
Qed.

Theorem combine_wones : forall sz1 sz2, combine (wones sz1) (wones sz2) = wones (sz1 + sz2).
Proof.
  induction sz1; auto.
  intros; simpl; f_equal; auto.
Qed.

Theorem wordToN_nat : forall sz (w : word sz), wordToN w = N_of_nat (wordToNat w).
Proof.
  induction w; intuition.
  destruct b; unfold wordToN, wordToNat; fold wordToN; fold wordToNat.

  rewrite N_of_S.
  rewrite N_of_mult.
  rewrite <- IHw.
  rewrite Nmult_comm.
  reflexivity.

  rewrite N_of_mult.
  rewrite <- IHw.
  rewrite Nmult_comm.
  reflexivity.
Qed.

Lemma wordToN_to_nat sz: forall (w: word sz), BinNat.N.to_nat (wordToN w) = wordToNat w.
Proof.
  intros.
  rewrite wordToN_nat.
  rewrite Nnat.Nat2N.id.
  reflexivity.
Qed.

Local Hint Extern 1 (@eq nat _ _) => omega.

Theorem mod2_S : forall n k,
  2 * k = S n
  -> mod2 n = true.
  induction n as [n] using strong; intros.
  destruct n; simpl in *.
  elimtype False; omega.
  destruct n; simpl in *; auto.
  destruct k as [|k]; simpl in *.
  discriminate.
  apply H with k; auto.
Qed.

Theorem wzero'_def : forall sz, wzero' sz = wzero sz.
  unfold wzero; induction sz; simpl; intuition.
  congruence.
Qed.

Theorem posToWord_nat : forall p sz, posToWord sz p = natToWord sz (nat_of_P p).
  induction p as [ p IHp | p IHp | ]; destruct sz; simpl; intuition; f_equal; try rewrite wzero'_def in *.

  rewrite ZL6.
  destruct (ZL4 p) as [x Heq]; rewrite Heq; simpl.
  replace (x + S x) with (S (2 * x)) by omega.
  symmetry; apply mod2_S_double.

  rewrite IHp.
  rewrite ZL6.
  destruct (nat_of_P p); simpl; intuition.
  replace (n + S n) with (S (2 * n)) by omega.
  rewrite div2_S_double; auto.

  unfold nat_of_P; simpl.
  rewrite ZL6.
  replace (nat_of_P p + nat_of_P p) with (2 * nat_of_P p) by omega.
  symmetry; apply mod2_double.

  rewrite IHp.
  unfold nat_of_P; simpl.
  rewrite ZL6.
  replace (nat_of_P p + nat_of_P p) with (2 * nat_of_P p) by omega.
  rewrite div2_double.
  auto.
  auto.
Qed.

Lemma posToWord_sz0: forall p, posToWord 0 p = $0.
Proof.
  intros. unfold posToWord. destruct p; reflexivity.
Qed.

Theorem NToWord_nat : forall sz n, NToWord sz n = natToWord sz (nat_of_N n).
  destruct n; simpl; intuition; try rewrite wzero'_def in *.
  auto.
  apply posToWord_nat.
Qed.

Theorem wplus_alt : forall sz (x y : word sz), wplus x y = wplusN x y.
  unfold wplusN, wplus, wordBinN, wordBin; intros.

  repeat rewrite wordToN_nat; repeat rewrite NToWord_nat.
  rewrite nat_of_Nplus.
  repeat rewrite nat_of_N_of_nat.
  reflexivity.
Qed.

Theorem wmult_alt : forall sz (x y : word sz), wmult x y = wmultN x y.
  unfold wmultN, wmult, wordBinN, wordBin; intros.

  repeat rewrite wordToN_nat; repeat rewrite NToWord_nat.
  rewrite nat_of_Nmult.
  repeat rewrite nat_of_N_of_nat.
  reflexivity.
Qed.

Theorem wneg_alt : forall sz (x : word sz), wneg x = wnegN x.
  unfold wnegN, wneg; intros.
  repeat rewrite wordToN_nat; repeat rewrite NToWord_nat.
  rewrite nat_of_Nminus.
  do 2 f_equal.
  apply Npow2_nat.
  apply nat_of_N_of_nat.
Qed.

Theorem wminus_Alt : forall sz (x y : word sz), wminus x y = wminusN x y.
  intros; unfold wminusN, wminus; rewrite wneg_alt; apply wplus_alt.
Qed.

Theorem wplus_unit : forall sz (x : word sz), natToWord sz 0 ^+ x = x.
  intros; rewrite wplus_alt; unfold wplusN, wordBinN; intros.
  rewrite roundTrip_0; apply natToWord_wordToNat.
Qed.

Theorem wplus_comm : forall sz (x y : word sz), x ^+ y = y ^+ x.
  intros; repeat rewrite wplus_alt; unfold wplusN, wordBinN; f_equal; auto.
Qed.

Theorem drop_sub :
  forall sz n k,
    (k * pow2 sz <= n)%nat ->
    natToWord sz (n - k * pow2 sz) = natToWord sz n.
Proof.
  induction sz as [|sz IHsz]; simpl; intros n k *; intuition; repeat rewrite untimes2 in *; f_equal.

  rewrite mult_assoc.
  rewrite (mult_comm k).
  rewrite <- mult_assoc.
  apply drop_mod2.
  rewrite mult_assoc.
  rewrite (mult_comm 2).
  rewrite <- mult_assoc.
  auto.

  rewrite <- (IHsz (div2 n) k).
  rewrite mult_assoc.
  rewrite (mult_comm k).
  rewrite <- mult_assoc.
  rewrite div2_minus_2.
  reflexivity.
  rewrite mult_assoc.
  rewrite (mult_comm 2).
  rewrite <- mult_assoc.
  auto.

  apply div2_bound.
  rewrite mult_assoc.
  rewrite (mult_comm 2).
  rewrite <- mult_assoc.
  auto.
Qed.

Local Hint Extern 1 (_ <= _)%nat => omega.

Theorem wplus_assoc : forall sz (x y z : word sz), x ^+ (y ^+ z) = x ^+ y ^+ z.
  intros sz x y z *; repeat rewrite wplus_alt; unfold wplusN, wordBinN; intros.

  repeat match goal with
           | [ |- context[wordToNat (natToWord ?sz ?w)] ] =>
             let Heq := fresh "Heq" in
               destruct (wordToNat_natToWord sz w) as [? [Heq ?]]; rewrite Heq
         end.

  match goal with
  | [ |- context[wordToNat ?x + wordToNat ?y - ?x1 * pow2 ?sz + wordToNat ?z] ]
    => replace (wordToNat x + wordToNat y - x1 * pow2 sz + wordToNat z)
      with (wordToNat x + wordToNat y + wordToNat z - x1 * pow2 sz) by auto
  end.
  match goal with
  | [ |- context[wordToNat ?x + (wordToNat ?y + wordToNat ?z - ?x0 * pow2 ?sz)] ]
    => replace (wordToNat x + (wordToNat y + wordToNat z - x0 * pow2 sz))
      with (wordToNat x + wordToNat y + wordToNat z - x0 * pow2 sz) by auto
  end.
  repeat rewrite drop_sub; auto.
Qed.

Theorem roundTrip_1 : forall sz, wordToNat (natToWord (S sz) 1) = 1.
  induction sz; simpl in *; intuition.
Qed.

Theorem mod2_WS : forall sz (x : word sz) b, mod2 (wordToNat (WS b x)) = b.
  intros sz x b. rewrite wordToNat_wordToNat'.
  destruct b; simpl.

  rewrite untimes2.
  case_eq (2 * wordToNat x); intuition.
  eapply mod2_S; eauto.
  rewrite <- (mod2_double (wordToNat x)); f_equal; omega.
Qed.

Theorem div2_WS : forall sz (x : word sz) b, div2 (wordToNat (WS b x)) = wordToNat x.
  destruct b; rewrite wordToNat_wordToNat'; unfold wordToNat'; fold wordToNat'.
  apply div2_S_double.
  apply div2_double.
Qed.

Theorem wmult_unit : forall sz (x : word sz), natToWord sz 1 ^* x = x.
  intros sz x; rewrite wmult_alt; unfold wmultN, wordBinN; intros.
  destruct sz; simpl.
  rewrite (shatter_word x); reflexivity.
  rewrite roundTrip_0; simpl.
  rewrite plus_0_r.
  rewrite (shatter_word x).
  f_equal.

  apply mod2_WS.

  rewrite div2_WS.
  apply natToWord_wordToNat.
Qed.

Theorem wmult_comm : forall sz (x y : word sz), x ^* y = y ^* x.
  intros; repeat rewrite wmult_alt; unfold wmultN, wordBinN; auto with arith.
Qed.

Theorem wmult_unit_r : forall sz (x : word sz), x ^* natToWord sz 1 = x.
Proof.
  intros.
  rewrite wmult_comm.
  apply wmult_unit.
Qed.

Lemma wmult_neut_l: forall (sz : nat) (x : word sz), $0 ^* x = $0.
Proof.
  intros. unfold wmult. unfold wordBin. do 2 rewrite wordToN_nat.
  rewrite <- Nnat.Nat2N.inj_mul. rewrite roundTrip_0.
  rewrite Nat.mul_0_l. simpl. rewrite wzero'_def. reflexivity.
Qed.

Lemma wmult_neut_r: forall (sz : nat) (x : word sz), x ^* $0 = $0.
Proof.
  intros. unfold wmult. unfold wordBin. do 2 rewrite wordToN_nat.
  rewrite <- Nnat.Nat2N.inj_mul. rewrite roundTrip_0.
  rewrite Nat.mul_0_r. simpl. rewrite wzero'_def. reflexivity.
Qed.

Theorem wmult_assoc : forall sz (x y z : word sz), x ^* (y ^* z) = x ^* y ^* z.
  intros sz x y z; repeat rewrite wmult_alt; unfold wmultN, wordBinN; intros.

  repeat match goal with
           | [ |- context[wordToNat (natToWord ?sz ?w)] ] =>
             let Heq := fresh "Heq" in
               destruct (wordToNat_natToWord sz w) as [? [Heq ?]]; rewrite Heq
         end.

  rewrite mult_minus_distr_l.
  rewrite mult_minus_distr_r.
  match goal with
  | [ |- natToWord _ (_ - _ * (?x0' * _)) = natToWord _ (_ - ?x1' * _ * _) ]
    => rename x0' into x0, x1' into x1 (* force the names to not be autogenerated *)
  end.
  rewrite (mult_assoc (wordToNat x) x0).
  rewrite <- (mult_assoc x1).
  rewrite (mult_comm (pow2 sz)).
  rewrite (mult_assoc x1).
  repeat rewrite drop_sub; auto with arith.
  rewrite (mult_comm x1).
  rewrite <- (mult_assoc (wordToNat x)).
  rewrite (mult_comm (wordToNat y)).
  rewrite mult_assoc.
  rewrite (mult_comm (wordToNat x)).
  repeat rewrite <- mult_assoc.
  auto with arith.
  repeat rewrite <- mult_assoc.
  auto with arith.
Qed.

Theorem wmult_plus_distr : forall sz (x y z : word sz), (x ^+ y) ^* z = (x ^* z) ^+ (y ^* z).
  intros sz x y z; repeat rewrite wmult_alt; repeat rewrite wplus_alt; unfold wmultN, wplusN, wordBinN; intros.

  repeat match goal with
           | [ |- context[wordToNat (natToWord ?sz ?w)] ] =>
             let Heq := fresh "Heq" in
               destruct (wordToNat_natToWord sz w) as [? [Heq ?]]; rewrite Heq
         end.

  rewrite mult_minus_distr_r.
  match goal with
  | [ |- natToWord _ (_ - ?x0' * _ * _) = natToWord _ (_ - ?x1' * _ + (_ - ?x2' * _)) ]
    => rename x0' into x0, x1' into x1, x2' into x2 (* force the names to not be autogenerated *)
  end.
  rewrite <- (mult_assoc x0).
  rewrite (mult_comm (pow2 sz)).
  rewrite (mult_assoc x0).

  replace (wordToNat x * wordToNat z - x1 * pow2 sz +
    (wordToNat y * wordToNat z - x2 * pow2 sz))
    with (wordToNat x * wordToNat z + wordToNat y * wordToNat z - x1 * pow2 sz - x2 * pow2 sz).
  repeat rewrite drop_sub; auto with arith.
  rewrite (mult_comm x0).
  rewrite (mult_comm (wordToNat x + wordToNat y)).
  rewrite <- (mult_assoc (wordToNat z)).
  auto with arith.
  generalize dependent (wordToNat x * wordToNat z).
  generalize dependent (wordToNat y * wordToNat z).
  intros.
  omega.
Qed.

Theorem wminus_def : forall sz (x y : word sz), x ^- y = x ^+ ^~ y.
  reflexivity.
Qed.

Theorem wordToNat_bound : forall sz (w : word sz), (wordToNat w < pow2 sz)%nat.
  induction w as [|b]; simpl; intuition.
  destruct b; simpl; omega.
Qed.

Theorem natToWord_pow2 : forall sz, natToWord sz (pow2 sz) = natToWord sz 0.
  induction sz as [|sz]; simpl; intuition.

  generalize (div2_double (pow2 sz)); simpl; intro Hr; rewrite Hr; clear Hr.
  f_equal.
  generalize (mod2_double (pow2 sz)); auto.
  auto.
Qed.

Theorem wminus_inv : forall sz (x : word sz), x ^+ ^~ x = wzero sz.
  intros sz x; rewrite wneg_alt; rewrite wplus_alt; unfold wnegN, wplusN, wzero, wordBinN; intros.

  repeat match goal with
           | [ |- context[wordToNat (natToWord ?sz ?w)] ] =>
             let Heq := fresh "Heq" in
               destruct (wordToNat_natToWord sz w) as [? [Heq ?]]; rewrite Heq
         end.

  match goal with
  | [ |- context[wordToNat ?x + (pow2 ?sz - wordToNat ?x - ?x0 * pow2 ?sz)] ]
    => replace (wordToNat x + (pow2 sz - wordToNat x - x0 * pow2 sz))
      with (pow2 sz - x0 * pow2 sz)
  end.
  rewrite drop_sub; auto with arith.
  apply natToWord_pow2.
  generalize (wordToNat_bound x).
  omega.
Qed.

Definition wring (sz : nat) : ring_theory (wzero sz) (wone sz) (@wplus sz) (@wmult sz) (@wminus sz) (@wneg sz) (@eq _) :=
  mk_rt _ _ _ _ _ _ _
  (@wplus_unit _) (@wplus_comm _) (@wplus_assoc _)
  (@wmult_unit _) (@wmult_comm _) (@wmult_assoc _)
  (@wmult_plus_distr _) (@wminus_def _) (@wminus_inv _).

Theorem weqb_sound : forall sz (x y : word sz), weqb x y = true -> x = y.
Proof.
  eapply weqb_true_iff.
Qed.

Arguments weqb_sound : clear implicits.

Lemma weqb_eq: forall sz (a b: word sz), a = b -> weqb a b = true.
Proof. intros. rewrite weqb_true_iff. assumption. Qed.

Lemma weqb_ne: forall sz (a b: word sz), a <> b -> weqb a b = false.
Proof.
  intros. destruct (weqb a b) eqn: E.
  - rewrite weqb_true_iff in E. contradiction.
  - reflexivity.
Qed.

Ltac is_nat_cst n :=
  match eval hnf in n with
    | O => constr:(true)
    | S ?n' => is_nat_cst n'
    | _ => constr:(false)
  end.

Ltac isWcst w :=
  match eval hnf in w with
    | WO => constr:(true)
    | WS ?b ?w' =>
      match eval hnf in b with
        | true => isWcst w'
        | false => isWcst w'
        | _ => constr:(false)
      end
    | natToWord _ ?n => is_nat_cst n
    | _ => constr:(false)
  end.

Ltac wcst w :=
  let b := isWcst w in
    match b with
      | true => w
      | _ => constr:(NotConstant)
    end.

(* Here's how you can add a ring for a specific bit-width.
   There doesn't seem to be a polymorphic method, so this code really does need to be copied. *)

(*
Definition wring8 := wring 8.
Add Ring wring8 : wring8 (decidable (weqb_sound 8), constants [wcst]).
*)

Ltac noptac x := idtac.

Ltac PackWring sz F :=
  let RNG := (fun proj => proj
    inv_morph_nothing inv_morph_nothing noptac noptac
    (word sz) (@eq (word sz)) (wzero sz) (wone sz)
    (@wplus sz) (@wmult sz) (@wminus sz) (@wneg sz)
    (BinNums.Z) (BinNums.N) (id_phi_N)
    (pow_N (wone sz) (@wmult sz))
    (ring_correct (@Eqsth (word sz))
                  (Eq_ext _ _ _)
                  (Rth_ARth (@Eqsth (word sz)) (Eq_ext _ _ _) (wring sz))
                  (gen_phiZ_morph (@Eqsth (word sz)) (Eq_ext _ _ _) (wring sz))
                  (pow_N_th _ _ (@Eqsth (word sz)))
                  (triv_div_th (@Eqsth (word sz))
                               (Eq_ext _ _ _)
                               (Rth_ARth (@Eqsth (word sz)) (Eq_ext _ _ _) (wring sz))
                               (gen_phiZ_morph (@Eqsth (word sz)) (Eq_ext _ _ _) (wring sz)))
    )
    tt) in
  F RNG (@nil (word sz)) (@nil (word sz)).

Ltac ring_sz sz := PackWring sz Ring_gen.

Fact bitwp_wtl : forall sz (w w' : word (S sz)) op, bitwp op (wtl w) (wtl w') = wtl (bitwp op w w').
Proof.
  intros.
  rewrite (shatter_word w), (shatter_word w').
  auto.
Qed.

Lemma split1_bitwp_dist : forall sz1 sz2 w w' op,
  split1 sz1 sz2 (bitwp op w w') = bitwp op (split1 sz1 sz2 w) (split1 sz1 sz2 w').
Proof.
  induction sz1; intros; auto.
  simpl.
  f_equal.
  rewrite (shatter_word w), (shatter_word w'); auto.
  rewrite <- IHsz1, bitwp_wtl.
  reflexivity.
Qed.

Lemma split2_bitwp_dist : forall sz1 sz2 w w' op,
  split2 sz1 sz2 (bitwp op w w') = bitwp op (split2 sz1 sz2 w) (split2 sz1 sz2 w').
Proof.
  induction sz1; intros; auto.
  simpl; rewrite <- IHsz1, bitwp_wtl.
  reflexivity.
Qed.

Lemma combine_bitwp : forall sz1 sz2 (wa wa' : word sz1) (wb wb' : word sz2) op,
  combine (bitwp op wa wa') (bitwp op wb wb') = bitwp op (combine wa wb) (combine wa' wb').
Proof.
  induction sz1; intros; rewrite (shatter_word wa), (shatter_word wa'); simpl; f_equal; auto.
Qed.

Lemma eq_rect_bitwp : forall a b Heq f w1 w2,
  bitwp f w1 w2 = eq_rect a word (
    bitwp f (eq_rect b word w1 a Heq) (eq_rect b word w2 a Heq)) b (eq_sym Heq).
Proof.
  intros a b H; subst a.
  intros; eq_rect_simpl; reflexivity.
Qed.

Fact eq_rect_bitwp' : forall a b Heq f w1 w2,
  eq_rect b word (bitwp f w1 w2) a Heq = bitwp f (eq_rect b word w1 a Heq) (eq_rect b word w2 a Heq).
Proof.
  intros a b H1; subst a.
  intros; eq_rect_simpl; reflexivity.
Qed.

Fact eq_rect_bitwp_1 : forall a b Heq f w1 w2,
  bitwp f (eq_rect a word w1 b Heq) w2 = eq_rect a word (bitwp f w1 (eq_rect b word w2 a (eq_sym Heq))) b Heq.
Proof.
  intros a b H.
  subst a; intros; eq_rect_simpl; auto.
Qed.

Theorem wnot_wnot'_equiv : forall sz (w : word sz), wnot w = wnot' w.
Proof.
  unfold wnot'.
  induction sz; intros w; shatterer.
Qed.

Theorem wnot_split1 : forall sz1 sz2 w, wnot (split1 sz1 sz2 w) = split1 sz1 sz2 (wnot w).
Proof.
  intros.
  repeat rewrite wnot_wnot'_equiv.
  unfold wnot'.
  erewrite <- split1_combine with (w := wones _).
  rewrite <- split1_bitwp_dist, combine_wones.
  reflexivity.
Qed.

Theorem wnot_split2 : forall sz1 sz2 w, wnot (split2 sz1 sz2 w) = split2 sz1 sz2 (wnot w).
Proof.
  intros.
  repeat rewrite wnot_wnot'_equiv.
  unfold wnot'.
  erewrite <- split2_combine with (z := wones _).
  rewrite <- split2_bitwp_dist, combine_wones.
  reflexivity.
Qed.

Theorem wnot_combine : forall sz1 sz2 (w1 : word sz1) (w2 : word sz2),
  wnot (combine w1 w2) = combine (wnot w1) (wnot w2).
Proof.
  intros.
  repeat rewrite wnot_wnot'_equiv.
  unfold wnot'.
  rewrite <- combine_wones, combine_bitwp.
  reflexivity.
Qed.

Theorem wnot_zero: forall sz, wnot (wzero sz) = wones sz.
Proof.
  induction sz; simpl; f_equal; eauto.
Qed.

Theorem wnot_ones : forall sz, wnot (wones sz) = wzero sz.
Proof.
  induction sz; simpl; f_equal; try rewrite IHsz; eauto.
Qed.

Theorem wnot_eq_rect : forall a b H (w : word a), wnot (eq_rect a word w b H) = eq_rect a word (wnot w) b H.
Proof.
  intros.
  subst b; eq_rect_simpl; auto.
Qed.

Theorem wor_unit : forall sz (x : word sz), wzero sz ^| x = x.
Proof.
  unfold wzero, wor; induction x; simpl; intuition congruence.
Qed.

Theorem wor_comm : forall sz (x y : word sz), x ^| y = y ^| x.
Proof.
  unfold wor; induction x; intro y; rewrite (shatter_word y); simpl; intuition; f_equal; auto with bool.
Qed.

Theorem wor_assoc : forall sz (x y z : word sz), x ^| (y ^| z) = x ^| y ^| z.
Proof.
  unfold wor; induction x; intro y; rewrite (shatter_word y); simpl; intuition; f_equal; auto with bool.
Qed.

Theorem wand_unit : forall sz (x : word sz), wones sz ^& x = x.
Proof.
  unfold wand; induction x; simpl; intuition congruence.
Qed.

Theorem wand_kill : forall sz (x : word sz), wzero sz ^& x = wzero sz.
Proof.
  unfold wzero, wand; induction x; simpl; intuition congruence.
Qed.

Theorem wand_comm : forall sz (x y : word sz), x ^& y = y ^& x.
Proof.
  unfold wand; induction x; intro y; rewrite (shatter_word y); simpl; intuition; f_equal; auto with bool.
Qed.

Theorem wand_assoc : forall sz (x y z : word sz), x ^& (y ^& z) = x ^& y ^& z.
Proof.
  unfold wand; induction x; intro y; rewrite (shatter_word y); simpl; intuition; f_equal; auto with bool.
Qed.

Theorem wand_or_distr : forall sz (x y z : word sz), (x ^| y) ^& z = (x ^& z) ^| (y ^& z).
Proof.
  unfold wand, wor; induction x; intro y; rewrite (shatter_word y); intro z; rewrite (shatter_word z); simpl; intuition; f_equal; auto with bool.
  destruct (whd y); destruct (whd z); destruct b; reflexivity.
Qed.

Lemma wor_wones : forall sz w, wones sz ^| w = wones sz.
Proof.
  unfold wor; induction sz; intros; simpl; auto.
  rewrite IHsz; auto.
Qed.

Lemma wor_wzero : forall sz w, wzero sz ^| w = w.
Proof.
  unfold wor; induction sz; shatterer.
Qed.

Lemma wand_wones : forall sz w, wones sz ^& w = w.
Proof.
  unfold wand; induction sz; shatterer.
Qed.

Lemma wand_wzero : forall sz w, wzero sz ^& w = wzero sz.
Proof.
  intros. rewrite <- wzero'_def.
  unfold wand; induction sz; shatterer.
Qed.

Lemma wxor_wones : forall sz w, wxor (wones sz) w = wnot w.
Proof.
  unfold wxor; induction sz; shatterer.
Qed.

Lemma wxor_wzero : forall sz w, wxor (wzero sz) w = w.
Proof.
  unfold wxor; induction sz; shatterer; destruct (whd w); auto.
Qed.

Lemma wxor_comm : forall sz (w1 w2 : word sz), wxor w1 w2 = wxor w2 w1.
Proof.
  unfold wxor; induction sz. shatterer.
  intros. rewrite (shatter_word w1), (shatter_word w2).
  simpl.
  rewrite xorb_comm, IHsz.
  reflexivity.
Qed.

Lemma wxor_assoc : forall sz (w1 w2 w3 : word sz), wxor w1 (wxor w2 w3) = wxor (wxor w1 w2) w3.
Proof.
  unfold wxor.
  induction sz; intros; rewrite (shatter_word w1), (shatter_word w2), (shatter_word w3); auto.
  simpl; f_equal.
  rewrite xorb_assoc_reverse; auto.
  rewrite IHsz.
  reflexivity.
Qed.

Lemma wor_wone : forall sz (w : word sz) b,
  WS b w ^| wone _ = WS true w.
Proof.
  intros.
  compute [wone natToWord wor]. simpl.
  fold natToWord.
  change (natToWord sz 0) with (wzero sz).
  rewrite orb_true_r.
  rewrite wor_comm, wor_wzero.
  reflexivity.
Qed.

Lemma wand_wone : forall sz (w : word sz) b,
  WS b w ^& wone _ = WS b (wzero _).
Proof.
  intros.
  compute [wone natToWord wand]. simpl.
  fold natToWord.
  change (natToWord sz 0) with (wzero sz).
  rewrite andb_true_r.
  rewrite wand_comm, wand_wzero.
  reflexivity.
Qed.

Lemma wxor_wone : forall sz (w : word sz) b,
  wxor (WS b w) (wone _) = WS (negb b) w.
Proof.
  intros.
  compute [wone natToWord wxor]. simpl.
  fold natToWord.
  change (natToWord sz 0) with (wzero sz).
  rewrite xorb_true_r.
  rewrite wxor_comm, wxor_wzero.
  reflexivity.
Qed.

Definition wbring (sz : nat) : semi_ring_theory (wzero sz) (wones sz) (@wor sz) (@wand sz) (@eq _) :=
  mk_srt _ _ _ _ _
  (@wor_unit _) (@wor_comm _) (@wor_assoc _)
  (@wand_unit _) (@wand_kill _) (@wand_comm _) (@wand_assoc _)
  (@wand_or_distr _).

(** * Inequality proofs *)

Ltac word_simpl := unfold sext, zext, wzero in *; simpl in *.

Ltac word_eq := ring.

Ltac word_eq1 := match goal with
                   | _ => ring
                   | [ H : _ = _ |- _ ] => ring [H]
                 end.

Theorem word_neq : forall sz (w1 w2 : word sz),
  w1 ^- w2 <> wzero sz
  -> w1 <> w2.
  intros; intro; subst.
  unfold wminus in H.
  rewrite wminus_inv in H.
  tauto.
Qed.

Ltac word_neq := apply word_neq; let H := fresh "H" in intro H; simpl in H; ring_simplify in H; try discriminate.

Ltac word_contra := match goal with
                      | [ H : _ <> _ |- False ] => apply H; ring
                    end.

Ltac word_contra1 := match goal with
                       | [ H : _ <> _ |- False ] => apply H;
                         match goal with
                           | _ => ring
                           | [ H' : _ = _ |- _ ] => ring [H']
                         end
                     end.

Lemma not_wlt_ge : forall sz (l r : word sz),
  ((l < r) -> False) -> (r <= l).
Proof.
  intros.
  case_eq (wlt_dec l r); intros;
    try contradiction;
    auto.
Qed.

Lemma not_wle_gt : forall sz (l r : word sz),
  ((l <= r) -> False) -> (r < l).
Proof.
  intros.
  case_eq (wlt_dec r l); intros;
    try contradiction;
    auto.
Qed.

Lemma lt_le : forall sz (a b : word sz),
  a < b -> a <= b.
Proof.
  unfold wlt, N.lt. intros sz a b H H0. rewrite N.compare_antisym in H0. rewrite H in H0. simpl in *. congruence.
Qed.

Lemma eq_le : forall sz (a b : word sz),
  a = b -> a <= b.
Proof.
  intros; subst. unfold wlt, N.lt. rewrite N.compare_refl. congruence.
Qed.

Lemma wordToN_inj : forall sz (a b : word sz),
  wordToN a = wordToN b -> a = b.
Proof.
  induction a; intro b0; rewrite (shatter_word b0); intuition.
  simpl in H.
  destruct b; destruct (whd b0); intros.
  f_equal. eapply IHa. eapply N.succ_inj in H.
  destruct (wordToN a); destruct (wordToN (wtl b0)); try congruence.
  destruct (wordToN (wtl b0)); destruct (wordToN a); inversion H.
  destruct (wordToN (wtl b0)); destruct (wordToN a); inversion H.
  f_equal. eapply IHa.
  destruct (wordToN a); destruct (wordToN (wtl b0)); try congruence.
Qed.

Lemma wordToNat_inj : forall sz (a b : word sz),
  wordToNat a = wordToNat b -> a = b.
Proof.
  intros; apply wordToN_inj.
  repeat rewrite wordToN_nat.
  apply Nat2N.inj_iff; auto.
Qed.

Lemma unique_inverse : forall sz (a b1 b2 : word sz),
  a ^+ b1 = wzero _ ->
  a ^+ b2 = wzero _ ->
  b1 = b2.
Proof.
  intros sz a b1 b2 H *.
  transitivity (b1 ^+ wzero _).
  rewrite wplus_comm. rewrite wplus_unit. auto.
  transitivity (b1 ^+ (a ^+ b2)). congruence.
  rewrite wplus_assoc.
  rewrite (wplus_comm b1). rewrite H. rewrite wplus_unit. auto.
Qed.

Lemma sub_0_eq : forall sz (a b : word sz),
  a ^- b = wzero _ -> a = b.
Proof.
  intros sz a b H. destruct (weq (wneg b) (wneg a)) as [e|n].
  transitivity (a ^+ (^~ b ^+ b)).
  rewrite (wplus_comm (^~ b)). rewrite wminus_inv.
  rewrite wplus_comm. rewrite wplus_unit. auto.
  rewrite e. rewrite wplus_assoc. rewrite wminus_inv. rewrite wplus_unit. auto.
  unfold wminus in H.
  generalize (unique_inverse a (wneg a) (^~ b)).
  intro H0. elimtype False. apply n. symmetry; apply H0.
  apply wminus_inv.
  auto.
Qed.

Lemma le_neq_lt : forall sz (a b : word sz),
  b <= a -> a <> b -> b < a.
Proof.
  intros sz a b H H0; destruct (wlt_dec b a) as [?|n]; auto.
  elimtype False. apply H0. unfold wlt, N.lt in *.
  eapply wordToN_inj. eapply Ncompare_eq_correct.
  case_eq ((wordToN a ?= wordToN b)%N); auto; try congruence.
  intros H1. rewrite N.compare_antisym in n. rewrite H1 in n. simpl in *. congruence.
Qed.


Hint Resolve word_neq lt_le eq_le sub_0_eq le_neq_lt : worder.

Ltac shatter_word x :=
  match type of x with
    | word 0 => try rewrite (shatter_word_0 x) in *
    | word (S ?N) =>
      let x' := fresh in
      let H := fresh in
      destruct (@shatter_word_S N x) as [ ? [ x' H ] ];
      rewrite H in *; clear H; shatter_word x'
  end.


(** Uniqueness of equality proofs **)
Lemma rewrite_weq : forall sz (a b : word sz)
  (pf : a = b),
  weq a b = left _ pf.
Proof.
  intros sz a b *; destruct (weq a b); try solve [ elimtype False; auto ].
  f_equal.
  eapply UIP_dec. eapply weq.
Qed.


(** * Some more useful derived facts *)

Lemma natToWord_plus : forall sz n m, natToWord sz (n + m) = natToWord _ n ^+ natToWord _ m.
  destruct sz as [|sz]; intros n m; intuition.
  rewrite wplus_alt.
  unfold wplusN, wordBinN.
  destruct (wordToNat_natToWord (S sz) n); intuition.
  destruct (wordToNat_natToWord (S sz) m); intuition.
  do 2 match goal with H : _ |- _ => rewrite H; clear H end.
  match goal with
  | [ |- context[?n - ?x * pow2 (S ?sz) + (?m - ?x0 * pow2 (S ?sz))] ]
    => replace (n - x * pow2 (S sz) + (m - x0 * pow2 (S sz))) with (n + m - x * pow2 (S sz) - x0 * pow2 (S sz))
      by omega
  end.
  repeat rewrite drop_sub; auto; omega.
Qed.

Lemma natToWord_S : forall sz n, natToWord sz (S n) = natToWord _ 1 ^+ natToWord _ n.
  intros sz n; change (S n) with (1 + n); apply natToWord_plus.
Qed.

Theorem natToWord_inj : forall sz n m, natToWord sz n = natToWord sz m
  -> (n < pow2 sz)%nat
  -> (m < pow2 sz)%nat
  -> n = m.
  intros sz n m H H0 H1.
  apply (f_equal (@wordToNat _)) in H.
  destruct (wordToNat_natToWord sz n) as [x H2].
  destruct (wordToNat_natToWord sz m) as [x0 H3].
  intuition.
  match goal with
  | [ H : wordToNat ?x = wordToNat ?y, H' : wordToNat ?x = ?a, H'' : wordToNat ?y = ?b |- _ ]
    => let H0 := fresh in assert (H0 : a = b) by congruence; clear H H' H''; rename H0 into H
  end.
  assert (x = 0).
  destruct x; auto.
  simpl in *.
  generalize dependent (x * pow2 sz).
  intros.
  omega.
  assert (x0 = 0).
  destruct x0; auto.
  simpl in *.
  generalize dependent (x0 * pow2 sz).
  intros.
  omega.
  subst; simpl in *; omega.
Qed.

Lemma wordToNat_natToWord_idempotent : forall sz n,
  (N.of_nat n < Npow2 sz)%N
  -> wordToNat (natToWord sz n) = n.
  intros sz n H.
  destruct (wordToNat_natToWord sz n) as [x]; intuition.
  destruct x as [|x].
  simpl in *; omega.
  simpl in *.
  apply Nlt_out in H.
  autorewrite with N in *.
  rewrite Npow2_nat in *.
  generalize dependent (x * pow2 sz).
  intros; omega.
Qed.

Lemma wplus_cancel : forall sz (a b c : word sz),
  a ^+ c = b ^+ c
  -> a = b.
  intros sz a b c H.
  apply (f_equal (fun x => x ^+ ^~ c)) in H.
  repeat rewrite <- wplus_assoc in H.
  rewrite wminus_inv in H.
  repeat rewrite (wplus_comm _ (wzero sz)) in H.
  repeat rewrite wplus_unit in H.
  assumption.
Qed.

Lemma wminus_plus_distr:
  forall {sz} (x y z: word sz), x ^- (y ^+ z) = x ^- y ^- z.
Proof.
  intros.
  apply wplus_cancel with (c:= y ^+ z).
  rewrite wminus_def, <-wplus_assoc.
  rewrite wplus_comm with (y:= y ^+ z), wminus_inv.
  rewrite wplus_comm with (x:= x), wplus_unit.
  rewrite !wminus_def, <-wplus_assoc.
  rewrite wplus_assoc with (x:= ^~ z).
  rewrite wplus_comm with (x:= ^~ z).
  rewrite <-wplus_assoc with (x:= y).
  rewrite wplus_comm with (x:= ^~ z), wminus_inv.
  rewrite wplus_comm with (x:= y), wplus_unit.
  rewrite <-wplus_assoc.
  rewrite wplus_comm with (x:= ^~ y), wminus_inv.
  rewrite wplus_comm, wplus_unit.
  reflexivity.
Qed.

Lemma wminus_wplus_undo: forall sz (a b: word sz),
    a ^- b ^+ b = a.
Proof.
  intros.
  rewrite wminus_def.
  rewrite <- wplus_assoc.
  rewrite (wplus_comm (^~ b)).
  rewrite wminus_inv.
  rewrite wplus_comm.
  rewrite wplus_unit.
  reflexivity.
Qed.

Lemma wneg_zero:
  forall {sz} (w: word sz), ^~ w = (natToWord sz 0) -> w = natToWord sz 0.
Proof.
  intros.
  apply wplus_cancel with (c:= ^~ w).
  rewrite wminus_inv, wplus_unit; auto.
Qed.

Lemma wneg_idempotent:
  forall {sz} (w: word sz), ^~ (^~ w) = w.
Proof.
  intros.
  apply sub_0_eq.
  rewrite wminus_def.
  rewrite wplus_comm.
  apply wminus_inv.
Qed.

Lemma wneg_zero': forall sz,
  wneg (natToWord sz 0) = natToWord sz 0.
Proof.
  intros. apply wneg_zero. apply wneg_idempotent.
Qed.

Lemma wplus_one_neq: forall {sz} (w: word (S sz)), w ^+ (natToWord (S sz) 1) <> w.
Proof.
  intros; intro Hx.
  rewrite wplus_comm in Hx.
  assert ((natToWord (S sz) 1) ^+ w ^- w = w ^- w) by (rewrite Hx; reflexivity).
  clear Hx.
  do 2 rewrite wminus_def in H.
  rewrite <-wplus_assoc in H.
  rewrite wminus_inv in H.
  rewrite wplus_comm, wplus_unit in H.
  inversion H.
Qed.

Lemma wneg_one_pow2_minus_one: forall {sz}, wordToNat (^~ (natToWord sz 1)) = pow2 sz - 1.
Proof.
  destruct sz; auto.
  unfold wneg; intros.
  rewrite wordToN_nat, roundTrip_1.
  simpl BinNat.N.of_nat.
  rewrite NToWord_nat, Nnat.N2Nat.inj_sub, Npow2_nat.
  apply wordToNat_natToWord_2.
  pose (pow2_zero (S sz)).
  omega.
Qed.

Lemma wones_pow2_minus_one: forall {sz}, wordToNat (wones sz) = pow2 sz - 1.
Proof.
  induction sz; simpl; auto.
  rewrite IHsz; pose (pow2_zero sz).
  omega.
Qed.

Lemma pow2_minus_one_wones: forall {sz} (w: word sz),
    wordToNat w = pow2 sz - 1 -> w = wones sz.
Proof.
  intros; rewrite <-wones_pow2_minus_one in H.
  apply wordToNat_inj; auto.
Qed.

Lemma wones_natToWord: forall sz,
  wones sz = $ (pow2 sz - 1).
Proof.
  induction sz.
  - reflexivity.
  - unfold wones. fold wones. rewrite IHsz.
    unfold natToWord at 2. fold natToWord. f_equal.
    + rewrite mod2sub.
      * simpl. rewrite mod2_pow2_twice. reflexivity.
      * pose proof (zero_lt_pow2 (S sz)). omega.
    + f_equal. unfold pow2 at 2. fold pow2.
      rewrite <- (div2_S_double (pow2 sz - 1)). f_equal.
      pose proof (zero_lt_pow2 sz). omega.
Qed.

Lemma wones_wneg_one: forall {sz}, wones sz = ^~ (natToWord sz 1).
Proof.
  intros; apply wordToNat_inj.
  rewrite wneg_one_pow2_minus_one.
  rewrite wones_pow2_minus_one.
  reflexivity.
Qed.

Lemma wordToNat_natToWord_pred:
  forall {sz} (w: word sz), w <> wzero sz ->
                            pred (wordToNat w) =
                            wordToNat (w ^- (natToWord sz 1)).
Proof.
  intros; remember (wordToNat w) as wn; destruct wn; simpl in *.
  - elim H.
    apply wordToNat_inj.
    rewrite roundTrip_0; auto.
  - apply natToWord_inj with (sz:= sz).
    + rewrite natToWord_wordToNat.
      apply wplus_cancel with (c:= (natToWord sz 1)).
      rewrite wminus_def, <-wplus_assoc.
      rewrite wplus_comm with (x:= ^~ (natToWord sz 1)).
      rewrite wminus_inv.
      rewrite wplus_comm with (x:= w).
      rewrite wplus_unit.
      rewrite wplus_comm, <-natToWord_S.
      apply wordToNat_inj.
      rewrite wordToNat_natToWord_2; auto.
      rewrite Heqwn.
      apply wordToNat_bound.
    + pose proof (wordToNat_bound w); omega.
    + apply wordToNat_bound.
Qed.

Lemma natToWord_mult : forall sz n m, natToWord sz (n * m) = natToWord _ n ^* natToWord _ m.
Proof.
  destruct sz; intuition.
  rewrite wmult_alt.
  unfold wmultN, wordBinN.
  destruct (wordToNat_natToWord (S sz) n); intuition.
  destruct (wordToNat_natToWord (S sz) m); intuition.
  rewrite H0; rewrite H2; clear H0 H2.
  replace ((n - x * pow2 (S sz)) * (m - x0 * pow2 (S sz)))
    with ((n - x * pow2 (S sz)) * m - (n - x * pow2 (S sz)) * (x0 * pow2 (S sz)))
    by (rewrite Nat.mul_sub_distr_l; auto).
  rewrite mult_assoc; rewrite drop_sub.
  repeat rewrite mult_comm with (m:=m).
  replace (m * (n - x * pow2 (S sz)))
    with (m * n - m * (x * pow2 (S sz)))
    by (rewrite Nat.mul_sub_distr_l; auto).
  rewrite mult_assoc; rewrite drop_sub.
  auto.
  rewrite <- mult_assoc; apply Nat.mul_le_mono_l; auto.
  rewrite <- mult_assoc; apply Nat.mul_le_mono_l; auto.
Qed.

Lemma wlt_lt: forall sz (a b : word sz), a < b ->
  (wordToNat a < wordToNat b)%nat.
Proof.
  intros.
  unfold wlt in H.
  repeat rewrite wordToN_nat in *.
  apply Nlt_out in H.
  repeat rewrite Nat2N.id in *.
  auto.
Qed.

Lemma wle_le: forall sz (a b : word sz), (a <= b)%word ->
  (wordToNat a <= wordToNat b)%nat.
Proof.
  intros.
  unfold wlt in H.
  repeat rewrite wordToN_nat in *.
  apply Nge_out in H.
  repeat rewrite Nat2N.id in *.
  auto.
Qed.

Lemma wlt_lt': forall sz a b, (a < pow2 sz)%nat
  -> natToWord sz a < b
  -> (wordToNat (natToWord sz a) < wordToNat b)%nat.
Proof.
  intros.
  apply wlt_lt.
  auto.
Qed.

Lemma lt_word_lt_nat : forall (sz:nat) (n:word sz) (m:nat),
  (n < (natToWord sz m))%word ->
  (wordToNat n < m)%nat.
Proof.
  intros.
  apply wlt_lt in H.
  destruct (wordToNat_natToWord' sz m).
  rewrite <- H0.
  apply lt_plus_trans with (p := x * pow2 sz).
  assumption.
Qed.

Lemma le_word_le_nat : forall (sz:nat) (n:word sz) (m:nat),
  (n <= (natToWord sz m))%word ->
  (wordToNat n <= m)%nat.
Proof.
  intros.
  apply wle_le in H.
  destruct (wordToNat_natToWord' sz m).
  rewrite <- H0.
  apply le_plus_trans with (p := x * pow2 sz).
  assumption.
Qed.

(* Chain [lt_word_lt_nat] and [Nat.lt_le_incl]
    Avoids using [Hint Resolve Nat.lt_le_incl] for this specific lemma,
    though this may be a premature optimization. *)
Lemma lt_word_le_nat : forall (sz:nat) (n:word sz) (m:nat),
  (n < (natToWord sz m))%word ->
  (wordToNat n <= m)%nat.
Proof.
  intros.
  apply lt_word_lt_nat in H.
  apply Nat.lt_le_incl.
  assumption.
Qed.

Hint Resolve lt_word_le_nat.

Lemma wordToNat_natToWord_idempotent' : forall sz n,
  (n < pow2 sz)%nat
  -> wordToNat (natToWord sz n) = n.
Proof.
  intros.
  destruct (wordToNat_natToWord sz n); intuition.
  destruct x.
  simpl in *; omega.
  simpl in *.
  generalize dependent (x * pow2 sz).
  intros; omega.
Qed.

Lemma le_word_le_nat': forall (sz:nat) n m,
  (n < pow2 sz)%nat ->
  (natToWord sz n <= m)%word ->
  (n <= wordToNat m)%nat.
Proof.
  intros.
  apply wle_le in H0.
  rewrite wordToNat_natToWord_idempotent' in H0; auto.
Qed.

Lemma wordToNat_natToWord_bound : forall sz n (bound : word sz),
  (n <= wordToNat bound)%nat
  -> wordToNat (natToWord sz n) = n.
Proof.
  intros.
  apply wordToNat_natToWord_idempotent'.
  eapply le_lt_trans; eauto.
  apply wordToNat_bound.
Qed.

Lemma wordToNat_natToWord_le : forall sz n,
  (wordToNat (natToWord sz n) <= n)%nat.
Proof.
  intros.
  case_eq (lt_dec n (pow2 sz)); intros.
  rewrite wordToNat_natToWord_idempotent'; auto.
  eapply le_trans.
  apply Nat.lt_le_incl.
  apply wordToNat_bound.
  omega.
Qed.

Lemma wordToNat_natToWord_lt : forall sz n b,
  (n < b -> wordToNat (natToWord sz n) < b)%nat.
Proof.
  intros.
  eapply le_lt_trans.
  apply wordToNat_natToWord_le.
  auto.
Qed.

Lemma wordToNat_eq_natToWord : forall sz (w : word sz) n,
  wordToNat w = n
  -> w = natToWord sz n.
Proof.
  intros. rewrite <- H. rewrite natToWord_wordToNat. auto.
Qed.

Lemma wlt_lt_bound: forall sz (a : word sz) (b bound : nat),
  (a < natToWord sz b)%word
  -> (b <= wordToNat (natToWord sz bound))%nat
  -> (wordToNat a < b)%nat.
Proof.
  intros.
  apply wlt_lt in H.
  erewrite wordToNat_natToWord_bound in H; eauto.
Qed.

Lemma natplus1_wordplus1_eq:
  forall sz (a bound : word sz),
    (0 < sz)%nat ->
    (a < bound)%word ->
    (wordToNat a) + 1 = wordToNat (a ^+ (natToWord sz 1)).
Proof.
  intros.
  rewrite wplus_alt. unfold wplusN, wordBinN. simpl.
  assert ((1 < pow2 sz)%nat).
  inversion H.
  simpl; auto.
  apply one_lt_pow2.
  erewrite wordToNat_natToWord_bound.
  rewrite wordToNat_natToWord_idempotent' by auto.
  reflexivity.
  apply wlt_lt in H0.
  rewrite wordToNat_natToWord_idempotent' by auto.
  instantiate (1:=bound). omega.
Qed.

Lemma lt_wlt: forall sz (n : word sz) m, (wordToNat n < wordToNat m)%nat ->
  n < m.
Proof.
  intros.
  unfold wlt.
  repeat rewrite wordToN_nat.
  apply Nlt_in.
  repeat rewrite Nat2N.id.
  auto.
Qed.

Lemma le_wle: forall sz (n : word sz) m, (wordToNat n <= wordToNat m)%nat ->
  n <= m.
Proof.
  intros.
  unfold wlt.
  repeat rewrite wordToN_nat.
  apply N.le_ngt.
  apply N.ge_le.
  apply Nge_in.
  repeat rewrite Nat2N.id.
  auto.
Qed.

Lemma wlt_wle_incl : forall sz (a b : word sz),
  (a < b)%word -> (a <= b)%word.
Proof.
  intros.
  apply wlt_lt in H.
  apply le_wle.
  omega.
Qed.

Lemma wminus_Alt2: forall sz x y, y <= x ->
  @wminusN sz x y = wordBinN minus x y.
Proof.
  intros.
  unfold wminusN, wplusN, wnegN, wordBinN.
  destruct (weq y (natToWord sz 0)); subst.

  rewrite roundTrip_0.
  repeat rewrite <- minus_n_O.
  rewrite <- drop_sub with (k:=1) (n:=pow2 sz); try omega.
  replace (pow2 sz - 1 * pow2 sz) with (0) by omega.
  rewrite roundTrip_0.
  rewrite <- plus_n_O.
  reflexivity.

  rewrite wordToNat_natToWord_idempotent' with (n:=pow2 sz - wordToNat y).
  rewrite <- drop_sub with (k:=1).
  simpl.
  rewrite <- plus_n_O.
  replace (wordToNat x + (pow2 sz - wordToNat y) - pow2 sz) with (wordToNat x - wordToNat y).
  auto.
  rewrite Nat.add_sub_assoc.
  omega.

  remember (wordToNat_bound y); omega.

  simpl. rewrite <- plus_n_O.
  rewrite Nat.add_sub_assoc; [| remember (wordToNat_bound y); omega ].
  rewrite plus_comm.
  rewrite <- Nat.add_sub_assoc.
  omega.

  apply Nat.nlt_ge.
  unfold not in *; intros.
  apply H.
  apply lt_wlt; auto.

  apply Nat.sub_lt.
  remember (wordToNat_bound y); omega.

  assert (wordToNat y <> 0); try omega.

  assert (wordToN y <> wordToN (natToWord sz 0)).
  unfold not in *. intros. apply n.
  apply wordToN_inj.
  auto.

  repeat rewrite wordToN_nat in H0.
  unfold not in *. intros. apply H0.
  apply N2Nat.inj.
  repeat rewrite Nat2N.id.
  rewrite roundTrip_0.
  auto.
Qed.

Theorem wlt_wf:
  forall sz, well_founded (@wlt sz).
Proof.
  intros.
  eapply well_founded_lt_compat with (f:=@wordToNat sz).
  apply wlt_lt.
Qed.

Ltac wlt_ind :=
  match goal with
  | [ |- forall (n: word ?len), ?P ] =>
    refine (well_founded_ind (@wlt_wf len) (fun n => P) _)
  end.

Theorem wordToNat_plusone: forall sz w w', w < w' ->
  wordToNat (w ^+ natToWord sz 1) = S (wordToNat w).
Proof.
  intros.

  destruct sz.
  exfalso.
  rewrite word0 with (w:=w') in H.
  rewrite word0 with (w:=w) in H.
  apply wlt_lt in H.
  omega.

  rewrite wplus_alt.
  unfold wplusN, wordBinN.
  rewrite wordToNat_natToWord_idempotent'.

  rewrite roundTrip_1.
  omega.

  eapply Nat.le_lt_trans; [| apply wordToNat_bound ].
  rewrite wordToNat_natToWord_idempotent';
    [| erewrite <- roundTrip_1 at 1; apply wordToNat_bound ].
  apply wlt_lt in H.
  instantiate (1:=w').
  omega.
Qed.


Theorem wordToNat_minus_one': forall sz n, n <> natToWord sz 0 ->
  S (wordToNat (n ^- natToWord sz 1)) = wordToNat n.
Proof.
  intros.
  destruct sz.
  rewrite word0 with (w:=n) in H.
  rewrite word0 with (w:=natToWord 0 0) in H.
  exfalso; auto.

  destruct (weq n (natToWord (S sz) 0)); intuition.
  rewrite wminus_Alt.
  rewrite wminus_Alt2.
  unfold wordBinN.
  rewrite roundTrip_1.
  erewrite wordToNat_natToWord_bound with (bound:=n); try omega.
  assert (wordToNat n <> 0); try omega.
  unfold not; intros; apply n0; clear n0.
  rewrite <- H0; rewrite natToWord_wordToNat; auto.
  unfold not; intros; apply n0; clear n0.
  apply wlt_lt in H0.
  replace n with (natToWord (S sz) (wordToNat n)) by (rewrite natToWord_wordToNat; auto).
  f_equal; rewrite roundTrip_1 in *.
  omega.
Qed.

Theorem wordToNat_minus_one: forall sz n, n <> natToWord sz 0 ->
  wordToNat (n ^- natToWord sz 1) = wordToNat n - 1.
Proof.
  intros.
  erewrite Nat.succ_inj with (n2 := wordToNat (n ^- (natToWord sz 1))); auto.
  rewrite wordToNat_minus_one'; auto.
  assert (wordToNat n <> 0).
  intuition.
  erewrite <- roundTrip_0 with (sz := sz) in H0.
  apply wordToNat_inj in H0; tauto.
  omega.
Qed.

Lemma lt_minus : forall a b c,
  (b <= a -> b < c -> a < c -> a - b < c)%nat.
Proof.
  intros; omega.
Qed.

Lemma wminus_minus : forall sz (a b : word sz),
  b <= a
  -> wordToNat (a ^- b) = wordToNat a - wordToNat b.
Proof.
  intros.
  rewrite wminus_Alt.
  rewrite wminus_Alt2; auto.
  unfold wordBinN.
  eapply wordToNat_natToWord_idempotent'.
  apply lt_minus.
  apply wle_le; auto.
  apply wordToNat_bound.
  apply wordToNat_bound.
Qed.

Lemma wminus_minus': forall (sz : nat) (a b : word sz),
    (#b <= #a)%nat ->
    #(a ^- b) = #a - #b.
Proof.
  intros. apply wminus_minus.
  unfold wlt. intro C.
  apply Nlt_out in C.
  rewrite! wordToN_to_nat in *.
  omega.
Qed.

Lemma wordToNat_neq_inj: forall sz (a b : word sz),
  a <> b <-> wordToNat a <> wordToNat b.
Proof.
  split; intuition.
  apply wordToNat_inj in H0; auto.
  subst; auto.
Qed.

Lemma natToWord_discriminate: forall sz, (sz > 0)%nat -> natToWord sz 0 <> natToWord sz 1.
Proof.
  unfold not.
  intros.
  induction sz.
  omega.
  unfold natToWord in H0; fold natToWord in H0.
  discriminate H0.
Qed.

Definition bit_dec : forall (a : word 1), {a = $0} + {a = $1}.
  intro.
  rewrite (shatter_word a).
  replace (wtl a) with WO by auto.
  destruct (whd a).
  right; apply eq_refl.
  left; apply eq_refl.
Defined.

Lemma neq0_wneq0: forall sz (n : word sz),
  wordToNat n <> 0  <-> n <> $0.
Proof.
  split; intros.
  apply wordToNat_neq_inj.
  rewrite roundTrip_0; auto.
  apply wordToNat_neq_inj in H.
  rewrite roundTrip_0 in H; auto.
Qed.

Lemma gt0_wneq0: forall sz (n : word sz),
  (wordToNat n > 0)%nat <-> n <> $0.
Proof.
  split; intros.
  apply neq0_wneq0; omega.
  apply wordToNat_neq_inj in H.
  rewrite roundTrip_0 in H; omega.
Qed.

Lemma weq_minus1_wlt: forall sz (a b : word sz),
  (a <> $0 -> a ^- $1 = b -> a > b)%word.
Proof.
  intros.
  apply lt_wlt; subst.
  rewrite wordToNat_minus_one; auto.
  apply gt0_wneq0 in H.
  omega.
Qed.

Lemma wordnat_minus1_eq : forall sz n (w : word sz),
  (n > 0)%nat
  -> n = wordToNat w
  -> n - 1 = wordToNat (w ^- $1).
Proof.
  intros; rewrite wordToNat_minus_one; auto.
  apply gt0_wneq0; subst; auto.
Qed.

Theorem wlshift_0 : forall sz (w : word sz), @wlshift sz w 0 = w.
Proof.
  intros.
  unfold wlshift.
  eapply split1_0.
Qed.

Theorem wrshift_0 : forall sz (w : word sz), @wrshift sz w 0 = w.
Proof.
  intros.
  unfold wrshift.
  simpl.
  rewrite combine_n_0.
  eq_rect_simpl. reflexivity.
Qed.

Theorem wlshift_gt : forall sz n (w : word sz), (n > sz)%nat ->
  wlshift w n = wzero sz.
Proof.
  intros sz n w H.
  generalize dependent w.
  remember (n - sz) as e.
  assert (n = sz + e) by omega; subst n.
  intros w.
  unfold wlshift.
  rewrite <- combine_wzero.
  erewrite combine_assoc, eq_rect_word_match.
  eq_rect_simpl.
  rewrite eq_rect_combine.
  apply split1_combine.
  Grab Existential Variables. omega.
Qed.

Theorem wrshift_gt : forall sz n (w : word sz), (n > sz)%nat ->
  wrshift w n = wzero sz.
Proof.
  intros sz n w H.
  generalize dependent w.
  remember (n - sz) as e.
  assert (n = sz + e) by omega; subst n.
  intros w.
  unfold wrshift.
  erewrite wzero_rev, <- combine_wzero.
  eq_rect_simpl.
  rewrite <- eq_rect_word_match, <- eq_rect_combine, eq_rect_word_match.
  eq_rect_simpl.
  rewrite eq_rect_combine_assoc', split2_combine.
  reflexivity.
  Grab Existential Variables. omega.
Qed.

Theorem wlshift_bitwp : forall sz (w1 w2 : word sz) f n,
  wlshift (bitwp f w1 w2) n = split1 sz n (
    eq_rec _ word (combine (wzero n) (bitwp f w1 w2)) _ (eq_sym (Nat.add_comm sz n))).
Proof.
  intros.
  unfold wlshift.
  eq_rect_simpl.
  reflexivity.
Qed.

Theorem wrshift_bitwp : forall sz (w1 w2 : word sz) f n,
  wrshift (bitwp f w1 w2) n = split2 n sz (
    eq_rect _ word (combine (bitwp f w1 w2) (wzero n)) _ (eq_sym (Nat.add_comm n sz))).
Proof.
  intros.
  unfold wrshift.
  eq_rect_simpl.
  reflexivity.
Qed.

Theorem wnot_wlshift : forall sz (w : word sz) n,
  wnot (wlshift w n) = split1 sz n (eq_rect _ word (combine (wones n) (wnot w)) _ (eq_sym (Nat.add_comm sz n))).
Proof.
  intros.
  unfold wlshift.
  rewrite wnot_split1.
  eq_rect_simpl.
  rewrite wnot_eq_rect.
  rewrite wnot_combine.
  rewrite wnot_zero.
  reflexivity.
Qed.

Theorem wnot_wrshift : forall sz (w : word sz) n,
  wnot (wrshift w n) = split2 n sz (eq_rect _ word (combine (wnot w) (wones n)) _ (eq_sym (Nat.add_comm n sz))).
Proof.
  intros.
  unfold wrshift.
  rewrite wnot_split2.
  eq_rect_simpl.
  rewrite wnot_eq_rect.
  rewrite wnot_combine.
  rewrite wnot_zero.
  reflexivity.
Qed.

Lemma wlshift_alt: forall sz n (a: word sz),
    wlshift' a n = wlshift a n.
Proof.
  intros. unfold wlshift, wlshift'.
  unfold eq_rec_r.
  unfold eq_rec.
  erewrite nat_cast_proof_irrel.
  rewrite nat_cast_eq_rect.
  reflexivity.
Qed.

Theorem div2_pow2_twice: forall n,
  Nat.div2 (pow2 n + (pow2 n + 0)) = pow2 n.
Proof.
  intros.
  replace (pow2 n + (pow2 n + 0)) with (2 * pow2 n) by omega.
  rewrite Nat.div2_double.
  auto.
Qed.

Theorem zero_or_wordToNat_S: forall sz (n : word sz),
  n = $0 \/
  exists nn, wordToNat n = S nn /\ wordToNat (n ^- $1) = nn.
Proof.
  intros.
  destruct sz.
  left. rewrite (word0 n). auto.
  destruct (weq n $0); intuition.
  right.
  exists (wordToNat (n ^- $1)); intuition.
  rewrite wminus_Alt.
  rewrite wminus_Alt2.
  unfold wordBinN.
  rewrite roundTrip_1.
  erewrite wordToNat_natToWord_bound with (bound:=n); try omega.
  assert (wordToNat n <> 0); try omega.
  unfold not; intros; apply n0; clear n0.
  rewrite <- H. rewrite natToWord_wordToNat; auto.
  unfold not; intros; apply n0; clear n0.
  apply wlt_lt in H.
  replace n with (natToWord (S sz) (wordToNat n)) by (rewrite natToWord_wordToNat; auto).
  f_equal.
  rewrite roundTrip_1 in *.
  omega.
Qed.

Theorem wbit_or_same : forall sz sz' (n : word sz'), (wordToNat n < sz)%nat
  -> (wbit sz n) ^| (wbit sz n) <> wzero sz.
Proof.
  unfold not.
  induction sz; intros; try omega.
  unfold wbit, wzero, wor in *.
  simpl in *.
  destruct (zero_or_wordToNat_S n).
  subst; rewrite roundTrip_0 in *. discriminate.
  destruct H1. destruct H1.
  rewrite H1 in *.
  inversion H0.
  apply (inj_pair2_eq_dec _ eq_nat_dec) in H5.
  rewrite div2_pow2_twice in H5.
  repeat rewrite <- H2 in H5.
  eapply IHsz; eauto.
  omega.
Qed.

Theorem wbit_or_other : forall sz sz' (n1 n2 : word sz'), (wordToNat n1 < sz)%nat
  -> (wordToNat n2 < sz)%nat
  -> (n1 <> n2)
  -> (wbit sz n1) ^& (wbit sz n2) = wzero sz.
Proof.
  induction sz; intros; try omega.
  unfold wbit, wzero, wand.
  simpl.
  destruct (zero_or_wordToNat_S n1); destruct (zero_or_wordToNat_S n2);
    try congruence; destruct_conjs; subst; try rewrite roundTrip_0.

  repeat rewrite H4; simpl; repeat rewrite mod2_pow2_twice; f_equal.
  rewrite wand_kill; auto.

  repeat rewrite H4; simpl; repeat rewrite mod2_pow2_twice; f_equal.
  rewrite wand_comm; rewrite wand_kill; auto.

  repeat rewrite H4; repeat rewrite H6; simpl.
  repeat rewrite mod2_pow2_twice; f_equal.
  repeat rewrite div2_pow2_twice.
  eapply IHsz; try omega.

  apply word_neq.
  unfold not in *; intros; apply H1; clear H1.
  apply sub_0_eq; rewrite <- H2.
  ring_sz sz'.
Qed.

Theorem wbit_and_not: forall sz sz' (n : word sz'), (wordToNat n < sz)%nat
  -> (wbit sz n) ^& wnot (wbit sz n) = wzero sz.
Proof.
  induction sz; intros; try omega.
  unfold wbit, wzero, wand, wnot.
  simpl.
  f_equal.
  apply andb_negb_r.

  destruct (zero_or_wordToNat_S n); subst.
  rewrite roundTrip_0; simpl.
  apply wand_kill.

  do 2 destruct H0.
  rewrite H0; simpl.
  rewrite div2_pow2_twice.
  fold wnot.
  rewrite <- H1.
  eapply IHsz.
  omega.
Qed.

Theorem wbit_and_not_other: forall sz sz' (n1 n2 : word sz'), (wordToNat n1 < sz)%nat
  -> (wordToNat n2 < sz)%nat
  -> n1 <> n2
  -> (wbit sz n1) ^& wnot (wbit sz n2) = wbit sz n1.
Proof.
  induction sz; intros; try omega.
  unfold wbit, wzero, wand, wnot.
  simpl.
  destruct (zero_or_wordToNat_S n1); destruct (zero_or_wordToNat_S n2);
    try congruence; destruct_conjs; subst; fold wnot; try rewrite roundTrip_0; simpl;
    f_equal.

  rewrite H4; simpl; rewrite mod2_pow2_twice; auto.
  rewrite H4; simpl; rewrite div2_pow2_twice; apply wand_kill.

  rewrite H4; simpl; rewrite mod2_pow2_twice; auto.
  rewrite H4; simpl; rewrite div2_pow2_twice.
  rewrite wnot_zero. rewrite wand_comm. apply wand_unit.

  rewrite H4; simpl; rewrite mod2_pow2_twice; simpl; apply andb_true_r.
  rewrite H4; rewrite H6; simpl.
  repeat rewrite div2_pow2_twice.
  apply IHsz; try omega.

  apply word_neq.
  unfold not in *; intros; apply H1.
  apply sub_0_eq.
  rewrite <- H2.
  ring_sz sz'.
Qed.

Lemma wordToNat_wzero:
  forall sz, wordToNat (wzero sz) = 0.
Proof.
  unfold wzero; intros.
  apply roundTrip_0.
Qed.

Lemma wordToN_wzero:
  forall sz, wordToN (wzero sz) = 0%N.
Proof.
  intros; rewrite wordToN_nat.
  rewrite wordToNat_wzero.
  reflexivity.
Qed.

Lemma combine_zero:
  forall n m, combine (natToWord n 0) (natToWord m 0) = natToWord _ 0.
Proof.
  induction n; simpl; intros; [reflexivity|].
  rewrite IHn; reflexivity.
Qed.

Lemma combine_one:
  forall n m, combine (natToWord (S n) 1) (natToWord m 0) = natToWord _ 1.
Proof.
  cbn; intros.
  rewrite combine_zero; reflexivity.
Qed.

Lemma wmsb_wzero':
  forall sz, wmsb (wzero' sz) false = false.
Proof. induction sz; auto. Qed.

Lemma wmsb_wzero:
  forall sz, wmsb (wzero sz) false = false.
Proof.
  intros.
  rewrite <-wzero'_def.
  apply wmsb_wzero'.
Qed.

Lemma wmsb_wones:
  forall sz, wmsb (wones (S sz)) false = true.
Proof.
  induction sz; cbn; auto.
Qed.

Lemma wmsb_0: forall sz (m: word (S sz)) default,
  (# m < pow2 sz)%nat ->
  @wmsb (S sz) m default = false.
Proof.
  induction sz; intros.
  - simpl in *. assert (#m = 0) as N by omega.
    rewrite <- (roundTrip_0 1) in N.
    apply wordToNat_inj in N. subst m.
    simpl. reflexivity.
  - pose proof (shatter_word_S m) as P.
    destruct P as [b [m0 E]]. subst.
    unfold wmsb. fold wmsb.
    apply IHsz.
    simpl in H. destruct b; omega.
Qed.

Lemma wmsb_1: forall sz (m: word (S sz)) default,
  pow2 sz <= # m < 2 * pow2 sz ->
  @wmsb (S sz) m default = true.
Proof.
  induction sz; intros.
  - simpl in *. assert (#m = 1) as N by omega.
    rewrite <- (roundTrip_1 1) in N.
    apply (wordToNat_inj m ($ 1)) in N. subst m.
    simpl. reflexivity.
  - pose proof (shatter_word_S m) as P.
    destruct P as [b [m0 E]]. subst.
    unfold wmsb. fold wmsb.
    apply IHsz.
    simpl in H. destruct b; omega.
Qed.

Lemma wmsb_0_natToWord: forall sz n default,
  (2 * n < pow2 (S sz))%nat ->
  @wmsb (S sz) (natToWord (S sz) n) default = false.
Proof.
  intros. apply wmsb_0.
  pose proof (wordToNat_natToWord_le (S sz) n). unfold pow2 in H. fold pow2 in H. omega.
Qed.

Lemma wmsb_1_natToWord: forall sz n default,
  pow2 sz <= n < 2 * pow2 sz ->
  @wmsb (S sz) (natToWord (S sz) n) default = true.
Proof.
  intros. apply wmsb_1.
  rewrite wordToNat_natToWord_idempotent'; simpl; omega.
Qed.

Lemma wordToN_wzero':
  forall sz, wordToN (wzero' sz) = 0%N.
Proof.
  induction sz; simpl; auto.
  rewrite IHsz; auto.
Qed.

Lemma wordToZ_wzero':
  forall sz, wordToZ (wzero' sz) = 0%Z.
Proof.
  unfold wordToZ; intros.
  rewrite wmsb_wzero'.
  rewrite wordToN_wzero'.
  reflexivity.
Qed.

Lemma wordToZ_wzero:
  forall sz, wordToZ (wzero sz) = 0%Z.
Proof.
  unfold wordToZ; intros.
  rewrite wmsb_wzero.
  rewrite wordToN_wzero.
  reflexivity.
Qed.

Lemma wmsb_existT: (* Note: not axiom free *)
  forall sz1 (w1: word sz1) sz2 (w2: word sz2),
    existT word _ w1 = existT word _ w2 ->
    forall b, wmsb w1 b = wmsb w2 b.
Proof.
  intros.
  assert (sz1 = sz2) by (apply eq_sigT_fst in H; auto); subst.
  destruct_existT; reflexivity.
Qed.

Lemma destruct_word_S: forall sz (w: word (S sz)),
    exists v b, w = WS b v.
Proof.
  intros.
  refine (match w with
          | WO => _
          | WS b v => _
          end); unfold IDProp; eauto.
Qed.

Lemma induct_word_S: forall (P : forall n : nat, word (S n) -> Prop),
    (forall b, P 0 (WS b WO)) ->
    (forall b b0 n (w : word n), P n (WS b0 w) -> P (S n) (WS b (WS b0 w))) ->
    forall (n : nat) (w : word (S n)), P n w.
Proof.
  induction n; intros.
  - destruct (destruct_word_S w) as [v [b E]]. subst w.
    rewrite (word0 v).
    apply H.
  - destruct (destruct_word_S w) as [v [b E]]. subst w.
    destruct (destruct_word_S v) as [w [b0 E]]. subst v.
    apply H0.
    apply IHn.
Qed.

Lemma wmsb_ws:
  forall sz (w: word (S sz)) b a, wmsb (WS b w) a = wmsb w a.
Proof.
  intros. cbn.
  destruct (destruct_word_S w) as [v [c E]].
  rewrite E.
  reflexivity.
Qed.

Lemma wmsb_extz:
  forall sz (w: word sz) n,
    wmsb (extz w n) false = wmsb w false.
Proof.
  induction n; intros; auto.
Qed.

Lemma wmsb_default:
  forall sz (w: word sz) b1 b2,
    sz <> 0 -> wmsb w b1 = wmsb w b2.
Proof.
  dependent induction w; intros; intuition idtac.
Qed.

Lemma wmsb_nat_cast:
  forall sz1 (w: word sz1) sz2 (Hsz: sz1 = sz2) b,
    wmsb w b = wmsb (nat_cast word Hsz w) b.
Proof.
  destruct sz1; intros.
  - subst sz2. reflexivity.
  - destruct sz2; [discriminate|].
    destruct (destruct_word_S w) as [v [b0 E]]. subst w.
    pose proof (eq_add_S sz1 sz2 Hsz) as Hsz'.
    subst sz2.
    rewrite nat_cast_eq_rect.
    f_equal.
    erewrite (WS_eq_rect _ _ _ eq_refl).
    reflexivity.
Qed.

Lemma wmsb_eq_rect:
  forall sz1 (w: word sz1) sz2 (Hsz: sz1 = sz2) b,
    wmsb w b = wmsb (eq_rect _ word w _ Hsz) b.
Proof.
  intros. rewrite <- nat_cast_eq_rect. apply wmsb_nat_cast.
Qed.

Local Arguments nat_cast: simpl never.

Lemma nat_cast_inj: forall sz sz' (p: sz = sz') (w1 w2: word sz),
    nat_cast word p w1 = nat_cast word p w2 ->
    w1 = w2.
Proof.
  intros. destruct p. rewrite? nat_cast_same in H. assumption.
Qed.

Lemma wtl_nat_cast_WS: forall n m (q: n = m) (p: S n = S m) (w: word n) (b: bool),
    wtl (nat_cast word p (WS b w)) =
    nat_cast word q w.
Proof.
  intros n m. destruct q. intros.
  rewrite nat_cast_same.
  transitivity (wtl (WS b w)); [|reflexivity].
  f_equal.
  rewrite <- nat_cast_same.
  apply nat_cast_proof_irrel.
Qed.

Lemma wmsb_split2': forall sz (w: word (S sz)) b,
  wmsb w b = negb (weqb (split2 sz 1 (nat_cast _ (eq_sym (Nat.add_1_r sz)) w)) (natToWord _ 0)).
Proof.
  apply (induct_word_S (fun sz w => forall b, wmsb w b =
     negb (weqb (split2 sz 1 (nat_cast _ (eq_sym (Nat.add_1_r sz)) w)) (natToWord _ 0))));
  intros.
  - destruct b; reflexivity.
  - cbn in *. rewrite (H false). repeat f_equal.
    clear.
    apply (nat_cast_inj (Nat.add_1_r n)).
    erewrite wtl_nat_cast_WS.
    reflexivity.
Qed.

Lemma wmsb_split2:
  forall sz (w: word (sz + 1)) b,
    wmsb w b = if weq (split2 _ 1 w) (natToWord _ 0) then false else true.
Proof.
  intros.
  pose proof (@wmsb_split2' sz). specialize (H (nat_cast _ (Nat.add_1_r sz) w) b).
  simpl in H.
  rewrite nat_cast_fuse in H.
  rewrite <- (nat_cast_proof_irrel word _ _ eq_refl) in H.
  rewrite nat_cast_same in H.
  destruct (weq (split2 sz 1 w) $ (0)).
  - rewrite e in H. simpl in H. rewrite <- H. clear.
    apply wmsb_nat_cast.
  - simpl in n. apply weqb_ne in n. rewrite n in H. simpl in H. rewrite <- H. clear.
    apply wmsb_nat_cast.
Qed.

Lemma wmsb_true_split2_wones:
  forall sz (w: word (sz + 1)) b,
    wmsb w b = true ->
    wones 1 = split2 sz 1 w.
Proof.
  intros.
  pose proof (wmsb_split2 _ w b).
  destruct (weq _ _).
  - rewrite H in H0; discriminate.
  - clear -n.
    remember (split2 sz 1 w) as ww; clear Heqww w.
    destruct (destruct_word_S ww) as [w [b E]]. subst ww.
    rewrite (word0 w) in *. clear w. simpl in *. destruct b; congruence.
Qed.

Lemma wmsb_false_split2_wzero:
  forall sz (w: word (sz + 1)) b,
    wmsb w b = false ->
    wzero 1 = split2 sz 1 w.
Proof.
  intros.
  pose proof (wmsb_split2 _ w b).
  destruct (weq _ _); auto.
  rewrite H in H0; discriminate.
Qed.

Lemma wmsb_split1_sext:
  forall sz (w: word (sz + 1)),
    wmsb w false = wmsb (split1 _ 1 w) false ->
    exists sw, sext sw 1 = w.
Proof.
  unfold sext; intros.
  pose proof (combine_split _ _ w) as Hw.
  rewrite <-Hw; rewrite <-Hw in H at 2; clear Hw.
  rewrite split1_combine in H.
  exists (split1 sz 1 w).
  destruct (wmsb (split1 sz 1 w) false).
  - rewrite <-wmsb_true_split2_wones with (b:= false) by assumption.
    reflexivity.
  - rewrite <-wmsb_false_split2_wzero with (b:= false) by assumption.
    reflexivity.
Qed.

Lemma wmsb_combine_WO:
  forall sz (w: word sz) b,
    wmsb (combine w WO) b = wmsb w b.
Proof.
  dependent induction w; cbn; intros; auto.
Qed.

Lemma wmsb_combine:
  forall sz1 sz2 (w1: word sz1) (w2: word sz2) b1 b2,
    sz2 <> 0 ->
    wmsb (combine w1 w2) b1 = wmsb w2 b2.
Proof.
  dependent induction w1; cbn; intros.
  - auto using wmsb_default.
  - auto using IHw1.
Qed.

Lemma wmsb_combine_existT: (* Note: not axiom free *)
  forall sz (w: word sz) sz1 (w1: word sz1) sz2 (w2: word sz2) b1 b2,
    sz2 <> 0 ->
    existT word _ w = existT word _ (combine w1 w2) ->
    wmsb w b1 = wmsb w2 b2.
Proof.
  intros.
  pose proof (eq_sigT_fst H0); subst.
  destruct_existT.
  auto using wmsb_combine.
Qed.

Lemma wmsb_zext:
  forall sz (w: word sz) b n, n <> 0 -> wmsb (zext w n) b = false.
Proof.
  destruct n; cbn; intros; [elim H; reflexivity|].
  unfold zext.
  erewrite wmsb_combine with (b2:= false) by discriminate.
  apply wmsb_wzero.
Qed.

Lemma wordToN_zext:
  forall sz (w: word sz) n,
    wordToN (zext w n) = wordToN w.
Proof.
  dependent induction w; cbn; intros.
  - induction n; cbn; intros; [reflexivity|].
    unfold wzero in IHn; rewrite IHn; reflexivity.
  - rewrite IHw; reflexivity.
Qed.

Lemma wordToNat_zext:
  forall sz (w: word sz) n,
    wordToNat (zext w n) = wordToNat w.
Proof.
  dependent induction w; cbn; intros.
  - induction n; cbn; intros; [reflexivity|].
    unfold wzero in IHn; rewrite IHn; reflexivity.
  - rewrite IHw; reflexivity.
Qed.

Lemma zext_wordToNat_equal_Z:
  forall sz (w: word sz) n,
    n <> 0 -> wordToZ (zext w n) = Z.of_nat (wordToNat w).
Proof.
  unfold wordToZ, zext; intros.
  rewrite wmsb_combine with (b2:= false) by assumption.
  rewrite wmsb_wzero.
  replace (combine w (wzero n)) with (zext w n) by reflexivity.
  rewrite wordToN_zext.
  rewrite wordToN_nat.
  rewrite <-nat_N_Z.
  unfold Z.of_N; reflexivity.
Qed.

Lemma wordToN_WS_0:
  forall sz (w: word sz), wordToN w~0 = (2 * wordToN w)%N.
Proof. reflexivity. Qed.

Lemma wordToN_WS_1:
  forall sz (w: word sz), wordToN w~1 = (2 * wordToN w + 1)%N.
Proof.
  intros; cbn.
  unfold N.succ_double.
  destruct (wordToN w); reflexivity.
Qed.

Lemma NToWord_WS_0:
  forall sz n, NToWord (S sz) (2 * n) = (NToWord sz n)~0.
Proof.
  destruct n; intros; [reflexivity|].
  replace (2 * N.pos p)%N with (N.pos (p~0)) by reflexivity.
  reflexivity.
Qed.

Lemma NToWord_WS_1:
  forall sz n, NToWord (S sz) (2 * n + 1) = (NToWord sz n)~1.
Proof.
  destruct n; intros; [reflexivity|].
  replace (2 * N.pos p)%N with (N.pos (p~0)) by reflexivity.
  reflexivity.
Qed.

Lemma wneg_WS_0:
  forall sz (w: word sz), wneg w~0 = (wneg w)~0.
Proof.
  unfold wneg; intros.
  rewrite wordToN_WS_0.
  replace (Npow2 (S sz)) with (2 * Npow2 sz)%N by reflexivity.
  rewrite <-N.mul_sub_distr_l.
  apply NToWord_WS_0.
Qed.

Lemma NToWord_wordToN:
  forall sz (w: word sz), NToWord sz (wordToN w) = w.
Proof.
  intros.
  rewrite wordToN_nat, NToWord_nat.
  rewrite Nat2N.id.
  apply natToWord_wordToNat.
Qed.

Lemma roundTripN_0:
  forall sz, wordToN (NToWord sz 0) = 0%N.
Proof.
  intros.
  rewrite wordToN_nat, NToWord_nat.
  rewrite roundTrip_0; reflexivity.
Qed.

Lemma wordToN_NToWord:
  forall sz n,
  exists k, wordToN (NToWord sz n) = (n - k * Npow2 sz)%N /\ (k * Npow2 sz <= n)%N.
Proof.
  intros.
  rewrite wordToN_nat, NToWord_nat.
  pose proof (wordToNat_natToWord sz (N.to_nat n)).
  destruct H as [k [? ?]].
  exists (N.of_nat k).
  split.
  - apply N2Nat.inj.
    rewrite Nat2N.id, N2Nat.inj_sub, N2Nat.inj_mul.
    rewrite Nat2N.id.
    rewrite Npow2_nat.
    assumption.
  - rewrite nat_compare_le, Nat2N.inj_compare in H0.
    rewrite Nat2N.inj_mul, <-Npow2_nat in H0.
    do 2 rewrite N2Nat.id in H0.
    assumption.
Qed.

Lemma wordToN_NToWord_2:
  forall sz n, (n < Npow2 sz)%N -> wordToN (NToWord sz n) = n.
Proof.
  intros.
  rewrite wordToN_nat, NToWord_nat.
  rewrite wordToNat_natToWord_2.
  - apply N2Nat.id.
  - rewrite <-Npow2_nat.
    apply Nlt_out; auto.
Qed.

Lemma wordToN_bound:
  forall sz (w: word sz), (wordToN w < Npow2 sz)%N.
Proof.
  intros.
  rewrite wordToN_nat.
  apply Nlt_in.
  rewrite Npow2_nat, Nat2N.id.
  apply wordToNat_bound.
Qed.

Lemma wordToN_plus: forall sz (a b: word sz),
    (wordToN a + wordToN b < Npow2 sz)%N ->
    wordToN (a ^+ b) = (wordToN a + wordToN b)%N.
Proof.
  intros. unfold wplus, wordBin.
  rewrite wordToN_NToWord_2 by assumption.
  reflexivity.
Qed.

Lemma wordToN_mult: forall sz (a b: word sz),
    (wordToN a * wordToN b < Npow2 sz)%N ->
    wordToN (a ^* b) = (wordToN a * wordToN b)%N.
Proof.
  intros. unfold wmult, wordBin.
  rewrite wordToN_NToWord_2 by assumption.
  reflexivity.
Qed.

Lemma wnot_def:
  forall sz (w: word sz), wnot w = NToWord sz (Npow2 sz - wordToN w - 1).
Proof.
  dependent induction w; cbn; [reflexivity|].
  destruct b; cbn.
  - rewrite IHw; clear IHw.
    rewrite <-NToWord_WS_0.
    f_equal.
    destruct (Npow2 n); [reflexivity|].
    destruct (wordToN w).
    + change (N.pos p~0) with (2 * N.pos p)%N.
      do 2 rewrite N.mul_sub_distr_l.
      do 2 rewrite <-N.sub_add_distr.
      reflexivity.
    + change (N.pos p~0) with (2 * N.pos p)%N.
      change (N.pos p0~0) with (2 * N.pos p0)%N.
      rewrite <-N.add_1_l.
      do 2 rewrite N.mul_sub_distr_l.
      do 2 rewrite <-N.sub_add_distr.
      rewrite N.add_comm with (n:= 1%N).
      rewrite <-N.add_assoc.
      reflexivity.
  - rewrite IHw; clear IHw.
    rewrite <-NToWord_WS_1.
    f_equal.
    pose proof (wordToN_bound w).
    remember (Npow2 n) as pn; destruct pn;
      [exfalso; eapply Npow2_not_zero; eauto|clear Heqpn].
    destruct (wordToN w).
    + change (N.pos p~0) with (2 * N.pos p)%N.
      do 2 rewrite N.mul_sub_distr_l.
      do 2 rewrite <-N.sub_add_distr.
      destruct p; cbn; reflexivity.
    + change (N.pos p~0) with (2 * N.pos p)%N.
      change (N.pos p0~0) with (2 * N.pos p0)%N.
      rewrite N.mul_sub_distr_l.
      rewrite <-N.mul_sub_distr_l with (n:= N.pos p).
      assert (exists pp, N.pos p - N.pos p0 = N.pos pp)%N.
      { apply N.sub_gt in H.
        destruct (N.pos p - N.pos p0)%N; [intuition idtac|].
        eexists; reflexivity.
      }
      destruct H0; rewrite H0.
      destruct x; cbn; reflexivity.
Qed.

Lemma wneg_wnot:
  forall sz (w: word sz), wnot w = wneg w ^- (natToWord _ 1).
Proof.
  unfold wneg; intros.
  rewrite wnot_def.

  destruct (weq w (wzero _)); subst.

  - rewrite wordToN_nat.
    unfold wzero; rewrite roundTrip_0; cbn.
    rewrite N.sub_0_r.
    do 2 rewrite NToWord_nat.
    rewrite Npow2_nat, natToWord_pow2, N2Nat.inj_sub.
    change (N.to_nat 1%N) with 1.
    rewrite Npow2_nat.
    apply wordToNat_inj.
    rewrite wordToNat_natToWord_2 by (pose proof (zero_lt_pow2 sz); omega).
    unfold wminus.
    rewrite wplus_unit, <-wones_wneg_one.
    apply eq_sym, wones_pow2_minus_one.

  - pose proof (wordToN_bound w).
    assert (Npow2 sz - wordToN w < Npow2 sz)%N.
    { apply N.sub_lt.
      { apply N.lt_le_incl; auto. }
      { assert (wordToN w <> 0)%N.
        { replace 0%N with (wordToN (wzero sz)).
          { intro Hx; elim n.
            apply wordToN_inj; auto.
          }
          { rewrite wordToN_nat.
            unfold wzero; rewrite roundTrip_0; reflexivity.
          }
        }
        nomega.
      }
    }
    apply N.sub_gt in H.
    remember (Npow2 sz - wordToN w)%N as p; clear Heqp.
    do 2 rewrite NToWord_nat.
    rewrite N2Nat.inj_sub.
    change (N.to_nat 1%N) with 1.
    assert (N.to_nat p < pow2 sz)%nat
      by (rewrite <-Npow2_nat; apply Nlt_out; auto); clear H0.
    assert (N.to_nat p <> 0)
      by (change 0 with (N.to_nat 0%N); intro Hx; elim H; apply N2Nat.inj; auto); clear H.
    apply wordToNat_inj.
    rewrite <-wordToNat_natToWord_pred.
    + do 2 rewrite wordToNat_natToWord_2 by omega.
      omega.
    + intro Hx; elim H0.
      apply natToWord_inj with (sz:= sz); try omega.
      assumption.
Qed.

Lemma wzero_wneg:
  forall n, wneg (wzero n) = wzero n.
Proof.
  intros.
  pose proof (wminus_inv (wzero n)).
  rewrite wplus_unit in H; auto.
Qed.

Lemma pow2_wneg:
  forall sz, wneg (natToWord (S sz) (pow2 sz)) = natToWord (S sz) (pow2 sz).
Proof.
  unfold wneg; intros.
  rewrite <-Npow2_nat, <-NToWord_nat.
  rewrite wordToN_NToWord_2
    by (apply Nlt_in; do 2 rewrite Npow2_nat;
        pose proof (zero_lt_pow2 sz); simpl; omega).
  rewrite Npow2_S.
  f_equal; nomega.
Qed.

Lemma wneg_WS_1:
  forall sz (w: word sz), wneg w~1 = (wnot w)~1.
Proof.
  intros.
  apply wordToN_inj.
  simpl; rewrite wnot_def.
  unfold wneg.
  rewrite wordToN_NToWord_2
    by (apply N.sub_lt; [apply N.lt_le_incl, wordToN_bound|nomega]).
  rewrite wordToN_NToWord_2.
  - rewrite wordToN_WS_1.
    change (Npow2 (S sz)) with (2 * Npow2 sz)%N.
    rewrite N.sub_add_distr.
    rewrite <-N.mul_sub_distr_l.
    assert (Npow2 sz - wordToN w <> 0)%N
      by (pose proof (wordToN_bound w); nomega).
    remember (Npow2 sz - wordToN w)%N as n; clear Heqn.
    destruct n; [intuition idtac|].
    remember (N.pos p - 1)%N as pp; destruct pp.
    + apply eq_sym, N.sub_0_le in Heqpp.
      apply N.le_1_r in Heqpp; destruct Heqpp; [discriminate|].
      rewrite H0; reflexivity.
    + change (N.pos p0~0) with (2 * N.pos p0)%N.
      rewrite Heqpp.
      rewrite <-N.add_1_r.
      rewrite N.mul_sub_distr_l.
      clear; destruct p; cbn; reflexivity.
  - rewrite <-N.sub_add_distr.
    apply N.sub_lt; [|nomega].
    pose proof (wordToN_bound w).
    apply N.le_succ_l in H.
    rewrite N.add_1_r; assumption.
Qed.

Lemma wordToZ_WS_0:
  forall sz (w: word sz), wordToZ w~0 = (2 * wordToZ w)%Z.
Proof.
  dependent destruction w; [reflexivity|].
  unfold wordToZ.
  rewrite wmsb_ws.
  destruct (wmsb (WS b w) false).
  - rewrite wneg_WS_0.
    rewrite wordToN_WS_0.
    destruct (wordToN (wneg (WS b w))); cbn; omega.
  - rewrite wordToN_WS_0.
    destruct (wordToN (WS b w)); cbn; omega.
Qed.

Lemma wordToZ_WS_1:
  forall sz (w: word (S sz)), wordToZ w~1 = (2 * wordToZ w + 1)%Z.
Proof.
  intros. destruct (destruct_word_S w) as [v [b E]]. rewrite E. clear w E. rename v into w.
  unfold wordToZ.
  rewrite wmsb_ws.
  remember (wmsb (WS b w) false) as msb.
  destruct msb.
  - rewrite wneg_WS_1.
    rewrite wordToN_WS_1.
    rewrite wnot_def.
    unfold wneg.

    assert (Npow2 (S sz) - wordToN (WS b w) <> 0)%N.
    { pose proof (wordToN_bound (WS b w)); nomega. }
    assert (Npow2 (S sz) - wordToN (WS b w) < Npow2 (S sz))%N.
    { apply N.sub_lt.
      { apply N.lt_le_incl, wordToN_bound. }
      { assert (wordToN (WS b w) <> 0)%N.
        { replace 0%N with (wordToN (wzero (S sz))).
          { intro Hx.
            apply wordToN_inj in Hx.
            rewrite Hx in Heqmsb.
            rewrite wmsb_wzero in Heqmsb; discriminate.
          }
          { rewrite wordToN_nat.
            unfold wzero; rewrite roundTrip_0; reflexivity.
          }
        }
        nomega.
      }
    }
    remember (Npow2 (S sz) - wordToN (WS b w))%N as n; clear Heqn.

    rewrite wordToN_NToWord_2 by nomega.
    rewrite wordToN_NToWord_2 by nomega.
    destruct n; [intuition idtac|].
    destruct p; cbn; reflexivity.

  - rewrite wordToN_WS_1.
    destruct (wordToN (WS b w)); cbn; omega.
Qed.

Lemma wordToZ_WS_1':
  forall sz (w: word (sz + 1)), wordToZ w~1 = (2 * wordToZ w + 1)%Z.
Proof.
  intro sz.
  replace (sz + 1) with (S sz) by omega.
  intros.
  apply wordToZ_WS_1.
Qed.

Lemma wordToZ_inj:
  forall sz (w1 w2: word sz),
    wordToZ w1 = wordToZ w2 -> w1 = w2.
Proof.
  unfold wordToZ; intros.
  remember (wmsb w1 false) as msb1.
  remember (wmsb w2 false) as msb2.
  destruct msb1, msb2.
  - remember (wordToN (wneg w1)) as wn1.
    remember (wordToN (wneg w2)) as wn2.
    destruct wn1, wn2; try discriminate.
    + assert (wneg w1 = wneg w2).
      { apply wordToN_inj.
        rewrite <-Heqwn1, <-Heqwn2; reflexivity.
      }
      rewrite <-wneg_idempotent with (w:= w1).
      rewrite <-wneg_idempotent with (w:= w2).
      rewrite H0; reflexivity.
    + inversion H; subst; clear H.
      assert (wneg w1 = wneg w2).
      { apply wordToN_inj.
        rewrite <-Heqwn1, <-Heqwn2; reflexivity.
      }
      rewrite <-wneg_idempotent with (w:= w1).
      rewrite <-wneg_idempotent with (w:= w2).
      rewrite H; reflexivity.
  - remember (wordToN (wneg w1)) as wn1.
    remember (wordToN w2) as wn2.
    destruct wn1, wn2; try discriminate.
    rewrite <-wordToN_wzero with (sz:= sz) in Heqwn1, Heqwn2.
    apply wordToN_inj in Heqwn1.
    apply wordToN_inj in Heqwn2.
    assert (w1 = wzero sz).
    { rewrite <-wneg_idempotent with (w:= w1), <-Heqwn1.
      apply wzero_wneg.
    }
    subst; reflexivity.
  - remember (wordToN w1) as wn1.
    remember (wordToN (wneg w2)) as wn2.
    destruct wn1, wn2; try discriminate.
    rewrite <-wordToN_wzero with (sz:= sz) in Heqwn1, Heqwn2.
    apply wordToN_inj in Heqwn1.
    apply wordToN_inj in Heqwn2.
    assert (w2 = wzero sz).
    { rewrite <-wneg_idempotent with (w:= w2), <-Heqwn2.
      apply wzero_wneg.
    }
    subst; reflexivity.
  - remember (wordToN w1) as wn1.
    remember (wordToN w2) as wn2.
    destruct wn1, wn2; try discriminate.
    + rewrite <-wordToN_wzero with (sz:= sz) in Heqwn1, Heqwn2.
      rewrite Heqwn1 in Heqwn2.
      apply wordToN_inj in Heqwn2; auto.
    + inversion H; subst; clear H.
      rewrite Heqwn1 in Heqwn2.
      apply wordToN_inj in Heqwn2; auto.
Qed.

Lemma wordToZ_wones:
  forall sz, sz <> 0 -> wordToZ (wones sz) = (-1)%Z.
Proof.
  induction sz; intros; [elim H; reflexivity|].
  simpl; destruct sz; [reflexivity|].
  rewrite wordToZ_WS_1.
  rewrite IHsz by discriminate.
  reflexivity.
Qed.

Lemma wordToNat_eq_rect:
  forall sz (w: word sz) nsz Hsz,
    wordToNat (eq_rect _ word w nsz Hsz) = wordToNat w.
Proof.
  intros; subst; simpl; reflexivity.
Qed.

Lemma wordToNat_existT:
  forall sz1 (w1: word sz1) sz2 (w2: word sz2) (Hsz: sz1 = sz2),
    wordToNat w1 = wordToNat w2 ->
    existT word _ w1 = existT word _ w2.
Proof.
  intros; subst.
  apply wordToNat_inj in H; subst.
  reflexivity.
Qed.

Lemma existT_wordToNat: (* Note: not axiom free *)
  forall sz1 (w1: word sz1) sz2 (w2: word sz2),
    existT word _ w1 = existT word _ w2 ->
    wordToNat w1 = wordToNat w2.
Proof.
  intros.
  pose proof (eq_sigT_fst H); subst.
  destruct_existT; reflexivity.
Qed.

Lemma wordToZ_eq_rect:
  forall sz (w: word sz) nsz Hsz,
    wordToZ (eq_rect _ word w nsz Hsz) = wordToZ w.
Proof.
  intros; subst; simpl; reflexivity.
Qed.

Lemma wordToZ_existT:
  forall sz1 (w1: word sz1) sz2 (w2: word sz2) (Hsz: sz1 = sz2),
    wordToZ w1 = wordToZ w2 ->
    existT word _ w1 = existT word _ w2.
Proof.
  intros; subst.
  apply wordToZ_inj in H; subst.
  reflexivity.
Qed.

Lemma existT_wordToZ: (* Note: not axiom free *)
  forall sz1 (w1: word sz1) sz2 (w2: word sz2),
    existT word _ w1 = existT word _ w2 ->
    wordToZ w1 = wordToZ w2.
Proof.
  intros.
  pose proof (eq_sigT_fst H); subst.
  destruct_existT.
  reflexivity.
Qed.

Lemma wplus_WS_0:
  forall sz (w1 w2: word sz) b, WS b (w1 ^+ w2) = WS b w1 ^+ w2~0.
Proof.
  intros.
  unfold wplus, wordBin; intros.
  rewrite wordToN_WS_0.
  destruct b.
  - rewrite wordToN_WS_1.
    rewrite <-N.add_assoc.
    rewrite N.add_comm with (n:= 1%N).
    rewrite N.add_assoc.
    rewrite <-N.mul_add_distr_l.
    apply eq_sym, NToWord_WS_1.
  - rewrite wordToN_WS_0.
    rewrite <-N.mul_add_distr_l.
    apply eq_sym, NToWord_WS_0.
Qed.

Corollary wplus_WS_0':
  forall sz (w1 w2: word sz) b, WS b (w1 ^+ w2) = w1~0 ^+ WS b w2.
Proof.
  intros.
  rewrite wplus_comm with (x:= w1).
  rewrite wplus_comm with (x:= w1~0).
  apply wplus_WS_0.
Qed.

Lemma wpow2_pow2:
  forall sz, wordToNat (wpow2 sz) = pow2 sz.
Proof.
  induction sz; simpl; intros; [reflexivity|].
  rewrite IHsz.
  omega.
Qed.

Lemma wpow2_Npow2:
  forall sz, wordToN (wpow2 sz) = Npow2 sz.
Proof.
  induction sz; simpl; intros; [reflexivity|].
  rewrite IHsz; reflexivity.
Qed.

Lemma wpow2_wneg:
  forall sz, wneg (wpow2 sz) = wpow2 sz.
Proof.
  induction sz; simpl; intros; [reflexivity|].
  rewrite wneg_WS_0.
  rewrite IHsz; reflexivity.
Qed.

Lemma wpow2_wmsb:
  forall sz, wmsb (wpow2 sz) false = true.
Proof.
  induction sz; simpl; intros; auto.
Qed.

Lemma wmsb_wnot:
  forall sz (w: word (S sz)) b1 b2,
    wmsb (wnot w) b1 = negb (wmsb w b2).
Proof.
  apply (induct_word_S (fun sz w => forall b1 b2, wmsb (wnot w) b1 = negb (wmsb w b2))); intros.
  - reflexivity.
  - simpl. apply (H true true).
Qed.

Lemma wmsb_wneg_true:
  forall sz (w: word (S sz)),
    w <> wpow2 sz ->
    forall b1 b2,
      wmsb w b1 = true ->
      wmsb (wneg w) b2 = false.
Proof.
  apply (induct_word_S (fun sz w => w <> wpow2 sz -> forall b1 b2, wmsb w b1 = true ->
                                                     wmsb (^~ w) b2 = false)); intros;
    [simpl in *; subst; elim H; reflexivity|].
  destruct b.
  - rewrite wneg_WS_1.
    rewrite wmsb_ws.
    rewrite wmsb_wnot with (b2:= false).
    simpl; apply negb_false_iff; assumption.
  - rewrite wneg_WS_0.
    eapply H with (b1 := false); eauto.
    intro Hx. elim H0.
    clear -Hx.
    simpl; rewrite Hx; reflexivity.
Qed.

Lemma wmsb_wneg_false:
  forall sz (w: word (S sz)),
    wordToNat w <> 0 ->
    forall b1 b2,
      wmsb w b1 = false ->
      wmsb (wneg w) b2 = true.
Proof.
  apply (induct_word_S (fun sz w => #w <> 0 -> forall b1 b2, wmsb w b1 = false ->
                                                             wmsb (^~ w) b2 = true)); intros;
    [simpl in *; subst; elim H; reflexivity|].
  destruct b.
  - rewrite wneg_WS_1.
    rewrite wmsb_ws.
    rewrite wmsb_ws in H1.
    rewrite wmsb_wnot with (b2:= false).
    apply negb_true_iff; assumption.
  - rewrite wneg_WS_0.
    eapply H with (b1:= false); eauto.
    intro Hx; elim H0.
    clear -Hx.
    simpl in *; omega.
Qed.

Lemma zext_WO_wzero:
  forall n, zext WO n = wzero n.
Proof.
  reflexivity.
Qed.

Lemma wmsb_wneg_zext: (* Note: not axiom free *)
  forall sz (w: word sz) b n,
    n <> 0 -> wordToNat w <> 0 ->
    wmsb (wneg (zext w n)) b = true.
Proof.
  intros.
  dependent destruction w; [elim H0; reflexivity|].
  apply wmsb_wneg_false with (b1:= false).
  - rewrite <-wordToNat_zext with (n:= n0) in H0.
    assumption.
  - apply wmsb_zext; assumption.
Qed.

Lemma wminus_WS_pos:
  forall sz (w1 w2: word (S sz)),
    wordToZ (WS true w1 ^- WS false w2) =
    (2 * wordToZ (w1 ^- w2) + 1)%Z.
Proof.
  unfold wminus; intros.
  cbn.
  rewrite wneg_WS_0.
  rewrite <-wplus_WS_0.
  rewrite wordToZ_WS_1.
  reflexivity.
Qed.

Lemma wminus_WS_pos':
  forall sz (w1 w2: word (sz + 1)),
    wordToZ (WS true w1 ^- WS false w2) =
    (2 * wordToZ (w1 ^- w2) + 1)%Z.
Proof.
  intro sz.
  replace (sz + 1) with (S sz) by omega.
  intros.
  apply wminus_WS_pos.
Qed.

Lemma wtl_combine:
  forall (x: word 1) sz (y: word sz),
    wtl (combine x y) = y.
Proof.
  intros.
  destruct (destruct_word_S x) as [v [b E]]. subst x.
  rewrite (word0 v).
  reflexivity.
Qed.

Lemma extz_combine:
  forall sz (w: word sz) n, extz w n = combine (natToWord n 0) w.
Proof.
  reflexivity.
Qed.

Lemma combine_assoc_existT:
  forall sz1 (w1: word sz1) sz2 (w2: word sz2) sz3 (w3: word sz3),
    existT word (sz1 + (sz2 + sz3)) (combine w1 (combine w2 w3)) =
    existT word (sz1 + sz2 + sz3) (combine (combine w1 w2) w3).
Proof.
  intros; apply EqdepFacts.eq_sigT_sig_eq.
  assert (Hsz: sz1 + (sz2 + sz3) = sz1 + sz2 + sz3) by omega.
  exists Hsz.
  rewrite (combine_assoc w1 w2 w3 Hsz).
  reflexivity.
Qed.

Lemma sext_combine: (* Note: not axiom free *)
  forall sz n (w: word (sz + n)) sz1 (w1: word sz1)
         sz2 (Hsz2: sz2 <> 0) (w2: word sz2),
    existT word _ w = existT word _ (combine w1 (sext w2 n)) ->
    exists sw, w = sext sw n /\ existT word _ sw = existT word _ (combine w1 w2).
Proof.
  intros; unfold sext in H.
  remember (wmsb w2 false) as msb2; destruct msb2.
  - rewrite combine_assoc_existT in H.
    assert (sz = sz1 + sz2) by (apply eq_sigT_fst in H; omega); subst.
    destruct_existT.
    exists (combine w1 w2).
    split; [|reflexivity].
    unfold sext.
    dependent destruction w2; [discriminate|].
    rewrite wmsb_combine with (b2:= false) by discriminate.
    rewrite <-Heqmsb2.
    reflexivity.
  - rewrite combine_assoc_existT in H.
    assert (sz = sz1 + sz2) by (apply eq_sigT_fst in H; omega); subst.
    destruct_existT.
    exists (combine w1 w2).
    split; [|reflexivity].
    unfold sext.
    dependent destruction w2; [intuition idtac|].
    rewrite wmsb_combine with (b2:= false) by discriminate.
    rewrite <-Heqmsb2.
    reflexivity.
Qed.

Lemma wplus_wzero_1:
  forall sz (w: word sz), w ^+ (wzero _) = w.
Proof.
  unfold wplus, wordBin; intros.
  rewrite wordToN_wzero.
  rewrite N.add_0_r.
  apply NToWord_wordToN.
Qed.

Lemma wplus_wzero_2:
  forall sz (w: word sz), (wzero _) ^+ w = w.
Proof.
  unfold wplus, wordBin; intros.
  rewrite wordToN_wzero.
  rewrite N.add_0_l.
  apply NToWord_wordToN.
Qed.

Lemma combine_wplus_1:
  forall sl (w1: word sl) su (w2 w3: word su),
    combine w1 (w2 ^+ w3) = combine w1 w2 ^+ extz w3 sl.
Proof.
  dependent induction w1; intros; [reflexivity|].
  cbn; rewrite IHw1.
  rewrite <-wplus_WS_0.
  rewrite extz_combine; reflexivity.
Qed.

Lemma combine_wplus_2:
  forall sl (w1: word sl) su (w2 w3: word su),
    combine w1 (w2 ^+ w3) = extz w2 sl ^+ combine w1 w3.
Proof.
  intros.
  rewrite wplus_comm.
  rewrite combine_wplus_1.
  apply wplus_comm.
Qed.

Lemma existT_wplus:
  forall sz (w1 w2: word sz) sz' (w3 w4: word sz'),
    existT word _ w1 = existT word _ w3 ->
    existT word _ w2 = existT word _ w4 ->
    existT word _ (w1 ^+ w2) = existT word _ (w3 ^+ w4).
Proof.
  intros.
  rewrite eq_sigT_sig_eq in H; destruct H as [Hsz1 ?].
  rewrite eq_sigT_sig_eq in H0; destruct H0 as [Hsz2 ?].
  subst; do 2 rewrite <-(eq_rect_eq_dec eq_nat_dec).
  reflexivity.
Qed.

Lemma existT_wminus:
  forall sz (w1 w2: word sz) sz' (w3 w4: word sz'),
    existT word _ w1 = existT word _ w3 ->
    existT word _ w2 = existT word _ w4 ->
    existT word _ (w1 ^- w2) = existT word _ (w3 ^- w4).
Proof.
  intros.
  rewrite eq_sigT_sig_eq in H; destruct H as [Hsz1 ?].
  rewrite eq_sigT_sig_eq in H0; destruct H0 as [Hsz2 ?].
  subst; do 2 rewrite <-(eq_rect_eq_dec eq_nat_dec).
  reflexivity.
Qed.


Lemma existT_sext:
  forall sz1 (w1: word sz1) sz2 (w2: word sz2) n,
    existT word _ w1 = existT word _ w2 ->
    existT word _ (sext w1 n) = existT word _ (sext w2 n).
Proof.
  intros; inversion H; reflexivity.
Qed.

Lemma existT_extz:
  forall sz1 (w1: word sz1) sz2 (w2: word sz2) n,
    existT word _ w1 = existT word _ w2 ->
    existT word _ (extz w1 n) = existT word _ (extz w2 n).
Proof.
  intros; inversion H; reflexivity.
Qed.

Lemma existT_wrshifta:
  forall sz1 (w1: word sz1) sz2 (w2: word sz2) n,
    existT word _ w1 = existT word _ w2 ->
    existT word _ (wrshifta w1 n) = existT word _ (wrshifta w2 n).
Proof.
  intros; inversion H; reflexivity.
Qed.

Lemma existT_wlshift:
  forall sz1 (w1: word sz1) sz2 (w2: word sz2) n,
    existT word _ w1 = existT word _ w2 ->
    existT word _ (wlshift w1 n) = existT word _ (wlshift w2 n).
Proof.
  intros; inversion H; reflexivity.
Qed.

Lemma eq_rect_wplus:
  forall sz (w1 w2: word sz) sz' Hsz,
    eq_rect sz word (w1 ^+ w2) sz' Hsz =
    (eq_rect sz word w1 sz' Hsz) ^+ (eq_rect sz word w2 sz' Hsz).
Proof.
  intros; subst.
  eq_rect_simpl; reflexivity.
Qed.

Lemma eq_rect_2:
  forall sz (pa: word sz) sz' Heq1 Heq2,
    eq_rect sz' word (eq_rect sz word pa sz' Heq1) sz Heq2 = pa.
Proof.
  intros; subst.
  do 2 rewrite <-(eq_rect_eq_dec eq_nat_dec).
  reflexivity.
Qed.

Lemma wzero_eq_rect:
  forall sz1 sz2 Heq,
    eq_rect sz1 word (wzero sz1) sz2 Heq = wzero sz2.
Proof.
  intros; subst.
  apply eq_sym, (eq_rect_eq_dec eq_nat_dec).
Qed.

Lemma wrshifta_0:
  forall sz (w: word sz), wrshifta w 0 = w.
Proof.
  unfold wrshifta; intros; simpl.
  unfold eq_rec_r, eq_rec.
  unfold sext.
  destruct (wmsb w false).
  - cbn; rewrite combine_n_0.
    rewrite eq_rect_2; reflexivity.
  - cbn; rewrite combine_n_0.
    rewrite eq_rect_2; reflexivity.
Qed.

Lemma wrshifta_WO:
  forall n, wrshifta WO n = WO.
Proof.
  unfold wrshifta; cbn; intros.
  unfold eq_rec_r, eq_rec.
  rewrite wzero_eq_rect.
  rewrite <-combine_wzero.
  rewrite split2_combine.
  reflexivity.
Qed.

Lemma split2_WO:
  forall n w, split2 n 0 w = WO.
Proof.
  induction n; cbn; intros; auto.
Qed.

Lemma sext_wzero:
  forall sz n, sext (wzero sz) n = wzero (sz + n).
Proof.
  unfold sext; intros.
  rewrite wmsb_wzero.
  apply combine_wzero.
Qed.

Lemma wrshifta_wzero:
  forall sz n, wrshifta (wzero sz) n = wzero _.
Proof.
  intros.
  unfold wrshifta; cbn.
  rewrite sext_wzero.
  unfold eq_rec_r, eq_rec.
  rewrite wzero_eq_rect.
  rewrite <-combine_wzero.
  rewrite split2_combine.
  reflexivity.
Qed.

Lemma extz_sext:
  forall sz (w: word sz) n1 n2,
    existT word _ (extz (sext w n1) n2) =
    existT word _ (sext (extz w n2) n1).
Proof.
  dependent destruction w; cbn; intros.
  - unfold wzero, extz, sext.
    rewrite combine_wzero.
    rewrite combine_wzero.
    rewrite wmsb_wzero.
    rewrite combine_wzero.
    replace (n2 + 0 + n1) with (n2 + n1) by omega.
    reflexivity.
  - unfold wzero, extz, sext.
    rewrite wmsb_combine with (b2:= false) by discriminate.
    destruct (wmsb (WS b w) false);
      try (rewrite <-combine_assoc_existT; reflexivity).
Qed.

Lemma sext_WS:
  forall sz (w: word (S sz)) b n,
    sext (WS b w) n = WS b (sext w n).
Proof.
  unfold sext; intros.
  rewrite wmsb_ws.
  destruct (wmsb w false); reflexivity.
Qed.

Lemma sext_wordToZ:
  forall sz n (w: word sz),
    wordToZ (sext w n) = wordToZ w.
Proof.
  dependent induction w; cbn; intros; [apply wordToZ_wzero|].
  dependent destruction w.
  - unfold sext; simpl.
    destruct b; cbn.
    + rewrite wordToZ_wones by discriminate.
      reflexivity.
    + rewrite wordToZ_wzero; reflexivity.
  - remember (WS b0 w) as ww; clear Heqww.
    rewrite sext_WS.
    destruct b.
    + change (S n0 + n) with (S (n0 + n)) in *.
      repeat rewrite wordToZ_WS_1.
      rewrite IHw.
      reflexivity.
    + change (S n0 + n) with (S (n0 + n)) in *.
      repeat rewrite wordToZ_WS_0.
      rewrite IHw.
      reflexivity.
Qed.

Lemma sext_natToWord': forall sz1 sz2 n,
  (2 * n < pow2 sz1)%nat ->
  sext (natToWord sz1 n) sz2 = natToWord (sz1 + sz2) n.
Proof.
  induction sz1; intros.
  - simpl. unfold sext. simpl. unfold wzero. unfold pow2 in *.
    assert (n=0) by omega. subst n. reflexivity.
  - unfold sext in *.
    assert (@wmsb (S sz1) (natToWord (S sz1) n) false = false) as E by
      (apply wmsb_0_natToWord; assumption).
    rewrite E. clear E.
    simpl. unfold natToWord. f_equal. fold natToWord.
    specialize (IHsz1 sz2 (Nat.div2 n)).
    rewrite <- IHsz1.
    + assert (@wmsb sz1 (natToWord sz1 (Nat.div2 n)) false = false) as E. {
        destruct sz1.
        - reflexivity.
        - apply wmsb_0_natToWord. unfold pow2 in *. fold pow2 in *.
          assert ((2 * Nat.div2 n <= n)%nat) by apply two_times_div2_bound. omega.
      }
      rewrite E. clear E. reflexivity.
    + replace (pow2 (S sz1)) with (2 * (pow2 sz1)) in H.
      * assert ((2 * Nat.div2 n <= n)%nat) by apply two_times_div2_bound. omega.
      * reflexivity.
Qed.

Lemma sext_natToWord: forall sz2 sz1 sz n (e: sz1 + sz2 = sz),
  (2 * n < pow2 sz1)%nat ->
  eq_rect (sz1 + sz2) word (sext (natToWord sz1 n) sz2) sz e = natToWord sz n.
Proof.
  intros. rewrite sext_natToWord' by assumption. rewrite e. reflexivity.
Qed.

Lemma sext_wneg_natToWord'': forall sz1 sz2 n,
  pow2 sz1 <= 2 * n < pow2 (S sz1) ->
  sext (natToWord sz1 n) sz2 = natToWord (sz1 + sz2) (pow2 (sz1+sz2) - (pow2 sz1 - n)).
Proof.
  induction sz1; intros.
  - unfold pow2 in H. omega. (* contradiction *)
  - unfold sext in *.
    assert (@wmsb (S sz1) (natToWord (S sz1) n) false = true) as E. {
      apply wmsb_1.
      rewrite wordToNat_natToWord_idempotent';
      (unfold pow2 in *; fold pow2 in *; omega).
    }
    rewrite E.
    match goal with
    | |- _ = $ ?a => remember a as b
    end.
    simpl. unfold natToWord. f_equal.
    + subst b. rewrite mod2sub.
      * rewrite mod2sub.
        { replace (S sz1 + sz2) with (S (sz1 + sz2)) by omega.
          simpl.
          do 2 rewrite mod2_pow2_twice.
          do 2 rewrite Bool.xorb_false_l.
          reflexivity.
        }
        simpl in *. omega.
      * rewrite pow2_add_mul in *. unfold pow2 in *. fold pow2 in *.
        apply Nat.le_trans with (m := 2 * pow2 sz1); [omega|].
        rewrite <- mult_assoc.
        apply mult_le_compat_l.
        rewrite <- Nat.mul_1_r at 1.
        apply mult_le_compat_l.
        apply one_le_pow2.
    + fold natToWord.
      specialize (IHsz1 sz2 (Nat.div2 n)).
      assert (Nat.div2 b = pow2 (sz1 + sz2) - (pow2 sz1 - (Nat.div2 n))) as D2. {
        rewrite minus_minus.
        - subst b. replace (S sz1 + sz2) with (S (sz1 + sz2)) by omega.
          unfold pow2. fold pow2.
          rewrite minus_minus.
          * rewrite <- Nat.mul_sub_distr_l.
            rewrite <- (Nat.add_comm n).
            rewrite div2_plus_2.
            apply Nat.add_comm.
          * rewrite pow2_add_mul. clear IHsz1. unfold pow2 in *. fold pow2 in *.
            split; [omega|].
            apply mult_le_compat_l.
            rewrite <- Nat.mul_1_r at 1.
            apply mult_le_compat_l.
            apply one_le_pow2.
        - unfold pow2 in H. fold pow2 in H.
          split.
          * pose proof (@div2_compat_lt_l (pow2 sz1) n) as P. omega.
          * rewrite pow2_add_mul. clear IHsz1.
            rewrite <- Nat.mul_1_r at 1.
            apply mult_le_compat_l.
            apply one_le_pow2.
      }
      rewrite D2.
      destruct sz1 as [|sz1'].
      * simpl in H. assert (n=1) by omega. subst n. simpl in D2. simpl.
        apply wones_natToWord.
      * assert (n <= S (2 * Nat.div2 n))%nat. {
          destruct (even_odd_destruct n) as [[m C]|[m C]]; subst n.
          - rewrite Nat.div2_double. constructor. constructor.
          - replace (2 * m + 1) with (S (2 * m)) by omega. rewrite Nat.div2_succ_double.
            constructor.
        }
       rewrite <- IHsz1.
        { assert (@wmsb (S sz1') (natToWord (S sz1') (Nat.div2 n)) false = true) as F. {
          apply wmsb_1_natToWord.
          unfold pow2 in *. fold pow2 in *.
          assert (2 * Nat.div2 n <= n)%nat by apply two_times_div2_bound.
          clear -H H0 H1.
          omega. }
          { rewrite F. reflexivity. }
        }
        { assert (2 * Nat.div2 n <= n)%nat by apply two_times_div2_bound.
          clear -H H0 H1.
          unfold pow2 in *. fold pow2 in *.
          omega. }
Qed.

Lemma sext_wneg_natToWord': forall sz1 sz2 n,
  (2 * n < pow2 sz1)%nat ->
  sext (wneg (natToWord sz1 n)) sz2 = wneg (natToWord (sz1 + sz2) n).
Proof.
  intros. rewrite wneg_alt. unfold wnegN.
  destruct n as [|n].
  - rewrite roundTrip_0. rewrite Nat.sub_0_r. rewrite natToWord_pow2.
    unfold sext.
    assert (wmsb (natToWord sz1 0) false = false) as W. {
      destruct sz1.
      + simpl. reflexivity.
      + apply wmsb_0_natToWord. assumption.
    }
    rewrite W.
    rewrite combine_wzero.
    symmetry.
    apply wneg_zero'.
  - rewrite sext_wneg_natToWord''.
    + rewrite wneg_alt. unfold wnegN.
      rewrite wordToNat_natToWord_idempotent' by omega.
      rewrite wordToNat_natToWord_idempotent'.
      * replace (pow2 sz1 - (pow2 sz1 - S n)) with (S n) by omega.
        reflexivity.
      * rewrite pow2_add_mul.
        apply Nat.le_trans with (m := pow2 sz1); [omega|].
        rewrite <- Nat.mul_1_r at 1.
        apply mult_le_compat_l.
        apply one_le_pow2.
    + rewrite wordToNat_natToWord_idempotent' by omega.
      simpl. omega.
Qed.

Lemma sext_wneg_natToWord: forall sz2 sz1 sz n (e: sz1 + sz2 = sz),
  (2 * n < pow2 sz1)%nat ->
  eq_rect (sz1 + sz2) word (sext (wneg (natToWord sz1 n)) sz2) sz e = wneg (natToWord sz n).
Proof.
  intros. rewrite sext_wneg_natToWord' by assumption. rewrite e. reflexivity.
Qed.

Lemma wordToNat_split1:
  forall sz1 sz2 (w: word (sz1 + sz2)),
    wordToNat (split1 _ _ w) =
    Nat.modulo (wordToNat w) (pow2 sz1).
Proof.
  induction sz1; intros; [reflexivity|].
  destruct (destruct_word_S w) as [v [b E]].
  match type of v with
  | word ?x => change x with (sz1 + sz2) in *
  end.
  subst w. rename v into w.
  simpl; rewrite IHsz1.
  pose proof (zero_lt_pow2 sz1).
  destruct b.
  - change (pow2 sz1 + (pow2 sz1 + 0)) with (2 * pow2 sz1).
    replace (S (wordToNat w * 2)) with (1 + 2 * wordToNat w) by omega.
    rewrite Nat.add_mod by omega.
    rewrite Nat.mul_mod_distr_l; [|omega|discriminate].
    rewrite Nat.mod_1_l by omega.
    rewrite Nat.mul_comm with (n:= 2).
    change (1 + wordToNat w mod pow2 sz1 * 2) with (S (wordToNat w mod pow2 sz1 * 2)).
    apply eq_sym, Nat.mod_small.
    assert (pow2 sz1 <> 0) by omega.
    pose proof (Nat.mod_upper_bound (wordToNat w) (pow2 sz1) H0).
    omega.
  - change (pow2 sz1 + (pow2 sz1 + 0)) with (2 * pow2 sz1).
    rewrite Nat.mul_comm with (n:= 2).
    rewrite Nat.mul_mod_distr_r; [|omega|discriminate].
    reflexivity.
Qed.

Lemma wordToNat_split2:
  forall sz1 sz2 (w: word (sz1 + sz2)),
    wordToNat (split2 _ _ w) =
    Nat.div (wordToNat w) (pow2 sz1).
Proof.
  induction sz1; intros;
    [rewrite Nat.div_1_r; reflexivity|].
  destruct (destruct_word_S w) as [v [b E]].
  match type of v with
  | word ?x => change x with (sz1 + sz2) in *
  end.
  subst w. rename v into w.
  change (split2 (S sz1) sz2 (WS b w))
    with (split2 sz1 sz2 w).
  rewrite IHsz1.
  destruct b.
  - unfold pow2; fold pow2.
    replace (@wordToNat (S sz1 + sz2) w~1)
      with (1 + 2 * wordToNat w) by (simpl; omega).
    rewrite <-Nat.div_div;
      [|discriminate|pose proof (zero_lt_pow2 sz1); omega].
    rewrite Nat.mul_comm, Nat.div_add by discriminate.
    rewrite Nat.div_small with (b := 2) by omega.
    reflexivity.
  - unfold pow2; fold pow2.
    replace (@wordToNat (S sz1 + sz2) w~0)
      with (2 * wordToNat w) by (simpl; omega).
    rewrite Nat.div_mul_cancel_l;
      [|pose proof (zero_lt_pow2 sz1); omega|discriminate].
    reflexivity.
Qed.

Lemma wordToNat_wrshifta:
  forall sz (w: word sz) n,
    wordToNat (wrshifta w n) =
    Nat.div (wordToNat (sext w n)) (pow2 n).
Proof.
  unfold wrshifta; intros.
  rewrite wordToNat_split2.
  unfold eq_rec_r, eq_rec.
  rewrite wordToNat_eq_rect.
  reflexivity.
Qed.

Lemma wordToNat_combine:
  forall sz1 (w1: word sz1) sz2 (w2: word sz2),
    wordToNat (combine w1 w2) =
    wordToNat w1 + pow2 sz1 * wordToNat w2.
Proof.
  dependent induction w1; intros; [simpl; omega|].
  unfold pow2; fold pow2.
  rewrite Nat.mul_comm with (n:= 2). (* to avoid [simpl] *)
  simpl; destruct b.
  - rewrite IHw1; simpl.
    rewrite Nat.mul_comm with (n:= pow2 n * 2).
    rewrite Nat.mul_assoc.
    rewrite <-Nat.mul_add_distr_r.
    rewrite Nat.mul_comm with (n:= pow2 n).
    reflexivity.
  - rewrite IHw1.
    rewrite Nat.mul_comm with (n:= pow2 n * 2).
    rewrite Nat.mul_assoc.
    rewrite <-Nat.mul_add_distr_r.
    rewrite Nat.mul_comm with (n:= pow2 n).
    reflexivity.
Qed.

Lemma wordToNat_wlshift:
  forall sz (w: word sz) n,
    wordToNat (wlshift w n) =
    Nat.mul (Nat.modulo (wordToNat w) (pow2 (sz - n))) (pow2 n).
Proof.
  intros; destruct (le_dec n sz).

  - unfold wlshift; intros.
    rewrite wordToNat_split1.
    unfold eq_rec_r, eq_rec.
    rewrite wordToNat_eq_rect.
    rewrite wordToNat_combine.
    rewrite wordToNat_wzero; simpl.
    replace (pow2 sz) with (pow2 (sz - n + n)) by (f_equal; omega).
    rewrite pow2_add_mul.
    rewrite Nat.mul_comm with (n:= pow2 (sz - n)).
    rewrite Nat.mul_mod_distr_l;
      [|pose proof (zero_lt_pow2 (sz - n)); omega
       |pose proof (zero_lt_pow2 n); omega].
    apply Nat.mul_comm.

  - assert (n > sz)%nat by omega.
    rewrite wlshift_gt by assumption.
    replace (sz - n) with 0 by omega.
    rewrite wordToNat_wzero; simpl; reflexivity.
Qed.

Lemma wordToNat_extz:
  forall sz (w: word sz) n,
    wordToNat (extz w n) = pow2 n * wordToNat w.
Proof.
  unfold extz; intros.
  rewrite wordToNat_combine.
  rewrite wordToNat_wzero.
  reflexivity.
Qed.

Lemma extz_is_mult_pow2: forall sz n d,
  extz (natToWord sz n) d = natToWord (d + sz) (pow2 d * n).
Proof.
  intros. induction d.
  - unfold extz.
    rewrite combine_0_n.
    simpl.
    f_equal.
    omega.
  - unfold extz in *.
    change (pow2 (S d) * n) with (2 * pow2 d * n).
    rewrite <- Nat.mul_assoc.
    change ((S d) + sz) with (S (d + sz)) in *.
    rewrite <- natToWord_times2.
    simpl.
    fold natToWord.
    f_equal.
    exact IHd.
Qed.

Lemma extz_is_mult_pow2_neg: forall sz n d,
  extz (wneg (natToWord sz n)) d = wneg (natToWord (d + sz) (pow2 d * n)).
Proof.
  intros. induction d.
  - unfold extz.
    rewrite combine_0_n.
    simpl.
    f_equal. f_equal.
    omega.
  - unfold extz in *.
    change (pow2 (S d) * n) with (2 * pow2 d * n).
    rewrite <- Nat.mul_assoc.
    change ((S d) + sz) with (S (d + sz)) in *.
    rewrite <- natToWord_times2.
    simpl.
    fold natToWord.
    f_equal.
    rewrite wneg_WS_0.
    f_equal.
    exact IHd.
Qed.

Lemma wordToNat_sext_bypass:
  forall sz1 (w1: word sz1) sz2 (w2: word sz2) (Hsz: sz1 = sz2) n,
    wordToNat w1 = wordToNat w2 ->
    wordToNat (sext w1 n) = wordToNat (sext w2 n).
Proof.
  intros; subst.
  apply wordToNat_inj in H; subst.
  reflexivity.
Qed.

Lemma combine_sext:
  forall sz1 (w1: word sz1) sz2 (w2: word (S sz2)) n,
    existT word _ (combine w1 (sext w2 n)) =
    existT word _ (sext (combine w1 w2) n).
Proof.
  unfold sext; intros.
  rewrite wmsb_combine with (b2:= false) by discriminate.
  destruct (wmsb w2 false); apply combine_assoc_existT.
Qed.

Lemma extz_extz:
  forall sz (w: word sz) n1 n2,
    existT word _ (extz (extz w n1) n2) =
    existT word _ (extz w (n2 + n1)).
Proof.
  unfold extz; cbn; intros.
  rewrite combine_assoc_existT.
  rewrite combine_wzero.
  reflexivity.
Qed.

Lemma wrshifta_extz_sext: (* Note: not axiom free *)
  forall sz (w: word sz) n1 n2,
    existT word _ (wrshifta (extz w (n1 + n2)) n1) =
    existT word _ (sext (extz w n2) n1).
Proof.
  intros.
  rewrite <-extz_sext.
  apply wordToNat_existT; [omega|].
  rewrite wordToNat_wrshifta.

  replace (wordToNat (sext (extz w (n1 + n2)) n1))
    with (wordToNat (sext (extz (extz w n2) n1) n1)).
  - replace (wordToNat (sext (extz (extz w n2) n1) n1))
      with (wordToNat (extz (sext (extz w n2) n1) n1))
      by apply existT_wordToNat, extz_sext.
    do 2 rewrite wordToNat_extz.
    rewrite Nat.mul_comm, Nat.div_mul
      by (pose proof (zero_lt_pow2 n1); omega).
    replace (wordToNat (sext (extz w n2) n1))
      with (wordToNat (extz (sext w n1) n2))
      by apply existT_wordToNat, extz_sext.
    rewrite wordToNat_extz.
    reflexivity.
  - apply wordToNat_sext_bypass; [omega|].
    apply existT_wordToNat.
    apply extz_extz.
Qed.

Lemma wordToNat_sext_modulo:
  forall sz (w: word sz) n,
    Nat.modulo (wordToNat (sext w n)) (pow2 sz) = wordToNat w.
Proof.
  unfold sext; intros.
  pose proof (zero_lt_pow2 sz).
  destruct (wmsb w false).
  - rewrite wordToNat_combine.
    rewrite Nat.mul_comm, Nat.mod_add by omega.
    apply Nat.mod_small.
    apply wordToNat_bound.
  - rewrite wordToNat_combine.
    rewrite Nat.mul_comm, Nat.mod_add by omega.
    apply Nat.mod_small.
    apply wordToNat_bound.
Qed.

Lemma wlshift_sext_extz:
  forall sz (w: word sz) n,
    existT word _ (wlshift (sext w n) n) =
    existT word _ (extz w n).
Proof.
  intros; apply wordToNat_existT; [omega|].
  rewrite wordToNat_wlshift.
  rewrite wordToNat_extz.
  replace (sz + n - n) with sz by omega.
  rewrite wordToNat_sext_modulo.
  apply Nat.mul_comm.
Qed.

Lemma wlshift_combine_extz:
  forall sn sl (wl: word sl) ssu (wu: word (ssu + sn)),
    existT word (sl + (ssu + sn)) (wlshift (combine wl wu) sn) =
    existT word (sn + (sl + ssu)) (extz (combine wl (split1 ssu _ wu)) sn).
Proof.
  intros; apply wordToNat_existT; [omega|].
  rewrite wordToNat_wlshift.
  rewrite wordToNat_combine.
  rewrite wordToNat_extz.
  rewrite wordToNat_combine.
  rewrite wordToNat_split1.

  replace (sl + (ssu + sn) - sn) with (sl + ssu) by omega.
  rewrite Nat.mul_comm; f_equal.
  rewrite pow2_add_mul.
  pose proof (zero_lt_pow2 sl).
  pose proof (zero_lt_pow2 ssu).
  rewrite Nat.mod_mul_r; try omega.
  rewrite Nat.mul_comm with (n:= pow2 sl) at 1.
  rewrite Nat.mod_add; [|omega].
  rewrite Nat.mod_small by apply wordToNat_bound.
  do 3 f_equal.
  rewrite Nat.mul_comm, Nat.div_add; [|omega].
  rewrite Nat.div_small by apply wordToNat_bound.
  reflexivity.
Qed.

Lemma extz_sext_eq_rect:
  forall sz (w: word sz) n1 n2 nsz Hnsz1,
  exists Hnsz2,
    eq_rect (n2 + (sz + n1)) word (extz (sext w n1) n2) nsz Hnsz1 =
    eq_rect (n2 + sz + n1) word (sext (extz w n2) n1) nsz Hnsz2.
Proof.
  intros; subst; simpl.
  assert (Hsz: n2 + sz + n1 = n2 + (sz + n1)) by omega.
  exists Hsz.
  pose proof (extz_sext w n1 n2).
  pose proof (eq_sigT_snd H).
  rewrite <-H0.
  eq_rect_simpl.
  reflexivity.
Qed.

Lemma sext_zero:
  forall n m, sext (natToWord n 0) m = natToWord _ 0.
Proof.
  unfold sext; intros.
  rewrite wmsb_wzero.
  rewrite combine_wzero.
  reflexivity.
Qed.

Lemma sext_split1:
  forall sz (w: word sz) n,
    split1 sz _ (sext w n) = w.
Proof.
  unfold sext; intros.
  destruct (wmsb w false); apply split1_combine.
Qed.

Lemma sext_sext:
  forall sz (w: word sz) n1 n2,
    existT word _ (sext w (n1 + n2)) = existT word _ (sext (sext w n1) n2).
Proof.
  unfold sext; intros.
  remember (wmsb w false) as wmsb; destruct wmsb.
  - destruct n1 as [|n1].
    + cbn; rewrite wmsb_combine_WO, <-Heqwmsb.
      rewrite <-combine_assoc_existT.
      reflexivity.
    + rewrite wmsb_combine with (b2:= false) by discriminate.
      rewrite wmsb_wones.
      rewrite <-combine_assoc_existT.
      rewrite combine_wones.
      reflexivity.
  - destruct n1 as [|n1].
    + cbn; rewrite wmsb_combine_WO, <-Heqwmsb.
      rewrite <-combine_assoc_existT.
      reflexivity.
    + rewrite wmsb_combine with (b2:= false) by discriminate.
      rewrite wmsb_wzero.
      rewrite <-combine_assoc_existT.
      rewrite combine_wzero.
      reflexivity.
Qed.

Lemma wneg_wordToN:
  forall sz (w: word sz),
    wordToN w <> 0%N ->
    wordToN (wneg w) = (Npow2 sz - wordToN w)%N.
Proof.
  unfold wneg; intros.
  rewrite wordToN_NToWord_2.
  - reflexivity.
  - pose proof (wordToN_bound w).
    nomega.
Qed.

Lemma Nmul_two:
  forall n, (n + n = 2 * n)%N.
Proof.
  intros.
  destruct n; simpl; auto.
  rewrite Pos.add_diag.
  reflexivity.
Qed.

Lemma wmsb_false_bound:
  forall sz (w: word (S sz)),
    wmsb w false = false -> (wordToN w < Npow2 sz)%N.
Proof.
  apply (induct_word_S (fun sz w => wmsb w false = false -> (wordToN w < Npow2 sz)%N));
    [simpl; intros; subst; nomega|].
  intros; rewrite Npow2_S, Nmul_two.
  specialize (H H0).
  destruct b.
  - rewrite wordToN_WS_1.
    rewrite N.add_comm.
    apply N.mul_2_mono_l; auto.
  - rewrite wordToN_WS_0.
    apply N.mul_lt_mono_pos_l; [nomega|].
    assumption.
Qed.

Lemma wmsb_true_bound:
  forall sz (w: word (S sz)),
    wmsb w false = true -> (Npow2 sz <= wordToN w)%N.
Proof.
  apply (induct_word_S (fun sz w => wmsb w false = true -> (Npow2 sz <= wordToN w)%N));
    [simpl; intros; subst; reflexivity|].
  intros; rewrite Npow2_S, Nmul_two.
  specialize (H H0).
  destruct b.
  - rewrite wordToN_WS_1.
    apply N.mul_le_mono_nonneg_l with (p:= 2%N) in H; [|compute; discriminate].
    rewrite N.add_1_r.
    apply N.le_le_succ_r.
    assumption.
  - rewrite wordToN_WS_0.
    apply N.mul_le_mono_nonneg_l; [compute; discriminate|].
    assumption.
Qed.

Lemma ZToWord_wordToZ:
  forall sz (w: word sz), ZToWord sz (wordToZ w) = w.
Proof.
  unfold ZToWord, wordToZ; intros.
  remember (wmsb w false) as msb; destruct msb.
  - remember (wordToN (wneg w)) as ww.
    destruct ww.
    + assert (wneg w = wzero _).
      { apply wordToN_inj; rewrite <-Heqww.
        rewrite wordToN_nat.
        rewrite roundTrip_0.
        reflexivity.
      }
      rewrite wzero'_def.
      rewrite <-wneg_idempotent, H.
      apply eq_sym, wzero_wneg.
    + assert (wneg w = NToWord _ (N.pos p)).
      { apply wordToN_inj; rewrite Heqww.
        rewrite NToWord_wordToN.
        reflexivity.
      }
      rewrite <-wneg_idempotent, H.
      reflexivity.
  - remember (wordToN w) as ww.
    destruct ww.
    + assert (w = wzero _); subst.
      { apply wordToN_inj; rewrite <-Heqww.
        rewrite wordToN_nat.
        rewrite roundTrip_0.
        reflexivity.
      }
      apply wzero'_def.
    + assert (w = NToWord _ (N.pos p)); subst.
      { apply wordToN_inj; rewrite Heqww.
        rewrite NToWord_wordToN.
        reflexivity.
      }
      reflexivity.
Qed.

Lemma wordToZ_ZToWord:
  forall z sz,
    (- Z.of_nat (pow2 sz) <= z < Z.of_nat (pow2 sz))%Z ->
    wordToZ (ZToWord (S sz) z) = z.
Proof.
  unfold wordToZ, ZToWord; intros.
  destruct z.
  - rewrite wmsb_wzero'.
    rewrite wordToN_wzero'.
    reflexivity.

  - rewrite posToWord_nat.
    remember (wmsb (natToWord (S sz) (Pos.to_nat p)) false) as msb.
    destruct msb.
    + exfalso.
      simpl in H; destruct H.
      apply eq_sym, wmsb_true_bound in Heqmsb.
      rewrite <-positive_N_nat, <-NToWord_nat in Heqmsb.
      rewrite <-positive_nat_Z in H0.
      apply Nat2Z.inj_lt in H0.
      rewrite <-positive_N_nat, <-Npow2_nat in H0.
      apply Nlt_in in H0.
      pose proof (wordToN_NToWord (S sz) (N.pos p)).
      destruct H1 as [k [? ?]].
      rewrite H1 in Heqmsb.
      assert (N.pos p - k * Npow2 (S sz) <= N.pos p)%N by apply N.le_sub_l.
      assert (Npow2 sz <= N.pos p)%N by (etransitivity; eassumption).
      apply N.le_ngt in H4; auto.
    + rewrite wordToN_nat, wordToNat_natToWord_2.
      * rewrite positive_nat_N; reflexivity.
      * rewrite <-Npow2_nat, <-positive_N_nat.
        apply Nlt_out.
        destruct H.
        rewrite <-N2Z.inj_pos, <-N_nat_Z in H0.
        apply Nat2Z.inj_lt in H0.
        rewrite <-Npow2_nat in H0.
        apply Nlt_in.
        rewrite Npow2_S, N2Nat.inj_add.
        omega.

  - rewrite wneg_idempotent.
    rewrite posToWord_nat.
    remember (wmsb (wneg (natToWord (S sz) (Pos.to_nat p))) false) as msb.
    destruct msb.
    + rewrite wordToN_nat, wordToNat_natToWord_2.
      * rewrite positive_nat_N; reflexivity.
      * rewrite <-Npow2_nat, <-positive_N_nat.
        apply Nlt_out.
        destruct H.
        apply Z.opp_le_mono in H.
        rewrite Pos2Z.opp_neg, Z.opp_involutive in H.
        rewrite <-N2Z.inj_pos, <-N_nat_Z in H.
        apply Nat2Z.inj_le in H.
        rewrite <-Npow2_nat in H.
        apply Nlt_in.
        rewrite Npow2_S, N2Nat.inj_add.
        assert (N.to_nat (Npow2 sz) > 0)%nat by (rewrite Npow2_nat; apply pow2_zero).
        omega.
    + exfalso.
      simpl in H.
      apply eq_sym, wmsb_false_bound in Heqmsb.
      rewrite wneg_wordToN in Heqmsb.
      * rewrite Npow2_S in Heqmsb.
        rewrite <-N.add_0_r in Heqmsb.
        rewrite <-N.add_sub_assoc in Heqmsb.
        { apply N.add_lt_mono_l in Heqmsb.
          exfalso; eapply N.nlt_0_r; eauto.
        }
        { destruct H.
          apply Z.opp_le_mono in H.
          rewrite Pos2Z.opp_neg, Z.opp_involutive in H.
          rewrite <-N2Z.inj_pos, <-N_nat_Z in H.
          apply Nat2Z.inj_le in H.
          rewrite positive_N_nat in H.
          rewrite <-positive_N_nat, <-NToWord_nat.
          pose proof (wordToN_NToWord (S sz) (N.pos p)).
          destruct H1 as [k [? ?]]; rewrite H1.
          etransitivity; [apply N.le_sub_l|].
          rewrite <-Npow2_nat in H.
          rewrite <-positive_N_nat in H.
          unfold N.le; rewrite N2Nat.inj_compare.
          apply nat_compare_le; auto.
        }
      * intro Hx.
        replace 0%N with (wordToN (wzero (S sz))) in Hx by apply wordToN_wzero.
        apply wordToN_inj in Hx.
        assert (wordToNat (natToWord (S sz) (Pos.to_nat p)) = 0)
          by (rewrite Hx; apply wordToNat_wzero).
        rewrite wordToNat_natToWord_2 in H0.
        { clear -H0.
          induction p; simpl in H0; try discriminate.
          elim IHp; rewrite Pos2Nat.inj_xO in H0; omega.
        }
        { destruct H.
          apply Z.opp_le_mono in H.
          rewrite Pos2Z.opp_neg, Z.opp_involutive in H.
          rewrite <-N2Z.inj_pos, <-N_nat_Z in H.
          apply Nat2Z.inj_le in H.
          rewrite positive_N_nat in H.
          simpl.
          pose proof (pow2_zero sz).
          omega.
        }
Qed.

Lemma wordToZ_wordToN:
  forall sz (w: word sz),
    wordToZ w = (Z.of_N (wordToN w) - Z.of_N (if wmsb w false then Npow2 sz else 0))%Z.
Proof.
  unfold wordToZ; intros.
  remember (wmsb w false) as msb; destruct msb;
    [|simpl; rewrite Z.sub_0_r; reflexivity].
  destruct (weq w (wzero _)); subst;
    [rewrite wmsb_wzero in Heqmsb; discriminate|].
  rewrite wneg_wordToN.
  - pose proof (wordToN_bound w).
    replace (Z.of_N (wordToN w) - Z.of_N (Npow2 sz))%Z
      with (- (Z.of_N (Npow2 sz) - Z.of_N (wordToN w)))%Z by omega.
    rewrite <-N2Z.inj_sub by (apply N.lt_le_incl; assumption).
    clear; destruct (Npow2 sz - wordToN w)%N; reflexivity.
  - intro Hx; elim n.
    rewrite <-wordToN_wzero with (sz:= sz) in Hx.
    apply wordToN_inj in Hx; auto.
Qed.

Lemma ZToWord_Z_of_N:
  forall sz n,
    ZToWord sz (Z.of_N n) = NToWord sz n.
Proof.
  unfold ZToWord, NToWord; intros.
  destruct n; reflexivity.
Qed.

Lemma ZToWord_Z_of_nat: forall sz x, ZToWord sz (Z.of_nat x) = natToWord sz x.
Proof.
  intros.
  rewrite <- nat_N_Z.
  rewrite ZToWord_Z_of_N.
  rewrite NToWord_nat.
  rewrite Nnat.Nat2N.id.
  reflexivity.
Qed.

Lemma natToWord_Z_to_nat: forall sz n,
    (0 <= n)%Z ->
    natToWord sz (Z.to_nat n) = ZToWord sz n.
Proof.
  intros. rewrite <- ZToWord_Z_of_nat.
  rewrite Z2Nat.id by assumption.
  reflexivity.
Qed.

Lemma ZToWord_sz0: forall z, ZToWord 0 z = $0.
Proof.
  intros. unfold ZToWord. destruct z; try rewrite posToWord_sz0; reflexivity.
Qed.

Lemma natToWord_pow2_add:
  forall sz n,
    natToWord sz (n + pow2 sz) = natToWord sz n.
Proof.
  induction sz; intros; [reflexivity|].
  unfold natToWord, pow2; fold natToWord pow2.
  rewrite drop_mod2_add, div2_plus_2, IHsz.
  reflexivity.
Qed.

Lemma nat_add_pow2_wzero:
  forall sz n1 n2,
    n1 + n2 = pow2 sz ->
    natToWord sz n1 ^+ natToWord sz n2 = wzero sz.
Proof.
  intros.
  rewrite <-natToWord_plus, H.
  rewrite natToWord_pow2.
  reflexivity.
Qed.

Lemma Npos_Npow2_wzero:
  forall sz p1 p2,
    N.pos (p1 + p2) = Npow2 sz ->
    posToWord sz p1 ^+ posToWord sz p2 = wzero sz.
Proof.
  intros.
  do 2 rewrite posToWord_nat.
  assert (Pos.to_nat p1 + Pos.to_nat p2 = pow2 sz).
  { rewrite <-Pos2Nat.inj_add, <-Npow2_nat.
    rewrite <-positive_N_nat.
    rewrite H; reflexivity.
  }
  apply nat_add_pow2_wzero; auto.
Qed.

Lemma ZToWord_Npow2_sub:
  forall sz z,
    ZToWord sz (z - Z.of_N (Npow2 sz)) = ZToWord sz z.
Proof.
  unfold ZToWord; intros.
  remember (z - Z.of_N (Npow2 sz))%Z as zz.
  destruct z.
  - destruct zz.
    + assert (Z.of_N (Npow2 sz) = 0)%Z by omega.
      change 0%Z with (Z.of_N 0%N) in H.
      apply N2Z.inj in H.
      exfalso; eapply Npow2_not_zero; eauto.
    + pose proof (N2Z.is_nonneg (Npow2 sz)).
      destruct (Z.of_N (Npow2 sz)); simpl in Heqzz, H;
        try discriminate.
      pose proof (Pos2Z.neg_is_neg p0); omega.
    + assert (Z.of_N (Npow2 sz) = Z.pos p).
      { rewrite Z.sub_0_l, <-Pos2Z.opp_pos in Heqzz.
        apply Z.opp_inj in Heqzz; auto.
      }
      rewrite <-N2Z.inj_pos in H.
      apply N2Z.inj in H.
      rewrite posToWord_nat, <-positive_N_nat, <-H.
      rewrite Npow2_nat, natToWord_pow2.
      rewrite wzero_wneg.
      apply eq_sym, wzero'_def.

  - destruct zz.
    + assert (Z.of_N (Npow2 sz) = Z.pos p) by omega.
      rewrite <-N2Z.inj_pos in H.
      apply N2Z.inj in H.
      rewrite posToWord_nat, <-positive_N_nat, <-H.
      rewrite Npow2_nat, natToWord_pow2.
      apply wzero'_def.
    + assert (Z.pos p = Z.pos p0 + Z.of_N (Npow2 sz))%Z by omega.
      do 2 rewrite <-N2Z.inj_pos in H.
      rewrite <-N2Z.inj_add in H.
      apply N2Z.inj in H.
      apply eq_sym.
      do 2 rewrite posToWord_nat, <-positive_N_nat.
      rewrite H, N2Nat.inj_add, Npow2_nat.
      apply natToWord_pow2_add.
    + assert (Z.pos p - Z.neg p0 = Z.of_N (Npow2 sz))%Z by omega.
      simpl in H.
      remember (Npow2 sz) as n; destruct n;
        [exfalso; eapply Npow2_not_zero; eauto|].
      rewrite N2Z.inj_pos in H; inversion H; subst; clear H.
      apply eq_sym, sub_0_eq.
      rewrite wminus_def, wneg_idempotent.
      apply Npos_Npow2_wzero; auto.

  - destruct zz.
    + assert (Z.neg p = Z.of_N (Npow2 sz))%Z by omega.
      pose proof (N2Z.is_nonneg (Npow2 sz)).
      rewrite <-H in H0.
      pose proof (Pos2Z.neg_is_neg p); omega.
    + assert (Z.neg p = Z.pos p0 + Z.of_N (Npow2 sz))%Z by omega.
      pose proof (N2Z.is_nonneg (Npow2 sz)).
      destruct (Z.of_N (Npow2 sz)); simpl in H;
        try discriminate.
      pose proof (Pos2Z.neg_is_neg p1); omega.
    + assert (Pos.to_nat p0 = Pos.to_nat p + pow2 sz).
      { rewrite <-Npow2_nat.
        do 2 rewrite <-positive_N_nat.
        rewrite <-N2Nat.inj_add.
        f_equal.
        pose proof (N2Z.is_nonneg (Npow2 sz)).
        remember (Z.of_N (Npow2 sz)) as z; destruct z.
        { change 0%Z with (Z.of_N 0) in Heqz.
          apply N2Z.inj in Heqz.
          exfalso; eapply Npow2_not_zero; eauto.
        }
        { simpl in Heqzz; inversion Heqzz; subst.
          rewrite <-N2Z.inj_pos in Heqz.
          apply N2Z.inj in Heqz.
          rewrite <-Heqz.
          reflexivity.
        }
        { pose proof (Zlt_neg_0 p1); omega. }
      }
      f_equal.
      do 2 rewrite posToWord_nat.
      rewrite H.
      apply natToWord_pow2_add.
Qed.

Lemma wplus_wplusZ:
  forall sz (w1 w2: word sz),
    w1 ^+ w2 = wplusZ w1 w2.
Proof.
  unfold wplus, wplusZ, wordBin, wordBinZ; intros.
  do 2 rewrite wordToZ_wordToN.
  match goal with
  | [ |- context[(?z1 - ?z2 + (?z3 - ?z4))%Z] ] =>
    replace (z1 - z2 + (z3 - z4))%Z with (z1 + z3 - z2 - z4)%Z by omega
  end.
  rewrite <-N2Z.inj_add.
  destruct (wmsb w1 false); destruct (wmsb w2 false).
  - simpl; do 2 rewrite ZToWord_Npow2_sub.
    apply eq_sym, ZToWord_Z_of_N.
  - simpl; rewrite Z.sub_0_r, ZToWord_Npow2_sub.
    apply eq_sym, ZToWord_Z_of_N.
  - simpl; rewrite Z.sub_0_r, ZToWord_Npow2_sub.
    apply eq_sym, ZToWord_Z_of_N.
  - simpl; do 2 rewrite Z.sub_0_r.
    apply eq_sym, ZToWord_Z_of_N.
Qed.

Lemma ZToWord_Npow2_sub_k : forall (sz : nat) (z : Z) (k: nat),
    ZToWord sz (z - Z.of_nat k * Z.of_N (Npow2 sz)) = ZToWord sz z.
Proof.
  intros. induction k.
  - simpl. f_equal. omega.
  - rewrite <- IHk.
    replace (z - Z.of_nat (S k) * Z.of_N (Npow2 sz))%Z
       with ((z - Z.of_nat k * Z.of_N (Npow2 sz)) - Z.of_N (Npow2 sz))%Z by nia.
    apply ZToWord_Npow2_sub.
Qed.

Lemma ZToWord_Npow2_add_k : forall (sz : nat) (z : Z) (k: nat),
    ZToWord sz (z + Z.of_nat k * Z.of_N (Npow2 sz)) = ZToWord sz z.
Proof.
  intros.
  replace z with (z + Z.of_nat k * Z.of_N (Npow2 sz) - Z.of_nat k * Z.of_N (Npow2 sz))%Z at 2
    by omega.
  symmetry.
  apply ZToWord_Npow2_sub_k.
Qed.

Lemma ZToWord_Npow2_sub_z : forall (sz : nat) (z : Z) (k: Z),
    ZToWord sz (z - k * Z.of_N (Npow2 sz)) = ZToWord sz z.
Proof.
  intros. destruct k.
  - simpl. f_equal. omega.
  - rewrite <- positive_nat_Z. apply ZToWord_Npow2_sub_k.
  - rewrite <- Pos2Z.opp_pos.
    replace (z - - Z.pos p * Z.of_N (Npow2 sz))%Z
       with (z +   Z.pos p * Z.of_N (Npow2 sz))%Z by nia.
    rewrite <- positive_nat_Z. apply ZToWord_Npow2_add_k.
Qed.

Lemma wordToZ_ZToWord': forall sz w,
    exists k, wordToZ (ZToWord sz w) = (w - k * Z.of_N (Npow2 sz))%Z.
Proof.
  intros.
  destruct sz.
  - simpl. exists w%Z. rewrite ZToWord_sz0. rewrite wordToZ_wzero. omega.
  - exists ((w + Z.of_nat (pow2 sz)) / Z.of_N (Npow2 (S sz)))%Z.
    erewrite <- ZToWord_Npow2_sub_z.
    rewrite wordToZ_ZToWord.
    + reflexivity.
    + replace w with ((- Z.of_nat (pow2 sz)) + (w + Z.of_nat (pow2 sz)))%Z at 1 3 by omega.
      rewrite <- Z.add_sub_assoc.
      replace (Z.of_N (Npow2 (S sz))) with (2 * Z.of_nat (pow2 sz))%Z.
      * remember (Z.of_nat (pow2 sz)) as M.
        assert (M > 0)%Z. {
          subst. destruct (pow2 sz) eqn: E.
          - exfalso. eapply pow2_ne_zero. exact E.
          - simpl. constructor.
        }
        rewrite <- Zdiv.Zmod_eq_full by omega.
        pose proof (Zdiv.Z_mod_lt (w + M) (2 * M)). omega.
      * rewrite <- Npow2_nat. rewrite N_nat_Z.
        rewrite Npow2_S. rewrite N2Z.inj_add. omega.
Qed.

Lemma ZToWord_plus: forall sz a b, ZToWord sz (a + b) = ZToWord sz a ^+ ZToWord sz b.
Proof.
  destruct sz as [|sz]; intros n m; intuition.
  rewrite wplus_wplusZ.
  unfold wplusZ, wordBinZ.
  destruct (wordToZ_ZToWord' (S sz) n) as [k1 D1].
  destruct (wordToZ_ZToWord' (S sz) m) as [k2 D2].
  rewrite D1.
  rewrite D2.
  replace (n - k1 * Z.of_N (Npow2 (S sz)) + (m - k2 * Z.of_N (Npow2 (S sz))))%Z
     with (n + m - (k1 + k2) * Z.of_N (Npow2 (S sz)))%Z by nia.
  symmetry.
  apply ZToWord_Npow2_sub_z.
Qed.

Lemma else_0_to_ex_N: forall (b: bool) (a: N),
    exists k, (if b then a else 0%N) = (k * a)%N.
Proof.
  intros. destruct b.
  - exists 1%N. nia.
  - exists 0%N. reflexivity.
Qed.

Local Lemma wmultZ_helper: forall a b k1 k2 p,
    ((a - k1 * p) * (b - k2 * p) = a * b - (k1 * b + k2 * a - k1 * k2 * p) * p)%Z.
Proof. intros. nia. Qed.

Lemma wmult_wmultZ: forall (sz : nat) (w1 w2 : word sz), w1 ^* w2 = wmultZ w1 w2.
Proof.
  unfold wmultZ, wmult, wordBinZ, wordBin. intros.
  do 2 rewrite wordToZ_wordToN.
  destruct (else_0_to_ex_N (wmsb w1 false) (Npow2 sz)) as [k1 E1]. rewrite E1. clear E1.
  destruct (else_0_to_ex_N (wmsb w2 false) (Npow2 sz)) as [k2 E2]. rewrite E2. clear E2.
  do 2 rewrite N2Z.inj_mul.
  rewrite wmultZ_helper.
  rewrite <- N2Z.inj_mul.
  rewrite ZToWord_Npow2_sub_z.
  rewrite ZToWord_Z_of_N.
  reflexivity.
Qed.

Lemma ZToWord_mult: forall sz a b, ZToWord sz (a * b) = ZToWord sz a ^* ZToWord sz b.
Proof.
  intros. rewrite wmult_wmultZ. unfold wmultZ, wordBinZ.
  destruct (wordToZ_ZToWord' sz a) as [k1 D1]. rewrite D1. clear D1.
  destruct (wordToZ_ZToWord' sz b) as [k2 D2]. rewrite D2. clear D2.
  rewrite wmultZ_helper.
  symmetry.
  apply ZToWord_Npow2_sub_z.
Qed.

Lemma ZToWord_0: forall sz, ZToWord sz 0 = wzero sz.
Proof.
  intros. unfold ZToWord. apply wzero'_def.
Qed.

Lemma wordToZ_wplus_bound:
  forall sz (w1 w2: word (S sz)),
    (- Z.of_nat (pow2 sz) <= wordToZ w1 + wordToZ w2 < Z.of_nat (pow2 sz))%Z ->
    (wordToZ w1 + wordToZ w2 = wordToZ (w1 ^+ w2))%Z.
Proof.
  intros.
  rewrite wplus_wplusZ.
  unfold wplusZ, wordBinZ.
  remember (wordToZ w1 + wordToZ w2)%Z as z; clear Heqz.
  apply eq_sym, wordToZ_ZToWord; assumption.
Qed.

Lemma wordToZ_wplus_bound':
  forall sz (w1 w2: word sz),
    sz <> 0 ->
    (- Z.of_nat (pow2 (pred sz)) <= wordToZ w1 + wordToZ w2 < Z.of_nat (pow2 (pred sz)))%Z ->
    (wordToZ w1 + wordToZ w2 = wordToZ (w1 ^+ w2))%Z.
Proof.
  intros.
  destruct sz; [exfalso; auto|clear H].
  apply wordToZ_wplus_bound; auto.
Qed.

Lemma wordToZ_size':
  forall sz (w: word (S sz)),
    (- Z.of_nat (pow2 sz) <= wordToZ w < Z.of_nat (pow2 sz))%Z.
Proof.
  unfold wordToZ; intros.
  remember (wmsb w false) as msb; destruct msb.
  - destruct (weq w (wpow2 _)).
    + subst; rewrite wpow2_wneg.
      rewrite wpow2_Npow2.
      remember (Npow2 sz) as np.
      destruct np; [exfalso; eapply Npow2_not_zero; eauto|].
      split.
      * rewrite <-Pos2Z.opp_pos, <-N2Z.inj_pos.
        rewrite Heqnp.
        rewrite <-Npow2_nat.
        rewrite N_nat_Z.
        reflexivity.
      * etransitivity.
        { apply Pos2Z.neg_is_neg. }
        { change 0%Z with (Z.of_nat 0).
          apply Nat2Z.inj_lt.
          apply zero_lt_pow2.
        }
    + assert (wordToN (wneg w) < Npow2 sz)%N.
      { apply wmsb_false_bound.
        eapply wmsb_wneg_true; eauto.
      }
      remember (wordToN (wneg w)) as ww; clear Heqww.
      destruct ww; simpl.
      * split; try omega.
        change 0%Z with (Z.of_nat 0).
        apply Nat2Z.inj_lt.
        apply zero_lt_pow2.
      * split.
        { rewrite <-Pos2Z.opp_pos, <-N2Z.inj_pos.
          rewrite <-Npow2_nat.
          rewrite N_nat_Z.
          rewrite <-Z.opp_le_mono.
          apply N2Z.inj_le.
          apply N.lt_le_incl.
          assumption.
        }
        { etransitivity.
          { apply Pos2Z.neg_is_neg. }
          { change 0%Z with (Z.of_nat 0).
            apply Nat2Z.inj_lt.
            apply zero_lt_pow2.
          }
        }
  - apply eq_sym, wmsb_false_bound in Heqmsb.
    destruct (wordToN w); simpl.
    * split; try omega.
      change 0%Z with (Z.of_nat 0).
      apply Nat2Z.inj_lt.
      apply zero_lt_pow2.
    * split.
      { etransitivity.
        { apply Z.opp_nonpos_nonneg.
          change 0%Z with (Z.of_nat 0).
          apply Nat2Z.inj_le.
          pose proof (zero_lt_pow2 sz); omega.
        }
        { pose proof (Pos2Z.is_pos p); omega. }
      }
      { rewrite <-N2Z.inj_pos.
        rewrite <-Npow2_nat.
        rewrite N_nat_Z.
        apply N2Z.inj_lt.
        assumption.
      }
Qed.

Lemma wordToZ_size:
  forall sz (w: word (S sz)),
    (Z.abs (wordToZ w) <= Z.of_nat (pow2 sz))%Z.
Proof.
  intros.
  pose proof (wordToZ_size' w).
  destruct H.
  apply Z.abs_le.
  split; omega.
Qed.

Lemma wneg_wzero:
  forall sz (w: word sz), wneg w = wzero sz -> w = wzero sz.
Proof.
  intros.
  pose proof (wminus_inv w).
  rewrite H in H0.
  rewrite wplus_comm, wplus_unit in H0; subst.
  reflexivity.
Qed.

Lemma wmsb_false_pos:
  forall sz (w: word sz),
    wmsb w false = false <-> (wordToZ w >= 0)%Z.
Proof.
  unfold wordToZ; split; intros.
  - rewrite H.
    destruct (wordToN w).
    + omega.
    + pose proof (Zgt_pos_0 p); omega.
  - remember (wmsb w false) as b; destruct b; auto.
    remember (wordToN (wneg w)) as n; destruct n.
    + replace 0%N with (wordToN (wzero sz)) in Heqn.
      * apply wordToN_inj in Heqn.
        apply eq_sym, wneg_wzero in Heqn; subst.
        rewrite wmsb_wzero in Heqb; discriminate.
      * rewrite <-wzero'_def.
        apply wordToN_wzero'.
    + exfalso; pose proof (Zlt_neg_0 p); omega.
Qed.

Lemma wmsb_true_neg:
  forall sz (w: word sz),
    wmsb w false = true <-> (wordToZ w < 0)%Z.
Proof.
  unfold wordToZ; split; intros.
  - rewrite H.
    remember (wordToN (wneg w)) as n; destruct n.
    + replace 0%N with (wordToN (wzero sz)) in Heqn.
      * apply wordToN_inj in Heqn.
        apply eq_sym, wneg_wzero in Heqn; subst.
        rewrite wmsb_wzero in H; discriminate.
      * rewrite <-wzero'_def.
        apply wordToN_wzero'.
    + pose proof (Zlt_neg_0 p); omega.
  - remember (wmsb w false) as b; destruct b; auto.
    remember (wordToN w) as n; destruct n.
    + omega.
    + pose proof (Zgt_pos_0 p); omega.
Qed.

Lemma wordToZ_distr_diff_wmsb:
  forall sz (w1 w2: word sz),
    wmsb w1 false = negb (wmsb w2 false) ->
    wordToZ (w1 ^+ w2) = (wordToZ w1 + wordToZ w2)%Z.
Proof.
  intros.
  destruct sz;
    [rewrite (shatter_word w1), (shatter_word w2); reflexivity|].
  eapply eq_sym, wordToZ_wplus_bound.
  pose proof (wordToZ_size' w1).
  pose proof (wordToZ_size' w2).
  remember (wmsb w1 false) as msb1; destruct msb1.
  - apply eq_sym, wmsb_true_neg in Heqmsb1.
    apply eq_sym, negb_true_iff, wmsb_false_pos in H.
    destruct H0, H1.
    split; omega.
  - apply eq_sym, wmsb_false_pos in Heqmsb1.
    apply eq_sym, negb_false_iff, wmsb_true_neg in H.
    destruct H0, H1.
    split; omega.
Qed.

Lemma sext_wplus_wordToZ_distr:
  forall sz (w1 w2: word sz) n,
    n <> 0 -> wordToZ (sext w1 n ^+ sext w2 n) =
              (wordToZ (sext w1 n) + wordToZ (sext w2 n))%Z.
Proof.
  intros.
  destruct n; [exfalso; auto|clear H].
  apply eq_sym, wordToZ_wplus_bound'; [omega|].

  do 2 rewrite sext_wordToZ.
  destruct sz.
  - rewrite (shatter_word w1), (shatter_word w2).
    cbn; split; try (pose proof (pow2_zero n); omega).
  - replace (pred (S sz + S n)) with (S (sz + n)) by omega.
    pose proof (wordToZ_size' w1); destruct H.
    pose proof (wordToZ_size' w2); destruct H1.
    split.
    + rewrite pow2_S_z.
      etransitivity; [|apply Z.add_le_mono; eassumption].
      rewrite <-Z.add_diag, Z.opp_add_distr.
      apply Z.add_le_mono;
        rewrite <-Z.opp_le_mono; apply Nat2Z.inj_le, pow2_le; omega.
    + rewrite pow2_S_z.
      eapply Z.lt_le_trans; [apply Z.add_lt_mono; eassumption|].
      rewrite <-Z.add_diag.
      apply Z.add_le_mono; apply Nat2Z.inj_le, pow2_le; omega.
Qed.

Lemma sext_wplus_wordToZ_distr_existT: (* Note: not axiom free *)
  forall sz (w1 w2: word sz) ssz (sw1 sw2: word ssz) n,
    existT word _ w1 = existT word _ (sext sw1 n) ->
    existT word _ w2 = existT word _ (sext sw2 n) ->
    n <> 0 -> wordToZ (w1 ^+ w2) = (wordToZ w1 + wordToZ w2)%Z.
Proof.
  intros.
  assert (sz = ssz + n) by (apply eq_sigT_fst in H; auto); subst.
  destruct_existT.
  apply sext_wplus_wordToZ_distr; auto.
Qed.

Lemma split1_existT: (* Note: not axiom free *)
  forall n sz1 (w1: word (n + sz1)) sz2 (w2: word (n + sz2)),
    existT word _ w1 = existT word _ w2 ->
    split1 n _ w1 = split1 n _ w2.
Proof.
  intros.
  assert (sz1 = sz2) by (apply eq_sigT_fst in H; omega); subst.
  destruct_existT.
  reflexivity.
Qed.

Lemma word_combinable:
  forall sz1 sz2 (w: word (sz1 + sz2)),
  exists w1 w2, w = combine w1 w2.
Proof.
  intros.
  exists (split1 _ _ w), (split2 _ _ w).
  apply eq_sym, combine_split.
Qed.

Lemma split1_combine_existT: (* Note: not axiom free *)
  forall sz n (w: word (n + sz)) sl (wl: word (n + sl)) su (wu: word su),
    existT word _ w = existT word _ (combine wl wu) ->
    split1 n _ w = split1 n _ wl.
Proof.
  intros.
  pose proof (word_combinable _ _ w).
  destruct H0 as [? [? ?]]; subst.
  pose proof (word_combinable _ _ wl).
  destruct H0 as [? [? ?]]; subst.
  assert (sz = sl + su) by (apply eq_sigT_fst in H; omega); subst.
  pose proof (word_combinable _ _ x0).
  destruct H0 as [? [? ?]]; subst.
  do 2 rewrite split1_combine.
  rewrite combine_assoc_existT in H.
  destruct_existT.
  assert (split1 _ _ (split1 _ _ (combine (combine x x3) x4)) =
          split1 _ _ (split1 _ _ (combine (combine x1 x2) wu)))
    by (rewrite H; reflexivity).
  repeat rewrite split1_combine in H0.
  assumption.
Qed.

Lemma extz_pow2_wordToZ:
  forall sz (w: word sz) n,
    wordToZ (extz w n) = (wordToZ w * Z.of_nat (pow2 n))%Z.
Proof.
  induction n; [cbn; omega|].
  rewrite pow2_S_z.
  change (wordToZ (extz w (S n))) with (wordToZ (combine (natToWord n 0) w)~0).
  rewrite wordToZ_WS_0.
  unfold extz, wzero in IHn.
  rewrite IHn.
  rewrite Z.mul_assoc.
  rewrite Z.mul_comm with (n:= 2%Z).
  apply eq_sym, Z.mul_assoc.
Qed.

Lemma extz_wneg:
  forall sz (w: word sz) n,
    extz (wneg w) n = wneg (extz w n).
Proof.
  induction n; intros; [reflexivity|].
  cbn; rewrite wneg_WS_0.
  unfold extz, wzero in IHn.
  rewrite IHn.
  reflexivity.
Qed.

Lemma wneg_wordToZ:
  forall sz (w: word (S sz)),
    w <> wpow2 sz ->
    wordToZ (wneg w) = (- wordToZ w)%Z.
Proof.
  intros.
  assert (wordToZ (wneg w) + wordToZ w = 0)%Z.
  { destruct (weq w (wzero _)).
    { subst; rewrite wzero_wneg, wordToZ_wzero.
      reflexivity.
    }
    { rewrite <-wordToZ_distr_diff_wmsb.
      { rewrite wplus_comm, wminus_inv.
        apply wordToZ_wzero.
      }
      { remember (wmsb w false) as msb; destruct msb.
        { eapply wmsb_wneg_true; eauto. }
        { eapply wmsb_wneg_false; eauto.
          intro Hx; elim n.
          apply wordToNat_inj.
          rewrite wordToNat_wzero, Hx; reflexivity.
        }
      }
    }
  }
  omega.
Qed.

Lemma wneg_wordToZ':
  forall sz (w: word (S sz)) z,
    w <> wpow2 sz ->
    (z + wordToZ (wneg w))%Z = (z - wordToZ w)%Z.
Proof.
  intros.
  rewrite wneg_wordToZ by assumption.
  omega.
Qed.

Lemma wneg_wplus_distr:
  forall sz (w1 w2: word sz),
    wneg (w1 ^+ w2) = wneg w1 ^+ wneg w2.
Proof.
  intros.
  apply wplus_cancel with (c:= w1 ^+ w2).
  rewrite wplus_comm, wminus_inv.
  rewrite wplus_comm, wplus_assoc.
  rewrite <-wplus_assoc with (x:= w1).
  rewrite wplus_comm with (x:= w2).
  rewrite wplus_assoc.
  rewrite wminus_inv.
  rewrite wplus_wzero_2.
  rewrite wminus_inv.
  reflexivity.
Qed.

Lemma wminus_wneg:
  forall sz (w1 w2: word sz),
    wneg (w1 ^- w2) = w2 ^- w1.
Proof.
  unfold wminus; intros.
  rewrite wneg_wplus_distr.
  rewrite wneg_idempotent.
  apply wplus_comm.
Qed.

Lemma wminus_wordToZ:
  forall sz (w1 w2: word (S sz)),
    w2 ^- w1 <> wpow2 sz ->
    wordToZ (w1 ^- w2) = (- wordToZ (w2 ^- w1))%Z.
Proof.
  intros.
  rewrite <-wneg_idempotent with (w:= w1 ^- w2).
  rewrite wminus_wneg.
  rewrite wneg_wordToZ by assumption.
  reflexivity.
Qed.

Lemma wminus_wordToZ':
  forall sz (w1 w2: word (sz + 1)),
    existT word _ (w2 ^- w1) <> existT word _ (wpow2 sz) ->
    wordToZ (w1 ^- w2) = (- wordToZ (w2 ^- w1))%Z.
Proof.
  intro sz.
  replace (sz + 1) with (S sz) by omega.
  intros.
  apply wminus_wordToZ.
  intro Hx; elim H.
  rewrite Hx; reflexivity.
Qed.

Lemma wminus_wminusZ: forall (sz : nat) (w1 w2 : word sz), w1 ^- w2 = wminusZ w1 w2.
Proof.
  unfold wminusZ, wminus, wordBinZ. intros. rewrite <- Z.add_opp_r.
  rewrite wplus_wplusZ. unfold wplusZ, wordBinZ.
  destruct sz.
  - do 2 rewrite ZToWord_sz0. reflexivity.
  - destruct (weq w2 (wpow2 sz)).
    + subst. rewrite wpow2_wneg.
      replace (wordToZ w1 + - wordToZ (wpow2 sz))%Z
         with (wordToZ w1 + wordToZ (wpow2 sz) - 2 * wordToZ (wpow2 sz))%Z by omega.
      replace (2 * wordToZ (wpow2 sz))%Z with (- 1 * Z.of_N (Npow2 (S sz)))%Z.
      * symmetry. apply ZToWord_Npow2_sub_z.
      * rewrite wordToZ_wordToN.
        rewrite wpow2_wmsb.
        rewrite wpow2_Npow2.
        rewrite Npow2_S.
        rewrite N2Z.inj_add.
        omega.
    + rewrite wneg_wordToZ by assumption. reflexivity.
Qed.

Local Lemma wminusZ_helper: forall a b k1 k2 p,
    ((a - k1 * p) - (b - k2 * p) = a - b - (k1 - k2) * p)%Z.
Proof. intros. nia. Qed.

Lemma ZToWord_minus: forall sz a b, ZToWord sz (a - b) = ZToWord sz a ^- ZToWord sz b.
Proof.
  intros. rewrite wminus_wminusZ. unfold wminusZ, wordBinZ.
  destruct (wordToZ_ZToWord' sz a) as [k1 D1]. rewrite D1. clear D1.
  destruct (wordToZ_ZToWord' sz b) as [k2 D2]. rewrite D2. clear D2.
  rewrite wminusZ_helper.
  symmetry.
  apply ZToWord_Npow2_sub_z.
Qed.

Lemma extz_zero:
  forall sz n, extz (natToWord sz 0) n = wzero _.
Proof.
  unfold wzero; intros.
  rewrite extz_combine.
  apply combine_zero.
Qed.

Lemma sext_eq_rect:
  forall sz (w: word sz) n nsz Hsz1,
  exists Hsz2,
    eq_rect (sz + n) word (sext w n) (nsz + n) Hsz1 =
    sext (eq_rect sz word w nsz Hsz2) n.
Proof.
  intros.
  assert (Hsz: sz = nsz) by omega.
  exists Hsz.
  subst; simpl.
  eq_rect_simpl.
  reflexivity.
Qed.

Lemma wmsb_sext:
  forall sz (w: word sz) n,
    wmsb (sext w n) false = wmsb w false.
Proof.
  unfold sext; intros.
  remember (wmsb w false) as ww; destruct ww.
  - destruct n; cbn.
    + rewrite wmsb_combine_WO; auto.
    + rewrite wmsb_combine with (b2:= false) by discriminate; cbn.
      clear; induction n; cbn; auto.
  - destruct n; cbn.
    + rewrite wmsb_combine_WO; auto.
    + rewrite wmsb_combine with (b2:= false) by discriminate; cbn.
      clear; induction n; cbn; auto.
Qed.

Lemma wmsb_wlshift_sext: (* Note: not axiom free *)
  forall sz (w: word sz) n,
    wmsb (sext w n) false = wmsb (wlshift (sext w n) n) false.
Proof.
  intros.
  pose proof (wlshift_sext_extz w n).
  apply wmsb_existT with (b:= false) in H.
  rewrite H.
  rewrite wmsb_sext.
  rewrite wmsb_extz.
  reflexivity.
Qed.

Lemma wordToZ_wordToNat_pos:
  forall sz (w: word sz),
    wmsb w false = false ->
    Z.of_nat (wordToNat w) = wordToZ w.
Proof.
  unfold wordToZ; intros.
  rewrite H.
  rewrite <-wordToN_to_nat.
  destruct (wordToN w).
  - reflexivity.
  - simpl; apply positive_nat_Z.
Qed.

Corollary wmsb_Zabs_pos:
  forall sz (w: word sz),
    wmsb w false = false -> Z.abs (wordToZ w) = wordToZ w.
Proof.
  intros.
  apply wmsb_false_pos in H.
  unfold Z.abs.
  destruct (wordToZ w); auto.
  pose proof (Zlt_neg_0 p); omega.
Qed.

Corollary wmsb_Zabs_neg:
  forall sz (w: word sz),
    wmsb w false = true -> (Z.abs (wordToZ w) = - wordToZ w)%Z.
Proof.
  intros.
  apply wmsb_true_neg in H.
  unfold Z.abs.
  destruct (wordToZ w); auto.
  pose proof (Zgt_pos_0 p); omega.
Qed.

Lemma wordToN_combine:
  forall sz1 (w1: word sz1) sz2 (w2: word sz2),
    wordToN (combine w1 w2) = (wordToN w1 + Npow2 sz1 * wordToN w2)%N.
Proof.
  intros.
  repeat rewrite wordToN_nat.
  rewrite pow2_N.
  rewrite <-Nat2N.inj_mul, <-Nat2N.inj_add.
  rewrite wordToNat_combine; reflexivity.
Qed.

Lemma word_exists_bound:
  forall sz z,
    (- Z.of_nat (pow2 sz) <= z < Z.of_nat (pow2 sz))%Z ->
    exists w: word (S sz), wordToZ w = z.
Proof.
  intros.
  exists (ZToWord (S sz) z).
  apply wordToZ_ZToWord; assumption.
Qed.

Lemma sext_size:
  forall sz n (w: word (sz + n)),
    sz <> 0 ->
    (- Z.of_nat (pow2 (sz - 1)) <= wordToZ w < Z.of_nat (pow2 (sz - 1)))%Z ->
    exists sw, w = sext sw n.
Proof.
  intros.
  destruct sz; [exfalso; auto|clear H].
  simpl in *.
  replace (sz - 0) with sz in H0 by omega.
  apply word_exists_bound in H0.
  destruct H0 as [sw ?].
  exists sw.
  apply wordToZ_inj.
  change (S (sz + n)) with (S sz + n).
  rewrite sext_wordToZ.
  auto.
Qed.

Lemma wordToZ_combine_WO:
  forall sz (w: word sz),
    wordToZ (combine w WO) = wordToZ w.
Proof.
  dependent induction w; [reflexivity|].
  simpl; destruct b.
  - destruct n; [rewrite (shatter_word w); reflexivity|].
    change (S n + 0) with (S (n + 0)) in *.
    do 2 rewrite wordToZ_WS_1.
    rewrite IHw; reflexivity.
  - do 2 rewrite wordToZ_WS_0.
    rewrite IHw; reflexivity.
Qed.

Lemma combine_WO:
  forall sz (w: word sz),
    combine w WO = eq_rect _ word w _ (Nat.add_comm 0 sz).
Proof.
  intros.
  apply wordToZ_inj.
  rewrite wordToZ_eq_rect.
  apply wordToZ_combine_WO.
Qed.

Lemma zext_zero:
  forall sz (w: word sz),
    zext w 0 = eq_rect _ word w _ (Nat.add_comm 0 sz).
Proof.
  unfold zext; intros.
  apply combine_WO.
Qed.

Lemma wmsb_false_wordToNat_eq:
  forall sz (w: word (S sz)),
    wmsb w false = false ->
    wordToNat w = wordToNat (split1 sz _ (eq_rect _ word w _ (Nat.add_comm 1 sz))).
Proof.
  intros.
  remember (eq_rect _ word w _ (Nat.add_comm 1 sz)) as ww.
  assert (wmsb ww false = false) by (subst; rewrite <-wmsb_eq_rect; assumption).
  replace (wordToNat w) with (wordToNat ww) by (subst; rewrite wordToNat_eq_rect; reflexivity).
  clear Heqww H w.
  apply wmsb_false_split2_wzero in H0.
  rewrite <-combine_split with (w:= ww) at 1.
  rewrite wordToNat_combine.
  rewrite <-H0.
  cbn; omega.
Qed.

Lemma wordToZ_bound_weakened:
  forall z n, (Z.abs z < n)%Z -> (- n <= z < n)%Z.
Proof.
  intros.
  apply Z.abs_lt in H.
  omega.
Qed.

Lemma zext_size:
  forall sz n (w: word (sz + n)),
    (- Z.of_nat (pow2 sz) <= wordToZ w < Z.of_nat (pow2 sz))%Z ->
    wmsb w false = false ->
    exists sw, w = zext sw n.
Proof.
  intros.
  destruct n.
  - exists (eq_rect _ word w _ (Nat.add_comm _ _)).
    rewrite zext_zero.
    apply eq_sym, eq_rect_2.
  - apply word_exists_bound in H.
    destruct H as [ssw ?].
    assert (wmsb ssw false = false).
    { apply wmsb_false_pos; apply wmsb_false_pos in H0.
      rewrite H; assumption.
    }
    eexists.
    apply wordToZ_inj.
    rewrite zext_wordToNat_equal_Z by discriminate.
    rewrite <-H.
    rewrite <-wordToZ_wordToNat_pos by assumption.
    rewrite wmsb_false_wordToNat_eq by assumption.
    reflexivity.
Qed.

Lemma zext_size_1: (* Note: not axiom free *)
  forall sz (w: word (sz + 1)),
    wmsb w false = false ->
    exists sw, w = zext sw 1.
Proof.
  intros.
  apply zext_size; auto.
  generalize dependent w.
  replace (sz + 1) with (S sz) by omega.
  intros.
  unfold wordToZ.
  rewrite H.
  apply wmsb_false_bound in H.
  remember (wordToN w) as n; destruct n; simpl.
  - split.
    + omega.
    + pose proof (pow2_zero sz); omega.
  - rewrite <-N2Z.inj_pos.
    rewrite <-N_nat_Z.
    split; [omega|].
    apply inj_lt.
    rewrite <-Npow2_nat.
    apply Nlt_out; auto.
Qed.

Lemma sext_wplus_exist:
  forall sz (w1 w2: word sz) n,
  exists w: word (S sz),
    existT word _ (sext w1 (S n) ^+ sext w2 (S n)) =
    existT word _ (sext w n).
Proof.
  intros; eexists.
  apply wordToZ_existT; [omega|].
  rewrite sext_wplus_wordToZ_distr by discriminate.
  do 3 rewrite sext_wordToZ.
  assert (- Z.of_nat (pow2 sz) <= wordToZ w1 + wordToZ w2 < Z.of_nat (pow2 sz))%Z.
  { clear n.
    dependent destruction w1.
    { rewrite (shatter_word w2); cbn; omega. }
    { remember (WS b w1) as ww1; clear Heqww1 w1 b.
      pose proof (wordToZ_size' ww1).
      pose proof (wordToZ_size' w2).
      destruct H, H0.
      split.
      { simpl; do 2 rewrite Nat2Z.inj_add; omega. }
      { simpl; do 2 rewrite Nat2Z.inj_add; omega. }
    }
  }
  apply wordToZ_ZToWord in H.
  rewrite <-H.
  reflexivity.
Qed.

(* Don't allow simpl to expand out these functions *)
Arguments natToWord : simpl never.
Arguments weq : simpl never.

(* Making wlt_dec opaque is necessary to prevent the [exact H] in the
 * example below from blowing up..
 *)
Global Opaque wlt_dec.
Definition test_wlt_f (a : nat) (b : nat) : nat :=
  if wlt_dec (natToWord 64 a) $0 then 0 else 0.
Theorem test_wlt_f_example: forall x y z, test_wlt_f x y = 0 -> test_wlt_f x z = 0.
Proof.
  intros.
  exact H.
Qed.

Lemma wordToNat_eq1: forall sz (a b: word sz), a = b -> wordToNat a = wordToNat b.
Proof.
  intros; subst; reflexivity.
Qed.

Lemma wordToNat_eq2: forall sz (a b: word sz), wordToNat a = wordToNat b -> a = b.
Proof.
  intros.
  rewrite <- natToWord_wordToNat with (w := a).
  rewrite <- natToWord_wordToNat with (w := b).
  rewrite H.
  reflexivity.
Qed.

Lemma wordToNat_lt1: forall sz (a b: word sz), a < b -> (wordToNat a < wordToNat b)%nat.
Proof.
  intros.
  pre_nomega.
  repeat rewrite wordToN_to_nat in H.
  assumption.
Qed.

Lemma wordToNat_lt2: forall sz (a b: word sz), (wordToNat a < wordToNat b)%nat -> a < b.
Proof.
  intros.
  pre_nomega.
  repeat rewrite wordToN_to_nat.
  assumption.
Qed.

Lemma wordToNat_gt1: forall sz (a b: word sz), a > b -> (wordToNat a > wordToNat b)%nat.
Proof.
  intros.
  pre_nomega.
  repeat rewrite wordToN_to_nat in H.
  assumption.
Qed.

Lemma wordToNat_gt2: forall sz (a b: word sz), (wordToNat a > wordToNat b)%nat -> a > b.
Proof.
  intros.
  pre_nomega.
  repeat rewrite wordToN_to_nat.
  assumption.
Qed.

Lemma wordToNat_le1: forall sz (a b: word sz), a <= b -> (wordToNat a <= wordToNat b)%nat.
Proof.
  intros.
  pre_nomega.
  repeat rewrite wordToN_to_nat in H.
  assumption.
Qed.

Lemma wordToNat_le2: forall sz (a b: word sz), (wordToNat a <= wordToNat b)%nat -> a <= b.
Proof.
  intros.
  pre_nomega.
  repeat rewrite wordToN_to_nat.
  assumption.
Qed.

Lemma wordToNat_ge1: forall sz (a b: word sz), a >= b -> (wordToNat a >= wordToNat b)%nat.
Proof.
  intros.
  pre_nomega.
  repeat rewrite wordToN_to_nat in H.
  assumption.
Qed.

Lemma wordToNat_ge2: forall sz (a b: word sz), (wordToNat a >= wordToNat b)%nat -> a >= b.
Proof.
  intros.
  pre_nomega.
  repeat rewrite wordToN_to_nat.
  assumption.
Qed.

Lemma wordToNat_neq1: forall sz (a b: word sz), a <> b -> wordToNat a <> wordToNat b.
Proof.
  unfold not.
  intros.
  apply wordToNat_eq2 in H0.
  tauto.
Qed.

Lemma wordToNat_neq2: forall sz (a b: word sz), wordToNat a <> wordToNat b -> a <> b.
Proof.
  unfold not.
  intros.
  subst.
  tauto.
Qed.

Lemma wordToNat_wplus': forall sz (a b: word sz),
    (#a + #b < pow2 sz)%nat ->
    #(a ^+ b) = #a + #b.
Proof.
  intros.
  rewrite <-? wordToN_to_nat in *.
  rewrite <-? Nnat.N2Nat.inj_add in *.
  rewrite <- Npow2_nat in *.
  apply Nlt_in in H.
  rewrite wordToN_plus by assumption.
  reflexivity.
Qed.

Lemma wordToNat_wmult': forall sz (a b: word sz),
    (#a * #b < pow2 sz)%nat ->
    #(a ^* b) = #a * #b.
Proof.
  intros.
  rewrite <-? wordToN_to_nat in *.
  rewrite <-? Nnat.N2Nat.inj_mul in *.
  rewrite <- Npow2_nat in *.
  apply Nlt_in in H.
  rewrite wordToN_mult by assumption.
  reflexivity.
Qed.

Lemma wordNotNot: forall sz (a b: word sz), (a <> b -> False) -> a = b.
Proof.
  intros.
  destruct (weq a b); subst; tauto.
Qed.

Ltac pre_word_omega :=
  unfold wzero, wone in *;
  repeat match goal with
           | H: @eq ?T ?a ?b |- _ =>
             match T with
               | word ?sz =>
                 apply (@wordToNat_eq1 sz a b) in H;
                   rewrite ?roundTrip_0, ?roundTrip_1, ?wones_pow2_minus_one in H;
                   simpl in H
             end
           | |- @eq ?T ?a ?b =>
             match T with
               | word ?sz =>
                 apply (@wordToNat_eq2 sz a b);
                   rewrite ?roundTrip_0, ?roundTrip_1, ?wones_pow2_minus_one;
                   simpl
             end
           | H: ?a < ?b |- _ =>
             apply wordToNat_lt1 in H;
               rewrite ?roundTrip_0, ?roundTrip_1, ?wones_pow2_minus_one in H;
               simpl in H
           | |- ?a < ?b =>
             apply wordToNat_lt2;
               rewrite ?roundTrip_0, ?roundTrip_1, ?wones_pow2_minus_one;
               simpl
           | H: ?a > ?b |- _ =>
             apply wordToNat_gt1 in H;
               rewrite ?roundTrip_0, ?roundTrip_1, ?wones_pow2_minus_one in H;
               simpl in H
           | |- ?a > ?b =>
             apply wordToNat_gt2;
               rewrite ?roundTrip_0, ?roundTrip_1, ?wones_pow2_minus_one;
               simpl
           | H: ?a <= ?b |- _ =>
             apply wordToNat_le1 in H;
               rewrite ?roundTrip_0, ?roundTrip_1, ?wones_pow2_minus_one in H;
               simpl in H
           | |- ?a <= ?b =>
             apply wordToNat_le2;
               rewrite ?roundTrip_0, ?roundTrip_1, ?wones_pow2_minus_one;
               simpl
           | H: ?a > ?b -> False |- _ =>
             apply wordToNat_le1 in H;
               rewrite ?roundTrip_0, ?roundTrip_1, ?wones_pow2_minus_one in H;
               simpl in H
           | |- ?a > ?b -> False =>
             apply wordToNat_le2;
               rewrite ?roundTrip_0, ?roundTrip_1, ?wones_pow2_minus_one;
               simpl
           | H: ?a < ?b -> False |- _ =>
             apply wordToNat_ge1 in H;
               rewrite ?roundTrip_0, ?roundTrip_1, ?wones_pow2_minus_one in H;
               simpl in H
           | |- ?a < ?b -> False =>
             apply wordToNat_ge2;
               rewrite ?roundTrip_0, ?roundTrip_1, ?wones_pow2_minus_one;
               simpl
           | H: not (@eq ?T ?a ?b) |- _ =>
             match T with
               | word ?sz =>
                 apply (@wordToNat_neq1 sz a b) in H;
                   rewrite ?roundTrip_0, ?roundTrip_1, ?wones_pow2_minus_one in H;
                   simpl in H
             end
           | |- not (@eq ?T ?a ?b) =>
             match T with
               | word ?sz =>
                 apply (@wordToNat_neq2 sz a b);
                   rewrite ?roundTrip_0, ?roundTrip_1, ?wones_pow2_minus_one;
                   simpl
             end
           | H: @eq ?T ?a ?b -> False |- _ =>
             match T with
               | word ?sz =>
                 apply (@wordToNat_neq1 sz a b) in H;
                   rewrite ?roundTrip_0, ?roundTrip_1, ?wones_pow2_minus_one in H;
                   simpl in H
             end
           | |- @eq ?T ?a ?b -> False =>
             match T with
               | word ?sz =>
                 apply (@wordToNat_neq2 sz a b);
                   rewrite ?roundTrip_0, ?roundTrip_1, ?wones_pow2_minus_one;
                   simpl
             end
           | H: (@eq ?T ?a ?b -> False) -> False |- _ =>
             match T with
               | word ?sz =>
                 apply (@wordNotNot sz a b) in H
             end
           | H: (not (@eq ?T ?a ?b)) -> False |- _ =>
             match T with
               | word ?sz =>
                 apply (@wordNotNot sz a b) in H
             end
           | H: not (@eq ?T ?a ?b -> False) |- _ =>
             match T with
               | word ?sz =>
                 apply (@wordNotNot sz a b) in H
             end
           | H: not (not (@eq ?T ?a ?b)) |- _ =>
             match T with
               | word ?sz =>
                 apply (@wordNotNot sz a b) in H
             end
         end.


Ltac word_omega := pre_word_omega; omega.



Lemma word_le_ge_eq sz (w1 w2: word sz): w1 <= w2 -> w1 >= w2 -> w1 = w2.
Proof.
  intros; word_omega.
Qed.

Lemma word_le_zero sz (w: word sz): w <= wzero sz -> w = wzero sz.
Proof.
  intros; word_omega.
Qed.

Close Scope word_scope.

Open Scope word_scope.
Local Open Scope nat.

Lemma wzero_wones: forall sz, sz >= 1 ->
                              natToWord sz 0 <> wones sz.
Proof.
  intros.
  unfold not.
  intros.
  pose proof (f_equal (@wordToNat sz) H0) as sth.
  unfold wzero in *.
  rewrite roundTrip_0 in *.
  rewrite wones_pow2_minus_one in sth.
  destruct sz; [omega | ].
  pose proof (NatLib.one_lt_pow2 sz).
  omega.
Qed.

Lemma wzero_wplus: forall sz w, wzero sz ^+ w = w.
Proof.
  intros.
  unfold wzero.
  apply wplus_unit.
Qed.

Lemma wordToNat_nonZero sz (w: word sz):
  w <> wzero sz -> wordToNat w > 0.
Proof.
  induction w; simpl; unfold wzero; simpl; intros.
  - tauto.
  - destruct b.
    + omega.
    + assert (sth: w <> (natToWord n 0)).
      { intro.
        subst.
        tauto.
      }
      assert (sth2: wordToNat w <> 0).
      { intro sth3.
        specialize (IHw sth).
        omega.
      }
      omega.
Qed.

Lemma split2_pow2: forall sz n,
    2 ^ sz <= n < 2 ^ S sz ->
    wordToNat (split2 sz 1 (natToWord (sz + 1) n)) = 1.
Proof.
  intros.
  rewrite wordToNat_split2.
  simpl in *.
  rewrite Nat.add_0_r in *.
  (* pose proof (wordToNat_natToWord sz n). *)
  rewrite wordToNat_natToWord_bound with (bound := wones _).
  - destruct H.
    assert (sth: pow2 sz <> 0) by omega.
    pose proof (Nat.div_le_mono _ _ (pow2 sz) sth H) as sth2.
    rewrite Nat.div_same in sth2 by auto.
    apply Nat.lt_le_pred in H0.
    pose proof (Nat.div_le_mono _ _ (pow2 sz) sth H0) as sth3.
    rewrite <- Nat.sub_1_r in sth3.
    assert (sth4: pow2 sz = 1 * pow2 sz) by omega.
    rewrite sth4 in sth3 at 2.
    assert (sth5: 1 * pow2 sz + pow2 sz - 1 = 1 * pow2 sz + (pow2 sz - 1)) by omega.
    rewrite sth5 in sth3.
    rewrite Nat.div_add_l in sth3 by omega.
    rewrite Nat.div_small with (a := pow2 sz - 1) in sth3 by omega.
    omega.
  - rewrite wones_pow2_minus_one.
    assert (sth: sz + 1 = S sz) by omega.
    rewrite sth.
    simpl.
    omega.
Qed.

Lemma combine_wones_WO sz:
  forall w, w <> wzero sz -> split2 sz 1 (combine (wones sz) ($ 0) ^+ combine w ($ 0)) = WO~1.
Proof.
  intros.
  match goal with
  | |- split2 _ _ (?a ^+ ?b) = _ =>
    rewrite <- (@natToWord_wordToNat _ a);
      rewrite <- (@natToWord_wordToNat _ b)
  end.
  rewrite <- natToWord_plus.
  rewrite ?wordToNat_combine.
  simpl.
  rewrite wones_pow2_minus_one.
  pose proof (wordToNat_bound w) as sth.
  pose proof (wordToNat_nonZero H).
  assert (sth2: 2^sz <= 2 ^ sz - 1 + wordToNat w < 2 ^ (S sz)). {
    pose proof (pow2_zero sz) as sth3.
    split; simpl; omega.
  }
  apply split2_pow2 in sth2.
  rewrite Nat.mul_0_r.
  rewrite ?Nat.add_0_r.
  apply (f_equal (natToWord 1)) in sth2.
  rewrite natToWord_wordToNat in sth2.
  assumption.
Qed.

Lemma wordToNat_plus sz (w1 w2: word sz):
  natToWord sz (wordToNat w1 + wordToNat w2) = w1 ^+ w2.
Proof.
  rewrite natToWord_plus.
  rewrite ?natToWord_wordToNat.
  auto.
Qed.

Lemma wordToNat_natToWord_eqn sz:
  forall n,
    wordToNat (natToWord sz n) = n mod (pow2 sz).
Proof.
  intros.
  pose proof (wordToNat_natToWord sz n).
  destruct H as [? [? ?]].
  rewrite H.
  assert (sth: pow2 sz * x = x * pow2 sz) by (apply Nat.mul_comm).
  rewrite <- sth in *.
  clear sth.
  pose proof (wordToNat_bound (natToWord sz n)).
  apply (Nat.mod_unique n (pow2 sz) x (n - pow2 sz * x)); try omega.
Qed.

Lemma mod_factor a b c:
  b <> 0 ->
  c <> 0 ->
  (a mod (b * c)) mod b = a mod b.
Proof.
  intros.
  pose proof (Nat.mod_mul_r a _ _ H H0).
  rewrite H1.
  rewrite Nat.add_mod_idemp_l by auto.
  rewrite Nat.add_mod by auto.
  assert (sth: b * ((a/b) mod c) = (a/b) mod c * b) by (apply Nat.mul_comm).
  rewrite sth.
  rewrite Nat.mod_mul by auto.
  rewrite Nat.add_0_r.
  rewrite Nat.mod_mod by auto.
  auto.
Qed.

Lemma split1_combine_wplus sz1 sz2 (w11 w21: word sz1) (w12 w22: word sz2):
  split1 _ _ (combine w11 w12 ^+ combine w21 w22) = w11 ^+ w21.
Proof.
  rewrite <- natToWord_wordToNat at 1.
  rewrite wordToNat_split1.
  rewrite <- wordToNat_plus.
  rewrite ?wordToNat_combine.
  assert (sth: #w11 + pow2 sz1 * #w12 + (#w21 + pow2 sz1 * #w22) = #w11 + #w21 + pow2 sz1 * (#w12 + #w22)) by ring.
  rewrite wordToNat_natToWord_eqn.
  rewrite sth.
  rewrite Nat.pow_add_r.
  assert (pow2 sz1 <> 0) by (pose proof (pow2_zero sz1); intro; omega).
  assert (pow2 sz2 <> 0) by (pose proof (pow2_zero sz2); intro; omega).
  rewrite mod_factor by auto.
  rewrite Nat.add_mod by auto.
  assert (sth2: pow2 sz1 * (# w12 + #w22) = (#w12 + #w22) * pow2 sz1) by ring.
  rewrite sth2.
  rewrite Nat.mod_mul by auto.
  rewrite Nat.add_0_r.
  rewrite Nat.mod_mod by auto.
  rewrite <- wordToNat_natToWord_eqn.
  rewrite natToWord_wordToNat.
  rewrite natToWord_plus.
  rewrite ?natToWord_wordToNat.
  auto.
Qed.

Lemma div_2 a b:
  b <> 0 ->
  a < b * 2 ->
  a >= b ->
  a / b = 1.
Proof.
  intros.
  assert (sth: b * 1 <= a) by omega.
  pose proof (Nat.div_le_lower_bound a b 1 H sth).
  pose proof (Nat.div_lt_upper_bound a b 2 H H0).
  omega.
Qed.

Lemma mod_sub a b:
  b <> 0 ->
  a < b * 2 ->
  a >= b ->
  a mod b = a - b.
Proof.
  intros.
  rewrite Nat.mod_eq; auto.
  repeat f_equal.
  rewrite div_2 by auto.
  rewrite Nat.mul_1_r; auto.
Qed.

Lemma wordToNat_wneg_non_0 sz: forall (a: word sz),
    a <> natToWord _ 0 ->
    # (wneg a) = pow2 sz - #a.
Proof.
  intros.
  unfold wneg.
  rewrite pow2_N.
  rewrite NToWord_nat.
  rewrite Nnat.N2Nat.inj_sub.
  rewrite wordToN_to_nat.
  rewrite Nnat.Nat2N.id.
  simpl.
  rewrite wordToNat_natToWord_idempotent'; auto.
  assert (#a <> 0) by word_omega.
  pose proof (pow2_zero sz).
  omega.
Qed.

Lemma wordToNat_wnot sz: forall (a: word sz),
    # (wnot a) = pow2 sz - #a - 1.
Proof.
  intros.
  rewrite wnot_def.
  rewrite pow2_N.
  rewrite NToWord_nat.
  rewrite Nnat.N2Nat.inj_sub.
  rewrite Nnat.N2Nat.inj_sub.
  rewrite wordToN_to_nat.
  rewrite Nnat.Nat2N.id.
  simpl.
  rewrite wordToNat_natToWord_idempotent'; auto.
  pose proof (pow2_zero sz).
  unfold Pos.to_nat; simpl.
  omega.
Qed.

Lemma wzero_wor: forall sz w, w ^| wzero sz = w.
Proof.
  intros.
  rewrite wor_comm.
  rewrite wor_wzero.
  auto.
Qed.

Lemma bool_prop1: forall a b, a && negb (a && b) = a && negb b.
Proof.
  destruct a, b; simpl; auto.
Qed.

Lemma wordToNat_wplus sz (w1 w2: word sz):
  #(w1 ^+ w2) = (#w1 + #w2) mod (pow2 sz).
Proof.
  rewrite <- (natToWord_wordToNat w1) at 1.
  rewrite <- (natToWord_wordToNat w2) at 1.
  rewrite <- natToWord_plus.
  rewrite wordToNat_natToWord_eqn.
  auto.
Qed.

Lemma wordToNat_wmult : forall (sz : nat) (w1 w2 : word sz),
    #(w1 ^* w2) = (#w1 * #w2) mod pow2 sz.
Proof using .
  clear. intros.
  rewrite <- (natToWord_wordToNat w1) at 1.
  rewrite <- (natToWord_wordToNat w2) at 1.
  rewrite <- natToWord_mult.
  rewrite wordToNat_natToWord_eqn.
  reflexivity.
Qed.

Lemma wor_r_wzero_1 sz: (* Note: not axiom free *)
  forall w1 w2,
    w1 ^| w2 = natToWord sz 0 ->
    w2 = natToWord sz 0.
Proof.
  induction w1; simpl; auto; intros.
  pose proof (shatter_word w2) as sth.
  simpl in sth.
  rewrite sth in *.
  unfold wor in H.
  simpl in H.
  unfold natToWord in H.
  unfold natToWord.
  fold (natToWord n (Nat.div2 0)) in *.
  unfold Nat.div2, mod2 in *.
  inversion H.
  destruct_existT.
  rewrite (IHw1 _ H2).
  f_equal.
  destruct b, (whd w2); auto.
Qed.

Lemma wor_r_wzero_2 sz: (* Note: not axiom free *)
  forall w1 w2,
    w1 ^| w2 = natToWord sz 0 ->
    w1 = natToWord sz 0.
Proof.
  induction w1; simpl; auto; intros.
  pose proof (shatter_word w2) as sth.
  simpl in sth.
  rewrite sth in *.
  unfold wor in H.
  simpl in H.
  unfold natToWord in H.
  unfold natToWord.
  fold (natToWord n (Nat.div2 0)) in *.
  unfold Nat.div2, mod2 in *.
  inversion H.
  destruct_existT.
  rewrite (IHw1 _ H2).
  f_equal.
  destruct b, (whd w2); auto.
Qed.

Fixpoint countLeadingZerosWord ni no: word ni -> word no :=
  match ni return word ni -> word no with
  | 0 => fun _ => $ 0
  | S m => fun e =>
             if (weq (split2 m 1 (nat_cast (fun n => word n) (eq_sym (Nat.add_1_r m)) e)) WO~0)
             then $ 1 ^+ @countLeadingZerosWord m no (split1 m 1 (nat_cast (fun n => word n) (eq_sym (Nat.add_1_r m)) e))
             else $ 0
  end.


Lemma countLeadingZerosWord_le_len no ni:
  ni < pow2 no ->
  forall w: word ni, (countLeadingZerosWord no w <= natToWord _ ni)%word.
Proof.
  induction ni; simpl; auto; intros.
  - word_omega.
  - match goal with
    | |- ((if ?P then _ else _) <= _)%word => destruct P; simpl; auto
    end; [| word_omega].
    assert (sth: ni < pow2 no) by omega.
    specialize (IHni sth).
    assert (sth1: natToWord no (S ni) = natToWord no (1 + ni)) by auto.
    rewrite sth1.
    rewrite natToWord_plus.
    match goal with
    | |- ((_ ^+ countLeadingZerosWord no ?P) <= _)%word => specialize (IHni P)
    end.
    match goal with
    | |- (?a ^+ ?b <= ?c ^+ ?d)%word =>
      rewrite (wplus_comm a b); rewrite (wplus_comm c d)
    end.
    pre_word_omega.
    assert (sth2: no > 0). {
      destruct no; [|omega].
      destruct ni; simpl in *; try omega.
    }
    rewrite <- ?(@natplus1_wordplus1_eq _ _ (wones no)); auto.
    + pre_word_omega.
      rewrite wordToNat_natToWord_eqn.
      rewrite Nat.mod_small; auto.
    + pre_word_omega.
      rewrite wordToNat_natToWord_eqn in IHni.
      rewrite Nat.mod_small in IHni; auto.
Qed.

Lemma countLeadingZerosWord_le_len_nat no ni:
  ni < pow2 no ->
  forall w: word ni, #(countLeadingZerosWord no w) <= ni.
Proof.
  intros H w.
  pose proof (countLeadingZerosWord_le_len H w) as sth.
  pre_word_omega.
  rewrite wordToNat_natToWord_idempotent' in * by assumption.
  assumption.
Qed.


Lemma wordToNat_zero sz: forall (w: word sz), #w = 0 -> w = natToWord _ 0.
Proof.
  intros.
  apply (f_equal (natToWord sz)) in H.
  rewrite natToWord_wordToNat in H.
  auto.
Qed.

Lemma wordToNat_notZero sz: forall (w: word sz), #w <> 0 -> w <> natToWord _ 0.
Proof.
  intros.
  intro.
  subst.
  pose proof (wordToNat_wzero sz); unfold wzero in *.
  tauto.
Qed.


Lemma natToWord_nzero sz x:
  0 < x ->
  x < pow2 sz ->
  natToWord sz x <> natToWord sz 0.
Proof.
  intros.
  pre_word_omega.
  rewrite wordToNat_natToWord_idempotent'; omega.
Qed.

Lemma pow2_lt_pow2_S:
  forall n, pow2 n < pow2 (n+1).
Proof.
  induction n; simpl; omega.
Qed.

Lemma combine_shiftl_plus_n n x:
  x < pow2 n ->
  (combine (natToWord n x) WO~1) = (natToWord (n + 1) (pow2 n)) ^+ natToWord (n + 1) x.
Proof.
  intros.
  apply wordToNat_eq2.
  rewrite ?wordToNat_combine.
  rewrite ?wordToNat_natToWord_idempotent'; simpl; auto.
  rewrite <- wordToNat_plus.
  pose proof (pow2_lt_pow2_S n) as sth.
  rewrite ?wordToNat_natToWord_idempotent'; simpl; try omega.
  rewrite ?wordToNat_natToWord_idempotent'; simpl; try omega.
  apply Nat.lt_add_lt_sub_l.
  rewrite Nat.add_1_r.
  simpl.
  omega.
Qed.

Lemma combine_natToWord_wzero n:
  forall x,
    x < pow2 n ->
    combine (natToWord n x) (natToWord 1 0) = natToWord (n+1) x.
Proof.
  intros.
  apply wordToNat_eq2.
  rewrite ?wordToNat_combine.
  simpl.
  rewrite Nat.mul_0_r.
  rewrite Nat.add_0_r.
  pose proof (pow2_lt_pow2_S n) as sth2.
  rewrite ?wordToNat_natToWord_idempotent' by omega.
  reflexivity.
Qed.

Lemma word_cancel_l sz (a b c: word sz):
  a = b -> c ^+ a = c ^+ b.
Proof.
  intro H; rewrite H; reflexivity.
Qed.


Lemma word_cancel_r sz (a b c: word sz):
  a = b -> a ^+ c = b ^+ c.
Proof.
  intro H; rewrite H; reflexivity.
Qed.

Lemma word_cancel_m sz (a b c a' b': word sz):
  a ^+ a' = b ^+ b'-> a ^+ c ^+ a' = b ^+ c ^+ b'.
Proof.
  intros.
  assert (sth: a ^+ c ^+ a' = a ^+ a'^+ c ).
  rewrite <- wplus_assoc.
  rewrite wplus_comm with (y := a').
  rewrite wplus_assoc.
  reflexivity.
  rewrite sth.
  rewrite H.
  rewrite <- wplus_assoc.
  rewrite wplus_comm with (x := b').
  rewrite wplus_assoc.
  reflexivity.
Qed.

Lemma move_wplus_wminus sz (a b c: word sz):
  a ^+ b = c <-> a = c ^- b.
Proof.
  split; intro.
  + rewrite <- H.
    rewrite wminus_def.
    rewrite <- wplus_assoc.
    rewrite wminus_inv.
    rewrite wplus_wzero_1.
    reflexivity.
  + rewrite H.
    rewrite wminus_def.
    rewrite <- wplus_assoc.
    rewrite wplus_comm with (x:= ^~b).
    rewrite wminus_inv.
    rewrite wplus_wzero_1.
    reflexivity.
Qed.

Lemma move_wplus_pow2 sz (w1 w2: word (S sz)):
  w1 = w2 ^+ $(pow2 sz) <->
  w1 ^+ $(pow2 sz) = w2.
Proof.
  split.
  + intro.
    apply move_wplus_wminus.
    rewrite wminus_def.
    rewrite pow2_wneg.
    assumption.
  + intro.
    apply move_wplus_wminus in H.
    rewrite <- pow2_wneg.
    assumption.
Qed.

Lemma move_wminus_pow2 sz (w1 w2: word (S sz)):
  w1 = w2 ^- $(pow2 sz) <->
  w1 ^- $(pow2 sz) = w2.
Proof.
  split.
  + intro.
    apply <- move_wplus_wminus.
    rewrite pow2_wneg.
    assumption.
  + intro.
    apply move_wplus_wminus.
    rewrite <- pow2_wneg.
    rewrite <- wminus_def.
    assumption.
Qed.

Lemma pow2_wzero sz :
  $(pow2 sz) = wzero sz.
Proof.
  apply wordToNat_eq2.
  rewrite wordToNat_natToWord_eqn.
  rewrite Nat.mod_same.
  rewrite wordToNat_wzero; auto.
  pose proof (zero_lt_pow2 sz) as sth.
  omega.
Qed.

Lemma pow2_wplus_wzero sz:
  $(pow2 sz) ^+ $(pow2 sz) = wzero (sz + 1).
Proof.
  apply wordToNat_eq2.
  rewrite <- natToWord_plus.
  rewrite <- mul2_add.
  assert (pow2_1_mul: pow2 1 = 2) by auto.
  rewrite <- pow2_1_mul at 2.
  rewrite <- pow2_add_mul.
  rewrite pow2_wzero; auto.
Qed.

Lemma wplus_wplus_pow2 sz (x1 x2 y1 y2: word (sz + 1)):
  x1 = y1 ^+ $(pow2 sz) ->
  x2 = y2 ^+ $(pow2 sz) ->
  x1 ^+ x2 = y1 ^+ y2.
Proof.
  intros.
  rewrite H.
  rewrite <- wplus_assoc.
  rewrite wplus_comm.
  rewrite wplus_comm in H0.
  rewrite H0.
  rewrite wplus_assoc.
  rewrite pow2_wplus_wzero.
  rewrite wzero_wplus.
  rewrite wplus_comm.
  reflexivity.
Qed.



Lemma wlt_meaning sz (w1 w2: word sz):
  (w1 < w2)%word <-> #w1 < #w2.
Proof.
  pose proof (@wordToNat_gt1 sz w2 w1).
  pose proof (@wordToNat_gt2 sz w2 w1).
  tauto.
Qed.

Lemma combine_wplus sz (w1 w2: word sz):
  #w1 + #w2 < pow2 sz ->
  forall sz' (w': word sz'),
    combine (w1 ^+ w2) w' = combine w1 w' ^+ combine w2 ($ 0).
Proof.
  intros.
  pre_word_omega.
  rewrite wordToNat_wplus in *.
  rewrite ?wordToNat_combine.
  rewrite wordToNat_natToWord_idempotent' by (apply pow2_zero).
  rewrite Nat.mul_0_r, Nat.add_0_r.
  rewrite wordToNat_wplus.
  rewrite Nat.mod_small by assumption.
  assert (sth: #w1 + #w2 + pow2 sz * #w' = #w1 + pow2 sz * #w' + #w2) by ring.
  rewrite <- sth; clear sth.
  rewrite Nat.mod_small; auto.
  rewrite Nat.pow_add_r.
  assert (sth: pow2 sz' = 1 + (pow2 sz' - 1)) by (pose proof (pow2_zero sz'); omega).
  rewrite sth; clear sth.
  rewrite Nat.mul_add_distr_l.
  rewrite Nat.mul_1_r.
  pose proof (wordToNat_bound w').
  pose proof (pow2_zero sz).
  apply Nat.lt_le_pred in H0.
  rewrite pred_of_minus in H0.
  pose proof (mult_le_compat_l _ _ (pow2 sz) H0).
  omega.
Qed.

Lemma word1_neq (w: word 1):
  w <> WO~0 ->
  w <> WO~1 ->
  False.
Proof.
  shatter_word w; intros.
  destruct x; tauto.
Qed.

Lemma combine_1 sz:
  sz > 1 ->
  natToWord (sz + 1) 1 = combine ($ 1) WO~0.
Proof.
  intros.
  rewrite <- natToWord_wordToNat.
  f_equal.
  rewrite wordToNat_combine; simpl.
  rewrite Nat.mul_0_r, Nat.add_0_r.
  rewrite wordToNat_natToWord_idempotent'; auto.
  destruct sz; simpl; try omega.
  pose proof (pow2_zero sz).
  omega.
Qed.

Lemma wordToNat_cast ni no (pf: ni = no):
  forall w,
    #w = #(match pf in _ = Y return _ Y with
           | eq_refl => w
           end).
Proof.
  destruct pf; intros; auto.
Qed.


Lemma countLeadingZerosWord_lt_len no ni:
  ni < pow2 no ->
  forall w: word ni,
    w <> wzero ni ->
    (countLeadingZerosWord no w < natToWord _ ni)%word.
Proof.
  induction ni; auto; intros.
  - shatter_word w.
    tauto.
  - unfold countLeadingZerosWord; fold countLeadingZerosWord.
    rewrite nat_cast_cast.
    match goal with
    | |- ((if ?P then _ else _) < _)%word => destruct P; simpl; auto
    end.
    + assert (sth: ni < pow2 no) by omega.
      specialize (IHni sth).
      assert (sth1: natToWord no (S ni) = natToWord no (1 + ni)) by auto.
      rewrite sth1.
      rewrite natToWord_plus.
      match goal with
      | |- ((_ ^+ countLeadingZerosWord no ?P) < _)%word => specialize (IHni P)
      end.
      match goal with
      | |- (?a ^+ ?b < ?c ^+ ?d)%word =>
        rewrite (wplus_comm a b); rewrite (wplus_comm c d)
      end.
      pre_word_omega.
      assert (sth2: no > 0). {
        destruct no; [|omega].
        destruct ni; simpl in *; try omega.
      }
      apply wordToNat_zero in e.
      match type of IHni with
      | split1 ni 1 ?P <> _ -> _ =>
        assert (sth3: #P <> 0) by (rewrite <- wordToNat_cast; auto);
          apply wordToNat_notZero in sth3;
          rewrite <- (combine_split ni 1 P) in sth3
      end.
      rewrite e in *.
      match type of sth3 with
      | combine ?P _ <> _ => destruct (weq P (natToWord _ 0));
                               [rewrite e0 in *; rewrite combine_zero in sth3; tauto|]
      end.
      specialize (IHni n).
      rewrite <- ?(@natplus1_wordplus1_eq _ _ (wones no)); auto.
      * pre_word_omega.
        omega.
      * pre_word_omega.
        rewrite wordToNat_natToWord_eqn.
        rewrite Nat.mod_small; auto.
      *  pre_word_omega.
         rewrite wordToNat_natToWord_eqn in IHni.
         rewrite Nat.mod_small in IHni; auto.
    + pre_word_omega.
      rewrite wordToNat_natToWord_idempotent'; auto; try omega.
Qed.


Fixpoint countLeadingZerosWord_nat ni: word ni -> nat :=
  match ni return word ni -> nat with
  | 0 => fun _ => 0
  | S m => fun e =>
             if (weq (split2 m 1 (nat_cast (fun n => word n) (eq_sym (Nat.add_1_r m)) e)) WO~0)
             then 1 + @countLeadingZerosWord_nat m (split1 m 1 (nat_cast (fun n => word n) (eq_sym (Nat.add_1_r m)) e))
             else 0
  end.

Lemma countLeadingZerosWord_nat_correct ni:
  forall no (w: word ni),
    ni < pow2 no ->
    #(countLeadingZerosWord no w) = countLeadingZerosWord_nat w.
Proof.
  induction ni; intros; simpl; auto.
  - rewrite ?wordToNat_natToWord_idempotent'; auto.
  - match goal with
    | |- # (if ?P then _ else _) = if ?P then _ else _ => destruct P
    end.
    + rewrite <- wordToNat_plus.
      rewrite ?wordToNat_natToWord_idempotent'; try omega.
      * simpl;f_equal.
        rewrite IHni; auto.
      * rewrite ?wordToNat_natToWord_idempotent'; try omega.
        match goal with
        | |- 1 + #(countLeadingZerosWord no ?x) < _ => pose proof (@countLeadingZerosWord_le_len_nat no ni ltac:(omega) x) as sth
        end.
        omega.
    + rewrite roundTrip_0; auto.
Qed.

Lemma countLeadingZerosWord_nat_le_len ni (w: word ni):
  countLeadingZerosWord_nat w <= ni.
Proof.
  induction ni; simpl; auto; intros.
  match goal with
  | |- ((if ?P then _ else _) <= _) => destruct P; simpl; auto
  end.
  apply Le.le_n_S.
  eapply IHni.
Qed.

Lemma countLeadingZerosWord_enough_size ni no no' (pf: ni < pow2 no) (pf': ni < pow2 no'): forall (w: word ni),
    #(countLeadingZerosWord no w) =
    #(countLeadingZerosWord no' w).
Proof.
  intros.
  rewrite ?countLeadingZerosWord_nat_correct; auto.
Qed.

(* Usually this kind of lemmas would need a guarantee that "(wordToN a mod wordToN b)%N"
   does not overflow, but fortunately this can never overflow.
   And also, we don't need to prevent b from being 0. *)
Lemma wordToN_mod: forall sz (a b: word sz),
    wordToN (a ^% b) = (wordToN a mod wordToN b)%N.
Proof.
  intros. unfold wmod, wordBin.
  rewrite wordToN_NToWord_2; [ reflexivity | ].
  destruct (wordToN b) eqn: E.
  - unfold N.modulo, N.div_eucl. destruct (wordToN a) eqn: F; simpl.
    + apply Npow2_pos.
    + rewrite <- F. apply wordToN_bound.
  - eapply N.lt_trans.
    + apply N.mod_upper_bound. congruence.
    + rewrite <- E. apply wordToN_bound.
Qed.

Lemma N_to_Z_to_nat: forall (a: N), Z.to_nat (Z.of_N a) = N.to_nat a.
Proof.
  intros. rewrite <- (N2Z.id a) at 2.
  rewrite Z_N_nat. reflexivity.
Qed.

Section ThisShouldBeInCoqLibrary.

  Lemma N2Nat_inj_mod: forall (a b: N),
      (b <> 0)%N ->
      N.to_nat (a mod b)%N = (N.to_nat a) mod (N.to_nat b).
  Proof.
    intros.
    rewrite <-? N_to_Z_to_nat.
    rewrite N2Z.inj_mod by assumption.
    apply Nat2Z.inj.
    rewrite Zdiv.mod_Zmod.
    - rewrite? Z2Nat.id; try apply N2Z.is_nonneg.
      + reflexivity.
      + pose proof (Z.mod_pos_bound (Z.of_N a) (Z.of_N b)) as Q.
        destruct Q as [Q _].
        * destruct b; try contradiction. simpl. constructor.
        * exact Q.
    - destruct b; try contradiction. simpl.
      pose proof (Pos2Nat.is_pos p) as Q. omega.
  Qed.

  Lemma Nat2Z_inj_pow: forall n m : nat,
      Z.of_nat (n ^ m) = (Z.of_nat n ^ Z.of_nat m)%Z.
  Proof.
    intros. induction m.
    - reflexivity.
    - rewrite Nat2Z.inj_succ.
      rewrite Z.pow_succ_r by (apply Nat2Z.is_nonneg).
      rewrite <- IHm.
      rewrite <- Nat2Z.inj_mul.
      reflexivity.
  Qed.

  Lemma Z2Nat_inj_pow: forall n m : Z,
      (0 <= n)%Z ->
      (0 <= m)%Z ->
      Z.to_nat (n ^ m) = Z.to_nat n ^ Z.to_nat m.
  Proof.
    intros.
    pose proof (Nat2Z_inj_pow (Z.to_nat n) (Z.to_nat m)) as P.
    rewrite? Z2Nat.id in P by assumption.
    rewrite <- P.
    apply Nat2Z.id.
  Qed.

End ThisShouldBeInCoqLibrary.

Lemma wordToNat_mod: forall sz (a b: word sz),
    b <> $0 ->
    #(a ^% b) = #a mod #b.
Proof.
  intros.
  rewrite <-? wordToN_to_nat in *.
  rewrite <-? N2Nat_inj_mod in *.
  - rewrite wordToN_mod by assumption.
    reflexivity.
  - intro. apply H. replace 0%N with (wordToN (natToWord sz 0)) in H0.
    + apply wordToN_inj. exact H0.
    + erewrite <- wordToN_wzero. reflexivity.
Qed.

Lemma wlshift_mul_pow2: forall sz n (a: word sz),
    wlshift a n = a ^* $ (pow2 n).
Proof.
  intros.
  apply wordToNat_inj.
  unfold wlshift.
  rewrite? wordToNat_split1.
  unfold eq_rec_r, eq_rec.
  rewrite? wordToNat_eq_rect.
  rewrite? wordToNat_combine.
  rewrite? wordToNat_wzero.
  rewrite wordToNat_wmult.
  rewrite wordToNat_natToWord_eqn.
  rewrite Nat.add_0_l.
  rewrite Nat.mul_mod_idemp_r by (apply pow2_ne_zero).
  rewrite Nat.mul_comm.
  reflexivity.
Qed.

Lemma wlshift_mul_Zpow2: forall sz n (a: word sz),
    (0 <= n)%Z ->
    wlshift a (Z.to_nat n) = a ^* ZToWord sz (2 ^ n).
Proof.
  intros. rewrite wlshift_mul_pow2. f_equal.
  change 2 with (Z.to_nat 2).
  rewrite <- Z2Nat_inj_pow by omega.
  apply natToWord_Z_to_nat.
  apply Z.pow_nonneg.
  omega.
Qed.

Lemma wlshift_distr_plus: forall sz n (a b: word sz),
    wlshift (a ^+ b) n = wlshift a n ^+ wlshift b n.
Proof.
  intros.
  rewrite? wlshift_mul_pow2.
  apply wmult_plus_distr.
Qed.

Lemma wlshift'_distr_plus: forall sz n (a b: word sz),
    wlshift' (a ^+ b) n = wlshift' a n ^+ wlshift' b n.
Proof.
  intros. rewrite? wlshift_alt. apply wlshift_distr_plus.
Qed.

Lemma wlshift_iter: forall sz n1 n2 (a: word sz),
    wlshift (wlshift a n1) n2 = wlshift a (n1 + n2).
Proof.
  intros. rewrite? wlshift_mul_pow2.
  rewrite <- wmult_assoc.
  rewrite <- natToWord_mult.
  do 2 f_equal.
  symmetry.
  apply Nat.pow_add_r.
Qed.

Lemma wlshift'_iter: forall sz n1 n2 (a: word sz),
    wlshift' (wlshift' a n1) n2 = wlshift' a (n1 + n2).
Proof.
  intros. rewrite? wlshift_alt. apply wlshift_iter.
Qed.

Lemma wlshift_zero: forall sz n, wlshift $0 n = natToWord sz 0.
Proof.
  intros.
  apply wordToNat_inj.
  unfold wlshift.
  rewrite? wordToNat_split1.
  unfold eq_rec_r, eq_rec.
  rewrite? wordToNat_eq_rect.
  rewrite? wordToNat_combine.
  rewrite? wordToNat_wzero.
  rewrite Nat.mul_0_r.
  change (0 + 0) with 0.
  rewrite Nat.mod_0_l by (apply pow2_ne_zero).
  reflexivity.
Qed.

Lemma wlshift'_zero: forall sz n, wlshift' $0 n = natToWord sz 0.
Proof.
  intros. rewrite? wlshift_alt. apply wlshift_zero.
Qed.

Lemma sext_natToWord_nat_cast: forall sz2 sz1 sz n (e: sz1 + sz2 = sz),
  2 * n < pow2 sz1 ->
  nat_cast word e (sext (natToWord sz1 n) sz2) = natToWord sz n.
Proof.
  intros. rewrite nat_cast_eq_rect. apply sext_natToWord. assumption.
Qed.

Lemma sext_neg_natToWord_nat_cast: forall sz2 sz1 sz n (e: sz1 + sz2 = sz),
  2 * n < pow2 sz1 ->
  nat_cast word e (sext (wneg (natToWord sz1 n)) sz2) = wneg (natToWord sz n).
Proof.
  intros. rewrite nat_cast_eq_rect. apply sext_wneg_natToWord. assumption.
Qed.

Lemma sext0: forall sz0 sz (v: word sz) (e: sz0 = 0),
  sext v sz0 = nat_cast word (eq_ind_r (fun sz0 : nat => sz = sz + sz0) (plus_n_O sz) e) v.
Proof.
  intros. subst.
  unfold sext.
  destruct (wmsb v false) eqn: E;
    simpl; rewrite combine_n_0; rewrite <- nat_cast_eq_rect; apply nat_cast_proof_irrel.
Qed.

Lemma wordToN_wordToZ: forall (sz : nat) (w : word sz),
    wordToN w = Z.to_N (wordToZ w + Z.of_N (if wmsb w false then Npow2 sz else 0%N)).
Proof.
  intros.
  rewrite (wordToZ_wordToN w).
  remember (if wmsb w false then Npow2 sz else 0%N) as c; clear Heqc.
  rewrite Z.sub_add.
  symmetry.
  apply N2Z.id.
Qed.

Lemma uwordToZ_ZToWord_0: forall (z : Z) (sz : nat),
    (0 <= z < Z.of_N (Npow2 sz))%Z ->
    uwordToZ (ZToWord sz z) = z.
Proof.
  intros.
  unfold uwordToZ.
  pose proof (Z2N.id _ (proj1 H)).
  remember (Z.to_N z) as n; clear Heqn. subst z.
  apply proj2 in H.
  f_equal.
  rewrite ZToWord_Z_of_N.
  apply wordToN_NToWord_2.
  apply N2Z.inj_lt.
  assumption.
Qed.

Lemma uwordToZ_ZToWord: forall (z : Z) (sz : nat),
    (0 <= z < 2 ^ (Z.of_nat sz))%Z ->
    uwordToZ (ZToWord sz z) = z.
Proof.
  intros. apply uwordToZ_ZToWord_0.
  intuition idtac.
  change 2%Z with (Z.of_nat 2) in H1.
  rewrite <- Nat2Z_inj_pow in H1.
  rewrite <- N_nat_Z.
  rewrite Npow2_nat.
  assumption.
Qed.

Lemma wordToN_neq_0: forall sz (b : word sz),
    b <> $0 ->
    wordToN b <> 0%N.
Proof.
  intros.
  intro C.
  apply H.
  apply wordToN_inj.
  erewrite <- wordToN_wzero in C.
  unfold wzero in C.
  exact C.
Qed.

(* These counterexamples will hopefully be found by users who use commands
   such as "Search ((_ ^+ _) ^% _)" *)
Lemma wmod_plus_distr_does_not_hold: ~ forall sz (a b m: word sz),
    m <> $0 ->
    (a ^+ b) ^% m = ((a ^% m) ^+ (b ^% m)) ^% m.
Proof.
  intro C.
  specialize (C 4 $9 $11 $7). cbv in C.
  match type of C with (?A -> _) => assert A by (intro; discriminate) end.
  specialize (C H). discriminate.
Qed.

Lemma wmul_mod_distr_does_not_hold: ~ forall sz (a b n: word sz),
    n <> $0 ->
    (a ^* b) ^% n = ((a ^% n) ^* (b ^% n)) ^% n.
Proof.
  intro C.
  specialize (C 4 $9 $11 $7). cbv in C.
  match type of C with (?A -> _) => assert A by (intro; discriminate) end.
  specialize (C H). discriminate.
Qed.

Lemma Nmod_0_r: forall a : N, (a mod 0)%N = a.
Proof.
  intros. destruct a; reflexivity.
Qed.

Lemma wordToN_0: forall sz,
    wordToN (natToWord sz 0) = 0%N.
Proof.
  intros. change (natToWord sz 0) with (wzero sz).
  apply wordToN_wzero.
Qed.

Lemma NToWord_0: forall sz,
    NToWord sz 0 = $ (0).
Proof.
  intros. change 0%nat with (N.to_nat 0).
  apply NToWord_nat.
Qed.

Lemma wmod_0_r: forall sz (a: word sz), a ^% $0 = a.
Proof.
  intros. unfold wmod, wordBin.
  rewrite wordToN_0.
  rewrite Nmod_0_r.
  apply NToWord_wordToN.
Qed.

Lemma wordToN_NToWord_eqn: forall sz (n : N),
    wordToN (NToWord sz n) = (n mod Npow2 sz)%N.
Proof.
  intros.
  pose proof (Npow2_not_zero sz).
  apply Nnat.N2Nat.inj.
  rewrite wordToN_to_nat.
  rewrite N2Nat_inj_mod by assumption.
  rewrite Npow2_nat.
  rewrite <- wordToNat_natToWord_eqn.
  rewrite <- NToWord_nat.
  reflexivity.
Qed.

Lemma Nminus_mod_idemp_r: forall a b n : N,
    (n <> 0)%N ->
    (b <= a)%N ->
    ((a - b mod n) mod n)%N = ((a - b) mod n)%N.
Proof.
  intros.
  apply N2Z.inj.
  rewrite? N2Z.inj_mod by assumption.
  pose proof (N.mod_le b n H).
  rewrite N2Z.inj_sub by (eapply N.le_trans; eassumption).
  rewrite N2Z.inj_sub by assumption.
  rewrite? N2Z.inj_mod by assumption.
  apply Zdiv.Zminus_mod_idemp_r.
Qed.

Lemma drop_sub_N: forall sz (n k : N),
    (k * Npow2 sz <= n)%N ->
    NToWord sz (n - k * Npow2 sz) = NToWord sz n.
Proof.
  intros.
  apply wordToN_inj.
  pose proof (Npow2_not_zero sz).
  do 2 rewrite wordToN_NToWord_eqn.
  rewrite <- Nminus_mod_idemp_r by assumption.
  rewrite N.mod_mul by assumption.
  rewrite N.sub_0_r.
  reflexivity.
Qed.

Lemma wmod_divides: forall sz (a b: word sz),
    a ^% b = $0 ->
    exists k, a = b ^* k.
Proof.
  intros. destruct (weq b $0).
  - subst b. rewrite wmod_0_r in *. subst a. exists (natToWord sz 0).
    symmetry. apply wmult_neut_r.
  - unfold wmod, wmult, wordBin in *.
    pose proof (N.mod_divides (wordToN a) (wordToN b)) as P.
    apply wordToN_neq_0 in n.
    specialize (P n).
    destruct P as [ [k P] _].
    + apply (f_equal (@wordToN sz)) in H.
      rewrite wordToN_NToWord_2 in H.
      * rewrite H. apply wordToN_0.
      * pose proof (wordToN_bound a). remember (wordToN a) as c. clear Heqc a.
        pose proof (wordToN_bound b). remember (wordToN b) as d. clear Heqd b.
        pose proof (N.mod_upper_bound c d n).
        nomega.
    + exists (NToWord sz (k - k / (Npow2 sz) * Npow2 sz)).
      rewrite wordToN_NToWord_2.
      { rewrite N.mul_sub_distr_l.
        rewrite N.mul_assoc.
        rewrite drop_sub_N.
        - rewrite <- P. symmetry. apply NToWord_wordToN.
        - rewrite <- N.mul_assoc.
          rewrite <- (N.mul_comm (Npow2 sz)).
          apply N.mul_le_mono_l.
          apply (N.mul_div_le k (Npow2 sz)).
          apply Npow2_not_zero.
      }
      { rewrite <- N.mul_comm. rewrite <- N.mod_eq by (apply Npow2_not_zero).
        apply N.mod_upper_bound. apply Npow2_not_zero. }
Qed.

Lemma wmod_divides_other_direction_does_not_hold: ~ forall sz (a b: word sz),
    b <> $0 ->
    (exists k, a = b ^* k) ->
    a ^% b = $0.
Proof.
  intro C. specialize (C 4 $14 $5).
  match type of C with (?A -> _) => assert A by (intro; discriminate) end.
  specialize (C H).
  match type of C with (?A -> _) => assert A as B end.
  - exists (natToWord 4 6). reflexivity.
  - specialize (C B). cbv in C. discriminate.
Qed.

Lemma wmod_mul_does_not_hold: ~ forall sz (a b: word sz),
    b <> $0 ->
    (a ^* b) ^% b = $0.
Proof.
  intro C.
  specialize (C 4 $6 $5).
  match type of C with (?A -> _) => assert A by (intro; discriminate) end.
  specialize (C H).
  cbv in C.
  discriminate.
Qed.

Lemma wmult_plus_distr_l: forall (sz : nat) (x y z : word sz),
    z ^* (x ^+ y) = z ^* x ^+ z ^* y.
Proof.
  intros. rewrite! (wmult_comm z).
  apply wmult_plus_distr.
Qed.

Lemma wmod_same: forall sz (a: word sz), a ^% a = $0.
Proof.
  intros. destruct (weq a $0).
  - subst a. rewrite wmod_0_r in *. reflexivity.
  - unfold wmod, wordBin. apply wordToN_neq_0 in n. rewrite N.mod_same by assumption.
    apply NToWord_0.
Qed.

Lemma wmod_0_l: forall sz (m: word sz),
    $0 ^% m = $0.
Proof.
  intros. unfold wmod, wordBin.
  rewrite wordToN_0.
  destruct (N.eq_dec (wordToN m) 0%N).
  - rewrite e. change (0 mod 0)%N with 0%N. apply NToWord_0.
  - rewrite N.mod_0_l by assumption. apply NToWord_0.
Qed.

Lemma wmod_plus_distr: forall sz (a b m: word sz),
    (exists k, (wordToN m * k)%N = Npow2 sz) ->
    (a ^+ b) ^% m = ((a ^% m) ^+ (b ^% m)) ^% m.
Proof.
  intros. destruct H as [k E].
  assert (wordToN m <> 0%N) as H. {
    intro C. rewrite C in E. simpl in E. symmetry in E.
    apply Npow2_not_zero in E.
    assumption.
  }
  unfold wplus, wmod, wordBin.
  pose proof (wordToN_bound a). remember (wordToN a) as c. clear Heqc a.
  pose proof (wordToN_bound b). remember (wordToN b) as d. clear Heqd b.
  pose proof (wordToN_bound m). remember (wordToN m) as n. clear Heqn m.
  pose proof (N.mod_upper_bound c n H).
  pose proof (N.mod_upper_bound d n H).
  rewrite (@wordToN_NToWord_2 sz (c mod n)) by nomega.
  rewrite (@wordToN_NToWord_2 sz (d mod n)) by nomega.
  repeat match goal with
  | |- context [wordToN (NToWord ?sz ?n)] =>
    let k := fresh "k" in
    let E := fresh "E" in
    let B := fresh "B" in
    destruct (wordToN_NToWord sz n) as [ k [E B] ];
    rewrite E in *; clear E
  end.
  rewrite <- E in *.
  rewrite <- Nminus_mod_idemp_r by assumption.
  rewrite <- (@Nminus_mod_idemp_r (c mod n + d mod n)) by assumption.
  rewrite (N.mul_comm n k).
  do 2 rewrite N.mul_assoc.
  do 2 rewrite N.mod_mul by assumption.
  do 2 rewrite N.sub_0_r.
  f_equal.
  apply N.add_mod.
  assumption.
Qed.

Lemma wmod_mul: forall sz (a b: word sz),
    (exists k, (wordToN b * k)%N = Npow2 sz) ->
    (a ^* b) ^% b = $0.
Proof.
  intros. destruct H as [k E].
  assert (wordToN b <> 0%N) as H. {
    intro C. rewrite C in E. simpl in E. symmetry in E.
    apply Npow2_not_zero in E.
    assumption.
  }
  unfold wmult, wmod, wordBin.
  pose proof (wordToN_bound a). remember (wordToN a) as c. clear Heqc a.
  pose proof (wordToN_bound b). remember (wordToN b) as d. clear Heqd b.
  pose proof (N.mod_upper_bound c d H).
  repeat match goal with
  | |- context [wordToN (NToWord ?sz ?n)] =>
    let k := fresh "k" in
    let E := fresh "E" in
    let B := fresh "B" in
    destruct (wordToN_NToWord sz n) as [ k [E B] ];
    rewrite E in *; clear E
  end.
  rewrite <- E in *.
  rewrite <- Nminus_mod_idemp_r by assumption.
  rewrite (N.mul_comm d k).
  rewrite N.mul_assoc.
  rewrite N.mod_mul by assumption.
  rewrite N.sub_0_r.
  rewrite N.mul_mod by assumption.
  rewrite N.mod_same by assumption.
  rewrite N.mul_0_r.
  rewrite N.mod_0_l by assumption.
  apply NToWord_0.
Qed.

Local Close Scope nat.
Close Scope word_scope.
