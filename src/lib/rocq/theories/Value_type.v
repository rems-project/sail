Require Extraction.

Set Extraction KeepSingleton.
Set Extraction Output Directory ".".

From Stdlib Require Import Bool.
From Stdlib Require Import String.
From Stdlib Require Import ZArith.
From Stdlib Require Import QArith.
From Stdlib Require Import OrderedType.
From Stdlib Require Import RelationClasses.

From Stdlib Require ExtrOcamlBasic.
From Stdlib Require ExtrOcamlNatBigInt.
From Stdlib Require ExtrOcamlNativeString.
From Stdlib Require ExtrOcamlZBigInt.

Require Import Bit.
Require Import Ast.
Require Import IdUtil.

Import ListNotations.

Definition bit_eqb (lhs rhs : bit) : bool :=
  match (lhs, rhs) with
  | (B0, B0) => true
  | (B1, B1) => true
  | _ => false
  end.

Theorem bit_eqb_refl : forall b, bit_eqb b b = true.
Proof.
  destruct b; reflexivity.
Qed.

Fixpoint list_eqb {A} (pred : A -> A -> bool) (lhs rhs : list A) : bool :=
  match (lhs, rhs) with
  | ([], []) => true
  | ([], _) => false
  | (_, []) => false
  | (x :: xs, y :: ys) => pred x y && list_eqb pred xs ys
  end.

Lemma list_eqb_eq_right : forall A (pred : A -> A -> bool) lhs rhs,
  (forall x y, In x lhs -> pred x y = true -> x = y) -> list_eqb pred lhs rhs = true -> lhs = rhs.
Proof.
  intros A pred lhs rhs H.
  revert rhs.
  induction lhs as [| l_hd l_tl].
  - destruct rhs; easy.
  - destruct rhs as [| r_hd r_tl].
    + easy.
    + cbn.
      rewrite andb_true_iff.
      intro B.
      destruct B as (B1 & B2).
      rewrite (H l_hd r_hd (in_eq l_hd l_tl) B1).
      rewrite (fun P => IHl_tl P r_tl B2).
      reflexivity.
      intros x y In_x_l_tl XY.
      assert (In x (l_hd :: l_tl)) as In_x_l.
      apply in_cons; trivial.
      apply (H _ _ In_x_l XY).
Qed.

Theorem list_eqb_refl: forall A (pred : A -> A -> bool) xs, (forall x, In x xs -> pred x x = true) -> list_eqb pred xs xs = true.
Proof.
  intros A pred xs H.
  induction xs as [| x xs].
  - reflexivity.
  - cbn.
    rewrite (H _ (in_eq _ _)).
    rewrite IHxs.
    reflexivity.
    intros ? In_xs.
    apply (H _ (in_cons _ _ _ In_xs)).
Qed.

Theorem list_eqb_eq : forall A (pred : A -> A -> bool) lhs rhs,
  (forall x y, In x lhs -> pred x y = true <-> x = y) -> list_eqb pred lhs rhs = true <-> lhs = rhs.
Proof.
  intros A pred lhs rhs H.
  split.
  - apply (list_eqb_eq_right A pred lhs rhs (fun x y In => proj1 (H x y In))).
  - intro E.
    rewrite E in *.
    apply list_eqb_refl.
    intros x In_rhs.
    apply (proj2 (H x x In_rhs) eq_refl).
Qed.

(* A value is fully defined if it contains no unknown values *)
Fixpoint fully_defined (v : value) : bool :=
  match v with
  | V_vector vs | V_list vs | V_ctor _ vs => forallb fully_defined vs
  | V_record fields => forallb (fun '(_, v) => fully_defined v) fields
  | V_unknown => false
  | _ => true
  end.

Declare Scope Value_scope.
Delimit Scope Value_scope with value.

(* Induction rule for values, needed as they contain nested lists of values *)
Section value_ind.
  Variables (P : value -> Prop)
            (H_bitvector : forall bv, P (V_bitvector bv))
            (H_vector : forall vs, Forall P vs -> P (V_vector vs))
            (H_list : forall vs, Forall P vs -> P (V_list vs))
            (H_int : forall i, P (V_int i))
            (H_real : forall r, P (V_real r))
            (H_bool : forall b, P (V_bool b))
            (H_tuple : forall vs, Forall P vs -> P (V_tuple vs))
            (H_unit : P V_unit)
            (H_string : forall str, P (V_string str))
            (H_ref : forall id, P (V_ref id))
            (H_member : forall id, P (V_member id))
            (H_ctor : forall id vs, Forall P vs -> P (V_ctor id vs))
            (H_record : forall fields, Forall (fun f => P (snd f)) fields -> P (V_record fields))
            (H_unknown : P V_unknown).

  Fixpoint value_ind v : P v.
  Proof using All.
    destruct v.
    - apply H_bitvector.
    - apply H_vector.
      induction l.
      + trivial.
      + rewrite Forall_cons_iff. easy.
    - apply H_list.
      induction l.
      + trivial.
      + rewrite Forall_cons_iff. easy.
    - apply H_int.
    - apply H_real.
    - apply H_bool.
    - apply H_tuple.
      induction l.
      + trivial.
      + rewrite Forall_cons_iff. easy.
    - apply H_unit.
    - apply H_string.
    - apply H_ref.
    - apply H_member.
    - apply H_ctor.
      induction l.
      + trivial.
      + rewrite Forall_cons_iff. easy.
    - apply H_record.
      induction l.
      + trivial.
      + rewrite Forall_cons_iff. easy.
    - apply H_unknown.
  Qed.
End value_ind.

Fixpoint value_cmp (f : value -> bool) (lhs rhs : value) : bool :=
  match (lhs, rhs) with
  | (V_bitvector l_bv, V_bitvector r_bv) => list_eqb bit_eqb l_bv r_bv
  | (V_vector l_v, V_vector r_v) => list_eqb (value_cmp f) l_v r_v
  | (V_list l_xs, V_list r_ys) => list_eqb (value_cmp f) l_xs r_ys
  | (V_int l, V_int r) => (l =? r)%Z
  | (V_real l, V_real r) => QArith_base.Qeq_bool l r
  | (V_bool l, V_bool r) => Bool.eqb l r
  | (V_tuple l_v, V_tuple r_v) => list_eqb (value_cmp f) l_v r_v
  | (V_unit, V_unit) => true
  | (V_string l, V_string r) => (l =? r)%string
  | (V_ref l, V_ref r) => id_eqb l r
  | (V_member l, V_member r) => id_eqb l r
  | (V_ctor l_id l_v, V_ctor r_id r_v) => id_eqb l_id r_id && list_eqb (value_cmp f) l_v r_v
  | (V_record l_fields, V_record r_fields) =>
      list_eqb (fun '(l_id, l_v) '(r_id, r_v) => id_eqb l_id r_id && value_cmp f l_v r_v) l_fields r_fields
  | (v, V_unknown) => f v
  | _ => false
  end.

Definition is_unknown (v : value) : bool :=
  match v with
  | V_unknown => true
  | _ => false
  end.

Definition value_eqb (lhs rhs : value) : bool := value_cmp is_unknown lhs rhs.
Definition value_leb (lhs rhs : value) : bool := value_cmp (fun _ => true) lhs rhs.

Infix "=?" := value_eqb (at level 70, no associativity) : Value_scope.
Infix "<=?" := value_leb (at level 70, no associativity) : Value_scope.

Definition value_ltb (lhs rhs : value) : bool := (lhs <=? rhs)%value && negb (lhs =? rhs)%value.

Infix "<?" := value_ltb (at level 70, no associativity) : Value_scope.

Theorem forall_in : forall A P (x : A) xs, Forall P xs -> In x xs -> P x.
Proof.
  induction xs.
  - easy.
  - cbn.
    rewrite Forall_cons_iff.
    intros.
    destruct H0.
    + rewrite <- H0. easy.
    + apply (fun Q => IHxs Q H0). easy.
Qed.

Theorem list_eqb_sym: forall A (eq : A -> A -> bool) xs ys, (forall x y, eq x y = eq y x) -> list_eqb eq xs ys = true -> list_eqb eq ys xs = true.
Proof.
  intros A eq xs ys eq_sym.
  revert ys.
  induction xs as [| x xs].
  - destruct ys as [| y ys]; trivial.
  - destruct ys as [| y ys].
    + trivial.
    + cbn.
      rewrite andb_true_iff.
      intros H.
      destruct H as (H1 & H2).
      rewrite eq_sym.
      rewrite H1.
      rewrite IHxs.
      * reflexivity.
      * apply H2.
Qed.

Theorem list_eqb_comm: forall A (eq : A -> A -> bool) xs ys, (forall x y, eq x y = eq y x) -> list_eqb eq xs ys = list_eqb eq ys xs.
Proof.
  intros A eq xs ys eq_sym.
  apply eq_true_iff_eq.
  split.
  apply (list_eqb_sym A eq xs ys eq_sym).
  apply (list_eqb_sym A eq ys xs eq_sym).
Qed.

Theorem list_eqb_comm_in: forall A (eq : A -> A -> bool) xs ys, (forall x y, In x xs -> eq x y = eq y x) -> list_eqb eq xs ys = list_eqb eq ys xs.
Proof.
  intros A eq xs ys eq_sym.
  revert ys.
  induction xs as [| x xs].
  - destruct ys as [| y ys]; trivial.
  - destruct ys as [| y ys].
    + trivial.
    + cbn.
      rewrite eq_sym.
      rewrite IHxs.
      reflexivity.
      intros x0 y0 x0_in.
      apply eq_sym.
      cbn.
      apply or_intror.
      trivial.
      cbn.
      apply or_introl.
      easy.
Qed.

Theorem list_eqb_trans_in : forall A (eq : A -> A -> bool) xs ys zs,
  (forall x y z, In y ys -> eq x y = true -> eq y z = true -> eq x z = true) ->
  list_eqb eq xs ys = true ->
  list_eqb eq ys zs = true ->
  list_eqb eq xs zs = true.
Proof.
  intros A eq xs ys zs eq_sym.
  revert xs zs.
  induction ys as [| y ys].
  + intros xs zs.
    destruct zs.
    - trivial.
    - cbn. easy.
  + destruct zs as [| z zs].
    - cbn. easy.
    - destruct xs as [| x xs].
      * cbn. easy.
      * cbn.
        intros XY YZ.
        apply andb_true_iff in XY.
        apply andb_true_iff in YZ.
        destruct XY as (XY1 & XY2).
        destruct YZ as (YZ1 & YZ2).
        assert (eq x z = true) as Eq_xz.
        apply (fun P => eq_sym x y z P XY1 YZ1).
        cbn.
        auto.
        rewrite Eq_xz.
        rewrite (fun P => IHys P xs zs XY2 YZ2).
        reflexivity.
        intros x' y' z' In_y' Eq_xy' Eq_yz'.
        apply (eq_sym x' y' z' (in_cons _ _ _ In_y') Eq_xy' Eq_yz').
Qed.

Theorem list_eqb_trans : forall A (eq : A -> A -> bool) xs ys zs,
  (forall x y z, eq x y = true -> eq y z = true -> eq x z = true) ->
  list_eqb eq xs ys = true ->
  list_eqb eq ys zs = true ->
  list_eqb eq xs zs = true.
Proof.
  intros A eq xs ys zs eq_sym XY YZ.
  apply (fun P => list_eqb_trans_in A eq xs ys zs P XY YZ).
  intros x y z ? ? ?.
  apply (eq_sym _ y _); assumption.
Qed.

Create HintDb sail.

Hint Immediate id_eqb_refl : sail.
Hint Immediate bit_eqb_refl : sail.
Hint Immediate Z.eqb_refl : sail.
Hint Immediate Qeq_bool_refl : sail.
Hint Immediate eqb_reflx : sail.
Hint Immediate String.eqb_refl : sail.
Hint Resolve list_eqb_refl : sail.
Hint Resolve Forall_cons_iff : sail.

Theorem value_cmp_refl : forall f v, f V_unknown = true -> value_cmp f v v = true.
Proof.
  intros f v U.
  induction v using value_ind.
  (* Solve all the trivial non-recursive cases *)
  all: try (unfold value_cmp; solve [auto with sail]).
  (* Handle any cases where the value just contains a list of other values *)
  all: try (
    change (list_eqb (value_cmp f) vs vs = true);
    induction vs as [| v vs];
    match goal with
    | |- list_eqb (value_cmp _) [] [] = true => reflexivity
    | _ =>
        apply Forall_cons_iff in H;
        destruct H as (H1 & H2);
        cbn;
        rewrite H1;
        rewrite IHvs;
        reflexivity || apply H2
    end
  ).
  - induction vs as [| v vs].
    + change (id_eqb id id && true = true).
      solve [auto with sail bool].
    + apply Forall_cons_iff in H.
      destruct H as (H1 & H2).
      change (id_eqb id id && (value_cmp f v v && list_eqb (value_cmp f) vs vs) = true).
      rewrite H1.
      change (Forall (fun v : value => value_cmp f v v = true) vs ->
              id_eqb id id && list_eqb (value_cmp f) vs vs = true) in IHvs.
      auto with sail bool.
  - induction fields as [| fld flds].
    + reflexivity.
    + apply Forall_cons_iff in H.
      destruct H as (H1 & H2).
      destruct fld as [id v].
      change (id_eqb id id &&
              value_cmp f v v &&
              list_eqb (fun '(l_id, l_v) '(r_id, r_v) => andb (id_eqb l_id r_id) (value_cmp f l_v r_v)) flds flds = true).
      auto with sail bool.
Qed.

Theorem value_eqb_refl : forall v, (v =? v)%value = true.
Proof.
  intros.
  unfold value_eqb.
  apply (value_cmp_refl is_unknown).
  cbn.
  reflexivity.
Qed.

Theorem value_leb_refl : forall v, (v <=? v)%value = true.
Proof.
  intros.
  unfold value_leb.
  apply value_cmp_refl.
  reflexivity.
Qed.

Theorem value_ltb_not_eqb : forall x y, (x <? y)%value = true -> (x =? y)%value = false.
Proof.
  intros x y x_ltb_y.
  unfold value_ltb in x_ltb_y.
  rewrite andb_true_iff, negb_true_iff in x_ltb_y.
  tauto.
Qed.

Theorem value_eqb_comm : forall v1 v2, (v1 =? v2)%value = (v2 =? v1)%value.
Proof.
  intros v1.
  induction v1 using value_ind.
  - intros v2.
    induction v2 using value_ind; try reflexivity.
    cbn.
    apply list_eqb_comm.
    intros x y; destruct x; destruct y; reflexivity.
  - intros v2.
    induction v2 using value_ind; try reflexivity.
    cbn.
    apply list_eqb_comm_in.
    intros.
    destruct vs.
    cbn in H1.
    easy.
    apply (forall_in _ _ _ _ H H1).
  - intros v2.
    induction v2 using value_ind; try reflexivity.
    cbn.
    apply list_eqb_comm_in.
    intros.
    destruct vs.
    cbn in H1.
    easy.
    apply (forall_in _ _ _ _ H H1).
  - destruct v2; try reflexivity.
    cbn.
    apply Z.eqb_sym.
  - destruct v2; try reflexivity.
    cbn.
    apply Qeq_bool_comm.
  - destruct v2; try reflexivity.
    cbn.
    destruct b; destruct b0; reflexivity.
  - intros v2.
    induction v2 using value_ind; try reflexivity.
    cbn.
    apply list_eqb_comm_in.
    intros.
    destruct vs.
    cbn in H1.
    easy.
    apply (forall_in _ _ _ _ H H1).
  - destruct v2; try reflexivity.
  - destruct v2; try reflexivity.
    cbn.
    apply String.eqb_sym.
  - destruct v2; try reflexivity.
    unfold value_eqb.
    destruct id as [x_aux ?].
    destruct i as [y_aux ?].
    destruct x_aux as [| | x_s | x_s]; destruct y_aux as [| | y_s | y_s]; cbn; try trivial; rewrite String.eqb_sym; easy.
  - destruct v2; try reflexivity.
    unfold value_eqb.
    destruct id as [x_aux ?].
    destruct i as [y_aux ?].
    destruct x_aux as [| | x_s | x_s]; destruct y_aux as [| | y_s | y_s]; cbn; try trivial; rewrite String.eqb_sym; easy.
  - intros v2.
    induction v2 using value_ind; try reflexivity.
    change (id_eqb id id0 && list_eqb value_eqb vs vs0 = id_eqb id0 id && list_eqb value_eqb vs0 vs).
    assert (id_eqb id id0 = id_eqb id0 id).
    destruct id as [x_aux ?].
    destruct id0 as [y_aux ?].
    destruct x_aux as [| | x_s | x_s]; destruct y_aux as [| | y_s | y_s]; cbn; try trivial; rewrite String.eqb_sym; easy.
    rewrite H1.
    assert (list_eqb value_eqb vs vs0 = list_eqb value_eqb vs0 vs).
    cbn.
    apply list_eqb_comm_in.
    intros.
    destruct vs.
    cbn in H1.
    easy.
    apply (forall_in _ _ _ _ H H2).
    rewrite H2.
    reflexivity.
  - intros v2.
    induction v2 using value_ind; try reflexivity.
    change (list_eqb (fun '(l_id, l_v) '(r_id, r_v) => andb (id_eqb l_id r_id) (value_eqb l_v r_v)) fields fields0 =
            list_eqb (fun '(l_id, l_v) '(r_id, r_v) => andb (id_eqb l_id r_id) (value_eqb l_v r_v)) fields0 fields).
    apply list_eqb_comm_in.
    intros.
    destruct fields.
    cbn in H1.
    easy.
    destruct x.
    destruct y.
    assert (id_eqb i i0 = id_eqb i0 i).
    destruct i as [x_aux ?].
    destruct i0 as [y_aux ?].
    destruct x_aux as [| | x_s | x_s]; destruct y_aux as [| | y_s | y_s]; cbn; try trivial; rewrite String.eqb_sym; easy.
    rewrite H2.
    destruct p.
    assert (value_eqb v v0 = value_eqb v0 v).
    apply Forall_cons_iff in H.
    destruct H.
    cbn in H.
    cbn in H1.
    destruct H1.
    rewrite pair_equal_spec in H1.
    destruct H1.
    rewrite H4 in H.
    apply H.
    apply (forall_in _ _ _ _ H3 H1 v0).
    rewrite H3.
    reflexivity.
  - intros v2.
    destruct v2; trivial.
Qed.

Theorem value_cmp_ctor : forall f lid lvs rid rvs, value_cmp f (V_ctor lid lvs) (V_ctor rid rvs) = true <-> (id_eqb lid rid = true /\ list_eqb (value_cmp f) lvs rvs = true).
Proof.
  split; cbn in *; rewrite andb_true_iff in *; easy.
Qed.

Theorem value_cmp_trans : forall f x y z (F : (forall x, f x = true) \/ f = is_unknown \/ (forall x, x <> V_unknown -> f x = true)),
  value_cmp f x y = true ->
  value_cmp f y z = true ->
  value_cmp f x z = true.
Proof.
  intros f x y z F.
  revert x z.
  induction y as [ ybv | ys | ys | yi | yr | yb | ys | | ystr | yid | yid | yid ys | yfields | ] using value_ind.
  all: intro x; destruct x as [ xbv | xs | xs | xi | xr | xb | xs | | xstr | xid | xid | xid xs | xfields | ]; try easy.
  all: intro z; destruct z as [ zbv | zs | zs | zi | zr | zb | zs | | zstr | zid | zid | zid zs | zfields | ]; try easy.
  all: intros L R.
  all: try (
    unfold value_cmp in *;
    destruct F as [LE | [EQ | LT]];
    match goal with
    | [ LT : (forall (x : value), x <> V_unknown -> ?f x = true) |- ?f ?V = true ] => apply (LT V); discriminate
    | [ LE : (forall (x : value), ?f x = true) |- ?f ?V = true ] => apply (LE V)
    | [ EQ : ?f = is_unknown |- _ ] => rewrite EQ in *; cbn in *; assumption
    end
  ).
  - cbn in *.
    apply (fun P => list_eqb_trans _ bit_eqb xbv ybv zbv P L R).
    intros x y z; destruct x; destruct y; destruct z; easy.
  - cbn in *.
    apply (fun P => list_eqb_trans_in _ _ xs ys zs P L R).
    intros x y z In_y XY YZ.
    apply (forall_in _ _ _ _ H In_y); easy.
  - cbn in *.
    apply (fun P => list_eqb_trans_in _ _ xs ys zs P L R).
    intros x y z In_y XY YZ.
    apply (forall_in _ _ _ _ H In_y); easy.
  - cbn in *.
    rewrite Z.eqb_eq in *.
    apply (eq_trans L R).
  - cbn in *.
    apply (Qeq_bool_trans _ _ _ L R).
  - cbn in *.
    rewrite eqb_true_iff in *.
    apply (eq_trans L R).
  - cbn in *.
    apply (fun P => list_eqb_trans_in _ _ xs ys zs P L R).
    intros x y z In_y XY YZ.
    apply (forall_in _ _ _ _ H In_y); easy.
  - cbn in *.
    rewrite String.eqb_eq in *.
    apply (eq_trans L R).
  - apply (id_eqb_trans _ _ _ L R).
  - apply (id_eqb_trans _ _ _ L R).
  - rewrite value_cmp_ctor in *.
    destruct L as (Lid & Ll).
    destruct R as (Rid & Rl).
    split.
    + apply (id_eqb_trans _ yid _); assumption.
    + apply (list_eqb_trans_in _ _ _ ys _); try assumption.
      intros x y z In_y XY YZ.
      apply (forall_in _ _ _ _ H In_y); easy.
  - apply (list_eqb_trans_in _ _ _ yfields _); try assumption.
    intros x y z In_y XY YZ.
    destruct x as [xid xv].
    destruct y as [yid yv].
    destruct z as [zid zv].
    rewrite andb_true_iff in *.
    destruct XY as (XY1 & XY2).
    destruct YZ as (YZ1 & YZ2).
    split.
    + apply (id_eqb_trans _ yid _); assumption.
    + apply (forall_in _ _ (yid, yv) yfields H In_y); assumption.
Qed.

Theorem value_eqb_trans : forall x y z, (x =? y)%value = true -> (y =? z)%value = true -> (x =? z)%value = true.
Proof.
  intros x y z.
  apply value_cmp_trans.
  auto.
Qed.

Theorem value_leb_trans : forall x y z, (x <=? y)%value = true -> (y <=? z)%value = true -> (x <=? z)%value = true.
Proof.
  intros x y z.
  apply value_cmp_trans.
  auto.
Qed.

Theorem value_eqb_leb : forall x y, (x =? y)%value = true -> (x <=? y)%value = true.
Proof.
  intros x y.
  revert x.
  induction y as [ ybv | ys | ys | yi | yr | yb | ys | | ystr | yid | yid | yid ys | ys | ] using value_ind.
  all: intro x; destruct x as [ xbv | xs | xs | xi | xr | xb | xs | | xstr | xid | xid | xid xs | xs | ]; try easy.
  all: unfold value_leb, value_eqb; cbn iota delta - [id_eqb] zeta; try easy.
  all:
    revert H; revert xs;
    induction ys as [ | y ys]; intros xs H; destruct xs as [| x xs]; try easy;
    lazymatch goal with
    | x : _ * _, y : _ * _ |- _ => destruct x; destruct y
    | _ => idtac
    end;
    cbn iota delta - [id_eqb] zeta;
    repeat rewrite andb_true_iff;
    repeat split;
    lazymatch goal with
    | |- id_eqb _ _ = true => tauto
    | |- list_eqb _ _ _ = true =>
        assert (IH := IHys xs (Forall_inv_tail H));
        repeat rewrite andb_true_iff in IH;
        tauto
    | |- value_cmp _ _ _ = true =>
        apply (Forall_inv H); unfold value_eqb; tauto
    end.
Qed.

Theorem value_ltb_leb : forall x y, (x <? y)%value = true -> (x <=? y)%value = true.
Proof.
  intros x y H.
  unfold value_ltb in H.
  rewrite andb_true_iff in H.
  tauto.
Qed.

Fixpoint zip {A : Set} (xs ys : list A) : list (A * A) :=
  match (xs, ys) with
  | (x :: xs, y :: ys) => (x, y) :: zip xs ys
  | ([], _) => []
  | (_, []) => []
  end.

Theorem list_eqb_false : forall [A : Set] f (xs ys : list A),
  length xs = length ys -> list_eqb f xs ys = false <-> Exists (fun '(x, y) => f x y = false) (zip xs ys).
Proof.
  intros A f xs.
  induction xs as [| x xs]; intro ys; destruct ys as [| y ys]; try discriminate.
  - cbn. rewrite Exists_nil. easy.
  - intros Same_length.
    cbn.
    rewrite Exists_cons, andb_false_iff.
    apply or_iff_compat_l.
    apply IHxs.
    cbn in Same_length.
    apply (Nat.succ_inj _ _ Same_length).
Qed.

Theorem in_app_split : forall [A : Set] (x : A) xs, In x xs -> exists ys zs, xs = ys ++ (x :: zs).
Proof.
  intros A x xs x_in_xs.
  induction xs as [| y ys].
  - cbn in x_in_xs.
    contradiction.
  - apply in_inv in x_in_xs.
    destruct x_in_xs as [y_eq_x | x_in_ys].
    + rewrite y_eq_x.
      exists [].
      exists ys.
      reflexivity.
    + apply IHys in x_in_ys as H.
      destruct H as [zs].
      destruct H as [ws].
      exists (y :: zs).
      exists ws.
      rewrite H.
      reflexivity.
Qed.

Fixpoint drop {A : Set} (n : nat) (xs : list A) : list A :=
  match (n, xs) with
  | (0%nat, xs) => xs
  | (S m, []) => []
  | (S m, _ :: xs) => drop m xs
  end.

Fixpoint take {A : Set} (n : nat) (xs : list A) : list A :=
  match (n, xs) with
  | (0%nat, xs) => []
  | (S m, []) => []
  | (S m, x :: xs) => x :: take m xs
  end.

Theorem list_eqb_false_app_r : forall [A : Set] f (xs ys zs : list A), list_eqb f (drop (length ys) xs) zs = false -> list_eqb f xs (ys ++ zs) = false.
Proof.
  intros A f xs ys zs.
  revert xs zs.
  induction ys as [| y ys]; intros xs zs; destruct xs as [| x xs]; destruct zs as [| z zs]; try easy.
  - cbn.
    rewrite andb_false_iff.
    intros H.
    apply or_intror.
    apply (IHys _ _ H).
  - cbn.
    rewrite andb_false_iff.
    intros H.
    apply or_intror.
    apply (IHys _ _ H).
Qed.

Theorem map_fst_zip : forall [A : Set] (xs ys : list A), length xs = length ys -> map fst (zip xs ys) = xs.
Proof.
  intros A xs.
  induction xs as [| x xs]; intro ys; destruct ys as [| y ys]; try easy.
  cbn.
  intro Same_length.
  assert (H := IHxs _ (Nat.succ_inj _ _ Same_length)).
  rewrite <- H at 2.
  reflexivity.
Qed.

Theorem map_snd_zip : forall [A : Set] (xs ys : list A), length xs = length ys -> map snd (zip xs ys) = ys.
Proof.
  intros A xs.
  induction xs as [| x xs]; intro ys; destruct ys as [| y ys]; try easy.
  cbn.
  intro Same_length.
  assert (H := IHxs _ (Nat.succ_inj _ _ Same_length)).
  rewrite <- H at 2.
  reflexivity.
Qed.

Theorem zip_fst_snd : forall [A : Set] (xs ys: list A) zs,
  length xs = length ys ->
  zip xs ys = zs <-> xs = List.map fst zs /\ ys = List.map snd zs.
Proof.
  intros A xs ys zs.
  revert xs ys.
  induction zs as [| z zs]; intros xs ys; destruct xs as [| x xs]; destruct ys as [| y ys]; try easy.
  cbn.
  intro Same_length.
  assert (H := IHzs _ _ (Nat.succ_inj _ _ Same_length)).
  split.
  - intros L.
    injection L; intros L1 L2; rewrite <- L1; rewrite <- L2; cbn.
    rewrite (map_fst_zip _ _ (Nat.succ_inj _ _ Same_length)).
    rewrite (map_snd_zip _ _ (Nat.succ_inj _ _ Same_length)).
    easy.
  - intros L.
    destruct z as (x', y').
    cbn in L.
    destruct L as (L1 & L2).
    injection L1; intros L1_1 L1_2.
    injection L2; intros L2_1 L2_2.
    destruct H as [_ H].
    rewrite (H (conj L1_1 L2_1)), L1_2, L2_2.
    reflexivity.
Qed.

Theorem value_ltb_is_leb : forall x y, (x <? y)%value = true -> (x <=? y)%value = true.
Proof.
  intros x y.
  revert x.
  induction y as [ ybv | ys | ys | yi | yr | yb | ys | | ystr | yid | yid | yid ys | yfields | ] using value_ind.
  all: intro x; destruct x as [ xbv | xs | xs | xi | xr | xb | xs | | xstr | xid | xid | xid xs | xfields | ]; try easy.
  all: unfold value_ltb; cbn beta delta - [id_eqb] iota; rewrite andb_true_iff; easy.
Qed.

Theorem app_cons_in : forall [A : Set] (x : A) xs ys zs, xs = ys ++ (x :: zs) -> In x xs.
Proof.
  intros A x xs.
  induction xs as [| w ws]; intros ys zs H.
  - assert (NH := app_cons_not_nil ys zs x).
    tauto.
  - destruct ys as [| y ys].
    + rewrite app_nil_l in H.
      injection H; intros _ wx.
      rewrite wx.
      apply in_eq.
    + apply in_cons.
      apply (IHws ys zs).
      rewrite <- app_comm_cons in H.
      injection H.
      tauto.
Qed.

Theorem list_eqb_app : forall [A : Set] f (xs ys zs ws : list A),
  length xs = length zs ->
  list_eqb f (xs ++ ys) (zs ++ ws) = true ->
  list_eqb f ys ws = true.
Proof.
  intros A f xs ys zs ws.
  revert ys zs ws.
  induction xs as [| x xs]; intros ys zs ws; destruct zs as [| z zs]; try easy.
  cbn.
  intro Same_length.
  assert (H := IHxs ys zs ws (Nat.succ_inj _ _ Same_length)).
  rewrite andb_true_iff.
  tauto.
Qed.

Theorem take_drop_app_h : forall [A : Set] n (xs ys : list A), xs ++ ys = take n xs ++ drop n xs ++ ys.
Proof with reflexivity.
  intros A n.
  induction n; intros xs ys.
  - cbn...
  - destruct xs as [| x xs].
    + cbn...
    + cbn.
      rewrite IHn at 1...
Qed.

Theorem take_drop_app : forall [A : Set] n (xs : list A), xs = take n xs ++ drop n xs.
Proof.
  intros A n xs.
  assert (H := take_drop_app_h n xs []).
  repeat rewrite app_nil_r in H.
  assumption.
Qed.

Theorem take_length : forall [A : Set] n (xs : list A), (n <= length xs)%nat -> length (take n xs) = n.
Proof.
  intros A n.
  induction n; intros xs H.
  - cbn. reflexivity.
  - destruct xs as [| x xs].
    + cbn in *.
      assert (C := Nat.nle_succ_0 n).
      contradiction.
    + cbn in *.
      apply eq_S.
      apply (IHn _ (le_S_n _ _ H)).
Qed.

Theorem list_eqb_same_length : forall [A : Set] f (xs ys : list A), list_eqb f xs ys = true -> length xs = length ys.
Proof.
  intros A f xs.
  induction xs as [| x xs]; intros ys; destruct ys as [| y ys]; try easy.
  cbn.
  rewrite andb_true_iff.
  intros.
  apply eq_S.
  apply IHxs.
  tauto.
Qed.

Theorem value_ltb_trans_h : forall x y z, (x <=? y)%value = true -> (y <? z)%value = true -> (x =? z)%value = false.
Proof.
  intros x y z.
  revert x z.
  induction y as [ ybv | ys | ys | yi | yr | yb | ys | | ystr | yid | yid | yid ys | ys | ] using value_ind.
  all: intro x; destruct x as [ xbv | xs | xs | xi | xr | xb | xs | | xstr | xid | xid | xid xs | xs | ]; try easy.
  all: intro z; destruct z as [ zbv | zs | zs | zi | zr | zb | zs | | zstr | zid | zid | zid zs | zs | ]; try easy.
  all: intros L R.
  (* Solve all the non-recursive cases *)
  all: try (unfold value_ltb in R; cbn in R; rewrite andb_negb_r in R; discriminate).
  all: try (
    unfold value_ltb in R;
    rewrite andb_true_iff, negb_true_iff in R;
    destruct R as (Rleb & Rneqb);
    cbn iota beta delta - [id_eqb] in Rleb, Rneqb, L;
    lazymatch goal with
    | Rleb : _ && _ = true |- _ => rewrite andb_true_iff in Rleb; destruct Rleb as (yz_id & Rleb)
    | _ => idtac
    end;
    lazymatch goal with
    | L : _ && _ = true |- _ => rewrite andb_true_iff in L; destruct L as (xy_id & L)
    | _ => idtac
    end;
    lazymatch goal with
    | Rneqb : _ && _ = false |- _ =>
        rewrite andb_false_iff in Rneqb;
        destruct Rneqb as [yz_id_neq | Rneqb];
        [> rewrite yz_id in yz_id_neq; easy | idtac]
    | _ => idtac
    end;
    assert (ys_zs_length := list_eqb_same_length _ _ _ Rleb);
    rewrite -> (list_eqb_false _ _ _ ys_zs_length) in Rneqb;
    apply Exists_exists in Rneqb;
    destruct Rneqb as [pair H0];
    destruct pair as (v_y, v_z);
    destruct H0;
    apply in_app_split in H0;
    destruct H0 as [yzs1 H0];
    destruct H0 as [yzs2 H0];
    rewrite (zip_fst_snd _ _ _ ys_zs_length) in H0;
    repeat rewrite map_app in H0;
    cbn in H0;
    destruct H0;
    cbn iota beta delta - [id_eqb];
    match goal with
    | |- id_eqb _ _ && _ = false => rewrite andb_false_iff; apply or_intror
    | _ => idtac
    end;
    rewrite H2;
    apply list_eqb_false_app_r;
    remember (drop (Datatypes.length (map snd yzs1)) xs) as xstl;
    destruct xstl; [reflexivity | idtac];
    cbn;
    apply andb_false_intro1;
    apply (forall_in _ _ v_y _ H (app_cons_in _ _ _ _ H0)); [
      assert (xs_ys_length := list_eqb_same_length _ _ _ L);
      assert (xs_zs_length := list_eqb_same_length _ _ _ Rleb);
      unfold value_leb;
      rewrite (take_drop_app (length (map snd yzs1)) xs), H0 in L;
      apply list_eqb_app in L; [
        rewrite <- Heqxstl in L;
        cbn in L;
        apply andb_true_iff in L;
        tauto
      | repeat rewrite length_map;
        rewrite take_length; [ reflexivity | idtac ];
        rewrite xs_ys_length, H0, length_app, length_map;
        apply Nat.le_add_r
      ]
    | idtac
    ];
    unfold value_ltb, value_leb, value_eqb;
    cbn in Rleb;
    rewrite H0, H2 in Rleb;
    apply list_eqb_app in Rleb;
    [
      cbn in Rleb;
      apply andb_true_iff in Rleb;
      apply andb_true_iff;
      split; [ tauto | rewrite negb_true_iff; assumption ]
    | repeat rewrite length_map;
      reflexivity
    ]
  ).
  -
    unfold value_ltb in R;
    rewrite andb_true_iff, negb_true_iff in R;
    destruct R as (Rleb & Rneqb);
    cbn iota beta delta - [id_eqb] in Rleb, Rneqb, L;
    lazymatch goal with
    | Rleb : _ && _ = true |- _ => rewrite andb_true_iff in Rleb; destruct Rleb as (yz_id & Rleb)
    | _ => idtac
    end;
    lazymatch goal with
    | L : _ && _ = true |- _ => rewrite andb_true_iff in L; destruct L as (xy_id & L)
    | _ => idtac
    end;
    lazymatch goal with
    | Rneqb : _ && _ = false |- _ =>
        rewrite andb_false_iff in Rneqb;
        destruct Rneqb as [yz_id_neq | Rneqb];
        [> rewrite yz_id in yz_id_neq; easy | idtac]
    | _ => idtac
    end.
    assert (ys_zs_length := list_eqb_same_length _ _ _ Rleb);
    rewrite -> (list_eqb_false _ _ _ ys_zs_length) in Rneqb;
    apply Exists_exists in Rneqb;
    destruct Rneqb as [pair H0];
    destruct pair as (v_y, v_z).
    lazymatch goal with
    | v_y : _ * _, v_z : _ * _ |- _ =>
      remember v_y as V;
      destruct v_y as (f_y, v_y'); destruct v_z as (f_z, v_z)
    | _ => idtac
    end.
    destruct H0;
    apply in_app_split in H0;
    destruct H0 as [yzs1 H0];
    destruct H0 as [yzs2 H0];
    rewrite (zip_fst_snd _ _ _ ys_zs_length) in H0;
    repeat rewrite map_app in H0;
    cbn in H0;
    destruct H0.
    cbn iota beta delta - [id_eqb].
    lazymatch goal with
    | |- id_eqb _ _ && _ = false => rewrite andb_false_iff; apply or_intror
    | _ => idtac
    end.
    rewrite H2;
    apply list_eqb_false_app_r;
    remember (drop (Datatypes.length (map snd yzs1)) xs) as xstl.
    destruct xstl as [| h_xstl t_xstl]; [reflexivity | idtac].
    lazymatch goal with
    | h_xstl : _ * _ |- _ => destruct h_xstl
    | _ => idtac
    end.
    cbn iota beta delta - [id_eqb] zeta.
    apply andb_false_intro1.
    apply andb_false_intro2.
    apply (forall_in _ _ V _ H (app_cons_in _ _ _ _ H0)); rewrite HeqV.
    + assert (xs_ys_length := list_eqb_same_length _ _ _ L);
      assert (xs_zs_length := list_eqb_same_length _ _ _ Rleb).
      unfold value_leb;
      rewrite (take_drop_app (length (map snd yzs1)) xs), H0 in L.
      apply list_eqb_app in L.
      *
        rewrite <- Heqxstl in L.
        cbn iota beta delta - [id_eqb] zeta in L.
        rewrite HeqV in L, H1.
        repeat rewrite andb_true_iff in L.
        cbn.
        tauto.
      * repeat rewrite length_map;
        rewrite take_length; [ reflexivity | idtac ];
        rewrite xs_ys_length, H0, length_app, length_map;
        apply Nat.le_add_r.
    + unfold value_ltb, value_leb, value_eqb;
      cbn iota beta delta - [id_eqb] zeta in Rleb.
      rewrite H0, H2 in Rleb.
      apply list_eqb_app in Rleb.
      * cbn iota beta delta - [id_eqb] zeta in Rleb.
        rewrite HeqV in H1, Rleb.
        repeat rewrite andb_true_iff in Rleb;
        apply andb_true_iff.
        split.
        **
          cbn.
          tauto.
        **
          rewrite negb_true_iff; cbn.
          rewrite andb_false_iff in H1.
          destruct H1.
          *** rewrite H1 in Rleb. easy.
          *** assumption.
      * repeat rewrite length_map.
        reflexivity.
Qed.

Theorem value_ltb_trans : forall x y z, (x <? y)%value = true -> (y <? z)%value = true -> (x <? z)%value = true.
Proof.
  intros x y z XY YZ.
  apply value_ltb_leb in XY.
  unfold value_ltb.
  rewrite andb_true_iff, negb_true_iff.
  split.
  - apply (value_leb_trans _ y _ XY (value_ltb_leb _ _ YZ)).
  - apply (value_ltb_trans_h _ y _ XY YZ).
Qed.

Theorem value_leb_antisym : forall x y, (x <=? y)%value = true -> (y <=? x)%value = true -> (x =? y)%value = true.
Proof.
  intros x.
  induction x as [ xbv | xs | xs | xi | xr | xb | xs | | xstr | xid | xid | xid xs | xfields | ] using value_ind.
  all: intros y.
  all: destruct y as [ ybv | ys | ys | yi | yr | yb | ys | | ystr | yid | yid | yid ys | yfields | ]; try easy.
  - revert H. revert xs.
    induction ys as [ | y ys]; intros xs H; destruct xs as [| x xs]; try easy.
    intros X_le_Y Y_le_X.
    cbn in *.
    rewrite andb_true_iff in *.
    destruct X_le_Y as (x_le_y & xs_le_ys).
    destruct Y_le_X as (y_le_x & ys_le_xs).
    split.
    + unfold value_eqb, value_leb in H.
      apply (forall_in _ _ x (x :: xs) H (in_eq _ _) y x_le_y y_le_x).
    + apply (IHys xs (Forall_inv_tail H) xs_le_ys ys_le_xs).
  - revert H. revert xs.
    induction ys as [ | y ys]; intros xs H; destruct xs as [| x xs]; try easy.
    intros X_le_Y Y_le_X.
    cbn in *.
    rewrite andb_true_iff in *.
    destruct X_le_Y as (x_le_y & xs_le_ys).
    destruct Y_le_X as (y_le_x & ys_le_xs).
    split.
    + unfold value_eqb, value_leb in H.
      apply (forall_in _ _ x (x :: xs) H (in_eq _ _) y x_le_y y_le_x).
    + apply (IHys xs (Forall_inv_tail H) xs_le_ys ys_le_xs).
  - revert H. revert xs.
    induction ys as [ | y ys]; intros xs H; destruct xs as [| x xs]; try easy.
    intros X_le_Y Y_le_X.
    cbn in *.
    rewrite andb_true_iff in *.
    destruct X_le_Y as (x_le_y & xs_le_ys).
    destruct Y_le_X as (y_le_x & ys_le_xs).
    split.
    + unfold value_eqb, value_leb in H.
      apply (forall_in _ _ x (x :: xs) H (in_eq _ _) y x_le_y y_le_x).
    + apply (IHys xs (Forall_inv_tail H) xs_le_ys ys_le_xs).
  - cbn beta delta - [id_eqb] iota.
    repeat rewrite andb_true_iff.
    intros X_le_Y Y_le_X.
    split.
    + easy.
    + destruct X_le_Y as (_ & xs_le_ys).
      destruct Y_le_X as (_ & ys_le_xs).
      revert H xs_le_ys ys_le_xs. revert xs.
      induction ys as [| y ys]; intros xs H; destruct xs as [|x xs]; try easy.
      intros X_le_Y Y_le_X.
      cbn in *.
      rewrite andb_true_iff in *.
      destruct X_le_Y as (x_le_y & xs_le_ys).
      destruct Y_le_X as (y_le_x & ys_le_xs).
      split.
      * unfold value_eqb, value_leb in H.
        apply (forall_in _ _ x (x :: xs) H (in_eq _ _) y x_le_y y_le_x).
      * apply (IHys xs (Forall_inv_tail H) xs_le_ys ys_le_xs).
  - cbn beta delta - [id_eqb] iota.
    revert H. revert xfields.
    induction yfields as [| y yfields]; intros xfields H; destruct xfields as [| x xfields]; try easy.
    intros X_le_Y Y_le_X.
    cbn beta delta - [id_eqb] iota in *.
    destruct x as (x_id, x_v).
    destruct y as (y_id, y_v).
    repeat rewrite andb_true_iff in *.
    destruct X_le_Y as (X_le_Y & xs_le_ys).
    destruct Y_le_X as (Y_le_X & ys_le_xs).
    split; try split; try easy.
    + destruct X_le_Y as (_ & x_le_y).
      destruct Y_le_X as (_ & y_le_x).
      unfold value_eqb, value_leb in H.
      apply (forall_in _ _ (x_id, x_v) (_ :: xfields) H (in_eq _ _) _ x_le_y y_le_x).
    + apply (IHyfields _ (Forall_inv_tail H) xs_le_ys ys_le_xs).
Qed.


Module Order.
  Definition eq (x y : value) : Prop := Is_true (value_eqb x y).

  Definition le (x y : value) : Prop := Is_true (value_leb x y).

  Instance eq_Equivalence : Equivalence eq.
  Proof.
    split.
    - intro x.
      unfold eq.
      apply Is_true_eq_left.
      apply (value_eqb_refl x).
    - intros x y H.
      unfold eq in *.
      apply Is_true_eq_left.
      apply Is_true_eq_true in H.
      rewrite (value_eqb_comm y x).
      assumption.
    - intros x y z H1 H2.
      unfold eq in *.
      apply Is_true_eq_left.
      apply Is_true_eq_true in H1.
      apply Is_true_eq_true in H2.
      apply (value_eqb_trans x y z H1 H2).
  Qed.

  Instance le_PreOrder : PreOrder le.
  Proof.
    split.
    - intro x.
      unfold eq.
      apply Is_true_eq_left.
      apply (value_leb_refl x).
    - intros x y z H1 H2.
      unfold eq in *.
      apply Is_true_eq_left.
      apply Is_true_eq_true in H1.
      apply Is_true_eq_true in H2.
      apply (value_leb_trans x y z H1 H2).
  Qed.

  Instance le_Antisymmetric : Antisymmetric value eq le.
  Proof.
    intros x y XY YX.
    apply Is_true_eq_left.
    apply Is_true_eq_true in XY.
    apply Is_true_eq_true in YX.
    apply (value_leb_antisym _ _ XY YX).
  Qed.

  Instance le_PartialOrder : PartialOrder eq le.
  Proof.
    intros x y.
    cbn.
    unfold flip.
    split.
    - intros H.
      apply Is_true_eq_true in H.
      unfold eq, le in *.
      split.
      + apply Is_true_eq_left.
        apply (value_eqb_leb _ _ H).
      + apply Is_true_eq_left.
        rewrite value_eqb_comm in H.
        apply (value_eqb_leb _ _ H).
    - intros H.
      apply antisymmetry; tauto.
  Qed.
End Order.

Module Primops.
  Definition gt_int (v1 : value) (v2 : value) : option value :=
    match (v1, v2) with
    | (V_int v1, V_int v2) => Some (V_bool (Z.gtb v1 v2))
    | _ => None
    end.

  Definition lt_int (v1 : value) (v2 : value) : option value :=
    match (v1, v2) with
    | (V_int v1, V_int v2) => Some (V_bool (Z.ltb v1 v2))
    | _ => None
    end.

  Definition add_int (v1 : value) (v2 : value) : option value :=
    match (v1, v2) with
    | (V_int v1, V_int v2) => Some (V_int (Z.add v1 v2))
    | _ => None
    end.

  Definition sub_int (v1 : value) (v2 : value) : option value :=
    match (v1, v2) with
    | (V_int v1, V_int v2) => Some (V_int (Z.sub v1 v2))
    | _ => None
    end.

  Definition zero_extend (bits : value) (n : value) : option value :=
    match (bits, n) with
    | (V_bitvector bitlist, V_int n) =>
      let len := List.length bitlist in
      if Z.ltb n (Z.of_nat len) then
        None
      else
        let extend := Nat.sub (Z.to_nat n) len in
        Some (V_bitvector (List.repeat B0 extend ++ bitlist))
    | _ => None
    end.
End Primops.
