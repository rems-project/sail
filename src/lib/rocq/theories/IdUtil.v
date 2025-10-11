From Stdlib Require Import Bool.
From Stdlib Require Import FMapList.
From Stdlib Require Import Lia.
From Stdlib Require Import String.

Require Import Ast.

Lemma string_ltb_trans : forall (s1 s2 s3 : String.string),
  String.ltb s1 s2 = true -> String.ltb s2 s3 = true -> String.ltb s1 s3 = true.
Proof.
  induction s1 as [| c1 s1 ];
  induction s2 as [| c2 s2 ];
  induction s3 as [| c3 s3 ].
  all: unfold String.ltb; cbn; try congruence.
  case_eq (Ascii.compare c1 c2); case_eq (Ascii.compare c2 c3); case_eq (Ascii.compare c1 c3); try congruence.
  all: unfold Ascii.compare.
  all: repeat rewrite BinNat.N.compare_eq_iff.
  all: repeat rewrite BinNat.N.compare_lt_iff.
  all: repeat rewrite BinNat.N.compare_gt_iff.
  all: try lia.
  repeat rewrite match_ltb_string.
  intros.
  apply (IHs1 s2); easy.
Qed.

Lemma match_ltb_string (s1 s2 : String.string) : (match String.compare s1 s2 with Lt => true | _ => false end = true) = (String.ltb s1 s2 = true).
Proof.
  reflexivity.
Qed.

Lemma string_ltb_not_eqb : forall s1 s2, String.ltb s1 s2 = true -> String.eqb s1 s2 = false.
Proof.
  induction s1 as [| c1 s1 ];
  induction s2 as [| c2 s2 ].
  all: unfold String.ltb; cbn; try congruence.
  case_eq (Ascii.compare c1 c2); case_eq (Ascii.eqb c1 c2).
  all: unfold Ascii.compare.
  all: repeat rewrite Ascii.eqb_eq.
  all: repeat rewrite Ascii.eqb_neq.
  all: repeat rewrite BinNat.N.compare_eq_iff.
  all: repeat rewrite BinNat.N.compare_lt_iff.
  all: repeat rewrite BinNat.N.compare_gt_iff.
  all: try lia.
  rewrite match_ltb_string.
  intros.
  apply IHs1.
  assumption.
  intros E.
  rewrite E.
  lia.
Qed.

Lemma N_of_ascii_inj : forall c1 c2, Ascii.N_of_ascii c1 = Ascii.N_of_ascii c2 -> c1 = c2.
Proof.
  intros c1 c2 H.
  rewrite <- (Ascii.ascii_N_embedding c1).
  rewrite <- (Ascii.ascii_N_embedding c2).
  rewrite H.
  reflexivity.
Qed.

Lemma N_of_ascii_inj_contra : forall c1 c2, c1 <> c2 -> Ascii.N_of_ascii c1 <> Ascii.N_of_ascii c2.
Proof.
  intros c1 c2 H1 H2.
  apply N_of_ascii_inj in H2.
  tauto.
Qed.

Lemma string_ltb_as_gtb : forall s1 s2, String.ltb s1 s2 = false -> String.eqb s1 s2 = false -> String.ltb s2 s1 = true.
Proof.
  induction s1 as [| c1 s1 ];
  induction s2 as [| c2 s2 ].
  all: unfold String.ltb; cbn; try congruence.
  case_eq (Ascii.compare c1 c2); case_eq (Ascii.eqb c1 c2).
  all: unfold Ascii.compare.
  all: repeat rewrite Ascii.eqb_eq.
  all: repeat rewrite Ascii.eqb_neq.
  all: repeat rewrite BinNat.N.compare_eq_iff.
  all: repeat rewrite BinNat.N.compare_lt_iff.
  all: repeat rewrite BinNat.N.compare_gt_iff.
  all: try lia.
  all: try (intro E; rewrite E; try rewrite BinNat.N.compare_refl; lia).
  intro E. rewrite E.
  try rewrite BinNat.N.compare_refl.
  rewrite match_ltb_string.
  intros.
  apply IHs1; assumption.
  intro C.
  apply N_of_ascii_inj_contra in C.
  congruence.
  intros _ LT.
  rewrite <- BinNat.N.compare_lt_iff in LT.
  rewrite LT.
  reflexivity.
Qed.

Definition id_eqb (id1 : id) (id2 : id) : bool :=
  match (id1, id2) with
  | (Id_aux And_bool _, Id_aux And_bool _) => true
  | (Id_aux Or_bool _, Id_aux Or_bool _) => true
  | (Id_aux (Id s1) _, Id_aux (Id s2) _) => String.eqb s1 s2
  | (Id_aux (Operator s1) _, Id_aux (Operator s2) _) => String.eqb s1 s2
  | _ => false
  end.

Module IdMiniOrdered <: OrderedType.MiniOrderedType.
  Definition t := Ast.id.

  Definition eq (id1 : id) (id2 : id) : Prop :=
    match (id1, id2) with
    | (Id_aux (Id s1) _, Id_aux (Id s2) _) => Is_true (String.eqb s1 s2)
    | (Id_aux (Operator s1) _, Id_aux (Operator s2) _) => Is_true (String.eqb s1 s2)
    | (Id_aux And_bool _, Id_aux And_bool _) => True
    | (Id_aux Or_bool _, Id_aux Or_bool _) => True
    | _ => False
    end.

  Definition lt (id1 : id) (id2 : id) : Prop :=
    match (id1, id2) with
    | (Id_aux (Id s1) _, Id_aux (Id s2) _) => Is_true (String.ltb s1 s2)
    | (Id_aux (Operator s1) _, Id_aux (Operator s2) _) => Is_true (String.ltb s1 s2)
    | (Id_aux (Id _) _, Id_aux (Operator _) _) => True
    | (Id_aux (Operator _) _, Id_aux (Id _) _) => False
    | (Id_aux And_bool _, _) => False
    | (_, Id_aux And_bool _) => True
    | (Id_aux Or_bool _, _) => False
    | (_, Id_aux Or_bool _) => True
    end.

   Theorem eq_refl : forall x, eq x x.
   Proof.
     destruct x as [aux ?].
     destruct aux; cbn; try trivial; rewrite String.eqb_refl; reflexivity.
   Qed.

   Theorem eq_sym : forall x y, eq x y -> eq y x.
   Proof.
     destruct x as [x_aux ?].
     destruct y as [y_aux ?].
     destruct x_aux as [| | x_s | x_s]; destruct y_aux as [| | y_s | y_s]; cbn; try trivial; rewrite String.eqb_sym; easy.
   Qed.

  Theorem eq_trans : forall x y z, eq x y -> eq y z -> eq x z.
  Proof.
    destruct x as [x_aux ?].
    destruct y as [y_aux ?].
    destruct z as [z_aux ?].
    destruct x_aux as [| | x_s | x_s]; destruct y_aux as [| | y_s | y_s]; destruct z_aux as [| | z_s | z_s].
    all: cbn.
    all: try easy.
    all: intros A B.
    all: apply Is_true_eq_left.
    all: apply Is_true_eq_true in A.
    all: apply Is_true_eq_true in B.
    all: rewrite String.eqb_eq in *.
    all: congruence.
  Qed.

  Theorem lt_trans : forall x y z, lt x y -> lt y z -> lt x z.
  Proof.
    destruct x as [x_aux ?].
    destruct y as [y_aux ?].
    destruct z as [z_aux ?].
    destruct x_aux as [| | x_s | x_s]; destruct y_aux as [| | y_s | y_s]; destruct z_aux as [| | z_s | z_s].
    all: cbn.
    all: try easy.
    all: intros A B.
    all: apply Is_true_eq_left.
    all: apply Is_true_eq_true in A.
    all: apply Is_true_eq_true in B.
    all: apply (string_ltb_trans _ y_s _); easy.
  Qed.

  Theorem lt_not_eq : forall x y, lt x y -> ~ eq x y.
  Proof.
    destruct x as [x_aux ?].
    destruct y as [y_aux ?].
    destruct x_aux as [| | x_s | x_s]; destruct y_aux as [| | y_s | y_s].
    all: cbn.
    all: try easy.
    all: intros A.
    all: apply Is_true_eq_true in A.
    all: apply string_ltb_not_eqb in A.
    all: apply negb_prop_elim.
    all: rewrite A.
    all: reflexivity.
  Qed.

  Definition compare : forall (x y : id), OrderedType.Compare lt eq x y.
  Proof.
    intros x y.
    destruct x as [x_aux ?].
    destruct y as [y_aux ?].
    destruct x_aux as [| | x_s | x_s]; destruct y_aux as [| | y_s | y_s].
    all: try (apply OrderedType.LT; reflexivity).
    all: try (apply OrderedType.EQ; reflexivity).
    all: try (apply OrderedType.GT; reflexivity).
    - case_eq (String.ltb x_s y_s); intros Hlt.
      + apply OrderedType.LT. cbn. rewrite Hlt. reflexivity.
      + case_eq (String.eqb x_s y_s); intros Heq.
        * apply OrderedType.EQ. cbn. rewrite Heq. reflexivity.
        * apply OrderedType.GT.
          cbn.
          apply Is_true_eq_left.
          apply string_ltb_as_gtb; assumption.
    - case_eq (String.ltb x_s y_s); intros Hlt.
      + apply OrderedType.LT. cbn. rewrite Hlt. reflexivity.
      + case_eq (String.eqb x_s y_s); intros Heq.
        * apply OrderedType.EQ. cbn. rewrite Heq. reflexivity.
        * apply OrderedType.GT.
          cbn.
          apply Is_true_eq_left.
          apply string_ltb_as_gtb; assumption.
  Defined.
End IdMiniOrdered.

Module IdOrdered := OrderedType.MOT_to_OT(IdMiniOrdered).

Module IdMap := FMapList.Raw(IdOrdered).
