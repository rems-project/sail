Require Extraction.

Set Extraction KeepSingleton.
Set Extraction Output Directory ".".

From Stdlib Require Import Bool.
From Stdlib Require Import FMapList.
From Stdlib Require Import FunctionalExtensionality.
From Stdlib Require Import Lia.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Program.
From Stdlib Require Import String.
From Stdlib Require Import ZArith.
From Stdlib Require QArith.
From Stdlib Require Import Setoid.
From Stdlib Require Import Morphisms.

Require Import Ast.
Require Import AstInduction.
Require Import Bit.
Require Import IdUtil.
Require Import ListUtil.
Require Import PatternMatch.
Require Import Value_type.
Require TypeAnnot.

Import ListNotations.

Definition is_value {A : Set} (exp : exp A) : bool :=
  match exp with
  | E_aux (E_internal_value _) _ => true
  | _ => false
  end.

Inductive return_value : Set :=
| Return_ok : value -> return_value
| Return_exception : value -> return_value.

Inductive var_type : Set :=
| Var_local : var_type
| Var_register : var_type.

Inductive place : Set :=
| PL_id : id -> var_type -> place
| PL_register : id -> place
| PL_vector : place -> Z -> place
| PL_vector_range : place -> Z -> Z -> place
| PL_field : place -> id -> place.

Inductive destructure : Set :=
| DL_app : id -> list value -> destructure
| DL_tuple : list destructure -> destructure
| DL_vector_concat : list (vector_concat_split * destructure) -> destructure
| DL_place : place -> destructure.

Module Monad.
  Inductive t (a : Set) : Set :=
  | Pure : a -> t a
  | Early_return : value -> t a
  | Exception : value -> t a
  | Runtime_type_error : Ast.loc -> t a
  | Match_failure : Ast.loc -> t a
  | Assertion_failed : string -> t a
  | Call : id -> list value -> (return_value -> t a) -> t a
  | Read_var : place -> (value -> t a) -> t a
  | Write_var : place -> value -> (unit -> t a) -> t a
  | Get_undefined : typ -> (value -> t a) -> t a.

  Arguments Pure {_}.
  Arguments Early_return {_}.
  Arguments Exception {_}.
  Arguments Runtime_type_error {_}.
  Arguments Match_failure {_}.
  Arguments Assertion_failed {_}.
  Arguments Call {_}.
  Arguments Read_var {_}.
  Arguments Write_var {_}.
  Arguments Get_undefined {_}.

  Fixpoint bind {A B : Set} (m : t A) (f : A -> t B) : t B :=
    match m with
    | Pure x => f x
    | Early_return v => Early_return v
    | Exception v => Exception v
    | Runtime_type_error l => Runtime_type_error l
    | Match_failure l => Match_failure l
    | Assertion_failed msg => Assertion_failed msg
    | Call id args cont => Call id args (fun v => bind (cont v) f)
    | Read_var r cont => Read_var r (fun v => bind (cont v) f)
    | Write_var r v cont => Write_var r v (fun u => bind (cont u) f)
    | Get_undefined t cont => Get_undefined t (fun v => bind (cont v) f)
    end.

  Notation "x ← y ; z" := (bind y (fun x : _ => z))
    (at level 20, y at level 100, z at level 200, only parsing).

  Fixpoint fmap {A B : Set} (f : A -> B) (m : t A) : t B :=
    match m with
    | Pure x => Pure (f x)
    | Early_return v => Early_return v
    | Exception v => Exception v
    | Runtime_type_error l => Runtime_type_error l
    | Match_failure l => Match_failure l
    | Assertion_failed msg => Assertion_failed msg
    | Call id args cont => Call id args (fun v => fmap f (cont v))
    | Read_var r cont => Read_var r (fun v => fmap f (cont v))
    | Write_var r v cont => Write_var r v (fun u => fmap f (cont u))
    | Get_undefined t cont => Get_undefined t (fun v => fmap f (cont v))
    end.

  Definition pure {A : Set} (x : A) : t A := Pure x.

  Definition lift_option {A : Set} (l : loc) (x : option A) : t A :=
    match x with
    | Some y => Pure y
    | None => Runtime_type_error l
    end.

  Fixpoint sequence {A : Set} (ls : list (t A)) : t (list A) :=
  match ls with
  | m :: ms =>
      x ← m;
      xs ← sequence ms;
      pure (x :: xs)
  | [] => pure []
  end.

  Definition get_undefined (typ : Ast.typ) : t value := Get_undefined typ pure.

  Definition throw {A : Set} (v : value) : t A := Exception v.

  Inductive caught (a : Set) : Set :=
  | Continue : a -> caught a
  | Caught : value -> caught a.

  Arguments Continue {_}.
  Arguments Caught {_}.

  Definition catch {A : Set} (m : t A) : t (caught A) :=
    match m with
    | Pure x => Pure (Continue x)
    | Early_return v => Early_return v
    | Exception v => Pure (Caught v)
    | Runtime_type_error l => Runtime_type_error l
    | Match_failure l => Match_failure l
    | Assertion_failed msg => Assertion_failed msg
    | Call id args cont => Call id args (fun v => fmap Continue (cont v))
    | Read_var r cont => Read_var r (fun v => fmap Continue (cont v))
    | Write_var r v cont => Write_var r v (fun _ => fmap Continue (cont ()))
    | Get_undefined t cont => Get_undefined t (fun v => fmap Continue (cont v))
    end.

  Lemma bind_left_id : forall (A B : Set) (f : A -> t B) (x : A), bind (pure x) f = f x.
  Proof.
    cbn. reflexivity.
  Qed.

  Lemma bind_right_id : forall (A : Set) (m : t A), bind m pure = m.
  Proof.
    intros A m.
    induction m as [| | | | | | ? ? cont H | ? cont H | ? ? cont H | ? cont H]; try easy.
    all: cbn.
    all: f_equal.
    all: apply functional_extensionality.
    all: intros x.
    all: specialize (H x).
    all: assumption.
  Qed.

  Lemma bind_assoc : forall (A B C : Set) (f : A -> t B) (g : B -> t C) (x : t A),
      bind (bind x f) g = bind x (fun y => bind (f y) g).
  Proof.
    intros A B C f g x.
    induction x as [| | | | | | ? ? cont H | ? cont H | ? ? cont H | ? cont H]; try easy.
    all: cbn.
    all: f_equal.
    all: apply functional_extensionality.
    all: intros x.
    all: remember (cont x) as z eqn : Heqz.
    all: specialize (H x).
    all: rewrite <- Heqz in H.
    all: cbn in H.
    all: assumption.
 Qed.
End Monad.

Import Monad.

Inductive evaluated (a : Set) : Set :=
| Evaluated : a -> evaluated a
| Unevaluated : evaluated a.

Arguments Evaluated {a} _.
Arguments Unevaluated {a}.

Definition get_bool {A : Set} (exp : exp A) : t (evaluated bool) :=
  match exp with
  | E_aux (E_internal_value (V_bool b)) _ => pure (Evaluated b)
  | E_aux (E_internal_value _) annot => Runtime_type_error (fst annot)
  | _ => pure Unevaluated
  end.

Definition get_string {A : Set} (exp : exp A) : t (evaluated string) :=
  match exp with
  | E_aux (E_internal_value (V_string s)) _ => pure (Evaluated s)
  | E_aux (E_internal_value _) annot => Runtime_type_error (fst annot)
  | _ => pure Unevaluated
  end.

Definition get_value {A : Set} (exp : exp A) : evaluated value :=
  match exp with
  | E_aux (E_internal_value v) annot => Evaluated v
  | _ => Unevaluated
  end.

Fixpoint all_evaluated {A : Set} (xs : list (exp A)) : list value :=
  match xs with
  | [] => []
  | E_aux (E_internal_value v) _ :: xs =>
      cons v (all_evaluated xs)
  | _ :: xs => all_evaluated xs
  end.

Fixpoint take_evaluated {A : Set} (xs : list (exp A)) : list (exp A) :=
  match xs with
  | [] => []
  | E_aux (E_internal_value v) a :: xs =>
      cons (E_aux (E_internal_value v) a) (take_evaluated xs)
  | _ :: xs => []
  end.

Fixpoint drop_evaluated {A : Set} (xs : list (exp A)) : list (exp A) :=
  match xs with
  | [] => []
  | E_aux (E_internal_value v) _ :: xs => drop_evaluated xs
  | x :: xs => x :: xs
  end.

Lemma take_drop_evaluated_concat : forall (A : Set) (xs : list (exp A)),
    take_evaluated xs ++ drop_evaluated xs = xs.
Proof.
  intros A xs.
  induction xs as [| x xs IHxs].
  - cbn. reflexivity.
  - destruct x as [aux ?].
    destruct aux.
    all: cbn.
    all: try reflexivity.
    rewrite IHxs.
    reflexivity.
Qed.

Definition coerce_place {A : Set} (loc : Ast.loc) (d : destructure) : t place :=
  match d with
  | DL_place p => pure p
  | _ => Runtime_type_error loc
  end.

Fixpoint left_to_right {A : Set} (xs : list (exp A)) {struct xs} : (list (exp A) * list (exp A)) :=
  match xs with
  | [] => ([], [])
  | E_aux (E_internal_value v) annot :: xs =>
      let '(vs, xs') := left_to_right xs in
      (E_aux (E_internal_value v) annot :: vs, xs')
  | x :: xs => ([], x :: xs)
  end.

Lemma ltr_tuple : forall (A : Set) (xs : list (exp A)),
    left_to_right xs = (take_evaluated xs, drop_evaluated xs).
Proof.
  intros A xs.
  induction xs as [| x xs IHxs].
  - cbn.
    reflexivity.
  - destruct x as [aux ?].
    destruct aux.
    all: cbn.
    all: try reflexivity.
    rewrite IHxs.
    reflexivity.
Qed.

Fixpoint all_evaluated_fields {A : Set} (xs : list (fexp A)) : list (id * value) :=
  match xs with
  | [] => []
  | FE_aux (FE_fexp id (E_aux (E_internal_value v) _)) _ :: xs =>
      (id, v) :: all_evaluated_fields xs
  | _ :: xs => all_evaluated_fields xs
  end.

Fixpoint take_evaluated_fields {A : Set} (xs : list (fexp A)) : list (fexp A) :=
  match xs with
  | [] => []
  | FE_aux (FE_fexp id (E_aux (E_internal_value v) ann)) fe_ann :: xs =>
      FE_aux (FE_fexp id (E_aux (E_internal_value v) ann)) fe_ann :: take_evaluated_fields xs
  | _ :: xs => []
  end.

Fixpoint drop_evaluated_fields {A : Set} (xs : list (fexp A)) : list (fexp A) :=
  match xs with
  | [] => []
  | FE_aux (FE_fexp _ (E_aux (E_internal_value v) _)) _ :: xs => drop_evaluated_fields xs
  | x :: xs => x :: xs
  end.

Fixpoint left_to_right_fields {A : Set} (xs : list (fexp A)) {struct xs} : (list (fexp A) * list (fexp A)) :=
  match xs with
  | [] => ([], [])
  | FE_aux (FE_fexp id (E_aux (E_internal_value v) annot)) fe_annot :: xs =>
      let '(vs, xs') := left_to_right_fields xs in
      (FE_aux (FE_fexp id (E_aux (E_internal_value v) annot)) fe_annot :: vs, xs')
  | x :: xs => ([], x :: xs)
  end.

Lemma take_drop_evaluated_fields_concat : forall (A : Set) (fxs : list (fexp A)),
  take_evaluated_fields fxs ++ drop_evaluated_fields fxs = fxs.
Proof.
  intros A fxs.
  induction fxs as [| fx fxs IHfxs].
  - reflexivity.
  - destruct fx as [aux ?].
    destruct aux as [? e].
    destruct e as [e_aux ?].
    destruct e_aux.
    all: try reflexivity.
    cbn. rewrite IHfxs. reflexivity.
Qed.

Lemma ltr_fields_tuple : forall (A : Set) (fxs : list (fexp A)),
  left_to_right_fields fxs = (take_evaluated_fields fxs, drop_evaluated_fields fxs).
Proof.
  intros A fxs.
  induction fxs as [| fx fxs IHfxs].
  - reflexivity.
  - destruct fx as [aux ?].
    destruct aux as [? e].
    destruct e as [e_aux ?].
    destruct e_aux.
    all: try reflexivity.
    cbn. rewrite IHfxs. reflexivity.
Qed.

Inductive ltr2 (A : Set) : Set :=
| LTR2_0 : exp A -> exp A -> ltr2 A
| LTR2_1 : value -> exp A -> ltr2 A
| LTR2_2 : value -> value -> ltr2 A.

Arguments LTR2_0 {_}.
Arguments LTR2_1 {_}.
Arguments LTR2_2 {_}.

Definition left_to_right2 {A : Set} (x y : exp A) : ltr2 A :=
  match (x, y) with
  | (E_aux (E_internal_value v1) _, E_aux (E_internal_value v2) _) => LTR2_2 v1 v2
  | (E_aux (E_internal_value v1) _, _) => LTR2_1 v1 y
  | (_, _) => LTR2_0 x y
  end.

Inductive ltr3 (A : Set) : Set :=
| LTR3_0 : exp A -> exp A -> exp A -> ltr3 A
| LTR3_1 : value -> exp A -> exp A -> ltr3 A
| LTR3_2 : value -> value -> exp A -> ltr3 A
| LTR3_3 : value -> value -> value -> ltr3 A.

Arguments LTR3_0 {_}.
Arguments LTR3_1 {_}.
Arguments LTR3_2 {_}.
Arguments LTR3_3 {_}.

Definition left_to_right3 {A : Set} (x y z : exp A) : ltr3 A :=
  match (x, y, z) with
  | (E_aux (E_internal_value v1) _, E_aux (E_internal_value v2) _, E_aux (E_internal_value v3) _) => LTR3_3 v1 v2 v3
  | (E_aux (E_internal_value v1) _, E_aux (E_internal_value v2) _, _) => LTR3_2 v1 v2 z
  | (E_aux (E_internal_value v1) _, _, _) => LTR3_1 v1 y z
  | (_, _, _) => LTR3_0 x y z
  end.

Lemma fold_right_max_acc : forall x y zs, x <= y -> x < fold_right max y zs + 1.
Proof.
  intros ? ? zs.
  induction zs; cbn; lia.
Qed.

Lemma fold_right_max_acc2 : forall x y zs, x <= y -> x <= fold_right max y zs.
Proof.
  intros ? ? zs.
  induction zs; cbn; lia.
Qed.

Module Make (Tannot : TypeAnnot.S).

  Module PM := PatternMatch.Make(Tannot).
  Import PM.

  Fixpoint substitute {A} (n : Ast.id) (v : Ast.value) (x : exp A) : exp A :=
    let 'E_aux aux annot := x in
    match aux with
    | E_id m =>
        if id_eqb n m then E_aux (E_internal_value v) annot else E_aux (E_id m) annot
    | E_block xs => E_aux (E_block (map (substitute n v) xs)) annot
    | E_app f args => E_aux (E_app f (map (substitute n v) args)) annot
    | E_tuple xs => E_aux (E_tuple (map (substitute n v) xs)) annot
    | E_vector xs => E_aux (E_vector (map (substitute n v) xs)) annot
    | E_vector_append x y => E_aux (E_vector_append (substitute n v x) (substitute n v y)) annot
    | E_if i t e =>
        E_aux (E_if (substitute n v i) (substitute n v t) (substitute n v e)) annot
    | E_let pat y body =>
        if binds_id n pat then
          E_aux (E_let pat (substitute n v y) body) annot
        else
          E_aux (E_let pat (substitute n v y) (substitute n v body)) annot
    | E_var l x body =>
        E_aux (E_var (substitute_lexp n v l) (substitute n v x) (substitute n v body)) annot
    | E_match head_exp arms =>
        E_aux (E_match (substitute n v head_exp) (map (substitute_arm n v) arms)) annot
    | E_try head_exp arms =>
        E_aux (E_try (substitute n v head_exp) (map (substitute_arm n v) arms)) annot
    | E_list xs =>
        E_aux (E_list (map (substitute n v) xs)) annot
    | E_typ typ x => E_aux (E_typ typ (substitute n v x)) annot
    | E_lit _ => E_aux aux annot
    | E_throw exn => E_aux (E_throw (substitute n v exn)) annot
    | E_assert x msg =>
        E_aux (E_assert (substitute n v x) (substitute n v msg)) annot
    | E_assign l x =>
        E_aux (E_assign (substitute_lexp n v l) (substitute n v x)) annot
    | E_cons x xs =>
        E_aux (E_cons (substitute n v x) (substitute n v xs)) annot
    | E_field x f =>
        E_aux (E_field (substitute n v x) f) annot
    | E_loop loop_kind measure cond body => E_aux (E_loop loop_kind measure (substitute n v cond) (substitute n v body)) annot
    | E_for loop_var from to amount ord body =>
        if id_eqb n loop_var then
          E_aux (E_for loop_var (substitute n v from) (substitute n v to) (substitute n v amount) ord body) annot
        else
          E_aux (E_for loop_var (substitute n v from) (substitute n v to) (substitute n v amount) ord (substitute n v body)) annot
    | E_struct struct_name fields =>
        E_aux
          (E_struct
             struct_name
             (map
                (fun f =>
                   let 'FE_aux (FE_fexp name x) fe_annot := f in
                   FE_aux (FE_fexp name (substitute n v x)) fe_annot
                )
                fields))
          annot
    | E_struct_update x fields =>
        E_aux
          (E_struct_update
             (substitute n v x)
             (map
                (fun f =>
                   let 'FE_aux (FE_fexp name y) fe_annot := f in
                   FE_aux (FE_fexp name (substitute n v y)) fe_annot
                )
                fields))
          annot
    | E_return x => E_aux (E_return (substitute n v x)) annot
    | _ => x
    end
  with substitute_arm {A} (n : Ast.id) (v : Ast.value) (arm : pexp A) : pexp A :=
    let 'Pat_aux aux annot := arm in
    match aux with
    | Pat_exp pat body =>
        if binds_id n pat then
          Pat_aux (Pat_exp pat body) annot
        else
          Pat_aux (Pat_exp pat (substitute n v body)) annot
    | Pat_when pat guard body =>
        if binds_id n pat then
          Pat_aux (Pat_when pat guard body) annot
        else
          Pat_aux (Pat_when pat (substitute n v guard) (substitute n v body)) annot
    end
  with substitute_lexp {A} (n : Ast.id) (v : Ast.value) (l : lexp A) : lexp A :=
    let 'LE_aux aux annot := l in
    match aux with
    | LE_deref x => LE_aux (LE_deref (substitute n v x)) annot
    | LE_vector lx x => LE_aux (LE_vector (substitute_lexp n v lx) (substitute n v x)) annot
    | LE_vector_range lx x y =>
        LE_aux (LE_vector_range (substitute_lexp n v lx) (substitute n v x) (substitute n v y)) annot
    | LE_field lx f => LE_aux (LE_field (substitute_lexp n v lx) f) annot
    | LE_vector_concat lxs => LE_aux (LE_vector_concat (map (substitute_lexp n v) lxs)) annot
    | LE_tuple lxs => LE_aux (LE_tuple (map (substitute_lexp n v) lxs)) annot
    | _ => l
    end.

  Fixpoint bv_concat (l : loc) (vs : list value) : t (list bit) :=
    match vs with
    | [] => pure []
    | V_bitvector bs :: rest =>
        rest' ← bv_concat l rest;
        pure (bs ++ rest')
    | _ :: _ => Runtime_type_error l
    end.

  Definition value_of_lit (lit : Ast.lit) : value :=
    let 'L_aux aux _ := lit in
    match aux with
    | L_unit => V_unit
    | L_true => V_bool true
    | L_false => V_bool false
    | L_num n => V_int n
    | L_hex h => V_bitvector (BitList.of_hex_lit h)
    | L_bin b => V_bitvector (BitList.of_bin_lit b)
    | L_real r => V_real r
    | L_string s => V_string s
    end.

  Fixpoint lookup_field (l : Ast.loc) (name : id) (fields : list (id * value)) {struct fields} : t value :=
      match fields with
      | [] => Runtime_type_error l
      | (name', v) :: fields =>
          if id_eqb name name' then
            pure v
          else
            lookup_field l name fields
      end.

  Lemma max_lhs_plus_1_le : forall x y z, x <= y -> x < max y z + 1.
  Proof.
    lia.
  Qed.

  Lemma depth_if : forall (b : bool) (x y : exp Tannot.t), depth (if b then x else y) <= max (depth x) (depth y).
  Proof.
    intro b; destruct b; lia.
  Qed.

  Lemma fexp_subst : forall f (lx : fexp Tannot.t),
    (let 'FE_aux (FE_fexp id x) ann := lx in FE_aux (FE_fexp id (f x)) ann) =
    FE_aux (FE_fexp (fexp_name lx) (f (fexp_exp lx))) (fexp_annot lx).
  Proof.
    intros ? lx.
    destruct lx as [aux ?].
    destruct aux.
    cbn.
    reflexivity.
  Qed.

  Lemma depth_subst_helper : forall x y z w, x <= z -> y + 1 <= w + 1 -> max x y + 1 <= max z w + 1.
  Proof.
    lia.
  Qed.

  Lemma depth_subst : forall n v (x : exp Tannot.t), depth (substitute n v x) <= depth x.
  Proof with lia.
    intros n v x.
    einduction x using exp_ind_mutual_g.
    all: (cbn; try easy; try lia).
    - induction xs.
      + reflexivity.
      + cbn.
        rewrite Forall_cons_iff in H.
        inversion H as [Hhd Htl].
        apply IHxs in Htl...
    - cbn.
      apply (PeanoNat.Nat.le_trans _ _ _ (depth_if _ _ _)).
      reflexivity.
    - induction xs.
      + reflexivity.
      + cbn.
        rewrite Forall_cons_iff in H.
        inversion H as [Hhd Htl].
        apply IHxs in Htl...
    - induction xs.
      + reflexivity.
      + cbn.
        rewrite Forall_cons_iff in H.
        inversion H as [Hhd Htl].
        apply IHxs in Htl...
    - cbn.
      apply (PeanoNat.Nat.le_trans _ _ _ (depth_if _ _ _)).
      cbn...
    - induction xs.
      + reflexivity.
      + cbn.
        rewrite Forall_cons_iff in H.
        inversion H as [Hhd Htl].
        apply IHxs in Htl...
    - induction xs.
      + reflexivity.
      + cbn.
        rewrite Forall_cons_iff in H.
        inversion H as [Hhd Htl].
        apply IHxs in Htl...
    - induction fields.
      + reflexivity.
      + rewrite Forall_cons_iff in H.
        inversion H as [Hhd Htl].
        apply IHfields in Htl.
        cbn.
        rewrite map_map.
        setoid_rewrite fexp_subst.
        cbn in Htl.
        rewrite map_map in Htl.
        setoid_rewrite fexp_subst in Htl.
        apply depth_subst_helper; [ idtac | lia ].
        apply (PeanoNat.Nat.le_trans _ _ _ Hhd).
        destruct a.
        destruct f.
        reflexivity.
    - cbn.
      apply depth_subst_helper.
      assumption.
      induction fields.
      + reflexivity.
      + rewrite Forall_cons_iff in H.
        inversion H as [Hhd Htl].
        apply IHfields in Htl.
        cbn.
        rewrite map_map.
        setoid_rewrite fexp_subst.
        cbn in Htl.
        rewrite map_map in Htl.
        setoid_rewrite fexp_subst in Htl.
        apply depth_subst_helper; [ idtac | lia ].
        apply (PeanoNat.Nat.le_trans _ _ _ Hhd).
        destruct a.
        destruct f.
        reflexivity.
    - apply depth_subst_helper.
      assumption.
      induction arms.
      + reflexivity.
      + rewrite Forall_cons_iff in H.
        inversion H as [Hhd Htl].
        apply IHarms in Htl.
        cbn.
        apply depth_subst_helper; [ idtac | assumption ].
        cbn in Hhd.
        destruct a as [aux ?].
        destruct aux; cbn; destruct (binds_id n p); try reflexivity; try assumption.
        cbn in Hhd...
    - destruct (binds_id n p); cbn; lia.
    - apply depth_subst_helper; [ apply IHe | lia ].
    - apply depth_subst_helper; [ assumption | idtac ].
      induction arms.
      + reflexivity.
      + rewrite Forall_cons_iff in H.
        inversion H as [Hhd Htl].
        apply IHarms in Htl.
        cbn.
        apply depth_subst_helper; [ idtac | assumption ].
        cbn in Hhd.
        destruct a as [aux ?].
        destruct aux; cbn; destruct (binds_id n p); try reflexivity; try assumption.
        cbn in Hhd...
    - cbn in IHe1...
    - cbn; reflexivity.
    - cbn; try assumption...
    - cbn; reflexivity.
    - cbn; reflexivity.
    - cbn.
      induction lxs.
      + reflexivity.
      + rewrite Forall_cons_iff in H.
        inversion H as [Hhd Htl].
        cbn.
        apply depth_subst_helper.
        assumption.
        apply IHlxs in Htl.
        assumption.
    - cbn.
      induction lxs.
      + reflexivity.
      + rewrite Forall_cons_iff in H.
        inversion H as [Hhd Htl].
        cbn.
        apply depth_subst_helper; [ assumption | idtac ].
        apply IHlxs in Htl.
        assumption.
    - cbn. cbn in IHe...
    - cbn. cbn in IHe1...
    - cbn. cbn in IHe...
  Qed.

  Fixpoint destructuring_assignment (annot : Ast.annot Tannot.t) (d : destructure) (v : value) : t unit :=
    match d with
    | DL_place p =>
        Write_var p v (fun _ => pure tt)
    | DL_tuple ds =>
        match v with
        | V_tuple vs =>
            if Nat.eqb (List.length ds) (List.length vs) then
              let '(assignment, _) :=
                fold_left
                  (fun acc d =>
                     match acc with
                     | (prev, v :: vs) =>
                         (bind prev (fun _ => destructuring_assignment annot d v), vs)
                     | (prev, []) => (prev, [])
                     end
                  )
                  ds
                  (pure tt, vs)
              in
              assignment
            else
              Runtime_type_error (fst annot)
        | _ =>
            Runtime_type_error (fst annot)
        end
    | DL_vector_concat ds =>
        match v with
        | V_bitvector bs =>
            let '(assignment, _) :=
              fold_left
                (fun acc d =>
                   let '(s, d) := d in
                   match s with
                   | Split s =>
                       match acc with
                       | (prev, []) => (prev, [])
                       | (prev, bs) =>
                           let '(bs_take, bs_drop) := take_drop s bs in
                           (bind prev (fun _ => destructuring_assignment annot d (V_bitvector bs_take)), bs_drop)
                       end
                   | No_split => (Runtime_type_error (fst annot), [])
                   end
                )
                ds
                (pure tt, bs)
            in
            assignment
        | V_vector vs =>
            let '(assignment, _) :=
              fold_left
                (fun acc d =>
                   let '(s, d) := d in
                   match s with
                   | Split s =>
                       match acc with
                       | (prev, []) => (prev, [])
                       | (prev, vs) =>
                           let '(vs_take, vs_drop) := take_drop s vs in
                           (bind prev (fun _ => destructuring_assignment annot d (V_vector vs_take)), vs_drop)
                       end
                   | No_split => (Runtime_type_error (fst annot), [])
                   end
                )
                ds
                (pure tt, vs)
            in
            assignment
        | _ => Runtime_type_error (fst annot)
        end
    | _ =>
        Runtime_type_error (fst annot)
    end.

  Fixpoint lexp_to_destructure (l : lexp Tannot.t) {struct l} : t destructure :=
    let 'LE_aux aux annot := l in
    match aux with
    | LE_id var
    | LE_typ _ var =>
        match Tannot.get_id_type (snd annot) var with
        | Global_register =>
            pure (DL_place (PL_id var Var_register))
        | Local_variable =>
            pure (DL_place (PL_id var Var_local))
        | Enum_member =>
            Runtime_type_error (fst annot)
        end
    | LE_deref x =>
        match x with
        | E_aux (E_internal_value (V_ref r)) _ =>
            pure (DL_place (PL_register r))
        | _ =>
            Runtime_type_error (fst annot)
        end
    | LE_app name args =>
        let evaluated := all_evaluated args in
        pure (DL_app name evaluated)
    | LE_tuple ls =>
        ds ← sequence (map lexp_to_destructure ls);
        pure (DL_tuple ds)
    | LE_vector_concat ls =>
        ds ← sequence (map (fun '((LE_aux _ annot) as l) => d ← lexp_to_destructure l; pure (Tannot.get_split (snd annot), d)) ls);
        pure (DL_vector_concat ds)
    | LE_field l f =>
        p ← bind (lexp_to_destructure l) (@coerce_place Tannot.t (fst annot));
        pure (DL_place (PL_field p f))
    | LE_vector l n =>
        p ← bind (lexp_to_destructure l) (@coerce_place Tannot.t (fst annot));
        match n with
        | E_aux (E_internal_value (V_int n)) _ =>
            pure (DL_place (PL_vector p n))
        | _ =>
            Runtime_type_error (fst annot)
        end
    | LE_vector_range l n m =>
        p ← bind (lexp_to_destructure l) (@coerce_place Tannot.t (fst annot));
        match (n, m) with
        | (E_aux (E_internal_value (V_int n)) _, E_aux (E_internal_value (V_int m)) _) =>
            pure (DL_place (PL_vector_range p n m))
        | _ =>
            Runtime_type_error (fst annot)
        end
    end.

  Fixpoint update_field (name : id) (v : value) (fields : list (id * value)) : list (id * value) :=
    match fields with
    | (name', old_v) :: rest =>
        if id_eqb name name' then
          (name, v) :: rest
        else
          (name', old_v) :: update_field name v rest
    | [] => []
    end.

  Lemma NoDupA_cons : forall [A] [eqA : A -> A -> Prop] (E : RelationClasses.Equivalence eqA) [x : A] [xs : list A],
    SetoidList.NoDupA eqA (x :: xs) -> SetoidList.NoDupA eqA xs.
  Proof.
    intros A eqA E x xs H.
    change (SetoidList.NoDupA eqA ([] ++ x :: xs)) in H.
    apply (SetoidList.NoDupA_split H).
  Qed.

  Lemma NoDupA_eqA_h : forall [A] [eqA : A -> A -> Prop] (E : RelationClasses.Equivalence eqA) [x x' : A] [xs xs' : list A],
    xs = (x :: x' :: xs') -> SetoidList.NoDupA eqA xs -> ~ (eqA x x').
  Proof.
    intros A eqA E x x' xs xs' X ND.
    rewrite SetoidList.NoDupA_altdef in ND.
    revert X.
    revert xs' x x'.
    induction ND.
    - intros. discriminate.
    - unfold not.
      intros ys x x' L Eq.
      inversion L; subst.
      apply Forall_inv in H.
      unfold RelationClasses.complement in H.
      tauto.
  Qed.

  Lemma NoDupA_eqA : forall [A] [eqA : A -> A -> Prop] (E : RelationClasses.Equivalence eqA) [x x' : A] [xs : list A],
    SetoidList.NoDupA eqA (x :: x' :: xs) -> ~ (eqA x x').
  Proof.
    intros A eqA E x x' xs H.
    apply (NoDupA_eqA_h E eq_refl H).
  Qed.

  Lemma NoDupA_in_tl : forall [A] [eqA : A -> A -> Prop] (E : RelationClasses.Equivalence eqA) [x x' : A] (xs : list A),
    SetoidList.NoDupA eqA (x :: xs) -> SetoidList.InA eqA x' xs -> ~ (eqA x x').
  Proof.
    intros A eqA E x x' xs.
    revert x'.
    induction xs as [| y ys].
    - intro. rewrite SetoidList.InA_nil; tauto.
    - intros z ND In.
      unfold not.
      intros Eq_x_z.
      rewrite SetoidList.InA_cons in In.
      destruct In as [Eq_z_y | In].
      + apply (NoDupA_eqA E) in ND.
        assert (L : eqA x y); [ setoid_transitivity z; assumption | idtac ].
        tauto.
      + assert (L : ~ eqA x z).
        {
          apply (fun H => IHys z H In).
          change (SetoidList.NoDupA eqA ([x] ++ y :: ys)) in ND.
          apply (SetoidList.NoDupA_swap E) in ND.
          apply (NoDupA_cons E) in ND.
          assumption.
        }
        tauto.
  Qed.

  Lemma fold_right_last_to_first : forall [A B] [eqB : B -> B -> Prop] (E : RelationClasses.Equivalence eqB) (f : B -> A -> A) (acc : A) (x : B) xs,
    (forall y z, SetoidList.InA eqB y xs -> f y (f x z) = f x (f y z)) ->
    fold_right f (f x acc) xs = f x (fold_right f acc xs).
  Proof.
    intros A B eqB E f acc x xs H.
    induction xs as [| x' xs].
    - cbn; reflexivity.
    - cbn.
      rewrite IHxs.
      + apply H.
        apply SetoidList.InA_cons_hd.
        setoid_reflexivity.
      + intros y z In_y.
        apply H.
        apply SetoidList.InA_cons_tl; assumption.
  Qed.

  Lemma id_eqb_sym_neg : forall x y, id_eqb x y = false -> id_eqb y x = false.
  Proof.
    intros x y.
    destruct x as [x_aux ?].
    destruct y as [y_aux ?].
    destruct x_aux as [| | x_s | x_s]; destruct y_aux as [| | y_s | y_s].
    all: cbn; try easy.
    all: repeat rewrite String.eqb_neq.
    all: congruence.
  Qed.

  Lemma substitute_swap : forall [A] id1 id2 v1 v2 (exp : exp A),
    id_eqb id1 id2 = false ->
    substitute id1 v1 (substitute id2 v2 exp) = substitute id2 v2 (substitute id1 v1 exp).
  Proof.
    intros A id1 id2 v1 v2 exp NE.

    einduction exp using exp_ind_mutual_g.

    Unshelve.
    all: try (
      apply (fun lx : lexp A => substitute_lexp id1 v1 (substitute_lexp id2 v2 lx) = substitute_lexp id2 v2 (substitute_lexp id1 v1 lx))
    ).

    (* First try to discharge as many simple cases as we can. *)
    all: cbn beta delta - [id_eqb] iota zeta.
    all: repeat (f_equal; try reflexivity; [idtac]).
    all: try reflexivity.
    all: repeat rewrite map_map; try (apply map_ext_Forall; apply H).
    all: try (apply IHe).
    all: try (rewrite IHe1; rewrite IHe2; reflexivity).
    all: try (rewrite IHe1; rewrite IHe2; rewrite IHe3; reflexivity).
    all: try (cbn in IHe; rewrite IHe, IHe0; reflexivity).

    (* First interesting case is when exp is an identifier. *)
    - case_eq (id_eqb id1 id); case_eq (id_eqb id2 id); intros I1 I2.
      all: cbn beta delta - [id_eqb] iota zeta.
      all: repeat (rewrite I1 + rewrite I2).
      all: cbn beta delta - [id_eqb] iota zeta.
      all: repeat (rewrite I1 + rewrite I2).
      all: try reflexivity.
      exfalso.
      apply id_eqb_sym in I1.
      assert (C := id_eqb_trans id1 id id2 I2 I1).
      rewrite NE in C.
      discriminate.

    (* Next case is the for loop, as loop variable id affects substitutio.n *)
    - case_eq (id_eqb id1 id); case_eq (id_eqb id2 id); intros I1 I2.
      all: cbn beta delta - [id_eqb] iota zeta.
      all: repeat (rewrite I1 + rewrite I2 + rewrite IHe1 + rewrite IHe2 + rewrite IHe3 + rewrite IHe4).
      all: reflexivity.

    (* Struct expression, just requires some extra destructuring. *)
    - apply map_ext_Forall.
      apply (fun Q P => Forall_impl Q P H).
      clear H.
      intros fexp IHfexp.
      destruct fexp as [aux ?].
      destruct aux.
      cbn in IHfexp.
      rewrite IHfexp.
      reflexivity.

    (* Struct update expression, same as above. *)
    - f_equal; [ assumption | idtac].
      apply map_ext_Forall.
      apply (fun Q P => Forall_impl Q P H).
      clear H IHe.
      intros fexp IHfexp.
      destruct fexp as [aux ?].
      destruct aux.
      cbn in IHfexp.
      rewrite IHfexp.
      reflexivity.

    (* Pattern matching, essentially simplifies to a list of let-expressions. *)
    - f_equal; [ assumption | idtac].
      apply map_ext_Forall.
      apply (fun Q P => Forall_impl Q P H).
      clear H IHe.
      intros pexp.
      destruct pexp as [aux ?].
      destruct aux as [pat arm | pat guard arm]; cbn.
      + intros IH.
        case_eq (binds_id id1 pat); case_eq (binds_id id2 pat); intros I1 I2.
        all: cbn beta delta - [id_eqb] iota zeta.
        all: repeat (rewrite I1 + rewrite I2 + rewrite IH).
        all: reflexivity.
      + intros IH.
        destruct IH as [IHguard IHarm].
        case_eq (binds_id id1 pat); case_eq (binds_id id2 pat); intros I1 I2.
        all: cbn beta delta - [id_eqb] iota zeta.
        all: repeat (rewrite I1 + rewrite I2 + rewrite IHarm + rewrite IHguard).
        all: reflexivity.

    (* let-expressions we just split on whether either pattern binds. *)
    - case_eq (binds_id id1 p); case_eq (binds_id id2 p); intros I1 I2.
      all: cbn beta delta - [id_eqb] iota zeta.
      all: repeat (rewrite I1 + rewrite I2 + rewrite IHe1 + rewrite IHe2).
      all: reflexivity.

    (* try-expression - See match above. *)
    - f_equal; [ assumption | idtac].
      apply map_ext_Forall.
      apply (fun Q P => Forall_impl Q P H).
      clear H IHe.
      intros pexp.
      destruct pexp as [aux ?].
      destruct aux as [pat arm | pat guard arm]; cbn.
      + intros IH.
        case_eq (binds_id id1 pat); case_eq (binds_id id2 pat); intros I1 I2.
        all: cbn beta delta - [id_eqb] iota zeta.
        all: repeat (rewrite I1 + rewrite I2 + rewrite IH).
        all: reflexivity.
      + intros IH.
        destruct IH as [IHguard IHarm].
        case_eq (binds_id id1 pat); case_eq (binds_id id2 pat); intros I1 I2.
        all: cbn beta delta - [id_eqb] iota zeta.
        all: repeat (rewrite I1 + rewrite I2 + rewrite IHarm + rewrite IHguard).
        all: reflexivity.
  Qed.

  Lemma substitute_fold : forall substs (exp : exp Tannot.t),
    SetoidList.NoDupA (IdMap.eq_key (elt:=value)) substs ->
    fold_left (fun exp s => substitute (fst s) (snd s) exp) substs exp =
    fold_right (fun s exp => substitute (fst s) (snd s) exp) exp substs.
  Proof.
    intros substs exp H.
    revert exp.
    induction substs as [| s substs].
    - cbn; reflexivity.
    - cbn; intros exp.
      rewrite IHsubsts.
      rewrite (fold_right_last_to_first (eqB:=IdMap.eq_key (elt:=value))_ (fun (s : id * value) (exp : Ast.exp Tannot.t) => substitute (fst s) (snd s) exp)).
      + reflexivity.
      + intros s' exp' In_s'.
        apply substitute_swap.
        assert (S := NoDupA_in_tl _ _ H In_s').
        unfold IdMap.eq_key in S. unfold IdMap.Raw.PX.eqk in S.
        apply negb_prop_intro, Is_true_eq_true, negb_true_iff in S.
        rewrite id_eqb_comm.
        assumption.
      + apply (NoDupA_cons _ H).
  Qed.

  Ltac is_true_step :=
    lazymatch goal with
    | [ pair : _ * _ |- _ ] => destruct pair
    | |- Is_true ?P => apply Is_true_eq_left
    | |- ~ Is_true ?P => apply negb_prop_elim
    | |- negb ?P = true => apply negb_true_iff
    | [ H : Is_true ?P |- _ ] => apply Is_true_eq_true in H
    | |- id_eqb ?x ?x = true => apply (id_eqb_refl x)
    | [ _ : id_eqb ?x ?y = true |- id_eqb ?y ?x = true ] => apply id_eqb_sym; assumption
    | [ L : id_eqb ?x ?y = true, R : id_eqb ?y ?z =  true |- id_eqb ?x ?z = true ] => apply (id_eqb_trans _ _ _ L R)
    | [ _ : ?P |- ?P ] => assumption
    end.

  Ltac is_true_simp := repeat is_true_step.

  Ltac is_true_solve := solve [ intros; repeat is_true_step ].

  Lemma not_find_in_iff_r: forall [elt : Type] (m : IdMap.t elt) (x : IdMap.key),
    ~ IdMap.In (elt:=elt) x m -> IdMap.find (elt:=elt) x m = None.
  Proof.
    intros.
    apply IdMapP.P.F.not_find_in_iff.
    assumption.
  Qed.

  Lemma not_in_remove : forall [A : Type] (m : IdMap.t A) (x y : IdMap.key),
    ~ (IdMap.In x m) -> ~ (IdMap.In x (IdMap.remove y m)).
  Proof.
    intros A m x y H.
    case_eq (id_eqb y x); intros.
    - change (~ (exists b, IdMap.MapsTo x b m)) in H.
    cbn in H.
    unfold not.
    intros In_remove.
    change (exists b, IdMap.MapsTo x b (IdMap.remove y m)) in In_remove.
    destruct In_remove as [b].
    destruct H.
    apply IdMap.find_1 in H1.
    exists b.
    apply IdMap.find_2.
    rewrite IdMapP.P.F.remove_eq_o in H1.
    + discriminate.
    + is_true_simp.
    -change (~ (exists b, IdMap.MapsTo x b m)) in H.
    cbn in H.
    unfold not.
    intros In_remove.
    change (exists b, IdMap.MapsTo x b (IdMap.remove y m)) in In_remove.
    destruct In_remove as [b].
    destruct H.
    apply IdMap.find_1 in H1.
    exists b.
    apply IdMap.find_2.
    rewrite IdMapP.P.F.remove_neq_o in H1.
    + assumption.
    + is_true_simp.
  Qed.

  Lemma Empty_Equal_empty : forall [A m], IdMap.Empty (elt:=A) m -> IdMap.Equal m (IdMap.empty _).
  Proof.
    intros.
    rewrite IdMapP.P.F.Equal_mapsto_iff.
    intros k e.
    split.
    - intros M.
      apply IdMap.find_1 in M.
      rewrite IdMapP.P.elements_Empty in H.
      rewrite IdMapP.P.F.elements_o in M.
      rewrite H in M.
      cbn in M.
      discriminate.
    - intros M.
      apply IdMap.find_1 in M.
      rewrite IdMapP.P.elements_Empty in H.
      rewrite IdMapP.P.F.elements_o in M.
      rewrite IdMapP.P.elements_empty in M.
      cbn in M.
      discriminate.
  Qed.

  Lemma find_map_remove_comm : forall [A B] (f : A -> B) k m x,
    IdMap.find x (IdMap.map f (IdMap.remove k m)) = IdMap.find x (IdMap.remove k (IdMap.map f m)).
  Proof.
    intros A B f k m x.
    induction m using IdMapP.P.map_induction.
    - rewrite IdMapP.P.F.map_o.
      rewrite not_find_in_iff_r.
      rewrite not_find_in_iff_r.
      + reflexivity.
      + apply not_in_remove.
        unfold not.
        intros In_map.
        change (exists b, IdMap.MapsTo x b (IdMap.map f m)) in In_map.
        destruct In_map as [b].
        apply IdMap.find_1 in H0.
        rewrite IdMapP.P.F.map_o in H0.
        rewrite not_find_in_iff_r in H0.
        cbn in H0.
        discriminate.
        unfold not.
        intros In_m.
        change (exists b, IdMap.MapsTo x b m) in In_m.
        destruct In_m as [b'].
        apply IdMap.find_1 in H1.
        rewrite H1 in H0.
        cbn in H0.
        rewrite IdMapP.P.elements_Empty in H.
        rewrite IdMapP.P.F.elements_o in H1.
        rewrite H in H1.
        cbn in H1.
        discriminate.
      + apply not_in_remove.
        unfold not.
        intros In_m.
        rewrite IdMapP.P.elements_Empty in H.
        change (exists b, IdMap.MapsTo x b m) in In_m.
        destruct In_m as [b'].
        apply IdMap.find_1 in H0.
        rewrite IdMapP.P.F.elements_o in H0.
        rewrite H in H0.
        cbn in H0.
        discriminate.
    - unfold IdMapP.P.Add in H0.
      case_eq (id_eqb k x); intros Key.
      + rewrite IdMapP.P.F.map_o.
        repeat rewrite IdMapP.P.F.remove_eq_o.
        * reflexivity.
        * is_true_simp.
        * is_true_simp.
      + rewrite IdMapP.P.F.map_o.
        repeat rewrite IdMapP.P.F.remove_neq_o.
        rewrite (H0 x).
        rewrite IdMapP.P.F.map_o .
        rewrite (H0 x).
        * reflexivity.
        * is_true_simp.
        * is_true_simp.
  Qed.

  Lemma equiv_cong : forall [A]  [eqA : A -> A -> Prop] (E : Equivalence eqA) (x y : A),
    x = y -> eqA x y.
  Proof.
    intros A eqA E x y H. rewrite H. setoid_reflexivity.
  Qed.

  Instance key_equiv (A : Type) : Equivalence (IdMap.eq_key (elt:=A)).
  Proof with is_true_solve.
    unfold IdMap.eq_key. unfold IdMap.Raw.PX.eqk.
    split.
    - intros []...
    - intros [] []...
    - intros [] [] []...
  Qed.

  Instance key_value_equiv (A : Type) : Equivalence (IdMapP.O.eqke (elt:=A)).
  Proof.
    unfold IdMapP.O.eqke. unfold IdMap.Raw.PX.eqk.
    split.
    - intros []; split; [ is_true_solve | reflexivity ].
    - intros [] []; split; destruct H as [H1 H2]; [ is_true_solve | symmetry; apply H2].
    - intros [] [] []; split.
      destruct H.
      destruct H0.
      is_true_solve.
      destruct H.
      destruct H0.
      transitivity (snd (i0, a0)); assumption.
  Qed.

  Lemma NoDupA_app_cons_swap_h : forall [A] [eqA : A -> A -> Prop] (E : RelationClasses.Equivalence eqA) [x : A] [xs : list A],
    SetoidList.NoDupA eqA (x :: xs) -> SetoidList.NoDupA eqA (xs ++ [x]).
  Proof.
    intros A eqA E x xs H.
    induction xs as [| x' xs].
    - cbn; assumption.
    - change (SetoidList.NoDupA eqA ([x] ++ x' :: xs)) in H.
      apply (SetoidList.NoDupA_swap E) in H.
      change (SetoidList.NoDupA eqA (([x'] ++ xs) ++ [x])).
      rewrite <- app_assoc.
      apply (SetoidList.NoDupA_app E).
      + apply SetoidList.NoDupA_singleton.
      + apply IHxs.
        apply (NoDupA_cons E) in H.
        assumption.
      + intros z Eq_z_x' In_z.
        rewrite SetoidList.InA_singleton in Eq_z_x'.
        apply SetoidList.InA_app in In_z.
        destruct In_z as [In_z | Eq_z_x].
        * assert (L : ~ eqA z x').
          {
            apply (NoDupA_in_tl E (x :: xs)).
            - apply SetoidList.NoDupA_cons.
              + exfalso.
                assert (C1 : ~ eqA x' x').
                {
                  apply (NoDupA_in_tl E (x :: xs) H).
                  apply SetoidList.InA_cons_tl.
                  apply (SetoidList.InA_eqA E Eq_z_x').
                  assumption.
                }
                assert (C2 : eqA x' x'); [ setoid_reflexivity | tauto ].
              + apply NoDupA_cons in H; assumption.
            - apply (SetoidList.InA_eqA E Eq_z_x').
              apply SetoidList.InA_cons.
              tauto.
          }
          tauto.
        * rewrite SetoidList.InA_singleton in Eq_z_x.
          apply (NoDupA_eqA E) in H.
          setoid_symmetry in Eq_z_x'.
          assert (L : eqA x' x); [ setoid_transitivity z; assumption | idtac ].
          tauto.
  Qed.

  Lemma NoDupA_app_cons_swap : forall [A] [eqA : A -> A -> Prop] (E : RelationClasses.Equivalence eqA) (x : A) (xs : list A),
    SetoidList.NoDupA eqA (x :: xs) <-> SetoidList.NoDupA eqA (xs ++ [x]).
  Proof.
    intros.
    split; intro H.
    - apply (NoDupA_app_cons_swap_h E H).
    - apply (SetoidList.NoDupA_swap E) in H.
      rewrite app_nil_r in H.
      assumption.
  Qed.

  Lemma NoDupA_app_comm : forall [A] [eqA : A -> A -> Prop] (E : RelationClasses.Equivalence eqA) (xs ys : list A),
    SetoidList.NoDupA eqA (xs ++ ys) <-> SetoidList.NoDupA eqA (ys ++ xs).
  Proof.
    intros A eqA E xs ys.
    revert xs.
    induction ys as [| y ys].
    - intros xs; cbn in *; rewrite app_nil_r; reflexivity.
    - intros xs.
      rewrite <- app_comm_cons.
      rewrite (NoDupA_app_cons_swap E).
      rewrite <- app_assoc.
      change (SetoidList.NoDupA eqA (xs ++ [y] ++ ys) <-> SetoidList.NoDupA eqA (ys ++ xs ++ [y])).
      rewrite app_assoc.
      rewrite IHys.
      reflexivity.
  Qed.

  Lemma proper_eqlist_NoDupA : forall [A] [eqA : A -> A -> Prop]
    (E : RelationClasses.Equivalence eqA),
    Proper (SetoidList.eqlistA eqA ==> flip impl) (SetoidList.NoDupA eqA).
  Proof.
    intros A eqA E xs ys Hxy.
    unfold flip, impl.
    intros NoDup.
    induction Hxy as [| x y xs ys].
    - apply SetoidList.NoDupA_nil.
    - apply SetoidList.NoDupA_cons.
      + setoid_rewrite H.
        setoid_rewrite Hxy.
        unfold not.
        intro y_in_ys.
        apply (NoDupA_in_tl E ys NoDup y_in_ys).
        setoid_reflexivity.
      + apply IHHxy.
        apply (NoDupA_cons E NoDup).
  Qed.

  Lemma eqlistA_cons_iff : forall [A] [eqA : A -> A -> Prop] (E : Equivalence eqA) x xs y ys,
    SetoidList.eqlistA eqA (x :: xs) (y :: ys) <-> eqA x y /\ SetoidList.eqlistA eqA xs ys.
  Proof.
    intros.
    repeat rewrite SetoidList.eqlistA_altdef.
    apply Forall2_cons_iff.
  Qed.

  Lemma eqlistA_weaken : forall [A] [eqA eqB : A -> A -> Prop]
    (EA : RelationClasses.Equivalence eqA)
    (EB : RelationClasses.Equivalence eqB)
    (Weak : forall x y, eqA x y -> eqB x y)
    [xs ys],
    SetoidList.eqlistA eqA xs ys -> SetoidList.eqlistA eqB xs ys.
  Proof.
    intros A eqA eqB EA EB Weak xs ys H.
    induction H as [| x y xs ys IH H Tl].
    - apply SetoidList.eqlistA_nil.
    - rewrite (eqlistA_cons_iff EB).
      split.
      + apply (Weak x y IH).
      + apply Tl.
  Qed.

  Lemma proper_eqlist_NoDupA_Weak : forall [A] [eqA eqB : A -> A -> Prop]
    (EA : RelationClasses.Equivalence eqA)
    (EB : RelationClasses.Equivalence eqB)
    (Weak : forall x y, eqA x y -> eqB x y),
    Proper (SetoidList.eqlistA eqA ==> flip impl) (SetoidList.NoDupA eqB).
  Proof.
    intros A eqA eqB EA EB Weak xs ys Hxy.
    unfold flip, impl.
    intros NoDup.
    induction Hxy as [| x y xs ys].
    - apply SetoidList.NoDupA_nil.
    - apply SetoidList.NoDupA_cons.
      + assert (L : SetoidList.eqlistA eqB xs ys). {
          apply (eqlistA_weaken EA EB Weak Hxy).
        }
        apply Weak in H.
        setoid_rewrite H.
        setoid_rewrite L.
        unfold not.
        intro y_in_ys.
        apply (NoDupA_in_tl EB ys NoDup y_in_ys).
        setoid_reflexivity.
      + apply IHHxy.
        apply (NoDupA_cons EB NoDup).
  Qed.

  Instance NoDupA_proper_key
    : Proper (SetoidList.eqlistA (IdMap.eq_key (elt:=value)) ==> flip impl) (SetoidList.NoDupA (IdMap.eq_key (elt:=value))) :=
    proper_eqlist_NoDupA (key_equiv value).

  Instance NoDupA_proper_key_value
    : Proper (SetoidList.eqlistA (IdMapP.O.eqke (elt:=value)) ==> flip impl) (SetoidList.NoDupA (IdMapP.O.eqke (elt:=value))) :=
    proper_eqlist_NoDupA (key_value_equiv value).

  Lemma eqke_is_eqk : forall x y, IdMapP.O.eqke (elt:=value) x y -> IdMap.eq_key (elt:=value) x y.
  Proof.
    unfold IdMapP.O.eqke, IdMap.eq_key, IdMap.Raw.PX.eqk.
    easy.
  Qed.

  Instance NoDupA_proper_key_value_to_key
    : Proper (SetoidList.eqlistA (IdMapP.O.eqke (elt:=value)) ==> flip impl) (SetoidList.NoDupA (IdMap.eq_key (elt:=value))) :=
    proper_eqlist_NoDupA_Weak (key_value_equiv value) (key_equiv value) eqke_is_eqk.

  Lemma min_elt_None_iff : forall [A] (m : IdMap.t A), IdMapP.min_elt m = None <-> IdMap.Empty (elt:=A) m.
  Proof.
    intros A m.
    split.
    - apply IdMapP.min_elt_Empty.
    - intros H.
      unfold IdMapP.min_elt.
      rewrite IdMapP.P.elements_Empty in H.
      rewrite H.
      reflexivity.
  Qed.

  Lemma min_elt_elements_iff : forall [A] (m : IdMap.t A), IdMapP.min_elt m = None <-> IdMap.elements m = [].
  Proof.
    intros A m.
    unfold IdMapP.min_elt.
    case_eq (IdMap.elements m).
    - intros; split; reflexivity.
    - intros kv ? ?.
      destruct kv; split; intros; discriminate.
  Qed.

  Lemma min_elt_elements : forall [A] (m : IdMap.t A) k v,
    IdMapP.min_elt m = Some (k, v) <-> IdMap.elements m = (k, v) :: tl (IdMap.elements m).
  Proof.
    intros A m k v.
    split; intros H.
    - unfold IdMapP.min_elt in H.
      case_eq (IdMap.elements m).
      + intros Elems_m.
        rewrite Elems_m in H.
        discriminate.
      + intros m_kv ? Elems_m.
        destruct m_kv as (km, vm).
        rewrite Elems_m in H.
        injection H; intros; subst.
        cbn.
        reflexivity.
    - unfold IdMapP.min_elt.
      case_eq (IdMap.elements m).
      + intros Elems_m.
        rewrite Elems_m in H.
        cbn in H.
        discriminate.
      + intros m_kv ? Elems_m.
        destruct m_kv as (km, vm).
        rewrite Elems_m in H.
        cbn in H.
        injection H; intros; subst.
        reflexivity.
  Qed.

  Lemma min_elt_elements_right : forall [A] (m : IdMap.t A) k v,
    IdMapP.min_elt m = Some (k, v) -> IdMap.elements m = (k, v) :: tl (IdMap.elements m).
  Proof.
    intros A m k v.
    apply min_elt_elements.
  Qed.

  Lemma find_none_Empty : forall [A] (m : IdMap.t A), (forall k, IdMap.find k m = None) <-> IdMap.Empty m.
  Proof.
    intros A m.
    split; intros H.
    - assert (L : IdMap.Equal m (IdMap.empty A)).
      {
        rewrite IdMapP.P.F.Equal_mapsto_iff.
        intros k ?.
        split; intros M.
        - apply IdMapP.P.F.find_mapsto_iff in M.
          specialize (H k).
          rewrite H in M.
          discriminate.
        - apply IdMapP.P.F.empty_mapsto_iff in M.
          tauto.
      }
      setoid_rewrite L.
      apply (IdMap.empty_1).
    - intros k.
      apply Empty_Equal_empty in H.
      setoid_rewrite H.
      apply IdMapP.P.F.empty_o.
  Qed.

  Lemma Equal_add_remove : forall [A] k v (m : IdMap.t A), IdMap.MapsTo k v m -> IdMap.Equal m (IdMap.add k v (IdMap.remove k m)).
  Proof.
    intros A k v m H.
    rewrite IdMapP.P.F.Equal_mapsto_iff.
    intros k' v'.
    case_eq (id_eqb k k'); intros KE.
    - split.
      + intros M'.
        assert (Same_v : v = v').
        {
          apply (IdMapP.P.F.MapsTo_fun H).
          apply (fun P => IdMap.MapsTo_1 P M').
          is_true_simp.
        }
        rewrite Same_v.
        apply IdMap.add_1.
        is_true_simp.
      + intros M_add_rem.
        apply IdMapP.P.F.add_mapsto_iff in M_add_rem.
        destruct M_add_rem.
        * destruct H0.
          rewrite <- H1.
          apply (fun P => IdMap.MapsTo_1 P H).
          is_true_simp.
        * destruct H0.
          rewrite KE in H0.
          apply negb_prop_intro in H0.
          apply Is_true_eq_true in H0.
          cbn in H0.
          discriminate.
    - split.
      + intros M'.
        apply IdMapP.P.F.add_mapsto_iff.
        apply or_intror.
        split.
        * apply negb_prop_elim.
          apply Is_true_eq_left.
          apply negb_true_iff.
          apply KE.
        * apply IdMapP.P.F.remove_mapsto_iff.
          split.
          ** apply negb_prop_elim.
             apply Is_true_eq_left.
             apply negb_true_iff.
             apply KE.
          ** assumption.
      + intros M_add_rem.
        apply IdMapP.P.F.add_mapsto_iff in M_add_rem.
        destruct M_add_rem.
        * destruct H0.
          apply Is_true_eq_true in H0.
          rewrite KE in H0.
          discriminate.
        * destruct H0.
          apply IdMapP.P.F.remove_mapsto_iff in H1.
          tauto.
  Qed.

  Lemma elements_cons_mapsto : forall [A] [k v] [m : IdMap.t A] elems,
    SetoidList.eqlistA (IdMapP.O.eqke (elt:=A))
      (IdMap.elements m)
      ((k, v) :: elems) ->
    IdMap.MapsTo k v m.
  Proof.
    intros A k v m elems H.
    case_eq (IdMap.elements m).
    - intros Empty.
      rewrite Empty in H.
      apply SetoidList.eqlistA_length in H.
      cbn in H.
      discriminate.
    - intros p ? Not_empty.
      rewrite Not_empty in H.
      rewrite (eqlistA_cons_iff (key_value_equiv A)) in H.
      destruct p as (k', v').
      destruct H as [H1 H2].
      unfold IdMapP.O.eqke in H1.
      destruct H1 as [KE VE].
      cbn in VE.
      rewrite <- VE.
      cbn iota beta delta - [id_eqb] in KE.
      apply IdMap.elements_2.
      rewrite Not_empty.
      rewrite SetoidList.InA_cons.
      apply or_introl.
      unfold IdMap.eq_key_elt, IdMap.Raw.PX.eqke.
      cbn iota beta delta - [id_eqb].
      easy.
  Qed.

  Lemma add_empty : forall {A k v}, IdMap.elements (IdMap.add k v (IdMap.empty A)) = [(k, v)].
  Proof.
    intros A k v.
    unfold IdMap.empty, IdMap.add, IdMap.elements, IdMap.Raw.elements.
    reflexivity.
  Qed.

  Lemma In_key_diff : forall [A] [m : IdMap.t A] [k k' : id], ~ IdMap.In k m -> IdMap.In k' m -> id_eqb k k' = false.
  Proof.
    intros A m k k' NI I.
    apply IdMapP.P.F.not_find_in_iff in NI.
    case_eq (id_eqb k k'); intros K.
    - exfalso.
      apply IdMapP.P.F.not_find_in_iff in I.
      + apply I.
      + rewrite <- NI.
        apply IdMapP.P.F.find_o.
        is_true_simp.
    - reflexivity.
  Qed.

  Lemma id_eqb_ltb_compat_left : forall x y z, id_eqb x y = true -> id_ltb x z = true -> id_ltb y z = true.
  Proof.
    destruct x as [x_aux x_l].
    destruct y as [y_aux y_l].
    destruct z as [z_aux z_l].
    destruct x_aux as [| | x_s | x_s]; destruct y_aux as [| | y_s | y_s]; destruct z_aux as [| | z_s | z_s].
    all: cbn; try easy.
    all: (
      intros H;
      apply (id_eqb_string_is_eq x_s y_s x_l y_l) in H;
      rewrite H;
      tauto
    ).
  Qed.

  Lemma sorted_keys : forall [A] [k k' v v' xs ys],
    id_eqb k k' = false ->
    Sorted.Sorted (IdMap.lt_key (elt:=A)) xs ->
    SetoidList.InA (IdMapP.O.eqke (elt:=A)) (k', v') xs ->
    SetoidList.eqlistA (IdMapP.O.eqke (elt:=A)) xs ((k, v) :: ys) ->
    id_ltb k k' = true.
  Proof.
    intros A k k' v v' xs ys Key_neq Sorted_xs In_xs Eq.
    destruct xs as [| x xs].
    - apply SetoidList.InA_nil in In_xs. easy.
    - destruct x as (hd_k, hd_v).
      apply Sorted.Sorted_inv in Sorted_xs.
      destruct Sorted_xs as [Sorted_xs HdRel_xs].
      apply SetoidList.InA_cons in In_xs.
      apply (eqlistA_cons_iff (key_value_equiv A)) in Eq.
      destruct Eq as [Eq_hd Eq_xs].

      destruct In_xs as [H | In_xs].
      + exfalso.
        unfold IdMapP.O.eqke in H, Eq_hd.
        destruct H as [H _].
        destruct Eq_hd as [Eq_hd _].
        cbn beta delta - [id_eqb] iota in H, Eq_hd.
        is_true_simp.
        assert (T := id_eqb_trans _ _ _ H Eq_hd).
        apply id_eqb_sym in T.
        rewrite Key_neq in T.
        discriminate.
      + assert (L : IdMap.lt_key (elt:=A) (hd_k, hd_v) (k', v')).
        {
          apply (fun SO P => SetoidList.SortA_InfA_InA (key_value_equiv A) SO P Sorted_xs HdRel_xs In_xs);
          auto with typeclass_instances.
        }
        unfold IdMap.lt_key, IdMap.Raw.PX.ltk in L.
        cbn beta delta - [id_ltb] iota in L.
        unfold IdMapP.O.eqke in Eq_hd.
        destruct Eq_hd as [Eq_hd _].
        cbn beta delta - [id_eqb] iota in Eq_hd.
        is_true_simp.
        apply (id_eqb_ltb_compat_left _ _ _ Eq_hd L).
  Qed.

  Lemma in_elements : forall [A] [m : IdMap.t A] [k], IdMap.In k m -> exists v, SetoidList.InA (IdMapP.O.eqke (elt:=A)) (k, v) (IdMap.elements m).
  Proof.
    intros A m k H.
    change (exists v, IdMap.MapsTo k v m) in H.
    destruct H as [v].
    exists v.
    apply (IdMap.elements_1 H).
  Qed.

  Lemma elements_csubsts_remove_h : forall substs k v elems,
    SetoidList.eqlistA (IdMapP.O.eqke (elt:=value)) (IdMap.elements substs) ((k, v) :: elems) ->
    SetoidList.eqlistA (IdMapP.O.eqke (elt:=value)) (IdMap.elements (IdMap.remove k substs)) elems.
  Proof.
    intros substs k v elems H.
    assert (Remove_k : ~ IdMap.In (elt:=value) k (IdMap.remove k substs)).
    {
      apply IdMap.remove_1.
      is_true_solve.
    }
    assert (Below_remove : IdMapP.Below k (IdMap.remove (elt:=value) k substs)).
    {
      unfold IdMapP.Below.
      intros k' In_substs.
      is_true_simp.
      assert (Not_k : id_eqb k k' = false).
      {
        apply (In_key_diff Remove_k In_substs).
      }
      rewrite IdMapP.P.F.remove_neq_in_iff in In_substs; [ idtac | is_true_simp ].
      apply in_elements in In_substs.
      destruct In_substs as [v' In_substs].
      apply (fun S => sorted_keys Not_k S In_substs H).
      apply IdMap.elements_3.
    }
    assert (Add_Remove : IdMapP.P.Add k v (IdMap.remove k substs) substs).
    {
      unfold IdMapP.P.Add.
      intros k'.
      apply (IdMapP.P.F.find_m).
      - is_true_simp.
      - apply Equal_add_remove.
        apply (elements_cons_mapsto elems H).
    }
    setoid_rewrite (@IdMapP.elements_Add_Below value (IdMap.remove k substs) substs k v Below_remove Add_Remove) in H.
    rewrite (eqlistA_cons_iff (key_value_equiv value)) in H.
    destruct H as [H_hd H_tl].
    setoid_rewrite <- H_tl.
    setoid_reflexivity.
  Qed.

  Lemma eqlistA_map_remove_comm : forall [A B] [f : A -> B] [k : IdMap.key] (m : IdMap.t A),
    SetoidList.eqlistA (IdMapP.O.eqke (elt:=B))
      (IdMap.elements (IdMap.map f (IdMap.remove k m)))
      (IdMap.elements (IdMap.remove k (IdMap.map f m))).
  Proof.
    intros A B f k m.
    apply IdMapP.elements_Equal_eqlistA.
    unfold IdMap.Equal.
    apply find_map_remove_comm.
  Qed.

  Lemma elements_complete_substs_remove : forall substs k v elems,
    SetoidList.eqlistA (IdMapP.O.eqke (elt:=value)) (IdMap.elements (complete_bindings substs)) ((k, v) :: elems) ->
    SetoidList.eqlistA (IdMapP.O.eqke (elt:=value)) (IdMap.elements (complete_bindings (IdMap.remove k substs))) elems.
  Proof.
    intros substs k v elems H.
    unfold complete_bindings in *.
    setoid_rewrite (eqlistA_map_remove_comm substs).
    setoid_rewrite <- (elements_csubsts_remove_h _ _ _ _ H).
    setoid_reflexivity.
  Qed.

  #[local]
  Obligation Tactic := solve [ program_simpl; try easy; cbn; try lia ] + program_simpl.

  Program Fixpoint step (orig_exp : exp Tannot.t) {measure (depth orig_exp)} : t (exp Tannot.t) :=
    let 'E_aux aux annot := orig_exp in
    let wrap e_aux' := pure (E_aux e_aux' annot) in
    match aux with
    | E_block xs =>
        match xs with
        | [] => wrap (E_internal_value V_unit)
        | [E_aux (E_internal_value v) annot] => wrap (E_internal_value v)
        | [E_aux (E_block ys) annot] => wrap (E_block ys)
        | x :: xs =>
            if is_value x then
              wrap (E_block xs)
            else
              x' ← step x;
              wrap (E_block (x' :: xs))
        end
    | E_id id =>
        match Tannot.get_id_type (snd annot) id with
        | Global_register =>
            Read_var (PL_id id Var_register) (fun v => wrap (E_internal_value v))
        | Local_variable =>
            Read_var (PL_id id Var_local) (fun v => wrap (E_internal_value v))
        | Enum_member =>
            wrap (E_internal_value (V_member id))
        end
    | E_return x =>
        match get_value x with
        | Evaluated v => Early_return v
        | Unevaluated =>
            x' ← step x;
            wrap (E_return x')
        end
    | E_assign lx x =>
        let subexps := lexp_subexps lx in
        let '(evaluated, unevaluated) := left_to_right subexps in
        match unevaluated with
        | u :: us =>
            u' ← step u;
            let '(l', _) := update_lexp_subexps (evaluated ++ (u' :: us)) lx in
            wrap (E_assign l' x)
        | [] =>
            match get_value x with
            | Evaluated v =>
                d ← lexp_to_destructure lx;
                _ ← destructuring_assignment annot d v;
                wrap (E_internal_value V_unit)
            | Unevaluated =>
                x' ← step x;
                wrap (E_assign lx x')
            end
        end
    | E_var l x body => wrap (E_block (E_aux (E_assign l x) annot :: [body]))
    | E_match head_exp arms =>
        match head_exp with
        | E_aux (E_internal_value v) _ =>
            match arms with
            | Pat_aux (Pat_exp pat body) _ :: next_arms =>
                match pattern_match pat v with
                | Matched arm_substs =>
                    pure (IdMap.fold (fun id v body => substitute id v body) (complete_bindings arm_substs) body)
                | _ =>
                    wrap (E_match head_exp next_arms)
                end
            | Pat_aux (Pat_when pat guard body) pexp_annot :: next_arms =>
                match pattern_match pat v with
                | Matched arm_substs =>
                    let guard := IdMap.fold (fun id v g => substitute id v g) (complete_bindings arm_substs) guard in
                    match guard with
                    | E_aux (E_internal_value v_guard) _ =>
                        match v_guard with
                        | V_bool true =>
                            match pattern_match pat v with
                            | Matched arm_substs =>
                                pure (IdMap.fold (fun id v body => substitute id v body) (complete_bindings arm_substs) body)
                            | _ =>
                                wrap (E_match head_exp next_arms)
                            end
                        | V_bool false =>
                            wrap (E_match head_exp next_arms)
                        | _ => Runtime_type_error (fst pexp_annot)
                        end
                    | _ =>
                        guard' ← step guard;
                        wrap (E_match head_exp (Pat_aux (Pat_when pat guard' body) pexp_annot :: next_arms))
                    end
                | _ =>
                    wrap (E_match head_exp next_arms)
                end
            | [] => Match_failure (fst annot)
            end
        | _ =>
            head_exp' ← step head_exp;
            wrap (E_match head_exp' arms)
        end
    | E_let pat x body =>
        match x with
        | E_aux (E_internal_value v) _ =>
            match pattern_match pat v with
            | Matched body_substs =>
                pure (IdMap.fold (fun id v body => substitute id v body) (complete_bindings body_substs) body)
            | _ =>
                Match_failure (fst annot)
            end
        | _ =>
            x' ← step x;
            wrap (E_let pat x' body)
        end
    | E_lit lit =>
        wrap (E_internal_value (value_of_lit lit))
    | E_tuple xs =>
        let '(evaluated, unevaluated) := left_to_right xs in
        match unevaluated with
        | x :: xs =>
            x' ← step x;
            wrap (E_tuple (evaluated ++ (x' :: xs)))
        | [] => wrap (E_internal_value (V_tuple (all_evaluated evaluated)))
        end
    | E_typ _ x => step x
    | E_app id args =>
        match id with
        | Id_aux Or_bool _ =>
            match args with
            | [lhs; rhs] =>
                b ← get_bool lhs;
                match b with
                | Evaluated true => wrap (E_internal_value (V_bool true))
                | Evaluated false => pure rhs
                | Unevaluated =>
                    lhs' ← step lhs;
                    wrap (E_app id [lhs'; rhs])
                end
            | _ => Runtime_type_error (fst annot)
            end
        | Id_aux And_bool _ =>
            match args with
            | [lhs; rhs] =>
                b ← get_bool lhs;
                match b with
                | Evaluated true => pure rhs
                | Evaluated false => wrap (E_internal_value (V_bool false))
                | Unevaluated =>
                    lhs' ← step lhs;
                    wrap (E_app id [lhs'; rhs])
                end
            | _ => Runtime_type_error (fst annot)
            end
        | _ =>
            let '(evaluated, unevaluated) := left_to_right args in
            match unevaluated with
            | u :: us =>
                u' ← step u;
                wrap (E_app id (evaluated ++ (u' :: us)))
            | [] =>
                r ← Call id (all_evaluated evaluated) pure;
                match r with
                | Return_ok v => wrap (E_internal_value v)
                | Return_exception exn => wrap (E_throw (E_aux (E_internal_value exn) annot))
                end
            end
        end
    | E_if i t e =>
        b ← get_bool i;
        match b with
        | Unevaluated =>
            i' ← step i;
            wrap (E_if i' t e)
        | Evaluated true => pure t
        | Evaluated false => pure e
        end
    | E_assert x msg =>
        b ← get_bool x;
        match b with
        | Unevaluated =>
            x' ← step x;
            wrap (E_assert x' msg)
        | Evaluated b =>
            s ← get_string msg;
            match s with
            | Unevaluated =>
                msg' ← step msg;
                wrap (E_assert x msg')
            | Evaluated s =>
                if b then
                  wrap (E_internal_value V_unit)
                else
                  Assertion_failed s
            end
        end
    | E_field x f =>
        match get_value x with
        | Evaluated v =>
            match v with
            | V_record fields =>
                v_field ← lookup_field (fst annot) f fields;
                wrap (E_internal_value v_field)
            | _ => Runtime_type_error (fst annot)
            end
        | Unevaluated =>
            x' ← step x;
            wrap (E_field x' f)
        end
    | E_struct struct_id fs =>
        let '(evaluated, unevaluated) := left_to_right_fields fs in
        match unevaluated with
        | FE_aux (FE_fexp name x) annot :: xs =>
            x' ← step x;
            wrap (E_struct struct_id (evaluated ++ (FE_aux (FE_fexp name x') annot :: xs)))
        | [] =>
            wrap (E_internal_value (V_record (all_evaluated_fields evaluated)))
        end
    | E_struct_update x fs =>
        match x with
        | E_aux (E_internal_value (V_record fields)) _ =>
            let '(evaluated, unevaluated) := left_to_right_fields fs in
            match unevaluated with
            | FE_aux (FE_fexp name y) annot :: ys =>
                y' ← step y;
                wrap (E_struct_update x (evaluated ++ (FE_aux (FE_fexp name y') annot :: ys)))
            | [] =>
                let updates := all_evaluated_fields evaluated in
                let fields := fold_left (fun fields s => update_field (fst s) (snd s) fields) updates fields in
                wrap (E_internal_value (V_record fields))
            end
        | E_aux (E_internal_value _) _ => Runtime_type_error (fst annot)
        | _ =>
            x' ← step x;
            wrap (E_struct_update x' fs)
        end
    | E_vector xs =>
        let '(evaluated, unevaluated) := left_to_right xs in
        match unevaluated with
        | u :: us =>
            u' ← step u;
            wrap (E_vector (evaluated ++ (u' :: us)))
        | [] =>
            if Tannot.is_bitvector (snd annot) then
              bits ← bv_concat (fst annot) (all_evaluated evaluated);
              wrap (E_internal_value (V_bitvector bits))
            else
              wrap (E_internal_value (V_vector (all_evaluated evaluated)))
        end
    | E_list xs =>
        let '(evaluated, unevaluated) := left_to_right xs in
        match unevaluated with
        | u :: us =>
            u' ← step u;
            wrap (E_list (evaluated ++ (u' :: us)))
        | [] =>
            wrap (E_internal_value (V_list (all_evaluated evaluated)))
        end
    | E_cons x xs =>
        match left_to_right2 x xs with
        | LTR2_0 _ _ =>
            x' ← step x;
            wrap (E_cons x' xs)
        | LTR2_1 _ _ =>
            xs' ← step xs;
            wrap (E_cons x xs')
        | LTR2_2 vx vxs =>
            match vxs with
            | V_list elems =>
                wrap (E_internal_value (V_list (vx :: elems)))
            | _ =>
                Runtime_type_error (fst annot)
            end
        end
    | E_throw x =>
        match get_value x with
        | Evaluated v =>
            throw v
        | Unevaluated =>
            x' ← step x;
            wrap (E_throw x')
        end
    | E_try x arms =>
        match x with
        | E_aux (E_internal_value v) annot => pure (E_aux (E_internal_value v) annot)
        | _ =>
            x' ← catch (step x);
            match x' with
            | Caught exn => wrap (E_match (E_aux (E_internal_value exn) annot) (arms ++ [Tannot.fallthrough]))
            | Continue x'' => wrap (E_try x'' arms)
            end
        end
    | E_internal_value v => wrap (E_internal_value v)
    | E_ref register_name =>
        wrap (E_internal_value (V_ref register_name))
    | E_loop While measure cond body =>
        wrap (E_if cond (E_aux (E_block [body; orig_exp]) annot) (E_aux (E_internal_value V_unit) annot))
    | E_loop Until measure cond body =>
        wrap (E_block [body; E_aux (E_if cond (E_aux (E_internal_value V_unit) annot) orig_exp) annot])
    | E_for loop_var from to amount ord body =>
        match left_to_right3 from to amount with
        | LTR3_0 _ _ _ =>
            from' ← step from;
            wrap (E_for loop_var from' to amount ord body)
        | LTR3_1 _ _ _ =>
            to' ← step to;
            wrap (E_for loop_var from to' amount ord body)
        | LTR3_2 _ _ _ =>
            amount' ← step amount;
            wrap (E_for loop_var from to amount' ord body)
        | LTR3_3 v_from v_to v_amount =>
            match ord with
            | Ord_aux Ord_inc _ =>
                cmp ← lift_option (fst annot) (Primops.gt_int v_from v_to);
                match cmp with
                | V_bool true => wrap (E_internal_value V_unit)
                | V_bool false =>
                    next ← lift_option (fst annot) (Primops.add_int v_from v_amount);
                    wrap
                      (E_block
                         [
                           substitute loop_var v_from body;
                           E_aux (E_for loop_var (E_aux (E_internal_value next) annot) to amount ord body) annot
                         ]
                      )
                | _ => Runtime_type_error (fst annot)
                end
            | Ord_aux Ord_dec _ =>
                cmp ← lift_option (fst annot) (Primops.lt_int v_from v_to);
                match cmp with
                | V_bool true => wrap (E_internal_value V_unit)
                | V_bool false =>
                    next ← lift_option (fst annot) (Primops.sub_int v_from v_amount);
                    wrap
                      (E_block
                         [
                           substitute loop_var v_from body;
                           E_aux (E_for loop_var (E_aux (E_internal_value next) annot) to amount ord body) annot
                         ]
                      )
                | _ => Runtime_type_error (fst annot)
                end
            end
        end
    | E_undef =>
        u ← get_undefined (Tannot.get_type (snd annot));
        wrap (E_internal_value u)
    | E_vector_append _ _ => Runtime_type_error (fst annot)
    | E_sizeof _ => Runtime_type_error (fst annot)
    | E_constraint _ => Runtime_type_error (fst annot)
    | E_exit _ => Runtime_type_error (fst annot)
    | E_config _ => Runtime_type_error (fst annot)
    | E_internal_plet _ _ _ => Runtime_type_error (fst annot)
    | E_internal_return _ => Runtime_type_error (fst annot)
    | E_internal_assume _ _ => Runtime_type_error (fst annot)
    end.
  Next Obligation.
    cbn.
    rewrite ltr_tuple in Heq_anonymous.
    apply max_lhs_plus_1_le.
    apply (PeanoNat.Nat.le_trans _ (fold_right max 0 (map depth (lexp_subexps lx))) _).
    rewrite <- (take_drop_evaluated_concat Tannot.t (lexp_subexps lx)).
    inversion Heq_anonymous.
    rewrite map_app.
    rewrite fold_right_app.
    cbn.
    apply fold_right_max_acc2.
    lia.
    apply lexp_subexps_depth.
  Defined.
  Next Obligation.
    clear Heq_anonymous.
    clear n.
    rewrite IdMap.fold_1.
    remember (IdMap.elements (complete_bindings arm_substs)) as elems.
    apply eq_sym in Heqelems.
    apply (equiv_cong (SetoidList.eqlistA_equiv (key_value_equiv value))) in Heqelems.
    revert Heqelems.
    revert arm_substs.
    induction elems.
    - cbn; lia.
    - intros. destruct a.
      rewrite substitute_fold.
      rewrite substitute_fold in IHelems.
      cbn.
      apply (PeanoNat.Nat.le_lt_trans _ _ _ (depth_subst _ _ _)).
      apply (IHelems (IdMap.remove k arm_substs)).
      + apply (elements_complete_substs_remove _ _ _ _ Heqelems).
      + assert (E := SetoidList.eqlistA_equiv (key_value_equiv value)).
        assert (Q := elements_complete_substs_remove _ _ _ _ Heqelems).
        setoid_rewrite <- Q.
        apply IdMap.elements_3w.
      + setoid_rewrite <- Heqelems.
        apply IdMap.elements_3w.
  Defined.
  Next Obligation.
    cbn.
    rewrite ltr_tuple in Heq_anonymous.
    inversion Heq_anonymous.
    rewrite <- (take_drop_evaluated_concat Tannot.t xs0).
    rewrite <- H1.
    rewrite <- H0.
    rewrite map_app.
    rewrite fold_right_app.
    cbn.
    apply fold_right_max_acc.
    lia.
  Defined.
  Next Obligation.
    cbn.
    rewrite ltr_tuple in Heq_anonymous.
    inversion Heq_anonymous.
    rewrite <- (take_drop_evaluated_concat Tannot.t args).
    rewrite <- H3.
    rewrite <- H2.
    rewrite map_app.
    rewrite fold_right_app.
    cbn.
    apply fold_right_max_acc.
    lia.
  Defined.
  Next Obligation.
    rewrite ltr_fields_tuple in Heq_anonymous.
    inversion Heq_anonymous.
    rewrite <- (take_drop_evaluated_fields_concat Tannot.t _).
    rewrite <- H0.
    rewrite <- H1.
    cbn.
    rewrite map_app.
    rewrite fold_right_app.
    cbn.
    apply fold_right_max_acc.
    lia.
  Defined.
  Next Obligation.
    rewrite ltr_fields_tuple in Heq_anonymous.
    inversion Heq_anonymous.
    rewrite <- (take_drop_evaluated_fields_concat Tannot.t _).
    rewrite <- H0.
    rewrite <- H1.
    cbn.
    rewrite map_app.
    rewrite fold_right_app.
    cbn.
    apply fold_right_max_acc.
    lia.
  Defined.
  Next Obligation.
    cbn.
    rewrite ltr_tuple in Heq_anonymous.
    inversion Heq_anonymous.
    rewrite <- (take_drop_evaluated_concat Tannot.t xs).
    rewrite <- H1.
    rewrite <- H0.
    rewrite map_app.
    rewrite fold_right_app.
    cbn.
    apply fold_right_max_acc.
    lia.
  Defined.
  Final Obligation.
    cbn.
    rewrite ltr_tuple in Heq_anonymous.
    inversion Heq_anonymous.
    rewrite <- (take_drop_evaluated_concat Tannot.t xs).
    rewrite <- H1.
    rewrite <- H0.
    rewrite map_app.
    rewrite fold_right_app.
    cbn.
    apply fold_right_max_acc.
    lia.
  Defined.
End Make.
