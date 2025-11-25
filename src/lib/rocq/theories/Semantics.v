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

Require Import Value_type.
Require Import Ast.
Require Import AstInduction.
Require Import IdUtil.

Import ListNotations.

Inductive binding :=
| Complete : value -> binding
| Partial : list (value * Z * Z) -> binding.

Definition combine_binding (l r : option binding) : option binding :=
  match (l, r) with
  | (None, None) => None
  | (Some b, None) => Some b
  | (None, Some b) => Some b
  | (Some lb, Some rb) =>
      match (lb, rb) with
      | (Complete v, _) => Some (Complete v)
      | (_, Complete v) => Some (Complete v)
      | (Partial lv, Partial rv) => Some (Partial (lv ++ rv))
      end
  end.

Definition merge_bindings (l r : IdMap.t binding) : IdMap.t binding :=
  IdMap.map2 combine_binding l r.

Infix "⋈" := merge_bindings (right associativity, at level 60).

Definition to_gvector (v : value) : value :=
  match v with
  | V_bitvector bs => V_vector (List.map (fun b => V_bitvector [b]) bs)
  | v => v
  end.

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

Inductive id_type :=
| Local_variable : id_type
| Global_register : id_type
| Enum_member : id_type.

Inductive place : Set :=
| PL_id : id -> var_type -> place
| PL_register : string -> place
| PL_vector : place -> Z -> place
| PL_vector_range : place -> Z -> Z -> place
| PL_field : place -> id -> place.

Inductive vector_concat_split :=
| No_split : vector_concat_split
| Split : nat -> vector_concat_split.

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

  Theorem bind_left_id : forall (A B : Set) (f : A -> t B) (x : A), bind (pure x) f = f x.
  Proof.
    cbn. reflexivity.
  Qed.

  Theorem bind_right_id : forall (A : Set) (m : t A), bind m pure = m.
  Proof.
    induction m as [| | | | | | ? ? cont | ? cont | ? ? cont | ? cont]; try easy.
    all: cbn.
    all: f_equal.
    all: apply functional_extensionality.
    all: intros.
    all: specialize (H x).
    all: assumption.
  Qed.

  Theorem bind_assoc : forall (A B C : Set) (f : A -> t B) (g : B -> t C) (x : t A),
      bind (bind x f) g = bind x (fun y => bind (f y) g).
  Proof.
    induction x as [| | | | | | ? ? cont | ? cont | ? ? cont | ? cont]; try easy.
    all: cbn.
    all: f_equal.
    all: apply functional_extensionality.
    all: intros.
    all: remember (cont x) as z.
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
  induction xs.
  - cbn. reflexivity.
  - destruct a.
    destruct e.
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
  induction xs.
  - cbn.
    reflexivity.
  - destruct a.
    destruct e.
    all: cbn.
    all: try reflexivity.
    rewrite IHxs.
    reflexivity.
Qed.

Fixpoint all_evaluated_fields {A : Set} (f : id -> string) (xs : list (fexp A)) : list (string * value) :=
  match xs with
  | [] => []
  | FE_aux (FE_fexp id (E_aux (E_internal_value v) _)) _ :: xs =>
      (f id, v) :: all_evaluated_fields f xs
  | _ :: xs => all_evaluated_fields f xs
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
  induction fxs as [| fx fxs ].
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
  induction fxs as [| fx fxs ].
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
  induction zs.
  - cbn.
    lia.
  - cbn.
    lia.
Qed.

Lemma fold_right_max_acc2 : forall x y zs, x <= y -> x <= fold_right max y zs.
Proof.
  induction zs.
  - cbn.
    lia.
  - cbn.
    lia.
Qed.

Definition bitlist_of_hex_digit (h : hex_digit) : list bit :=
  match h with
  | Hex_0 => [B0; B0; B0; B0]
  | Hex_1 => [B0; B0; B0; B1]
  | Hex_2 => [B0; B0; B1; B0]
  | Hex_3 => [B0; B0; B1; B1]
  | Hex_4 => [B0; B1; B0; B0]
  | Hex_5 => [B0; B1; B0; B1]
  | Hex_6 => [B0; B1; B1; B0]
  | Hex_7 => [B0; B1; B1; B1]
  | Hex_8 => [B1; B0; B0; B0]
  | Hex_9 => [B1; B0; B0; B1]
  | Hex_A => [B1; B0; B1; B0]
  | Hex_B => [B1; B0; B1; B1]
  | Hex_C => [B1; B1; B0; B0]
  | Hex_D => [B1; B1; B0; B1]
  | Hex_E => [B1; B1; B1; B0]
  | Hex_F => [B1; B1; B1; B1]
  end.

Definition hex_digit_of_nibble (b1 b2 b3 b4 : bit) : hex_digit :=
  match (b1, b2, b3, b4) with
  | (B0, B0, B0, B0) => Hex_0
  | (B0, B0, B0, B1) => Hex_1
  | (B0, B0, B1, B0) => Hex_2
  | (B0, B0, B1, B1) => Hex_3
  | (B0, B1, B0, B0) => Hex_4
  | (B0, B1, B0, B1) => Hex_5
  | (B0, B1, B1, B0) => Hex_6
  | (B0, B1, B1, B1) => Hex_7
  | (B1, B0, B0, B0) => Hex_8
  | (B1, B0, B0, B1) => Hex_9
  | (B1, B0, B1, B0) => Hex_A
  | (B1, B0, B1, B1) => Hex_B
  | (B1, B1, B0, B0) => Hex_C
  | (B1, B1, B0, B1) => Hex_D
  | (B1, B1, B1, B0) => Hex_E
  | (B1, B1, B1, B1) => Hex_F
  end.

Fixpoint hex_digits_of_bitlist (bits : list bit) : option (list hex_digit) :=
  match bits with
  | b1 :: b2 :: b3 :: b4 :: rest =>
      let digit := hex_digit_of_nibble b1 b2 b3 b4 in
      match hex_digits_of_bitlist rest with
      | None => None
      | Some digits => Some (digit :: digits)
      end
  | [] => Some []
  | _ => None
  end.

Definition non_empty_to_list {A : Set} (xs : non_empty A) : list A :=
  let 'Non_empty y ys := xs in y :: ys.

Definition bitlist_of_hex_lit (hex : list (non_empty hex_digit)) : list bit :=
  let digits := List.concat (List.map non_empty_to_list hex) in
  List.concat (List.map bitlist_of_hex_digit digits).

Lemma hex_lit_bitlist_rt : forall (d : hex_digit), hex_digits_of_bitlist (bitlist_of_hex_lit [Non_empty d []]) = Some [d].
Proof.
  induction d.
  all: cbn.
  all: reflexivity.
Qed.

Definition bitlist_of_bin_lit (bin : list (non_empty bin_digit)) : list bit :=
  let digits := List.concat (List.map non_empty_to_list bin) in
  List.map (fun b =>
      match b with
      | Bin_0 => B0
      | Bin_1 => B1
      end
    ) digits.

(** Sail annotates terms with custom type annotation data, which we
    don't have access to here. Instead use a functor parameterised by
    the following SemanticExt signature, which can provide the methods we
    need. *)
Module Type SemanticExt.
  Parameter tannot : Set.

  Parameter get_type : tannot -> typ.

  Parameter get_id_type : tannot -> id -> id_type.

  Parameter get_split : tannot -> vector_concat_split.

  Parameter is_bitvector : tannot -> bool.

  Parameter num_equal : Z -> Z -> bool.

  Parameter rational_equal : rational -> rational -> bool.

  Parameter id_equal_string : id -> string -> bool.

  Parameter string_of_id : id -> string.

  Parameter rational_of_string : string -> rational.

  Parameter fallthrough : Ast.pexp tannot.

  Parameter complete_value : list (value * Z * Z) -> value.
End SemanticExt.

Module Make (T : SemanticExt).
  Fixpoint binds_id {A} (n : Ast.id) (p : Ast.pat A) : bool :=
    let 'P_aux aux annot := p in
    match aux with
    | P_lit _ | P_wild | P_not _ => false
    | P_id m => id_eqb n m
    | P_typ _ p | P_var p _ => binds_id n p
    | P_as pat m => binds_id n pat || id_eqb n m
    | P_tuple ps | P_list ps | P_vector ps | P_app _ ps | P_vector_concat ps | P_string_append ps =>
        fold_left orb (map (binds_id n) ps) false
    | P_or p1 p2 | P_cons p1 p2 => binds_id n p1 || binds_id n p2
    | P_struct _ ps _ => fold_left orb (map (fun fp => binds_id n (snd fp)) ps) false
    | P_vector_subrange m _ _ => id_eqb n m
    end.

  Fixpoint substitute {A} (n : Ast.id) (v : Value_type.value) (x : exp A) : exp A :=
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
    | E_let (LB_aux (LB_val pat y) lb_annot) body =>
        if binds_id n pat then
          E_aux (E_let (LB_aux (LB_val pat (substitute n v y)) lb_annot) body) annot
        else
          E_aux (E_let (LB_aux (LB_val pat (substitute n v y)) lb_annot) (substitute n v body)) annot
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
  with substitute_arm {A} (n : Ast.id) (v : Value_type.value) (arm : pexp A) : pexp A :=
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
  with substitute_lexp {A} (n : Ast.id) (v : Value_type.value) (l : lexp A) : lexp A :=
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

  Definition value_of_lit (lit : Ast.lit) (typ : Ast.typ) : t value :=
    let 'L_aux aux _ := lit in
    match aux with
    | L_unit => pure V_unit
    | L_true => pure (V_bool true)
    | L_false => pure (V_bool false)
    | L_num n => pure (V_int n)
    | L_hex h => pure (V_bitvector (bitlist_of_hex_lit h))
    | L_bin b => pure (V_bitvector (bitlist_of_bin_lit b))
    | L_real r => pure (V_real (T.rational_of_string r))
    | L_string s => pure (V_string s)
    | L_undef => get_undefined typ
    end.

  Definition same_bits (bs : list bit) (vs : list bit) : bool :=
    fst (fold_left
           (fun match_info b =>
              match match_info with
              | (_, []) => (false, [])
              | (false, _) => (false, [])
              | (true, B0 :: vs) =>
                match b with
                | B0 => (true, vs)
                | B1 => (false, [])
                end
              | (true, B1 :: vs) =>
                match b with
                | B1 => (true, vs)
                | B0 => (false, [])
                end
              end
           )
           bs
           (true, vs)).

  Lemma same_bits_cons : forall (b : bit) (bs : list bit),
      same_bits (b :: bs) (b :: bs) = same_bits bs bs.
  Proof.
    intros.
    destruct b.
    all: unfold same_bits.
    all: cbn.
    all: reflexivity.
  Qed.

  Lemma same_bits_refl : forall (bs : list bit),
      same_bits bs bs = true.
  Proof.
    induction bs.
    easy.
    rewrite same_bits_cons.
    assumption.
  Qed.

  Definition pattern_match_literal (l : Ast.lit) (v : value) : bool :=
    let 'L_aux aux annot := l in
    match (aux, v) with
    | (L_unit, V_unit) => true
    | (L_true, V_bool true) => true
    | (L_false, V_bool false) => true
    | (L_num n, V_int m) => T.num_equal n m
    | (L_hex s, V_bitvector vs) => same_bits (bitlist_of_hex_lit s) vs
    | (L_bin s, V_bitvector vs) => same_bits (bitlist_of_bin_lit s) vs
    | (L_string s1, V_string s2) => String.eqb s1 s2
    | (L_real r1, V_real r2) => T.rational_equal (T.rational_of_string r1) r2
    | _ => false
    end.

  Fixpoint get_struct_field (name : string) (fields : list (string * value)) {struct fields} : value :=
    match fields with
    | (name', v) :: rest_fields =>
        if String.eqb name name' then
          v
        else
          get_struct_field name rest_fields
    | [] => V_unit
    end.

  Definition no_match : bool * IdMap.t binding := (false, @IdMap.empty binding).

  Definition empty_bindings : IdMap.t binding := @IdMap.empty binding.

  Definition complete_bindings (m : IdMap.t binding) : IdMap.t value :=
    IdMap.map
      (fun b =>
         match b with
         | Complete v => v
         | Partial vs => T.complete_value vs
         end
      )
      m.

  Fixpoint pattern_match (p : Ast.pat T.tannot) (v : value) {struct p} : bool * IdMap.t binding :=
    let 'P_aux aux annot := p in
    match aux with
    | P_wild => (true, [])
    | P_id n =>
        match T.get_id_type (snd annot) n with
        | Enum_member =>
            match v with
            | V_member m =>
                (T.id_equal_string n m, empty_bindings)
            | _ => no_match
            end
        | _ =>
            (true, IdMap.add n (Complete v) empty_bindings)
        end
    | P_typ _ p => pattern_match p v
    | P_lit l => (pattern_match_literal l v, empty_bindings)
    | P_as p n =>
        let '(matched, bindings) := pattern_match p v in
        (matched, IdMap.add n (Complete v) bindings)
    | P_app ctor ps =>
        match v with
        | V_ctor v_ctor vs =>
            if T.id_equal_string ctor v_ctor then
              fst (fold_left
                     (fun match_info p =>
                        match match_info with
                        (* The arguments and pattern are different lengths, so no match *)
                        | (_, []) => (no_match, [])
                        (* A previous argument pattern already failed *)
                        | ((false, _), v :: vs) => (no_match, vs)
                        | ((true, vars), v :: vs) =>
                            let '(matched, more_vars) := pattern_match p v in
                            ((matched, vars ⋈ more_vars), vs)
                        end
                     )
                     ps
                     ((true, []), vs))
            else
              no_match
        | _ => no_match
        end
    | P_tuple [] =>
        match v with
        | V_unit => (true, [])
        | _ => no_match
        end
    | P_tuple ps =>
        match v with
        | V_tuple vs =>
            fst (fold_left
                   (fun match_info p =>
                      match match_info with
                      (* The tuple and pattern are different lengths, so no match *)
                      | (_, []) => (no_match, [])
                      (* A previous element pattern already failed *)
                      | ((false, _), v :: vs) => (no_match, vs)
                      | ((true, vars), v :: vs) =>
                          let '(matched, more_vars) := pattern_match p v in
                          ((matched, vars ⋈ more_vars), vs)
                      end
                   )
                   ps
                   ((true, []), vs))
        | _ => no_match
        end
    | P_list ps =>
        match v with
        | V_list vs =>
            if Nat.eqb (List.length ps) (List.length vs) then
              fst (fold_left
                     (fun match_info p =>
                        match match_info with
                        (* The list and pattern are different lengths, so no match *)
                        | (_, []) => (no_match, [])
                        (* A previous element pattern already failed *)
                        | ((false, _), v :: vs) => (no_match, vs)
                        | ((true, vars), v :: vs) =>
                            let '(matched, more_vars) := pattern_match p v in
                            ((matched, vars ⋈ more_vars), vs)
                        end
                     )
                     ps
                     ((true, []), vs))
            else
              no_match
        (* Matching a list on a non-list *)
        | _ => no_match
        end
    | P_vector ps =>
        match to_gvector v with
        | V_vector vs =>
            fst (fold_left
                   (fun match_info p =>
                      match match_info with
                      (* The vector and pattern are different lengths, so no match *)
                      | (_, []) => (no_match, [])
                      (* A previous element pattern already failed *)
                      | ((false, _), v :: vs) => (no_match, vs)
                      | ((true, vars), v :: vs) =>
                          let '(matched, more_vars) := pattern_match p v in
                     ((matched, vars ⋈ more_vars), vs)
                      end
                   )
                   ps
                   ((true, []), vs))
        (* Matching a list on a non-list *)
        | _ => no_match
        end
    | P_vector_concat ps =>
        match v with
        | V_bitvector bs =>
            fst (fold_left
                   (fun match_info p =>
                    let '(P_aux _ annot) := p in
                    match T.get_split (snd annot) with
                    | Split s =>
                        match match_info with
                        | (_, []) => (no_match, [])
                        | ((false, _), bs) => (no_match, bs)
                        | ((true, bound), bs) =>
                            let '(bs_take, bs_drop) := take_drop s bs in
                            let '(matched, more_bound) := pattern_match p (V_bitvector bs_take) in
                            ((matched, bound ⋈ more_bound), bs_drop)
                        end
                    | No_split => (no_match, [])
                    end)
                   ps
                   ((true, []), bs))
        | V_vector vs =>
            fst (fold_left
                   (fun match_info p =>
                    let '(P_aux _ annot) := p in
                    match T.get_split (snd annot) with
                    | Split s =>
                        match match_info with
                        | (_, []) => (no_match, [])
                        | ((false, _), vs) => (no_match, vs)
                        | ((true, bound), vs) =>
                            let '(vs_take, vs_drop) := take_drop s vs in
                            let '(matched, more_bound) := pattern_match p (V_vector vs_take) in
                            ((matched, bound ⋈ more_bound), vs_drop)
                        end
                    | No_split => (no_match, [])
                    end)
                   ps
                   ((true, []), vs))
        | _ => no_match
        end
    | P_cons p ps =>
        match v with
        | V_list nil => no_match
        | V_list (v :: vs) =>
            let '(hd_matched, hd_bound) := pattern_match p v in
            let '(tl_matched, tl_bound) := pattern_match ps (V_list vs) in
            (andb hd_matched tl_matched, hd_bound ⋈ tl_bound)
        | _ => no_match
        end
    | P_or lhs_p rhs_p =>
        let '(lhs_matched, lhs_bound) := pattern_match lhs_p v in
        let '(rhs_matched, rhs_bound) := pattern_match rhs_p v in
        if lhs_matched then
          (true, lhs_bound)
        else if rhs_matched then
               (true, rhs_bound)
             else
               no_match
    | P_not p =>
        let '(p_matched, _) := pattern_match p v in
        (negb p_matched, [])
    | P_var p _ => pattern_match p v
    | P_struct _ field_patterns _ =>
        match v with
        | V_record fields =>
            fold_left
              (fun match_info fp =>
                 let '(prev_matched, prev_bound) := match_info in
                 let '(name, p) := fp in
                 let v := get_struct_field (T.string_of_id name) fields in
                 let '(matched, bound) := pattern_match p v in
                 (andb prev_matched matched, prev_bound ⋈ bound)
              )
              field_patterns
              (true, [])
        | _ => no_match
        end
    | P_vector_subrange id n m => (true, IdMap.add id (Partial [(v, n, m)]) empty_bindings)
    (* TODO *)
    | P_string_append _ => (true, empty_bindings)
    end.

  Fixpoint lookup_field (l : Ast.loc) (name : string) (fields : list (string * value)) {struct fields} : t value :=
      match fields with
      | [] => Runtime_type_error l
      | (name', v) :: fields =>
          if String.eqb name name' then
            pure v
          else
            lookup_field l name fields
      end.

  Lemma max_lhs_plus_1_le : forall x y z, x <= y -> x < max y z + 1.
  Proof.
    lia.
  Qed.

  Lemma depth_if : forall (b : bool) (x y : exp T.tannot), depth (if b then x else y) <= max (depth x) (depth y).
  Proof.
    destruct b; lia.
  Qed.

  Lemma fexp_subst : forall f (lx : fexp T.tannot),
    (let 'FE_aux (FE_fexp id x) ann := lx in FE_aux (FE_fexp id (f x)) ann) =
    FE_aux (FE_fexp (fexp_name lx) (f (fexp_exp lx))) (fexp_annot lx).
  Proof.
    destruct lx as [aux ?].
    destruct aux.
    cbn.
    reflexivity.
  Qed.

  Lemma depth_subst_helper : forall x y z w, x <= z -> y + 1 <= w + 1 -> max x y + 1 <= max z w + 1.
  Proof.
    lia.
  Qed.

  Theorem depth_subst : forall n v (x : exp T.tannot), depth (substitute n v x) <= depth x.
  Proof.
    intros n v.
    einduction x using exp_ind_mutual_g.
    all: (cbn; try easy; try lia).
    - induction xs.
      + reflexivity.
      + cbn.
        rewrite Forall_cons_iff in H.
        inversion H as [Hhd Htl].
        apply IHxs in Htl.
        lia.
    - cbn.
      apply (PeanoNat.Nat.le_trans _ _ _ (depth_if _ _ _)).
      reflexivity.
    - induction xs.
      + reflexivity.
      + cbn.
        rewrite Forall_cons_iff in H.
        inversion H as [Hhd Htl].
        apply IHxs in Htl.
        lia.
    - induction xs.
      + reflexivity.
      + cbn.
        rewrite Forall_cons_iff in H.
        inversion H as [Hhd Htl].
        apply IHxs in Htl.
        lia.
    - cbn.
      apply (PeanoNat.Nat.le_trans _ _ _ (depth_if _ _ _)).
      cbn.
      lia.
    - induction xs.
      + reflexivity.
      + cbn.
        rewrite Forall_cons_iff in H.
        inversion H as [Hhd Htl].
        apply IHxs in Htl.
        lia.
    - induction xs.
      + reflexivity.
      + cbn.
        rewrite Forall_cons_iff in H.
        inversion H as [Hhd Htl].
        apply IHxs in Htl.
        lia.
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
        apply depth_subst_helper.
        apply (PeanoNat.Nat.le_trans _ _ _ Hhd).
        destruct a.
        destruct f.
        reflexivity.
        lia.
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
        apply depth_subst_helper.
        apply (PeanoNat.Nat.le_trans _ _ _ Hhd).
        destruct a.
        destruct f.
        reflexivity.
        lia.
    - apply depth_subst_helper.
      assumption.
      induction arms.
      + reflexivity.
      + rewrite Forall_cons_iff in H.
        inversion H as [Hhd Htl].
        apply IHarms in Htl.
        cbn.
        apply depth_subst_helper.
        cbn in Hhd.
        destruct a as [aux ?].
        destruct aux; cbn; destruct (binds_id n p); try reflexivity; try assumption.
        cbn in Hhd.
        lia.
        assumption.
    - destruct (binds_id n p); cbn; lia.
    - apply depth_subst_helper.
      apply IHe.
      lia.
    - apply depth_subst_helper.
      assumption.
      induction arms.
      + reflexivity.
      + rewrite Forall_cons_iff in H.
        inversion H as [Hhd Htl].
        apply IHarms in Htl.
        cbn.
        apply depth_subst_helper.
        cbn in Hhd.
        destruct a as [aux ?].
        destruct aux; cbn; destruct (binds_id n p); try reflexivity; try assumption.
        cbn in Hhd.
        lia.
        assumption.
    - cbn in IHe1; lia.
    - cbn; reflexivity.
    - cbn; try assumption; lia.
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
        apply depth_subst_helper.
        assumption.
        apply IHlxs in Htl.
        assumption.
    - cbn. cbn in IHe. lia.
    - cbn. cbn in IHe1. lia.
    - cbn. cbn in IHe. lia.
  Qed.

  Fixpoint destructuring_assignment (annot : Ast.annot T.tannot) (d : destructure) (v : value) : t unit :=
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

  Fixpoint lexp_to_destructure (l : lexp T.tannot) {struct l} : t destructure :=
    let 'LE_aux aux annot := l in
    match aux with
    | LE_id var
    | LE_typ _ var =>
        match T.get_id_type (snd annot) var with
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
        ds ← sequence (map (fun '((LE_aux _ annot) as l) => d ← lexp_to_destructure l; pure (T.get_split (snd annot), d)) ls);
        pure (DL_vector_concat ds)
    | LE_field l f =>
        p ← bind (lexp_to_destructure l) (@coerce_place T.tannot (fst annot));
        pure (DL_place (PL_field p f))
    | LE_vector l n =>
        p ← bind (lexp_to_destructure l) (@coerce_place T.tannot (fst annot));
        match n with
        | E_aux (E_internal_value (V_int n)) _ =>
            pure (DL_place (PL_vector p n))
        | _ =>
            Runtime_type_error (fst annot)
        end
    | LE_vector_range l n m =>
        p ← bind (lexp_to_destructure l) (@coerce_place T.tannot (fst annot));
        match (n, m) with
        | (E_aux (E_internal_value (V_int n)) _, E_aux (E_internal_value (V_int m)) _) =>
            pure (DL_place (PL_vector_range p n m))
        | _ =>
            Runtime_type_error (fst annot)
        end
    end.

  Fixpoint update_field (name : string) (v : value) (fields : list (string * value)) : list (string * value) :=
    match fields with
    | (name', old_v) :: rest =>
        if String.eqb name name' then
          (name, v) :: rest
        else
          (name', old_v) :: update_field name v rest
    | [] => []
    end.

  #[local]
  Obligation Tactic := (program_simpl; try easy; cbn; try lia).

  Program Fixpoint step (orig_exp : exp T.tannot) {measure (depth orig_exp)} : t (exp T.tannot) :=
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
        match T.get_id_type (snd annot) id with
        | Global_register =>
            Read_var (PL_id id Var_register) (fun v => wrap (E_internal_value v))
        | Local_variable =>
            Read_var (PL_id id Var_local) (fun v => wrap (E_internal_value v))
        | Enum_member =>
            wrap (E_internal_value (V_member (T.string_of_id id)))
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
                let '(matched, arm_substs) := pattern_match pat v in
                if matched then
                  pure (fold_right (fun s body => substitute (fst s) (snd s) body) body (complete_bindings arm_substs))
                else
                  wrap (E_match head_exp next_arms)
            | Pat_aux (Pat_when pat guard body) pexp_annot :: next_arms =>
                let '(matched, arm_substs) := pattern_match pat v in
                if matched then
                  let guard := fold_right (fun s g => substitute (fst s) (snd s) g)  guard (complete_bindings arm_substs) in
                  match guard with
                  | E_aux (E_internal_value v_guard) _ =>
                      match v_guard with
                      | V_bool true =>
                          let '(matched, arm_substs) := pattern_match pat v in
                          if matched then
                            pure (fold_right (fun s body => substitute (fst s) (snd s) body) body (complete_bindings arm_substs))
                          else
                            wrap (E_match head_exp next_arms)
                      | V_bool false =>
                          wrap (E_match head_exp next_arms)
                      | _ => Runtime_type_error (fst pexp_annot)
                      end
                  | _ =>
                      guard' ← step guard;
                      wrap (E_match head_exp (Pat_aux (Pat_when pat guard' body) pexp_annot :: next_arms))
                  end
                else
                  wrap (E_match head_exp next_arms)
            | [] => Match_failure (fst annot)
            end
        | _ =>
            head_exp' ← step head_exp;
            wrap (E_match head_exp' arms)
        end
    | E_let (LB_aux (LB_val pat x) lb_annot) body =>
        match x with
        | E_aux (E_internal_value v) _ =>
            let '(matched, body_substs) := pattern_match pat v in
            if matched then
              pure (fold_left (fun body s => substitute (fst s) (snd s) body) (complete_bindings body_substs) body)
            else
              Match_failure (fst annot)
        | _ =>
            x' ← step x;
            wrap (E_let (LB_aux (LB_val pat x') lb_annot) body)
        end
    | E_lit lit =>
        v ← value_of_lit lit (T.get_type (snd annot));
        wrap (E_internal_value v)
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
                v_field ← lookup_field (fst annot) (T.string_of_id f) fields;
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
            wrap (E_internal_value (V_record (all_evaluated_fields T.string_of_id evaluated)))
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
                let updates := all_evaluated_fields T.string_of_id evaluated in
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
            if T.is_bitvector (snd annot) then
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
            | Caught exn => wrap (E_match (E_aux (E_internal_value exn) annot) (arms ++ [T.fallthrough]))
            | Continue x'' => wrap (E_try x'' arms)
            end
        end
    | E_internal_value v => wrap (E_internal_value v)
    | E_ref register_name =>
        wrap (E_internal_value (V_ref (T.string_of_id register_name)))
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
    rewrite <- (take_drop_evaluated_concat T.tannot (lexp_subexps lx)).
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
    induction arm_substs.
    - cbn; lia.
    - destruct a.
      cbn.
      apply (PeanoNat.Nat.le_lt_trans _ _ _ (depth_subst _ _ _)).
      apply IHarm_substs.
  Defined.
  Next Obligation.
    cbn.
    rewrite ltr_tuple in Heq_anonymous.
    inversion Heq_anonymous.
    rewrite <- (take_drop_evaluated_concat T.tannot xs0).
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
    rewrite <- (take_drop_evaluated_concat T.tannot args).
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
    rewrite <- (take_drop_evaluated_fields_concat T.tannot _).
    rewrite <- H0.
    rewrite <- H1.
    rewrite map_app.
    rewrite fold_right_app.
    cbn.
    apply fold_right_max_acc.
    lia.
  Defined.
  Next Obligation.
    rewrite ltr_fields_tuple in Heq_anonymous.
    inversion Heq_anonymous.
    rewrite <- (take_drop_evaluated_fields_concat T.tannot _).
    rewrite <- H0.
    rewrite <- H1.
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
    rewrite <- (take_drop_evaluated_concat T.tannot xs).
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
    rewrite <- (take_drop_evaluated_concat T.tannot xs).
    rewrite <- H1.
    rewrite <- H0.
    rewrite map_app.
    rewrite fold_right_app.
    cbn.
    apply fold_right_max_acc.
    lia.
  Defined.
End Make.

Extraction Blacklist Nat List String.

Separate Extraction Primops l attribute_data hex_digits_of_bitlist def impldef opt_default Make IdMap.
