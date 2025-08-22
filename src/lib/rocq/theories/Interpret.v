Require Extraction.

Set Extraction KeepSingleton.
Set Extraction Output Directory ".".

From Stdlib Require Import FunctionalExtensionality.
From Stdlib Require Import Lia.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Program.

Require Import Value_type.
Require Import Ast.

Import ListNotations.

Definition is_value {A : Set} (exp : exp A) : bool :=
  match exp with
  | E_aux (E_internal_value _) _ => true
  | _ => false
  end.

Inductive return_value : Set :=
| Return_ok : value -> return_value
| Return_exception : value -> return_value.

Module Monad.
  Inductive t (a : Set) : Set :=
  | Pure : a -> t a
  | Exception : value -> t a
  | Runtime_type_error : Ast.loc -> t a
  | Match_failure : Ast.loc -> t a
  | Assertion_failed : string -> t a
  | Call : id -> list value -> (return_value -> t a) -> t a
  | Read_reg : id -> (value -> t a) -> t a
  | Write_reg : id -> value -> (unit -> t a) -> t a
  | Get_undefined : typ -> (value -> t a) -> t a.

  Arguments Pure {_}.
  Arguments Exception {_}.
  Arguments Runtime_type_error {_}.
  Arguments Match_failure {_}.
  Arguments Assertion_failed {_}.
  Arguments Call {_}.
  Arguments Read_reg {_}.
  Arguments Write_reg {_}.
  Arguments Get_undefined {_}.

  Fixpoint bind {A B : Set} (m : t A) (f : A -> t B) : t B :=
    match m with
    | Pure x => f x
    | Exception v => Exception v
    | Runtime_type_error l => Runtime_type_error l
    | Match_failure l => Match_failure l
    | Assertion_failed msg => Assertion_failed msg
    | Call id args cont => Call id args (fun v => bind (cont v) f)
    | Read_reg r cont => Read_reg r (fun v => bind (cont v) f)
    | Write_reg r v cont => Write_reg r v (fun u => bind (cont u) f)
    | Get_undefined t cont => Get_undefined t (fun v => bind (cont v) f)
    end.

  Fixpoint fmap {A B : Set} (f : A -> B) (m : t A) : t B :=
    match m with
    | Pure x => Pure (f x)
    | Exception v => Exception v
    | Runtime_type_error l => Runtime_type_error l
    | Match_failure l => Match_failure l
    | Assertion_failed msg => Assertion_failed msg
    | Call id args cont => Call id args (fun v => fmap f (cont v))
    | Read_reg r cont => Read_reg r (fun v => fmap f (cont v))
    | Write_reg r v cont => Write_reg r v (fun u => fmap f (cont u))
    | Get_undefined t cont => Get_undefined t (fun v => fmap f (cont v))
    end.

  Definition pure {A : Set} (x : A) : t A := Pure x.

  Definition get_undefined (typ : Ast.typ) : t value := Get_undefined typ pure.

  Definition throw {A : Set} (v : value) : t A := Exception v.

  Inductive caught (a : Set) : Set :=
  | Continue : a -> caught a
  | Caught : value -> caught a.

  Arguments Continue {_}.
  Arguments Caught {_}.

  Fixpoint catch {A : Set} (m : t A) : t (caught A) :=
    match m with
    | Pure x => Pure (Continue x)
    | Exception v => Pure (Caught v)
    | Runtime_type_error l => Runtime_type_error l
    | Match_failure l => Match_failure l
    | Assertion_failed msg => Assertion_failed msg
    | Call id args cont => Call id args (fun v => fmap Continue (cont v))
    | Read_reg r cont => Read_reg r (fun v => fmap Continue (cont v))
    | Write_reg r v cont => Write_reg r v (fun _ => fmap Continue (cont ()))
    | Get_undefined t cont => Get_undefined t (fun v => fmap Continue (cont v))
    end.

  Theorem bind_pure : forall (A B : Set) (f : A -> t B) (x : A), bind (pure x) f = f x.
  Proof.
    unfold bind. unfold pure.
    reflexivity.
  Qed.

  Theorem bind_assoc : forall (A B C : Set) (f : A -> t B) (g : B -> t C) (x : t A),
      bind (bind x f) g = bind x (fun y => bind (f y) g).
  Proof.
    induction x as [| | | | | ? ? cont | ? cont | ? ? cont | ? cont]; try easy.
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

Definition is_bool {A : Set} (exp : exp A) : t (evaluated bool) :=
  match exp with
  | E_aux (E_internal_value (V_bool b)) _ => pure (Evaluated b)
  | E_aux (E_internal_value _) annot => Runtime_type_error (fst annot)
  | _ => pure Unevaluated
  end.

Definition is_string {A : Set} (exp : exp A) : t (evaluated string) :=
  match exp with
  | E_aux (E_internal_value (V_string s)) _ => pure (Evaluated s)
  | E_aux (E_internal_value _) annot => Runtime_type_error (fst annot)
  | _ => pure Unevaluated
  end.

Fixpoint all_evaluated {A : Set} (xs : list (exp A)) : list value :=
  match xs with
  | [] => []
  | E_aux (E_internal_value v) _ :: xs =>
      cons v (all_evaluated xs)
  | _ :: xs => all_evaluated xs
  end.

Fixpoint left_to_right {A : Set} (xs : list (exp A)) {struct xs} : (list (exp A) * list (exp A)) :=
  match xs with
  | [] => ([], [])
  | E_aux (E_internal_value v) annot :: xs =>
      let '(vs, xs') := left_to_right xs in
      (E_aux (E_internal_value v) annot :: vs, xs')
  | x :: xs => ([], x :: xs)
  end.

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

Fixpoint depth {A : Set} (x : exp A) {struct x} : nat :=
  let 'E_aux aux _ := x in
  match aux with
  | E_block xs => fold_right max 0 (map depth xs) + 1
  | E_tuple xs => fold_right max 0 (map depth xs) + 1
  | _ => 0
  end.

Lemma depth_block : forall (A : Set) (x : exp A) xs annot,
    depth (E_aux (E_block (x :: xs)) annot) = max (depth x) (fold_right max 0 (map depth xs)) + 1.
Proof.
  reflexivity.
Qed.

(** Sail annotates terms with custom type annotation data, which we
    don't have access to here. Instead use a functor parameterised by
    the following TANNOT signature, which can provide the methods we
    need. *)
Module Type TANNOT.
  Parameter tannot : Set.

  Parameter get_type : tannot -> typ.

  Parameter id_equal : id -> id -> bool.

  Parameter id_equal_string : id -> string -> bool.

  Parameter bits_of_hex_string : string -> list bit.

  Parameter bits_of_bin_string : string -> list bit.

  Parameter rational_of_string : string -> rational.
End TANNOT.

Module Semantics (T : TANNOT).
  Fixpoint binds_id {A} (n : Ast.id) (pat : Ast.pat A) : bool :=
    let 'P_aux aux annot := pat in
    match aux with
    | P_lit _ | P_wild => false
    | P_id m => T.id_equal n m
    | P_typ _ pat => binds_id n pat
    | P_as pat m => binds_id n pat || T.id_equal n m
    | _ => false
    end.

  Fixpoint substitute {A} (n : Ast.id) (v : Value_type.value) (x : exp A) : exp A :=
    let 'E_aux aux annot := x in
    match aux with
    | E_id m =>
        if T.id_equal n m then E_aux (E_internal_value v) annot else E_aux (E_id m) annot
    | E_block xs => E_aux (E_block (map (substitute n v) xs)) annot
    | E_app_infix x f y => E_aux (E_app_infix (substitute n v x) f (substitute n v y)) annot
    | E_app f args => E_aux (E_app f (map (substitute n v) args)) annot
    | E_tuple xs => E_aux (E_tuple (map (substitute n v) xs)) annot
    | E_vector xs => E_aux (E_vector (map (substitute n v) xs)) annot
    | E_if i t e =>
        E_aux (E_if (substitute n v i) (substitute n v t) (substitute n v e)) annot
    | E_let (LB_aux (LB_val pat y) lb_annot) body =>
        if binds_id n pat then
          E_aux (E_let (LB_aux (LB_val pat (substitute n v y)) lb_annot) body) annot
        else
          E_aux (E_let (LB_aux (LB_val pat (substitute n v y)) lb_annot) (substitute n v body)) annot
    | E_match head_exp arms =>
        E_aux (E_match (substitute n v head_exp) (map (substitute_arm n v) arms)) annot
    | E_list xs =>
        E_aux (E_list (map (substitute n v) xs)) annot
    | E_typ typ x => E_aux (E_typ typ (substitute n v x)) annot
    | E_lit _ => E_aux aux annot
    (* FIXME: Loops *)
    | E_loop _ _ _ _ => E_aux aux annot
    | E_for _ _ _ _ _ _ => E_aux aux annot
    | _ => E_aux aux annot
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
    end.

  Definition value_of_lit (lit : Ast.lit) (typ : Ast.typ) : t value :=
    let 'L_aux aux _ := lit in
    match aux with
    | L_unit => pure V_unit
    | L_zero => pure (V_bit B0)
    | L_one => pure (V_bit B1)
    | L_true => pure (V_bool true)
    | L_false => pure (V_bool false)
    | L_num n => pure (V_int n)
    (* Fix the representation of these internally, so they work nicely... *)
    | L_hex h => pure (V_vector (map V_bit (T.bits_of_hex_string h)))
    | L_bin b => pure (V_vector (map V_bit (T.bits_of_bin_string b)))
    | L_real r => pure (V_real (T.rational_of_string r))
    | L_string s => pure (V_string s)
    | L_undef => get_undefined typ
    end.

  Definition no_match : bool * list (id * value) := (false, nil).

  Fixpoint pattern_match (p : Ast.pat T.tannot) (v : value) {struct p} : bool * list (id * value) :=
    let 'P_aux aux annot := p in
    match aux with
    | P_wild => (true, [])
    | P_id n => (true, [(n, v)])
    | P_typ _ p => pattern_match p v
    | P_as p n =>
        let '(matched, bindings) := pattern_match p v in
        (matched, (n, v) :: bindings)
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
                            ((matched, vars ++ more_vars), vs)
                        end
                     )
                     ps
                     ((true, []), vs))
            else
              no_match
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
                          ((matched, vars ++ more_vars), vs)
                      end
                   )
                   ps
                   ((true, []), vs))
        | _ => no_match
        end
    | P_list ps =>
        match v with
        | V_list vs =>
            fst (fold_left
                   (fun match_info p =>
                      match match_info with
                      (* The list and pattern are different lengths, so no match *)
                      | (_, []) => (no_match, [])
                      (* A previous element pattern already failed *)
                      | ((false, _), v :: vs) => (no_match, vs)
                      | ((true, vars), v :: vs) =>
                          let '(matched, more_vars) := pattern_match p v in
                     ((matched, vars ++ more_vars), vs)
                      end
                   )
                   ps
                   ((true, []), vs))
        (* Matching a list on a non-list *)
        | _ => no_match
        end
    | _ =>
        (true, [])
    end.

  Program Fixpoint step (orig_exp : exp T.tannot) {measure (depth orig_exp)} : t (exp T.tannot) :=
    let 'E_aux aux annot := orig_exp in
    let wrap e_aux' := pure (E_aux e_aux' annot) in
    match aux with
    | E_block xs =>
        (
          match xs with
          | [] => wrap (E_internal_value V_unit)
          | [E_aux (E_internal_value v) annot] => pure (E_aux (E_internal_value v) annot)
          | [E_aux (E_block ys) annot] => pure (E_aux (E_block ys) annot)
          | x :: xs =>
              if is_value x then
                wrap (E_block xs)
              else
                bind (step x) (fun x' => wrap (E_block (x' :: xs)))
          end
        )
    | E_id id =>
        Read_reg id (fun v => wrap (E_internal_value v))
    | E_assign l x =>
        match x with
        | E_aux (E_internal_value v) _ =>
            match l with
            | LE_aux (LE_id var | LE_typ _ var) _ =>
                Write_reg var v (fun _ => wrap (E_internal_value V_unit))
            | _ =>
                Runtime_type_error (fst annot)
            end
        | _ =>
            bind (step x) (fun x' => wrap (E_assign l x'))
        end
    | E_var l x body => wrap (E_block (E_aux (E_assign l x) annot :: [body]))
    | E_match head_exp arms =>
        (
          match head_exp with
          | E_aux (E_internal_value v) _ =>
              (
                match arms with
                | Pat_aux (Pat_exp pat body) _ :: next_arms =>
                    let '(matched, arm_substs) := pattern_match pat v in
                    if matched then
                      pure (fold_left (fun body s => substitute (fst s) (snd s) body) arm_substs body)
                    else
                      wrap (E_match head_exp next_arms)
                | Pat_aux (Pat_when pat _ body) _ :: next_arms =>
                    let '(matched, arm_substs) := pattern_match pat v in
                    if matched then
                      pure (fold_left (fun body s => substitute (fst s) (snd s) body) arm_substs body)
                    else
                      wrap (E_match head_exp next_arms)
                | [] => Match_failure (fst annot)
                end
              )
          | _ =>
              bind (step head_exp) (fun head_exp' => wrap (E_match head_exp' arms))
          end
        )
    | E_let (LB_aux (LB_val pat x) lb_annot) body =>
        (
          match x with
          | E_aux (E_internal_value v) _ =>
              let '(matched, body_substs) := pattern_match pat v in
              if matched then
                pure (fold_left (fun body s => substitute (fst s) (snd s) body) body_substs body)
              else
                Match_failure (fst annot)
          | _ =>
              bind (step x) (fun x' => wrap (E_let (LB_aux (LB_val pat x') lb_annot) body))
          end
        )
    | E_lit lit =>
        bind (value_of_lit lit (T.get_type (snd annot)))
             (fun v => wrap (E_internal_value v))
    | E_tuple xs =>
        (
          let '(evaluated, unevaluated) := left_to_right xs in
          match unevaluated with
          | cons x xs =>
              bind (step x) (fun x' => wrap (E_tuple (x' :: xs)))
          | nil => wrap (E_internal_value (V_tuple (all_evaluated evaluated)))
          end
        )
    | E_typ _ x => pure x
    | E_app id args =>
        (
          let '(evaluated, unevaluated) := left_to_right args in
          match unevaluated with
          | x :: xs =>
              bind (step x) (fun x' => wrap (E_app id (evaluated ++ (x' :: xs))))
          | [] =>
              bind (Call id (all_evaluated evaluated) pure)
                (fun r =>
                   match r with
                   | Return_ok v => wrap (E_internal_value v)
                   | Return_exception exn => wrap (E_throw (E_aux (E_internal_value exn) annot))
                   end
                )
          end
        )
    | E_app_infix arg1 id arg2 =>
        (
          match left_to_right2 arg1 arg2 with
          | LTR2_0 _ _ =>
              bind (step arg1) (fun arg1' => wrap (E_app_infix arg1' id arg2))
          | LTR2_1 v1 _ =>
              bind (step arg2) (fun arg2' => wrap (E_app_infix arg1 id arg2'))
          | LTR2_2 v1 v2 =>
              bind (Call id [v1; v2] pure)
                (fun r =>
                   match r with
                   | Return_ok v => wrap (E_internal_value v)
                   | Return_exception exn => wrap (E_throw (E_aux (E_internal_value exn) annot))
                   end
                )
          end
        )
    | E_if i t e =>
        bind (is_bool i)
          (fun b =>
             match b with
             | Unevaluated =>
                 bind (step i) (fun i' => wrap (E_if i' t e))
             | Evaluated true => pure t
             | Evaluated false => pure e
             end
          )
    | E_assert x msg =>
        bind (is_bool x)
          (fun b =>
             match b with
             | Unevaluated =>
                 bind (step x) (fun x' => wrap (E_assert x' msg))
             | Evaluated b =>
                 bind (is_string msg)
                   (fun s =>
                      match s with
                      | Unevaluated =>
                          bind (step msg) (fun msg' => wrap (E_assert x msg'))
                      | Evaluated s =>
                          if b then
                            wrap (E_internal_value V_unit)
                          else
                            Assertion_failed s
                      end
                   )
             end
          )
    | E_vector xs =>
        (
          let '(evaluated, unevaluated) := left_to_right xs in
          match unevaluated with
          | cons y ys =>
              bind (step y) (fun y' => wrap (E_vector (evaluated ++ (y' :: ys))))
          | nil =>
              wrap (E_internal_value (V_vector (all_evaluated evaluated)))
          end
        )
    | E_list xs =>
        (
          let '(evaluated, unevaluated) := left_to_right xs in
          match unevaluated with
          | cons y ys =>
              bind (step y) (fun y' => wrap (E_list (evaluated ++ (y' :: ys))))
          | nil =>
              wrap (E_internal_value (V_list (all_evaluated evaluated)))
          end
        )
    | E_cons x xs =>
        (
          match left_to_right2 x xs with
          | LTR2_0 _ _ =>
              bind (step x) (fun x' => wrap (E_cons x' xs))
          | LTR2_1 _ _ =>
              bind (step xs) (fun xs' => wrap (E_cons x xs'))
          | LTR2_2 vx vxs =>
              match vxs with
              | V_list elems =>
                  wrap (E_internal_value (V_list (vx :: elems)))
              | _ =>
                  Runtime_type_error (fst annot)
              end
          end
        )
    | E_throw x =>
        match x with
        | E_aux (E_internal_value v) _ =>
            throw v
        | _ =>
            bind (step x) (fun x' => wrap (E_throw x'))
        end
    | E_try x arms =>
        match x with
        | E_aux (E_internal_value v) annot => pure (E_aux (E_internal_value v) annot)
        | _ =>
            bind
              (catch (step x))
              (fun x' =>
                 match x' with
                 | Caught exn => wrap (E_match (E_aux (E_internal_value exn) annot) arms)
                 | Continue x'' => wrap (E_try x'' arms)
                 end
              )
        end
    | _ => Runtime_type_error (fst annot)
    end.
  Next Obligation.
    cbn.
    lia.
  Defined.
  Admit Obligations.
End Semantics.

Extraction Blacklist List.

Separate Extraction l attribute_data def impldef opt_default Semantics.
