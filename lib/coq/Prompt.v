Require Import Sail.Values.
Require Import Sail.Prompt_monad.
Require Export ZArith.Zwf.
Require Import Lia.
Require Import List.
Import ListNotations.
Local Open Scope Z.
(*

val iter_aux : forall 'rv 'a 'e. integer -> (integer -> 'a -> monad 'rv unit 'e) -> list 'a -> monad 'rv unit 'e
let rec iter_aux i f xs = match xs with
  | x :: xs -> f i x >> iter_aux (i + 1) f xs
  | [] -> return ()
  end

declare {isabelle} termination_argument iter_aux = automatic

val iteri : forall 'rv 'a 'e. (integer -> 'a -> monad 'rv unit 'e) -> list 'a -> monad 'rv unit 'e
let iteri f xs = iter_aux 0 f xs

val iter : forall 'rv 'a 'e. ('a -> monad 'rv unit 'e) -> list 'a -> monad 'rv unit 'e
let iter f xs = iteri (fun _ x -> f x) xs

val foreachM : forall 'a 'rv 'vars 'e.
  list 'a -> 'vars -> ('a -> 'vars -> monad 'rv 'vars 'e) -> monad 'rv 'vars 'e*)
Fixpoint foreachM {a rv Vars e} (l : list a) (vars : Vars) (body : a -> Vars -> monad rv Vars e) : monad rv Vars e :=
match l with
| [] => returnm vars
| (x :: xs) =>
  body x vars >>= fun vars =>
  foreachM xs vars body
end.

Fixpoint foreach_ZM_up' {rv e Vars} (from to step off : Z) (n : nat) `{ArithFact (0 <? step)} `{ArithFact (0 <=? off)} (vars : Vars) (body : forall (z : Z) `(ArithFact (from <=? z <=? to)), Vars -> monad rv Vars e) {struct n} : monad rv Vars e.
exact (
  if sumbool_of_bool (from + off <=? to) then
    match n with
    | O => returnm vars
    | S n => body (from + off) _ vars >>= fun vars => foreach_ZM_up' rv e Vars from to step (off + step) n _ _ vars body
    end
  else returnm vars).
Defined.

Fixpoint foreach_ZM_down' {rv e Vars} (from to step off : Z) (n : nat) `{ArithFact (0 <? step)} `{ArithFact (off <=? 0)} (vars : Vars) (body : forall (z : Z) `(ArithFact (to <=? z <=? from)), Vars -> monad rv Vars e) {struct n} : monad rv Vars e.
exact (
  if sumbool_of_bool (to <=? from + off) then
    match n with
    | O => returnm vars
    | S n => body (from + off) _ vars >>= fun vars => foreach_ZM_down' _ _ _ from to step (off - step) n _ _ vars body
    end
  else returnm vars).
Defined.

Definition foreach_ZM_up {rv e Vars} from to step vars body `{ArithFact (0 <? step)} :=
    foreach_ZM_up' (rv := rv) (e := e) (Vars := Vars) from to step 0 (S (Z.abs_nat (from - to))) vars body.
Definition foreach_ZM_down {rv e Vars} from to step vars body `{ArithFact (0 <? step)} :=
    foreach_ZM_down' (rv := rv) (e := e) (Vars := Vars) from to step 0 (S (Z.abs_nat (from - to))) vars body.

(*declare {isabelle} termination_argument foreachM = automatic*)

Definition genlistM {A RV E} (f : nat -> monad RV A E) (n : nat) : monad RV (list A) E :=
  let indices := List.seq 0 n in
  foreachM indices [] (fun n xs => (f n >>= (fun x => returnm (xs ++ [x])))).

(*val and_boolM : forall 'rv 'e. monad 'rv bool 'e -> monad 'rv bool 'e -> monad 'rv bool 'e*)
Definition and_boolM {rv E} (l : monad rv bool E) (r : monad rv bool E) : monad rv bool E :=
 l >>= (fun l => if l then r else returnm false).

(* We introduce explicit definitions for these proofs so that they can be used in
   the state monad and program logic rules.  They are not currently used in the proof
   rules because it was more convenient to quantify over them instead. *)
Definition and_bool_left_proof {P Q R:bool -> Prop} :
  ArithFactP (P false) ->
  (forall l r, ArithFactP (P l -> ((l = true -> (Q r)) -> (R (andb l r))))) ->
  ArithFactP (R false).
intros [p] [h].
constructor.
change false with (andb false false).
apply h; auto.
congruence.
Qed.

Definition and_bool_full_proof {P Q R:bool -> Prop} {r} :
  ArithFactP (P true) ->
  ArithFactP (Q r) ->
  (forall l r, ArithFactP ((P l) -> ((l = true -> (Q r)) -> (R (andb l r))))) ->
  ArithFactP (R r).
intros [p] [q] [h].
constructor.
change r with (andb true r).
apply h; auto.
Qed.

Definition and_boolMP {rv E} {P Q R:bool->Prop} (x : monad rv {b:bool & ArithFactP (P b)} E) (y : monad rv {b:bool & ArithFactP (Q b)} E)
  `{H:forall l r, ArithFactP ((P l) -> ((l = true -> (Q r)) -> (R (andb l r))))}
  : monad rv {b:bool & ArithFactP (R b)} E :=
  x >>= fun '(existT _ x p) => (if x return ArithFactP (P x) -> _ then
    fun p => y >>= fun '(existT _ y q) => returnm (existT _ y (and_bool_full_proof p q H))
  else fun p => returnm (existT _ false (and_bool_left_proof p H))) p.

(*val or_boolM : forall 'rv 'e. monad 'rv bool 'e -> monad 'rv bool 'e -> monad 'rv bool 'e*)
Definition or_boolM {rv E} (l : monad rv bool E) (r : monad rv bool E) : monad rv bool E :=
 l >>= (fun l => if l then returnm true else r).


Definition or_bool_left_proof {P Q R:bool -> Prop} :
  ArithFactP (P true) ->
  (forall l r, ArithFactP ((P l) -> (((l = false) -> (Q r)) -> (R (orb l r))))) ->
  ArithFactP (R true).
intros [p] [h].
constructor.
change true with (orb true false).
apply h; auto.
congruence.
Qed.

Definition or_bool_full_proof {P Q R:bool -> Prop} {r} :
  ArithFactP (P false) ->
  ArithFactP (Q r) ->
  (forall l r, ArithFactP ((P l) -> (((l = false) -> (Q r)) -> (R (orb l r))))) ->
  ArithFactP (R r).
intros [p] [q] [h].
constructor.
change r with (orb false r).
apply h; auto.
Qed.

Definition or_boolMP {rv E} {P Q R:bool -> Prop} (l : monad rv {b : bool & ArithFactP (P b)} E) (r : monad rv {b : bool & ArithFactP (Q b)} E)
 `{forall l r, ArithFactP ((P l) -> (((l = false) -> (Q r)) -> (R (orb l r))))}
 : monad rv {b : bool & ArithFactP (R b)} E :=
 l >>= fun '(existT _ l p) =>
  (if l return ArithFactP (P l) -> _ then fun p => returnm (existT _ true (or_bool_left_proof p H))
   else fun p => r >>= fun '(existT _ r q) => returnm (existT _ r (or_bool_full_proof p q H))) p.

Definition build_trivial_ex {rv E} {T:Type} (x:monad rv T E) : monad rv {x : T & ArithFact true} E :=
  x >>= fun x => returnm (existT _ x (Build_ArithFactP _ eq_refl)).

(*val bool_of_bitU_fail : forall 'rv 'e. bitU -> monad 'rv bool 'e*)
Definition bool_of_bitU_fail {rv E} (b : bitU) : monad rv bool E :=
match b with
  | B0 => returnm false
  | B1 => returnm true
  | BU => Fail "bool_of_bitU"
end.

Definition bool_of_bitU_nondet {rv E} (b : bitU) : monad rv bool E :=
match b with
  | B0 => returnm false
  | B1 => returnm true
  | BU => choose_bool "bool_of_bitU"
end.

Definition bools_of_bits_nondet {rv E} (bits : list bitU) : monad rv (list bool) E :=
  foreachM bits []
    (fun b bools =>
      bool_of_bitU_nondet b >>= fun b => 
      returnm (bools ++ [b])).

Definition of_bits_nondet {rv A E} `{Bitvector A} (bits : list bitU) : monad rv A E :=
  bools_of_bits_nondet bits >>= fun bs =>
  returnm (of_bools bs).

Definition of_bits_fail {rv A E} `{Bitvector A} (bits : list bitU) : monad rv A E :=
  maybe_fail "of_bits" (of_bits bits).

(* For termination of recursive functions.  We don't name assertions, so use
   the type class mechanism to find it. *)
Definition _limit_reduces {_limit} (_acc:Acc (Zwf 0) _limit) `{ArithFact (_limit >=? 0)} : Acc (Zwf 0) (_limit - 1).
refine (Acc_inv _acc _).
destruct H.
unbool_comparisons.
red.
lia.
Defined.

(* A version of well-foundedness of measures with a guard to ensure that
   definitions can be reduced without inspecting proofs, based on a coq-club
   thread featuring Barras, Gonthier and Gregoire, see
     https://sympa.inria.fr/sympa/arc/coq-club/2007-07/msg00014.html *)

Fixpoint pos_guard_wf {A:Type} {R:A -> A -> Prop} (p:positive) : well_founded R -> well_founded R :=
 match p with
 | xH => fun wfR x => Acc_intro x (fun y _ => wfR y)
 | xO p' => fun wfR x => let F := pos_guard_wf p' in Acc_intro x (fun y _ => F (F 
wfR) y)
 | xI p' => fun wfR x => let F := pos_guard_wf p' in Acc_intro x (fun y _ => F (F 
wfR) y)
 end.

Definition Zwf_guarded (z:Z) : Acc (Zwf 0) z :=
  Acc_intro _ (fun y H => match z with
  | Zpos p => pos_guard_wf p (Zwf_well_founded _) _
  | Zneg p => pos_guard_wf p (Zwf_well_founded _) _
  | Z0 => Zwf_well_founded _ _
  end).

(*val whileM : forall 'rv 'vars 'e. 'vars -> ('vars -> monad 'rv bool 'e) ->
                ('vars -> monad 'rv 'vars 'e) -> monad 'rv 'vars 'e*)
Fixpoint whileMT' {RV Vars E} limit (vars : Vars) (cond : Vars -> monad RV bool E) (body : Vars -> monad RV Vars E) (acc : Acc (Zwf 0) limit) : monad RV Vars E.
exact (
  if Z_ge_dec limit 0 then
    cond vars >>= fun cond_val =>
    if cond_val then
      body vars >>= fun vars => whileMT' _ _ _ (limit - 1) vars cond body (_limit_reduces acc)
    else returnm vars
  else Fail "Termination limit reached").
Defined.

Definition whileMT {RV Vars E} (vars : Vars) (measure : Vars -> Z) (cond : Vars -> monad RV bool E) (body : Vars -> monad RV Vars E) : monad RV Vars E :=
  let limit := measure vars in
  whileMT' limit vars cond body (Zwf_guarded limit).

(*val untilM : forall 'rv 'vars 'e. 'vars -> ('vars -> monad 'rv bool 'e) ->
                ('vars -> monad 'rv 'vars 'e) -> monad 'rv 'vars 'e*)
Fixpoint untilMT' {RV Vars E} limit (vars : Vars) (cond : Vars -> monad RV bool E) (body : Vars -> monad RV Vars E) (acc : Acc (Zwf 0) limit) : monad RV Vars E.
exact (
  if Z_ge_dec limit 0 then
    body vars >>= fun vars =>
    cond vars >>= fun cond_val =>
    if cond_val then returnm vars else untilMT' _ _ _ (limit - 1) vars cond body (_limit_reduces acc)
  else Fail "Termination limit reached").
Defined.

Definition untilMT {RV Vars E} (vars : Vars) (measure : Vars -> Z) (cond : Vars -> monad RV bool E) (body : Vars -> monad RV Vars E) : monad RV Vars E :=
  let limit := measure vars in
  untilMT' limit vars cond body (Zwf_guarded limit).

(*let write_two_regs r1 r2 vec =
  let is_inc =
    let is_inc_r1 = is_inc_of_reg r1 in
    let is_inc_r2 = is_inc_of_reg r2 in
    let () = ensure (is_inc_r1 = is_inc_r2)
                    "write_two_regs called with vectors of different direction" in
    is_inc_r1 in

  let (size_r1 : integer) = size_of_reg r1 in
  let (start_vec : integer) = get_start vec in
  let size_vec = length vec in
  let r1_v =
    if is_inc
    then slice vec start_vec (size_r1 - start_vec - 1)
    else slice vec start_vec (start_vec - size_r1 - 1) in
  let r2_v =
    if is_inc
    then slice vec (size_r1 - start_vec) (size_vec - start_vec)
    else slice vec (start_vec - size_r1) (start_vec - size_vec) in
  write_reg r1 r1_v >> write_reg r2 r2_v*)

Definition choose_bools {RV E} (descr : string) (n : nat) : monad RV (list bool) E :=
  genlistM (fun _ => choose_bool descr) n.

Definition choose {RV A E} (descr : string) (xs : list A) : monad RV A E :=
  (* Use sufficiently many nondeterministically chosen bits and convert into an
     index into the list *)
  choose_bools descr (List.length xs) >>= fun bs =>
  let idx := ((nat_of_bools bs) mod List.length xs)%nat in
  match List.nth_error xs idx with
    | Some x => returnm x
    | None => Fail ("choose " ++ descr)
  end.

Definition internal_pick {rv a e} (xs : list a) : monad rv a e :=
  choose "internal_pick" xs.

Fixpoint undefined_word_nat {rv e} n : monad rv (Word.word n) e :=
  match n with
  | O => returnm Word.WO
  | S m =>
    choose_bool "undefined_word_nat" >>= fun b =>
    undefined_word_nat m >>= fun t =>
    returnm (Word.WS b t)
  end.

Definition undefined_bitvector {rv e} n `{ArithFact (n >=? 0)} : monad rv (mword n) e :=
  undefined_word_nat (Z.to_nat n) >>= fun w =>
  returnm (word_to_mword w).

(* If we need to build an existential after a monadic operation, assume that
   we can do it entirely from the type. *)

Definition build_ex_m {rv e} {T:Type} (x:monad rv T e) {P:T -> Prop} `{H:forall x, ArithFactP (P x)} : monad rv {x : T & ArithFactP (P x)} e :=
  x >>= fun y => returnm (existT _ y (H y)).

Definition projT1_m {rv e} {T:Type} {P:T -> Prop} (x: monad rv {x : T & P x} e) : monad rv T e :=
  x >>= fun y => returnm (projT1 y).

Definition derive_m {rv e} {T:Type} {P Q:T -> Prop} (x : monad rv {x : T & ArithFactP (P x)} e) `{forall x, ArithFactP (P x) -> ArithFactP (Q x)} : monad rv {x : T & (ArithFactP (Q x))} e :=
  x >>= fun y => returnm (build_ex (projT1 y)).
