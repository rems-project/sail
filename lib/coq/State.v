Require Import Sail.Values.
Require Import Sail.Prompt_monad.
Require Import Sail.Prompt.
Require Import Sail.State_monad.
Import ListNotations.
Local Open Scope Z.

(*val iterS_aux : forall 'rv 'a 'e. integer -> (integer -> 'a -> monadS 'rv unit 'e) -> list 'a -> monadS 'rv unit 'e*)
Fixpoint iterS_aux {RV A E} i (f : Z -> A -> monadS RV unit E) (xs : list A) :=
 match xs with
  | x :: xs => f i x >>$ iterS_aux (i + 1) f xs
  | [] => returnS tt
  end.

(*val iteriS : forall 'rv 'a 'e. (integer -> 'a -> monadS 'rv unit 'e) -> list 'a -> monadS 'rv unit 'e*)
Definition iteriS {RV A E} (f : Z -> A -> monadS RV unit E) (xs : list A) : monadS RV unit E :=
 iterS_aux 0 f xs.

(*val iterS : forall 'rv 'a 'e. ('a -> monadS 'rv unit 'e) -> list 'a -> monadS 'rv unit 'e*)
Definition iterS {RV A E} (f : A -> monadS RV unit E) (xs : list A) : monadS RV unit E :=
 iteriS (fun _ x => f x) xs.

(*val foreachS : forall 'a 'rv 'vars 'e.
  list 'a -> 'vars -> ('a -> 'vars -> monadS 'rv 'vars 'e) -> monadS 'rv 'vars 'e*)
Fixpoint foreachS {A RV Vars E} (xs : list A) (vars : Vars) (body : A -> Vars -> monadS RV Vars E) : monadS RV Vars E :=
 match xs with
  | [] => returnS vars
  | x :: xs =>
     body x vars >>$= fun vars =>
     foreachS xs vars body
end.

Fixpoint foreach_ZS_up' {rv e Vars} (from to step off : Z) (n : nat) `{ArithFact (0 <? step)} `{ArithFact (0 <=? off)} (vars : Vars) (body : forall (z : Z) `(ArithFact (from <=? z <=? to)), Vars -> monadS rv Vars e) {struct n} : monadS rv Vars e.
exact (
  match sumbool_of_bool (from + off <=? to) with left LE =>
    match n with
    | O => returnS vars
    | S n => body (from + off) _ vars >>$= fun vars => foreach_ZS_up' rv e Vars from to step (off + step) n _ _ vars body
    end
  | right _ => returnS vars
  end).
Defined.

Fixpoint foreach_ZS_down' {rv e Vars} (from to step off : Z) (n : nat) `{ArithFact (0 <? step)} `{ArithFact (off <=? 0)} (vars : Vars) (body : forall (z : Z) `(ArithFact (to <=? z <=? from)), Vars -> monadS rv Vars e) {struct n} : monadS rv Vars e.
exact (
  match sumbool_of_bool (to <=? from + off) with left LE =>
    match n with
    | O => returnS vars
    | S n => body (from + off) _ vars >>$= fun vars => foreach_ZS_down' _ _ _ from to step (off - step) n _ _ vars body
    end
  | right _ => returnS vars
  end).
Defined.

Definition foreach_ZS_up {rv e Vars} from to step vars body `{ArithFact (0 <? step)} :=
    foreach_ZS_up' (rv := rv) (e := e) (Vars := Vars) from to step 0 (S (Z.abs_nat (from - to))) vars body.
Definition foreach_ZS_down {rv e Vars} from to step vars body `{ArithFact (0 <? step)} :=
    foreach_ZS_down' (rv := rv) (e := e) (Vars := Vars) from to step 0 (S (Z.abs_nat (from - to))) vars body.

(*val genlistS : forall 'a 'rv 'e. (nat -> monadS 'rv 'a 'e) -> nat -> monadS 'rv (list 'a) 'e*)
Definition genlistS {A RV E} (f : nat -> monadS RV A E) n : monadS RV (list A) E :=
  let indices := List.seq 0 n in
  foreachS indices [] (fun n xs => (f n >>$= (fun x => returnS (xs ++ [x])))).

(*val and_boolS : forall 'rv 'e. monadS 'rv bool 'e -> monadS 'rv bool 'e -> monadS 'rv bool 'e*)
Definition and_boolS {RV E} (l r : monadS RV bool E) : monadS RV bool E :=
 l >>$= (fun l => if l then r else returnS false).

(*val or_boolS : forall 'rv 'e. monadS 'rv bool 'e -> monadS 'rv bool 'e -> monadS 'rv bool 'e*)
Definition or_boolS {RV E} (l r : monadS RV bool E) : monadS RV bool E :=
 l >>$= (fun l => if l then returnS true else r).

Definition and_boolSP {rv E} {P Q R:bool->Prop} (x : monadS rv {b:bool & ArithFactP (P b)} E) (y : monadS rv {b:bool & ArithFactP (Q b)} E)
  `{H:forall l r, ArithFactP ((P l) -> ((l = true -> (Q r)) -> (R (andb l r))))}
  : monadS rv {b:bool & ArithFactP (R b)} E :=
  x >>$= fun '(existT _ x p) => (if x return ArithFactP (P x) -> _ then
    fun p => y >>$= fun '(existT _ y q) => returnS (existT _ y (and_bool_full_proof p q H))
  else fun p => returnS (existT _ false (and_bool_left_proof p H))) p.

Definition or_boolSP {rv E} {P Q R:bool -> Prop} (l : monadS rv {b : bool & ArithFactP (P b)} E) (r : monadS rv {b : bool & ArithFactP (Q b)} E)
 `{forall l r, ArithFactP ((P l) -> (((l = false) -> (Q r)) -> (R (orb l r))))}
 : monadS rv {b : bool & ArithFactP (R b)} E :=
 l >>$= fun '(existT _ l p) =>
  (if l return ArithFactP (P l) -> _ then fun p => returnS (existT _ true (or_bool_left_proof p H))
   else fun p => r >>$= fun '(existT _ r q) => returnS (existT _ r (or_bool_full_proof p q H))) p.

Definition build_trivial_exS {rv E} {T:Type} (x : monadS rv T E) : monadS rv {x : T & ArithFact true} E :=
 x >>$= fun x => returnS (existT _ x (Build_ArithFactP _ eq_refl)).

(*val bool_of_bitU_fail : forall 'rv 'e. bitU -> monadS 'rv bool 'e*)
Definition bool_of_bitU_fail {RV E} (b : bitU) : monadS RV bool E :=
match b with
  | B0 => returnS false
  | B1 => returnS true
  | BU => failS "bool_of_bitU"
end.

(*val bool_of_bitU_nondetS : forall 'rv 'e. bitU -> monadS 'rv bool 'e*)
Definition bool_of_bitU_nondetS {RV E} (b : bitU) : monadS RV bool E :=
match b with
  | B0 => returnS false
  | B1 => returnS true
  | BU => undefined_boolS tt
end.

(*val bools_of_bits_nondetS : forall 'rv 'e. list bitU -> monadS 'rv (list bool) 'e*)
Definition bools_of_bits_nondetS {RV E} bits : monadS RV (list bool) E :=
  foreachS bits []
    (fun b bools =>
      bool_of_bitU_nondetS b >>$= (fun b =>
      returnS (bools ++ [b]))).

(*val of_bits_nondetS : forall 'rv 'a 'e. Bitvector 'a => list bitU -> monadS 'rv 'a 'e*)
Definition of_bits_nondetS {RV A E} bits `{ArithFact (A >=? 0)} : monadS RV (mword A) E :=
  bools_of_bits_nondetS bits >>$= (fun bs =>
  returnS (of_bools bs)).

(*val of_bits_failS : forall 'rv 'a 'e. Bitvector 'a => list bitU -> monadS 'rv 'a 'e*)
Definition of_bits_failS {RV A E} bits `{ArithFact (A >=? 0)} : monadS RV (mword A) E :=
 maybe_failS "of_bits" (of_bits bits).

(*val mword_nondetS : forall 'rv 'a 'e. Size 'a => unit -> monadS 'rv (mword 'a) 'e
let mword_nondetS () =
  bools_of_bits_nondetS (repeat [BU] (integerFromNat size)) >>$= (fun bs ->
  returnS (wordFromBitlist bs))


val whileS : forall 'rv 'vars 'e. 'vars -> ('vars -> monadS 'rv bool 'e) ->
                ('vars -> monadS 'rv 'vars 'e) -> monadS 'rv 'vars 'e
let rec whileS vars cond body s =
  (cond vars >>$= (fun cond_val s' ->
  if cond_val then
    (body vars >>$= (fun vars s'' -> whileS vars cond body s'')) s'
  else returnS vars s')) s

val untilS : forall 'rv 'vars 'e. 'vars -> ('vars -> monadS 'rv bool 'e) ->
                ('vars -> monadS 'rv 'vars 'e) -> monadS 'rv 'vars 'e
let rec untilS vars cond body s =
  (body vars >>$= (fun vars s' ->
  (cond vars >>$= (fun cond_val s'' ->
  if cond_val then returnS vars s'' else untilS vars cond body s'')) s')) s
*)

Fixpoint whileST' {RV Vars E} limit (vars : Vars) (cond : Vars -> monadS RV bool E) (body : Vars -> monadS RV Vars E) (acc : Acc (Zwf 0) limit) : monadS RV Vars E.
exact (
  if Z_ge_dec limit 0 then
    cond vars >>$= fun cond_val =>
    if cond_val then
      body vars >>$= fun vars => whileST' _ _ _ (limit - 1) vars cond body (_limit_reduces acc)
    else returnS vars
  else failS "Termination limit reached").
Defined.

Definition whileST {RV Vars E} (vars : Vars) measure (cond : Vars -> monadS RV bool E) (body : Vars -> monadS RV Vars E) : monadS RV Vars E :=
  let limit := measure vars in
  whileST' limit vars cond body (Zwf_guarded limit).

(*val untilM : forall 'rv 'vars 'e. 'vars -> ('vars -> monad 'rv bool 'e) ->
                ('vars -> monad 'rv 'vars 'e) -> monad 'rv 'vars 'e*)
Fixpoint untilST' {RV Vars E} limit (vars : Vars) (cond : Vars -> monadS RV bool E) (body : Vars -> monadS RV Vars E) (acc : Acc (Zwf 0) limit) : monadS RV Vars E.
exact (
  if Z_ge_dec limit 0 then
    body vars >>$= fun vars =>
    cond vars >>$= fun cond_val =>
    if cond_val then returnS vars else untilST' _ _ _ (limit - 1) vars cond body (_limit_reduces acc)
  else failS "Termination limit reached").
Defined.

Definition untilST {RV Vars E} (vars : Vars) measure (cond : Vars -> monadS RV bool E) (body : Vars -> monadS RV Vars E) : monadS RV Vars E :=
  let limit := measure vars in
  untilST' limit vars cond body (Zwf_guarded limit).


(*val choose_boolsS : forall 'rv 'e. nat -> monadS 'rv (list bool) 'e*)
Definition choose_boolsS {RV E} n : monadS RV (list bool) E :=
 genlistS (fun _ => choose_boolS tt) n.

(* TODO: Replace by chooseS and prove equivalence to prompt monad version *)
(*val internal_pickS : forall 'rv 'a 'e. list 'a -> monadS 'rv 'a 'e*)
Definition internal_pickS {RV A E} (xs : list A) : monadS RV A E :=
  (* Use sufficiently many nondeterministically chosen bits and convert into an
     index into the list *)
  choose_boolsS (List.length xs) >>$= fun bs =>
  let idx := ((nat_of_bools bs) mod List.length xs)%nat in
  match List.nth_error xs idx with
    | Some x => returnS x
    | None => failS "choose internal_pick"
  end.

Fixpoint undefined_word_natS {rv e} n : monadS rv (Word.word n) e :=
  match n with
  | O => returnS Word.WO
  | S m =>
    choose_boolS tt >>$= fun b =>
    undefined_word_natS m >>$= fun t =>
    returnS (Word.WS b t)
  end.

Definition undefined_bitvectorS {rv e} n `{ArithFact (n >=? 0)} : monadS rv (mword n) e :=
  undefined_word_natS (Z.to_nat n) >>$= fun w =>
  returnS (word_to_mword w).


