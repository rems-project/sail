(*Require Import Sail_impl_base*)
Require Import Sail2_values.
Require Import Sail2_prompt_monad.
Require Import Sail2_prompt.
Require Import Sail2_state_monad.
Import ListNotations.

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

(*val genlistS : forall 'a 'rv 'e. (nat -> monadS 'rv 'a 'e) -> nat -> monadS 'rv (list 'a) 'e*)
Definition genlistS {A RV E} (f : nat -> monadS RV A E) n : monadS RV (list A) E :=
  let indices := genlist (fun n => n) n in
  foreachS indices [] (fun n xs => (f n >>$= (fun x => returnS (xs ++ [x])))).

(*val and_boolS : forall 'rv 'e. monadS 'rv bool 'e -> monadS 'rv bool 'e -> monadS 'rv bool 'e*)
Definition and_boolS {RV E} (l r : monadS RV bool E) : monadS RV bool E :=
 l >>$= (fun l => if l then r else returnS false).

(*val or_boolS : forall 'rv 'e. monadS 'rv bool 'e -> monadS 'rv bool 'e -> monadS 'rv bool 'e*)
Definition or_boolS {RV E} (l r : monadS RV bool E) : monadS RV bool E :=
 l >>$= (fun l => if l then returnS true else r).

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
Definition of_bits_nondetS {RV A E} bits `{ArithFact (A >= 0)} : monadS RV (mword A) E :=
  bools_of_bits_nondetS bits >>$= (fun bs =>
  returnS (of_bools bs)).

(*val of_bits_failS : forall 'rv 'a 'e. Bitvector 'a => list bitU -> monadS 'rv 'a 'e*)
Definition of_bits_failS {RV A E} bits `{ArithFact (A >= 0)} : monadS RV (mword A) E :=
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
(*val choose_boolsS : forall 'rv 'e. nat -> monadS 'rv (list bool) 'e*)
Definition choose_boolsS {RV E} n : monadS RV (list bool) E :=
 genlistS (fun _ => choose_boolS tt) n.

(* TODO: Replace by chooseS and prove equivalence to prompt monad version *)
(*val internal_pickS : forall 'rv 'a 'e. list 'a -> monadS 'rv 'a 'e
let internal_pickS xs =
  (* Use sufficiently many nondeterministically chosen bits and convert into an
     index into the list *)
  choose_boolsS (List.length xs) >>$= fun bs ->
  let idx = (natFromNatural (nat_of_bools bs)) mod List.length xs in
  match index xs idx with
    | Just x -> returnS x
    | Nothing -> failS "choose internal_pick"
  end


*)
