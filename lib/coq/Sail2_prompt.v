(*Require Import Sail_impl_base*)
Require Import Sail2_values.
Require Import Sail2_prompt_monad.

Require Import List.
Import ListNotations.
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

(*declare {isabelle} termination_argument foreachM = automatic*)

(*val and_boolM : forall 'rv 'e. monad 'rv bool 'e -> monad 'rv bool 'e -> monad 'rv bool 'e*)
Definition and_boolM {rv E} (l : monad rv bool E) (r : monad rv bool E) : monad rv bool E :=
 l >>= (fun l => if l then r else returnm false).

(*val or_boolM : forall 'rv 'e. monad 'rv bool 'e -> monad 'rv bool 'e -> monad 'rv bool 'e*)
Definition or_boolM {rv E} (l : monad rv bool E) (r : monad rv bool E) : monad rv bool E :=
 l >>= (fun l => if l then returnm true else r).

(*val bool_of_bitU_fail : forall 'rv 'e. bitU -> monad 'rv bool 'e*)
Definition bool_of_bitU_fail {rv E} (b : bitU) : monad rv bool E :=
match b with
  | B0 => returnm false
  | B1 => returnm true
  | BU => Fail "bool_of_bitU"
end.

(*val bool_of_bitU_oracle : forall 'rv 'e. bitU -> monad 'rv bool 'e
Definition bool_of_bitU_oracle {rv E} (b : bitU) : monad rv bool E :=
match b with
  | B0 => returnm false
  | B1 => returnm true
  | BU => undefined_bool tt
end.


val whileM : forall 'rv 'vars 'e. 'vars -> ('vars -> monad 'rv bool 'e) ->
                ('vars -> monad 'rv 'vars 'e) -> monad 'rv 'vars 'e
let rec whileM vars cond body =
  cond vars >>= fun cond_val ->
  if cond_val then
    body vars >>= fun vars -> whileM vars cond body
  else return vars

val untilM : forall 'rv 'vars 'e. 'vars -> ('vars -> monad 'rv bool 'e) ->
                ('vars -> monad 'rv 'vars 'e) -> monad 'rv 'vars 'e
let rec untilM vars cond body =
  body vars >>= fun vars ->
  cond vars >>= fun cond_val ->
  if cond_val then return vars else untilM vars cond body

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

*)
