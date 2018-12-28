Require Import Sail2_instr_kinds.
Require Import Sail2_values.
Require Import Sail2_operators_bitlists.
Require Import Sail2_prompt_monad.
Require Import Sail2_prompt.
Require Import Sail2_real.

Axiom slice : forall {m} (_ : mword m) (_ : Z) (n : Z) `{ArithFact (m >= 0)} `{ArithFact (n >= 0)}, mword n.
Definition length {n} (x : mword n) := length_mword x.
Hint Unfold length : sail.


Lemma Replicate_lemma1 {N M O x} :
  O * M = N ->
  O = Z.quot N M ->
  x = Z.quot N M -> M * x = N.
intros. rewrite H1.
rewrite H0 in H.
rewrite Z.mul_comm.
assumption.
Qed.
Hint Resolve Replicate_lemma1 : sail.

Lemma Replicate_lemma2 {N M x} :
 M >= 0 /\ N >= 0 ->
 x = Z.quot N M ->
 x >= 0.
intros; subst.
destruct M; destruct N; intros; try easy.
unfold Z.quot, Z.quotrem.
destruct (N.pos_div_eucl p0 (N.pos p)) as [x y].
case x; easy.
Qed.
Hint Resolve Replicate_lemma2 : sail.


(*
let hexchar_to_bool_list c =
  if c = #'0' then      Just ([false;false;false;false])
  else if c = #'1' then Just ([false;false;false;true ])
  else if c = #'2' then Just ([false;false;true; false])
  else if c = #'3' then Just ([false;false;true; true ])
  else if c = #'4' then Just ([false;true; false;false])
  else if c = #'5' then Just ([false;true; false;true ])
  else if c = #'6' then Just ([false;true; true; false])
  else if c = #'7' then Just ([false;true; true; true ])
  else if c = #'8' then Just ([true; false;false;false])
  else if c = #'9' then Just ([true; false;false;true ])
  else if c = #'A' then Just ([true; false;true; false])
  else if c = #'a' then Just ([true; false;true; false])
  else if c = #'B' then Just ([true; false;true; true ])
  else if c = #'b' then Just ([true; false;true; true ])
  else if c = #'C' then Just ([true; true; false;false])
  else if c = #'c' then Just ([true; true; false;false])
  else if c = #'D' then Just ([true; true; false;true ])
  else if c = #'d' then Just ([true; true; false;true ])
  else if c = #'E' then Just ([true; true; true; false])
  else if c = #'e' then Just ([true; true; true; false])
  else if c = #'F' then Just ([true; true; true; true ])
  else if c = #'f' then Just ([true; true; true; true ])
  else Nothing

let hexstring_to_bools s =
  match (toCharList s) with
    | z :: x :: hs ->
       let str = if (z = #'0' && x = #'x') then hs else z :: x :: hs in
       Maybe.map List.concat (just_list (List.map hexchar_to_bool_list str))
    | _ -> Nothing
  end

val hex_slice : forall 'rv 'e. string -> integer -> integer -> monad 'rv (list bitU) 'e
let hex_slice v len lo =
  match hexstring_to_bools v with
    | Just bs ->
       let hi = len + lo - 1 in
       let bs = ext_list false (len + lo) bs in
       return (of_bools (subrange_list false bs hi lo))
    | Nothing -> Fail "hex_slice"
  end
*)
Axiom hex_slice : forall {rv e}, string -> forall n m, monad rv (mword (n - m)) e.

Definition internal_pick {rv a e} (vs : list a) : monad rv a e :=
match vs with
| (h::_) => returnm h
| _ => Fail "empty list in internal_pick"
end.
Definition undefined_string {rv e} (_:unit) : monad rv string e := returnm ""%string.
Definition undefined_unit {rv e} (_:unit) : monad rv unit e := returnm tt.
Definition undefined_int {rv e} (_:unit) : monad rv Z e := returnm (0:ii).
(*val undefined_vector : forall 'rv 'a 'e. integer -> 'a -> monad 'rv (list 'a) 'e*)
Definition undefined_vector {rv a e} len `{ArithFact (len >= 0)} (u : a) : monad rv (vec a len) e := returnm (vec_init u len).
(*val undefined_bitvector : forall 'rv 'a 'e. Bitvector 'a => integer -> monad 'rv 'a 'e*)
Definition undefined_bitvector {rv e} len `{ArithFact (len >= 0)} : monad rv (mword len) e := returnm (mword_of_int 0).
(*val undefined_bits : forall 'rv 'a 'e. Bitvector 'a => integer -> monad 'rv 'a 'e*)
Definition undefined_bits {rv e} := @undefined_bitvector rv e.
Definition undefined_bit {rv e} (_:unit) : monad rv bitU e := returnm BU.
Definition undefined_real {rv e} (_:unit) : monad rv R e := returnm (realFromFrac 0 1).
Definition undefined_range {rv e} i j `{ArithFact (i <= j)} : monad rv {z : Z & ArithFact (i <= z /\ z <= j)} e := returnm (build_ex i).
Definition undefined_atom {rv e} i : monad rv Z e := returnm i.
Definition undefined_nat {rv e} (_:unit) : monad rv Z e := returnm (0:ii).

(*
(* Use constants for undefined values for now *)
let undefined_string () = return ""
let undefined_unit () = return ()
let undefined_int () = return (0:ii)
val undefined_vector : forall 'rv 'a 'e. integer -> 'a -> monad 'rv (list 'a) 'e
let undefined_vector len u = return (repeat [u] len)
val undefined_bitvector : forall 'rv 'e. integer -> monad 'rv (list bitU) 'e
let undefined_bitvector len = return (of_bools (repeat [false] len))
val undefined_bits : forall 'rv 'e. integer -> monad 'rv (list bitU) 'e
let undefined_bits = undefined_bitvector
let undefined_bit () = return B0
let undefined_real () = return (realFromFrac 0 1)
let undefined_range i j = return i
let undefined_atom i = return i
let undefined_nat () = return (0:ii)

val write_ram : forall 'rv 'e.
  integer -> integer -> list bitU -> list bitU -> list bitU -> monad 'rv unit 'e*)
Definition write_ram {rv e} addrsize size (hexRAM : mword addrsize) (address : mword addrsize) (value : mword (8 * size)) : monad rv unit e :=
  write_mem_ea Write_plain address size >>
  write_mem_val value >>= fun _ =>
  returnm tt.

(*val read_ram : forall 'rv 'e.
  integer -> integer -> list bitU -> list bitU -> monad 'rv (list bitU) 'e*)
Definition read_ram {rv e} addrsize size `{ArithFact (size >= 0)} (hexRAM : mword addrsize) (address : mword addrsize) : monad rv (mword (8 * size)) e :=
  read_mem Read_plain address size.

(*val elf_entry : unit -> integer*)
Definition elf_entry (_:unit) := 0.
(*declare ocaml target_rep function elf_entry = `Elf_loader.elf_entry`
*)

Lemma mul_quot_8_helper : forall x, 8 * x = 8 * (Z.quot (8 * x) 8).
intro.
rewrite Z.mul_comm.
rewrite Z.quot_mul; auto with zarith.
Qed.
Hint Resolve mul_quot_8_helper : sail.

Lemma mul_quot_8_helper2 : forall x y, 8 * x = y -> 8 * x = 8 * (Z.quot y 8).
intros. subst.
apply mul_quot_8_helper.
Qed.
Hint Resolve mul_quot_8_helper2 : sail.

(* For aarch64_vector_arithmetic_binary_uniform_mul_int_dotp *)
Lemma quot4_ge {esize x} : 4 <= esize -> x = Z.quot esize 4 -> x >= 0.
intros.
apply Z.le_ge.
subst.
apply Z.quot_pos; omega.
Qed.
(* except that only proving the hard bit leads to an anomaly...
Hint Resolve quot4_ge : sail.*)
Lemma dotp_lemma {datasize esize x} :
 8 = datasize \/ 16 = datasize \/ 32 = datasize \/ 64 = datasize \/ 128 = datasize \/ False ->
 4 <= esize -> x = Z.quot esize 4 -> datasize >= 0 /\ x >= 0.
intros.
split.
* omega.
* eauto using quot4_ge.
Qed.
Hint Resolve dotp_lemma : sail.


Lemma quot4_gt {esize x} : 4 <= esize -> x = Z.quot esize 4 -> x > 0.
intros.
apply Z.lt_gt.
subst.
apply Z.quot_str_pos.
omega.
Qed.
Hint Resolve quot4_gt : sail.

Lemma vector_single_nowb_lemma {x y} : 0 <= x -> 0 <= y ->
  y * x >= 0.
intros.
apply Z.le_ge.
apply Z.mul_nonneg_nonneg; auto.
Qed.
Hint Resolve vector_single_nowb_lemma : sail.

Lemma vector_single_nowb_lemma2 {x esize} : 8 * x = esize -> 8 * (Z.quot esize 8) = esize.
intro H.
rewrite <- H.
rewrite (Z.mul_comm 8 x).
rewrite Z.quot_mul; auto with zarith.
Qed.
Hint Resolve vector_single_nowb_lemma2 : sail.

Lemma simdfp_register_lemma {datasize x0} :
  8 = datasize \/ 16 = datasize \/ 32 = datasize \/ 64 = datasize \/ 128 = datasize \/ False ->
  x0 = datasize ÷ 8 ->
  64 >= 0 /\ 8 * x0 >= 0.
intros.
split.
* omega.
* apply Z.le_ge.
  apply Z.mul_nonneg_nonneg; auto with zarith.
  subst.
  apply Z.quot_pos; omega.
Qed.
Hint Resolve simdfp_register_lemma : sail.

Lemma simdfp_register_lemma2 {datasize x0} :
  8 = datasize \/ 16 = datasize \/ 32 = datasize \/ 64 = datasize \/ 128 = datasize \/ False ->
  x0 = datasize ÷ 8 ->
  datasize = 8 * x0.
intros [H|[H|[H|[H|[H|[]]]]]] H'; subst;
reflexivity.
Qed.
Hint Resolve simdfp_register_lemma2 : sail.

Lemma atomicops_st_lemma {datasize} :
  8 = datasize \/ 16 = datasize \/ 32 = datasize \/ 64 = datasize \/ 128 = datasize \/ False ->
  8 * (datasize ÷ 8) > 0.
intros [H|[H|[H|[H|[H|[]]]]]]; subst;
reflexivity.
Qed.
Hint Resolve atomicops_st_lemma : sail.

Lemma atomicops_cas_pair_lemma1 {datasize x0} :
  8 = datasize \/ 16 = datasize \/ 32 = datasize \/ 64 = datasize \/ 128 = datasize \/ False ->
  x0 = 2 * datasize ÷ 8 ->
  64 >= 0 /\ 8 * x0 >= 0.
intros [H|[H|[H|[H|[H|[]]]]]]; subst;
intro H; compute in H; subst; omega.
Qed.

Lemma atomicops_cas_pair_lemma2 {datasize} :
  8 = datasize \/ 16 = datasize \/ 32 = datasize \/ 64 = datasize \/ 128 = datasize \/ False ->
  2 * datasize = 8 * (2 * datasize ÷ 8).
intros [H|[H|[H|[H|[H|[]]]]]]; subst; reflexivity.
Qed.

Lemma atomicops_cas_pair_lemma3 {datasize x0} :
  8 = datasize \/ 16 = datasize \/ 32 = datasize \/ 64 = datasize \/ 128 = datasize \/ False ->
  x0 = 2 * datasize ÷ 8 ->
  2 * datasize = 8 * x0.
intros [H|[H|[H|[H|[H|[]]]]]]; subst;
intro H; compute in H; subst; omega.
Qed.

Hint Resolve atomicops_cas_pair_lemma1 atomicops_cas_pair_lemma2 atomicops_cas_pair_lemma3 : sail.

