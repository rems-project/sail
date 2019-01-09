Require Import Sail2_instr_kinds.
Require Import Sail2_values.
Require Import Sail2_operators_mwords.
Require Import Sail2_prompt_monad.
Require Import Sail2_prompt.
Require Import String.
Require Import List.
Import List.ListNotations.

Axiom real : Type.

Definition MEM_fence_rw_rw {rv e} (_:unit) : monad rv unit e := barrier Barrier_RISCV_rw_rw.
Definition MEM_fence_r_rw  {rv e} (_:unit) : monad rv unit e := barrier Barrier_RISCV_r_rw.
Definition MEM_fence_r_r   {rv e} (_:unit) : monad rv unit e := barrier Barrier_RISCV_r_r.
Definition MEM_fence_rw_w  {rv e} (_:unit) : monad rv unit e := barrier Barrier_RISCV_rw_w.
Definition MEM_fence_w_w   {rv e} (_:unit) : monad rv unit e := barrier Barrier_RISCV_w_w.
Definition MEM_fence_w_rw  {rv e} (_:unit) : monad rv unit e := barrier Barrier_RISCV_w_rw.
Definition MEM_fence_rw_r  {rv e} (_:unit) : monad rv unit e := barrier Barrier_RISCV_rw_r.
Definition MEM_fence_r_w   {rv e} (_:unit) : monad rv unit e := barrier Barrier_RISCV_r_w.
Definition MEM_fence_w_r   {rv e} (_:unit) : monad rv unit e := barrier Barrier_RISCV_w_r.
Definition MEM_fence_tso   {rv e} (_:unit) : monad rv unit e := barrier Barrier_RISCV_tso.
Definition MEM_fence_i     {rv e} (_:unit) : monad rv unit e := barrier Barrier_RISCV_i.
(*
val MEMea                            : forall 'rv 'a 'e. Size 'a => bitvector 'a -> integer -> monad 'rv unit 'e
val MEMea_release                    : forall 'rv 'a 'e. Size 'a => bitvector 'a -> integer -> monad 'rv unit 'e
val MEMea_strong_release             : forall 'rv 'a 'e. Size 'a => bitvector 'a -> integer -> monad 'rv unit 'e
val MEMea_conditional                : forall 'rv 'a 'e. Size 'a => bitvector 'a -> integer -> monad 'rv unit 'e
val MEMea_conditional_release        : forall 'rv 'a 'e. Size 'a => bitvector 'a -> integer -> monad 'rv unit 'e
val MEMea_conditional_strong_release : forall 'rv 'a 'e. Size 'a => bitvector 'a -> integer -> monad 'rv unit 'e
*)
Definition MEMea {rv a e} (addr : mword a) size                     : monad rv unit e := write_mem_ea Write_plain addr size.
Definition MEMea_release {rv a e} (addr : mword a) size             : monad rv unit e := write_mem_ea Write_RISCV_release addr size.
Definition MEMea_strong_release {rv a e} (addr : mword a) size      : monad rv unit e := write_mem_ea Write_RISCV_strong_release addr size.
Definition MEMea_conditional {rv a e} (addr : mword a) size         : monad rv unit e := write_mem_ea Write_RISCV_conditional addr size.
Definition MEMea_conditional_release {rv a e} (addr : mword a) size : monad rv unit e := write_mem_ea Write_RISCV_conditional_release addr size.
Definition MEMea_conditional_strong_release {rv a e} (addr : mword a) size : monad rv unit e
                                          := write_mem_ea Write_RISCV_conditional_strong_release addr size.


(* Some wrappers copied from aarch64_extras *)
(* TODO: Harmonise into a common library *)
(*
Definition get_slice_int_bl len n lo :=
  (* TODO: Is this the intended behaviour? *)
  let hi := lo + len - 1 in
  let bs := bools_of_int (hi + 1) n in
  subrange_list false bs hi lo

val get_slice_int : forall 'a. Bitvector 'a => integer -> integer -> integer -> 'a
Definition get_slice_int len n lo := of_bools (get_slice_int_bl len n lo)
*)
Definition write_ram {rv e} m size (hexRAM : mword m) (addr : mword m) (data : mword (8 * size)) : monad rv bool e :=
  write_mem_val data.

Definition read_ram {rv e} m size `{ArithFact (size >= 0)} (_ : mword m) (addr : mword m) : monad rv (mword (8 * size)) e :=
 read_mem Read_plain addr size.
(*
Definition string_of_bits bs := string_of_bv (bits_of bs).
Definition string_of_int := show

Definition _sign_extend bits len := maybe_failwith (of_bits (exts_bv len bits))
Definition _zero_extend bits len := maybe_failwith (of_bits (extz_bv len bits))
*)
Definition shift_bits_left {a b} (v : mword a) (n : mword b) : mword a :=
  shiftl v (int_of_mword false n).

Definition shift_bits_right {a b} (v : mword a) (n : mword b) : mword a :=
  shiftr v (int_of_mword false n).

Definition shift_bits_right_arith {a b} (v : mword a) (n : mword b) : mword a :=
  arith_shiftr v (int_of_mword false n).

(* Use constants for undefined values for now *)
Definition internal_pick {rv a e} (vs : list a) : monad rv a e :=
match vs with
| (h::_) => returnm h
| _ => Fail "empty list in internal_pick"
end.
Definition undefined_string {rv e} (_:unit) : monad rv string e := returnm ""%string.
Definition undefined_unit {rv e} (_:unit) : monad rv unit e := returnm tt.
Definition undefined_int {rv e} (_:unit) : monad rv Z e := returnm (0:ii).
(*val undefined_vector : forall 'rv 'a 'e. integer -> 'a -> monad 'rv (list 'a) 'e*)
Definition undefined_vector {rv a e} len (u : a) `{ArithFact (len >= 0)} : monad rv (vec a len) e := returnm (vec_init u len).
(*val undefined_bitvector : forall 'rv 'a 'e. Bitvector 'a => integer -> monad 'rv 'a 'e*)
Definition undefined_bitvector {rv e} len `{ArithFact (len >= 0)} : monad rv (mword len) e := returnm (mword_of_int 0).
(*val undefined_bits : forall 'rv 'a 'e. Bitvector 'a => integer -> monad 'rv 'a 'e*)
Definition undefined_bits {rv e} := @undefined_bitvector rv e.
Definition undefined_bit {rv e} (_:unit) : monad rv bitU e := returnm BU.
(*Definition undefined_real {rv e} (_:unit) : monad rv real e := returnm (realFromFrac 0 1).*)
Definition undefined_range {rv e} i j `{ArithFact (i <= j)} : monad rv {z : Z & ArithFact (i <= z /\ z <= j)} e := returnm (build_ex i).
Definition undefined_atom {rv e} i : monad rv Z e := returnm i.
Definition undefined_nat {rv e} (_:unit) : monad rv Z e := returnm (0:ii).

Definition skip {rv e} (_:unit) : monad rv unit e := returnm tt.

(*val elf_entry : unit -> integer*)
Definition elf_entry (_:unit) : Z := 0.
(*declare ocaml target_rep function elf_entry := `Elf_loader.elf_entry`*)

Definition print_bits {n} msg (bs : mword n) := prerr_endline (msg ++ (string_of_bits bs)).

(*val get_time_ns : unit -> integer*)
Definition get_time_ns (_:unit) : Z := 0.
(*declare ocaml target_rep function get_time_ns := `(fun () -> Big_int.of_int (int_of_float (1e9 *. Unix.gettimeofday ())))`*)

Definition eq_bit (x : bitU) (y : bitU) : bool :=
  match x, y with
  | B0, B0 => true
  | B1, B1 => true
  | BU, BU => true
  | _,_ => false
  end.

Require Import Zeuclid.
Definition euclid_modulo (m n : Z) `{ArithFact (n > 0)} : {z : Z & ArithFact (0 <= z <= n-1)}.
apply existT with (x := ZEuclid.modulo m n).
constructor.
destruct H.
assert (Z.abs n = n). { rewrite Z.abs_eq; auto with zarith. }
rewrite <- H at 3.
lapply (ZEuclid.mod_always_pos m n); omega.
Qed.

(* Override the more general version *)

Definition mults_vec {n} (l : mword n) (r : mword n) : mword (2 * n) := mults_vec l r.
Definition mult_vec {n} (l : mword n) (r : mword n) : mword (2 * n) := mult_vec l r.


Definition print_endline (_:string) : unit := tt.
Definition prerr_endline (_:string) : unit := tt.
Definition prerr_string (_:string) : unit := tt.
Definition putchar {T} (_:T) : unit := tt.
Require DecimalString.
Definition string_of_int z := DecimalString.NilZero.string_of_int (Z.to_int z).

(* The constraint solver can do this itself, but a Coq bug puts
   anonymous_subproof into the term instead of an actual subproof. *)
Lemma n_leading_spaces_fact {w__0} :
  w__0 >= 0 -> exists ex17629_ : Z, 1 + w__0 = 1 + ex17629_ /\ 0 <= ex17629_.
intro.
exists w__0.
omega.
Qed.
Hint Resolve n_leading_spaces_fact : sail.
