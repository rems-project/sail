Require Import Sail2_instr_kinds.
Require Import Sail2_values.
Require Import Sail2_operators_mwords.
Require Import Sail2_prompt_monad.
Require Import Sail2_prompt.
Require Import String.
Require Import List.
Import List.ListNotations.

Axiom real : Type.

(*
val MEMr             : forall 'regval 'a 'b 'e. Bitvector 'a, Bitvector 'b => 'a -> integer -> monad 'regval 'b 'e
val MEMr_reserve     : forall 'regval 'a 'b 'e. Bitvector 'a, Bitvector 'b => 'a -> integer -> monad 'regval 'b 'e
val MEMr_tag         : forall 'regval 'a 'b 'e. Bitvector 'a, Bitvector 'b => 'a -> integer -> monad 'regval (bool * 'b) 'e
val MEMr_tag_reserve : forall 'regval 'a 'b 'e. Bitvector 'a, Bitvector 'b => 'a -> integer -> monad 'regval (bool * 'b) 'e
*)
Definition MEMr {regval a b e} `{ArithFact (b >= 0)} (addr : mword a) size            : monad regval (mword b) e := read_mem Read_plain addr size.
Definition MEMr_reserve {regval a b e} `{ArithFact (b >= 0)} (addr : mword a) size    : monad regval (mword b) e := read_mem Read_reserve addr size.

(*val read_tag_bool : forall 'regval 'a 'e. Bitvector 'a => 'a -> monad 'regval bool 'e*)
Definition read_tag_bool {regval a e} (addr : mword a) : monad regval bool e :=
  read_tag addr >>= fun t =>
  maybe_fail "read_tag_bool" (bool_of_bitU t).

(*val write_tag_bool : forall 'regval 'a 'e. Bitvector 'a => 'a -> bool -> monad 'regval unit 'e*)
Definition write_tag_bool {regval a e} (addr : mword a) t : monad regval unit e :=
 write_tag addr (bitU_of_bool t) >>= fun _ => returnm tt.

Definition MEMr_tag {regval a b e} `{ArithFact (b >= 0)} (addr : mword a) size : monad regval (bool * mword b) e :=
  read_mem Read_plain addr size >>= fun v =>
  read_tag_bool addr >>= fun t =>
  returnm (t, v).

Definition MEMr_tag_reserve {regval a b e} `{ArithFact (b >= 0)} (addr : mword a) size : monad regval (bool * mword b) e :=
  read_mem Read_plain addr size >>= fun v =>
  read_tag_bool addr >>= fun t =>
  returnm (t, v).

(*
val MEMea                 : forall 'regval 'a 'e. Bitvector 'a => 'a -> integer -> monad 'regval unit 'e
val MEMea_conditional     : forall 'regval 'a 'e. Bitvector 'a => 'a -> integer -> monad 'regval unit 'e
val MEMea_tag             : forall 'regval 'a 'e. Bitvector 'a => 'a -> integer -> monad 'regval unit 'e
val MEMea_tag_conditional : forall 'regval 'a 'e. Bitvector 'a => 'a -> integer -> monad 'regval unit 'e
*)
Definition MEMea {regval a e} (addr : mword a) size                : monad regval unit e := write_mem_ea Write_plain addr size.
Definition MEMea_conditional {regval a e} (addr : mword a) size    : monad regval unit e := write_mem_ea Write_conditional addr size.

Definition MEMea_tag {regval a e} (addr : mword a) size            : monad regval unit e := write_mem_ea Write_plain addr size.
Definition MEMea_tag_conditional {regval a e} (addr : mword a) size : monad regval unit e := write_mem_ea Write_conditional addr size.

(*
val MEMval                 : forall 'regval 'a 'b 'e. Bitvector 'a, Bitvector 'b => 'a -> integer -> 'b -> monad 'regval unit 'e
val MEMval_conditional     : forall 'regval 'a 'b 'e. Bitvector 'a, Bitvector 'b => 'a -> integer -> 'b -> monad 'regval bool 'e
val MEMval_tag             : forall 'regval 'a 'b 'e. Bitvector 'a, Bitvector 'b => 'a -> integer -> bool -> 'b -> monad 'regval unit 'e
val MEMval_tag_conditional : forall 'regval 'a 'b 'e. Bitvector 'a, Bitvector 'b => 'a -> integer -> bool -> 'b -> monad 'regval bool 'e
*)
Definition MEMval {regval a b e} (_ : mword a) (size : Z) (v : mword b)                      : monad regval unit e := write_mem_val v >>= fun _ => returnm tt.
Definition MEMval_conditional {regval a b e} (_ : mword a) (size : Z) (v : mword b)          : monad regval bool e := write_mem_val v >>= fun b => returnm (if b then true else false).
Definition MEMval_tag {regval a b e} (addr : mword a) (size : Z) t (v : mword b)             : monad regval unit e := write_mem_val v >>= fun _ => write_tag_bool addr t >>= fun _ => returnm tt.
Definition MEMval_tag_conditional {regval a b e} (addr : mword a) (size : Z) t (v : mword b) : monad regval bool e := write_mem_val v >>= fun b => write_tag_bool addr t >>= fun _ => returnm (if b then true else false).

(*val MEM_sync  : forall 'regval 'e. unit -> monad 'regval unit 'e*)

Definition MEM_sync {regval e} (_:unit) : monad regval unit e := barrier Barrier_MIPS_SYNC.

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

(*Definition print_bits msg bs := prerr_endline (msg ^ (string_of_bits bs))

val get_time_ns : unit -> integer*)
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
