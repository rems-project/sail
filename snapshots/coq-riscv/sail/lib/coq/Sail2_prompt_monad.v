Require Import String.
(*Require Import Sail_impl_base*)
Require Import Sail2_instr_kinds.
Require Import Sail2_values.



Definition register_name := string.
Definition address := list bitU.

Inductive monad regval a e :=
  | Done : a -> monad regval a e
  (* Read a number : bytes from memory, returned in little endian order *)
  | Read_mem : read_kind -> address -> nat -> (list memory_byte -> monad regval a e) -> monad regval a e
  (* Read the tag : a memory address *)
  | Read_tag : address -> (bitU -> monad regval a e) -> monad regval a e
  (* Tell the system a write is imminent, at address lifted, : size nat *)
  | Write_ea : write_kind -> address -> nat -> monad regval a e -> monad regval a e
  (* Request the result : store-exclusive *)
  | Excl_res : (bool -> monad regval a e) -> monad regval a e
  (* Request to write memory at last signalled address. Memory value should be 8
     times the size given in ea signal, given in little endian order *)
  | Write_memv : list memory_byte -> (bool -> monad regval a e) -> monad regval a e
  (* Request to write the tag at last signalled address. *)
  | Write_tag : address -> bitU -> (bool -> monad regval a e) -> monad regval a e
  (* Tell the system to dynamically recalculate dependency footprint *)
  | Footprint : monad regval a e -> monad regval a e
  (* Request a memory barrier *)
  | Barrier : barrier_kind -> monad regval a e -> monad regval a e
  (* Request to read register, will track dependency when mode.track_values *)
  | Read_reg : register_name -> (regval -> monad regval a e) -> monad regval a e
  (* Request to write register *)
  | Write_reg : register_name -> regval -> monad regval a e -> monad regval a e
  | Undefined : (bool -> monad regval a e) -> monad regval a e
  (*Result : a failed assert with possible error message to report*)
  | Fail : string -> monad regval a e
  | Error : string -> monad regval a e
  (* Exception : type e *)
  | Exception : e -> monad regval a e.
  (* TODO: Reading/writing tags *)

Arguments Done [_ _ _].
Arguments Read_mem [_ _ _].
Arguments Read_tag [_ _ _].
Arguments Write_ea [_ _ _].
Arguments Excl_res [_ _ _].
Arguments Write_memv [_ _ _].
Arguments Write_tag [_ _ _].
Arguments Footprint [_ _ _].
Arguments Barrier [_ _ _].
Arguments Read_reg [_ _ _].
Arguments Write_reg [_ _ _].
Arguments Undefined [_ _ _].
Arguments Fail [_ _ _].
Arguments Error [_ _ _].
Arguments Exception [_ _ _].

(*val return : forall rv a e. a -> monad rv a e*)
Definition returnm {rv A E} (a : A) : monad rv A E := Done a.

(*val bind : forall rv a b e. monad rv a e -> (a -> monad rv b e) -> monad rv b e*)
Fixpoint bind {rv A B E} (m : monad rv A E) (f : A -> monad rv B E) := match m with
  | Done a => f a
  | Read_mem rk a sz k => Read_mem rk a sz (fun v => bind (k v) f)
  | Read_tag a k =>       Read_tag a       (fun v => bind (k v) f)
  | Write_memv descr k => Write_memv descr (fun v => bind (k v) f)
  | Write_tag a t k =>    Write_tag a t    (fun v => bind (k v) f)
  | Read_reg descr k =>   Read_reg descr   (fun v => bind (k v) f)
  | Excl_res k =>         Excl_res         (fun v => bind (k v) f)
  | Undefined k =>        Undefined        (fun v => bind (k v) f)
  | Write_ea wk a sz k => Write_ea wk a sz (bind k f)
  | Footprint k =>        Footprint        (bind k f)
  | Barrier bk k =>       Barrier bk       (bind k f)
  | Write_reg r v k =>    Write_reg r v    (bind k f)
  | Fail descr =>         Fail descr
  | Error descr =>        Error descr
  | Exception e =>        Exception e
end.

Notation "m >>= f" := (bind m f) (at level 50, left associativity).
(*val (>>) : forall rv b e. monad rv unit e -> monad rv b e -> monad rv b e*)
Definition bind0 {rv A E} (m : monad rv unit E) (n : monad rv A E) :=
  m >>= fun (_ : unit) => n.
Notation "m >> n" := (bind0 m n) (at level 50, left associativity).

(*val exit : forall rv a e. unit -> monad rv a e*)
Definition exit {rv A E} (_ : unit) : monad rv A E := Fail "exit".

(*val undefined_bool : forall 'rv 'e. unit -> monad 'rv bool 'e*)
Definition undefined_bool {rv e} (_:unit) : monad rv bool e := Undefined returnm.

(*val assert_exp : forall rv e. bool -> string -> monad rv unit e*)
Definition assert_exp {rv E} (exp :bool) msg : monad rv unit E :=
 if exp then Done tt else Fail msg.

Definition assert_exp' {rv E} (exp :bool) msg : monad rv (exp = true) E :=
 if exp return monad rv (exp = true) E then Done eq_refl else Fail msg.
Definition bindH {rv A P E} (m : monad rv P E) (n : monad rv A E) :=
  m >>= fun (H : P) => n.
Notation "m >>> n" := (bindH m n) (at level 50, left associativity).

(*val throw : forall rv a e. e -> monad rv a e*)
Definition throw {rv A E} e : monad rv A E := Exception e.

(*val try_catch : forall rv a e1 e2. monad rv a e1 -> (e1 -> monad rv a e2) -> monad rv a e2*)
Fixpoint try_catch {rv A E1 E2} (m : monad rv A E1) (h : E1 -> monad rv A E2) := match m with
  | Done a =>             Done a
  | Read_mem rk a sz k => Read_mem rk a sz (fun v => try_catch (k v) h)
  | Read_tag a k =>       Read_tag a       (fun v => try_catch (k v) h)
  | Write_memv descr k => Write_memv descr (fun v => try_catch (k v) h)
  | Write_tag a t k =>    Write_tag a t     (fun v => try_catch (k v) h)
  | Read_reg descr k =>   Read_reg descr   (fun v => try_catch (k v) h)
  | Excl_res k =>         Excl_res         (fun v => try_catch (k v) h)
  | Undefined k =>        Undefined        (fun v => try_catch (k v) h)
  | Write_ea wk a sz k => Write_ea wk a sz (try_catch k h)
  | Footprint k =>        Footprint        (try_catch k h)
  | Barrier bk k =>       Barrier bk       (try_catch k h)
  | Write_reg r v k =>    Write_reg r v    (try_catch k h)
  | Fail descr =>         Fail descr
  | Error descr =>        Error descr
  | Exception e =>        h e
end.

(* For early return, we abuse exceptions by throwing and catching
   the return value. The exception type is "either r e", where "inr e"
   represents a proper exception and "inl r" an early return : value "r". *)
Definition monadR rv a r e := monad rv a (sum r e).

(*val early_return : forall rv a r e. r -> monadR rv a r e*)
Definition early_return {rv A R E} (r : R) : monadR rv A R E := throw (inl r).

(*val catch_early_return : forall rv a e. monadR rv a a e -> monad rv a e*)
Definition catch_early_return {rv A E} (m : monadR rv A A E) :=
  try_catch m
    (fun r => match r with
      | inl a => returnm a
      | inr e => throw e
     end).

(* Lift to monad with early return by wrapping exceptions *)
(*val liftR : forall rv a r e. monad rv a e -> monadR rv a r e*)
Definition liftR {rv A R E} (m : monad rv A E) : monadR rv A R E :=
 try_catch m (fun e => throw (inr e)).

(* Catch exceptions in the presence : early returns *)
(*val try_catchR : forall rv a r e1 e2. monadR rv a r e1 -> (e1 -> monadR rv a r e2) ->  monadR rv a r e2*)
Definition try_catchR {rv A R E1 E2} (m : monadR rv A R E1) (h : E1 -> monadR rv A R E2) :=
  try_catch m
    (fun r => match r with
      | inl r => throw (inl r)
      | inr e => h e
     end).

(*val maybe_fail : forall 'rv 'a 'e. string -> maybe 'a -> monad 'rv 'a 'e*)
Definition maybe_fail {rv A E} msg (x : option A) : monad rv A E :=
match x with
  | Some a => returnm a
  | None => Fail msg
end.

(*val read_mem_bytes : forall 'rv 'a 'b 'e. Bitvector 'a, Bitvector 'b => read_kind -> 'a -> integer -> monad 'rv (list memory_byte) 'e*)
Definition read_mem_bytes {rv A E} rk (addr : mword A) sz : monad rv (list memory_byte) E :=
  Read_mem rk (bits_of addr) (Z.to_nat sz) returnm.

(*val read_mem : forall 'rv 'a 'b 'e. Bitvector 'a, Bitvector 'b => read_kind -> 'a -> integer -> monad 'rv 'b 'e*)
Definition read_mem {rv A B E} `{ArithFact (B >= 0)} rk (addr : mword A) sz : monad rv (mword B) E :=
  bind
    (read_mem_bytes rk addr sz)
    (fun bytes =>
       maybe_fail "bits_of_mem_bytes" (of_bits (bits_of_mem_bytes bytes))).

(*val read_tag : forall rv a e. Bitvector a => a -> monad rv bitU e*)
Definition read_tag {rv a e} `{Bitvector a} (addr : a) : monad rv bitU e :=
 Read_tag (bits_of addr) returnm.

(*val excl_result : forall rv e. unit -> monad rv bool e*)
Definition excl_result {rv e} (_:unit) : monad rv bool e :=
  let k successful := (returnm successful) in
  Excl_res k.

Definition write_mem_ea {rv a E} `{Bitvector a} wk (addr: a) sz : monad rv unit E :=
 Write_ea wk (bits_of addr) (Z.to_nat sz) (Done tt).

Definition write_mem_val {rv a e} `{Bitvector a} (v : a) : monad rv bool e := match mem_bytes_of_bits v with
  | Some v => Write_memv v returnm
  | None => Fail "write_mem_val"
end.

(*val write_tag : forall rv a e. Bitvector 'a => 'a -> bitU -> monad rv bool e*)
Definition write_tag {rv a e} (addr : mword a) (b : bitU) : monad rv bool e := Write_tag (bits_of addr) b returnm.

Definition read_reg {s rv a e} (reg : register_ref s rv a) : monad rv a e :=
  let k v :=
    match reg.(of_regval) v with
      | Some v => Done v
      | None => Error "read_reg: unrecognised value"
    end
  in
  Read_reg reg.(name) k.

(* TODO
val read_reg_range : forall s r rv a e. Bitvector a => register_ref s rv r -> integer -> integer -> monad rv a e
Definition read_reg_range reg i j :=
  read_reg_aux of_bits (external_reg_slice reg (natFromInteger i,natFromInteger j))

Definition read_reg_bit reg i :=
  read_reg_aux (fun v -> v) (external_reg_slice reg (natFromInteger i,natFromInteger i)) >>= fun v ->
  returnm (extract_only_element v)

Definition read_reg_field reg regfield :=
  read_reg_aux (external_reg_field_whole reg regfield)

Definition read_reg_bitfield reg regfield :=
  read_reg_aux (external_reg_field_whole reg regfield) >>= fun v ->
  returnm (extract_only_element v)*)

Definition reg_deref {s rv a e} := @read_reg s rv a e.

(*Parameter write_reg : forall {s rv a e}, register_ref s rv a -> a -> monad rv unit e.*)
Definition write_reg {s rv a e} (reg : register_ref s rv a) (v : a) : monad rv unit e :=
 Write_reg reg.(name) (reg.(regval_of) v) (Done tt).

(* TODO
Definition write_reg reg v :=
  write_reg_aux (external_reg_whole reg) v
Definition write_reg_range reg i j v :=
  write_reg_aux (external_reg_slice reg (natFromInteger i,natFromInteger j)) v
Definition write_reg_pos reg i v :=
  let iN := natFromInteger i in
  write_reg_aux (external_reg_slice reg (iN,iN)) [v]
Definition write_reg_bit := write_reg_pos
Definition write_reg_field reg regfield v :=
  write_reg_aux (external_reg_field_whole reg regfield.field_name) v
Definition write_reg_field_bit reg regfield bit :=
  write_reg_aux (external_reg_field_whole reg regfield.field_name)
                (Vector [bit] 0 (is_inc_of_reg reg))
Definition write_reg_field_range reg regfield i j v :=
  write_reg_aux (external_reg_field_slice reg regfield.field_name (natFromInteger i,natFromInteger j)) v
Definition write_reg_field_pos reg regfield i v :=
  write_reg_field_range reg regfield i i [v]
Definition write_reg_field_bit := write_reg_field_pos*)

(*val barrier : forall rv e. barrier_kind -> monad rv unit e*)
Definition barrier {rv e} bk : monad rv unit e := Barrier bk (Done tt).

(*val footprint : forall rv e. unit -> monad rv unit e*)
Definition footprint {rv e} (_ : unit) : monad rv unit e := Footprint (Done tt).
