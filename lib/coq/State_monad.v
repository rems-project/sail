Require Import Sail.Instr_kinds.
Require Import Sail.Values.
Require FMapList.
Require Import OrderedType.
Require OrderedTypeEx.
Require Import List.
Require bbv.Word.
Import ListNotations.
Local Open Scope Z.

(* TODO: revisit choice of FMapList *)
Module NatMap := FMapList.Make(OrderedTypeEx.Nat_as_OT).

Definition Memstate : Type := NatMap.t memory_byte.
Definition Tagstate : Type := NatMap.t bitU.
(* type regstate = map string (vector bitU) *)

(* We deviate from the Lem library and prefix the fields with ss_ to avoid
   name clashes. *)
Record sequential_state {Regs} :=
  { ss_regstate : Regs;
    ss_memstate : Memstate;
    ss_tagstate : Tagstate }.
Arguments sequential_state : clear implicits.

(*val init_state : forall 'regs. 'regs -> sequential_state 'regs*)
Definition init_state {Regs} regs : sequential_state Regs :=
  {| ss_regstate := regs;
     ss_memstate := NatMap.empty _;
     ss_tagstate := NatMap.empty _ |}.

Inductive ex E :=
  | Failure : string -> ex E
  | Throw : E -> ex E.
Arguments Failure {E} _.
Arguments Throw {E} _.

Inductive result A E :=
  | Value : A -> result A E
  | Ex : ex E -> result A E.
Arguments Value {A} {E} _.
Arguments Ex {A} {E} _.

(* State, nondeterminism and exception monad with result value type 'a
   and exception type 'e. *)
(* TODO: the list was originally a set, can we reasonably go back to a set? *)
Definition monadS Regs a e : Type :=
 sequential_state Regs -> list (result a e * sequential_state Regs).

(*val returnS : forall 'regs 'a 'e. 'a -> monadS 'regs 'a 'e*)
Definition returnS {Regs A E} (a:A) : monadS Regs A E := fun s => [(Value a,s)].

(*val bindS : forall 'regs 'a 'b 'e. monadS 'regs 'a 'e -> ('a -> monadS 'regs 'b 'e) -> monadS 'regs 'b 'e*)
Definition bindS {Regs A B E} (m : monadS Regs A E) (f : A -> monadS Regs B E) : monadS Regs B E :=
 fun (s : sequential_state Regs) =>
  List.flat_map (fun v => match v with
             | (Value a, s') => f a s'
             | (Ex e, s') => [(Ex e, s')]
             end) (m s).

(*val seqS: forall 'regs 'b 'e. monadS 'regs unit 'e -> monadS 'regs 'b 'e -> monadS 'regs 'b 'e*)
Definition seqS {Regs B E} (m : monadS Regs unit E) (n : monadS Regs B E) : monadS Regs B E :=
 bindS m (fun (_ : unit) => n).
(*
let inline (>>$=) = bindS
let inline (>>$) = seqS
*)
Notation "m >>$= f" := (bindS m f) (at level 50, left associativity).
Notation "m >>$ n" := (seqS m n) (at level 50, left associativity).

(*val chooseS : forall 'regs 'a 'e. SetType 'a => list 'a -> monadS 'regs 'a 'e*)
Definition chooseS {Regs A E} (xs : list A) : monadS Regs A E :=
 fun s => (List.map (fun x => (Value x, s)) xs).

(*val readS : forall 'regs 'a 'e. (sequential_state 'regs -> 'a) -> monadS 'regs 'a 'e*)
Definition readS {Regs A E} (f : sequential_state Regs -> A) : monadS Regs A E :=
 (fun s => returnS (f s) s).

(*val updateS : forall 'regs 'e. (sequential_state 'regs -> sequential_state 'regs) -> monadS 'regs unit 'e*)
Definition updateS {Regs E} (f : sequential_state Regs -> sequential_state Regs) : monadS Regs unit E :=
 (fun s => returnS tt (f s)).

(*val failS : forall 'regs 'a 'e. string -> monadS 'regs 'a 'e*)
Definition failS {Regs A E} msg : monadS Regs A E :=
 fun s => [(Ex (Failure msg), s)].

(*val choose_boolS : forall 'regval 'regs 'a 'e. unit -> monadS 'regs bool 'e*)
Definition choose_boolS {Regs E} (_:unit) : monadS Regs bool E :=
 chooseS [false; true].
Definition undefined_boolS {Regs E} := @choose_boolS Regs E.

(*val exitS : forall 'regs 'e 'a. unit -> monadS 'regs 'a 'e*)
Definition exitS {Regs A E} (_:unit) : monadS Regs A E := failS "exit".

(*val throwS : forall 'regs 'a 'e. 'e -> monadS 'regs 'a 'e*)
Definition throwS {Regs A E} (e : E) :monadS Regs A E :=
 fun s => [(Ex (Throw e), s)].

(*val try_catchS : forall 'regs 'a 'e1 'e2. monadS 'regs 'a 'e1 -> ('e1 -> monadS 'regs 'a 'e2) ->  monadS 'regs 'a 'e2*)
Definition try_catchS {Regs A E1 E2} (m : monadS Regs A E1) (h : E1 -> monadS Regs A E2) : monadS Regs A E2 :=
fun s =>
  List.flat_map (fun v => match v with
                | (Value a, s') => returnS a s'
                | (Ex (Throw e), s') => h e s'
                | (Ex (Failure msg), s') => [(Ex (Failure msg), s')]
                end) (m s).

(*val assert_expS : forall 'regs 'e. bool -> string -> monadS 'regs unit 'e*)
Definition assert_expS {Regs E} (exp : bool) (msg : string) : monadS Regs unit E :=
 if exp then returnS tt else failS msg.

Definition assert_expS' {Regs E} (exp : bool) (msg : string) : monadS Regs (exp = true) E :=
 if exp return monadS Regs (exp = true) E then returnS eq_refl else failS msg.

(* For early return, we abuse exceptions by throwing and catching
   the return value. The exception type is "either 'r 'e", where "Right e"
   represents a proper exception and "Left r" an early return of value "r". *)
Definition monadRS Regs A R E := monadS Regs A (sum R E).

(*val early_returnS : forall 'regs 'a 'r 'e. 'r -> monadRS 'regs 'a 'r 'e*)
Definition early_returnS {Regs A R E} (r : R) : monadRS Regs A R E := throwS (inl r).

(*val catch_early_returnS : forall 'regs 'a 'e. monadRS 'regs 'a 'a 'e -> monadS 'regs 'a 'e*)
Definition catch_early_returnS {Regs A E} (m : monadRS Regs A A E) : monadS Regs A E :=
  try_catchS m
    (fun v => match v with
      | inl a => returnS a
      | inr e => throwS e
     end).

(* Lift to monad with early return by wrapping exceptions *)
(*val liftRS : forall 'a 'r 'regs 'e. monadS 'regs 'a 'e -> monadRS 'regs 'a 'r 'e*)
Definition liftRS {A R Regs E} (m : monadS Regs A E) : monadRS Regs A R E :=
 try_catchS m (fun e => throwS (inr e)).

(* Catch exceptions in the presence of early returns *)
(*val try_catchRS : forall 'regs 'a 'r 'e1 'e2. monadRS 'regs 'a 'r 'e1 -> ('e1 -> monadRS 'regs 'a 'r 'e2) ->  monadRS 'regs 'a 'r 'e2*)
Definition try_catchRS {Regs A R E1 E2} (m : monadRS Regs A R E1) (h : E1 -> monadRS Regs A R E2) : monadRS Regs A R E2 :=
  try_catchS m
    (fun v => match v with
      | inl r => throwS (inl r)
      | inr e => h e
     end).

(*val maybe_failS : forall 'regs 'a 'e. string -> maybe 'a -> monadS 'regs 'a 'e*)
Definition maybe_failS {Regs A E} msg (v : option A) : monadS Regs A E :=
match v with
  | Some a  => returnS a
  | None => failS msg
end.

(*val read_tagS : forall 'regs 'a 'e. Bitvector 'a => 'a -> monadS 'regs bitU 'e*)
Definition read_tagS {Regs A E} (addr : mword A) : monadS Regs bitU E :=
  let addr := Word.wordToNat (get_word addr) in
  readS (fun s => opt_def B0 (NatMap.find addr s.(ss_tagstate))).

Fixpoint genlist_acc {A:Type} (f : nat -> A) n acc : list A :=
  match n with
    | O => acc
    | S n' => genlist_acc f n' (f n' :: acc)
  end.
Definition genlist {A} f n := @genlist_acc A f n [].


(* Read bytes from memory and return in little endian order *)
(*val get_mem_bytes : forall 'regs. nat -> nat -> sequential_state 'regs -> maybe (list memory_byte * bitU)*)
Definition get_mem_bytes {Regs} addr sz (s : sequential_state Regs) : option (list memory_byte * bitU) :=
  let addrs := genlist (fun n => addr + n)%nat sz in
  let read_byte s addr := NatMap.find addr s.(ss_memstate) in
  let read_tag s addr := opt_def B0 (NatMap.find addr s.(ss_tagstate)) in
  option_map
    (fun mem_val => (mem_val, List.fold_left and_bit (List.map (read_tag s) addrs) B1))
    (just_list (List.map (read_byte s) addrs)).

(*val read_memt_bytesS : forall 'regs 'e. read_kind -> nat -> nat -> monadS 'regs (list memory_byte * bitU) 'e*)
Definition read_memt_bytesS {Regs E} (_ : read_kind) addr sz : monadS Regs (list memory_byte * bitU) E :=
  readS (get_mem_bytes addr sz) >>$=
  maybe_failS "read_memS".

(*val read_mem_bytesS : forall 'regs 'e. read_kind -> nat -> nat -> monadS 'regs (list memory_byte) 'e*)
Definition read_mem_bytesS {Regs E} (rk : read_kind) addr sz : monadS Regs (list memory_byte) E :=
  read_memt_bytesS rk addr sz >>$= (fun '(bytes, _) =>
  returnS bytes).

(*val read_memtS : forall 'regs 'e 'a 'b. Bitvector 'a, Bitvector 'b => read_kind -> 'a -> integer -> monadS 'regs ('b * bitU) 'e*)
Definition read_memtS {Regs E A B} (rk : read_kind) (a : mword A) sz `{ArithFact (B >=? 0)} : monadS Regs (mword B * bitU) E :=
  let a := Word.wordToNat (get_word a) in
  read_memt_bytesS rk a (Z.to_nat sz) >>$= (fun '(bytes, tag) =>
  maybe_failS "bits_of_mem_bytes" (of_bits (bits_of_mem_bytes bytes)) >>$= (fun mem_val =>
  returnS (mem_val, tag))).

(*val read_memS : forall 'regs 'e 'a 'b. Bitvector 'a, Bitvector 'b => read_kind -> 'a -> integer -> monadS 'regs 'b 'e*)
Definition read_memS {Regs E A B} rk (a : mword A) sz `{ArithFact (B >=? 0)} : monadS Regs (mword B) E :=
  read_memtS rk a sz >>$= (fun '(bytes, _) =>
  returnS bytes).

(*val excl_resultS : forall 'regs 'e. unit -> monadS 'regs bool 'e*)
Definition excl_resultS {Regs E} : unit -> monadS Regs bool E :=
  (* TODO: This used to be more deterministic, checking a flag in the state
     whether an exclusive load has occurred before.  However, this does not
     seem very precise; it might be safer to overapproximate the possible
     behaviours by always making a nondeterministic choice. *)
  @undefined_boolS Regs E.

(* Write little-endian list of bytes to given address *)
(*val put_mem_bytes : forall 'regs. nat -> nat -> list memory_byte -> bitU -> sequential_state 'regs -> sequential_state 'regs*)
Definition put_mem_bytes {Regs} addr sz (v : list memory_byte) (tag : bitU) (s : sequential_state Regs) : sequential_state Regs :=
  let addrs := genlist (fun n => addr + n)%nat sz in
  let a_v := List.combine addrs v in
  let write_byte mem '(addr, v) := NatMap.add addr v mem in
  let write_tag mem addr := NatMap.add addr tag mem in
  {| ss_regstate := s.(ss_regstate);
     ss_memstate := List.fold_left write_byte a_v s.(ss_memstate);
     ss_tagstate := List.fold_left write_tag addrs s.(ss_tagstate) |}.

(*val write_memt_bytesS : forall 'regs 'e. write_kind -> nat -> nat -> list memory_byte -> bitU -> monadS 'regs bool 'e*)
Definition write_memt_bytesS {Regs E} (_ : write_kind) addr sz (v : list memory_byte) (t : bitU) : monadS Regs bool E :=
  updateS (put_mem_bytes addr sz v t) >>$
  returnS true.

(*val write_mem_bytesS : forall 'regs 'e. write_kind -> nat -> nat -> list memory_byte -> monadS 'regs bool 'e*)
Definition write_mem_bytesS {Regs E} wk addr sz (v : list memory_byte) : monadS Regs bool E :=
 write_memt_bytesS wk addr sz v B0.

(*val write_memtS : forall 'regs 'e 'a 'b. Bitvector 'a, Bitvector 'b =>
  write_kind -> 'a -> integer -> 'b -> bitU -> monadS 'regs bool 'e*)
Definition write_memtS {Regs E A B} wk (addr : mword A) sz (v : mword B) (t : bitU) : monadS Regs bool E :=
  match (Word.wordToNat (get_word addr), mem_bytes_of_bits v) with
    | (addr, Some v) => write_memt_bytesS wk addr (Z.to_nat sz) v t
    | _ => failS "write_mem"
  end.

(*val write_memS : forall 'regs 'e 'a 'b. Bitvector 'a, Bitvector 'b =>
  write_kind -> 'a -> integer -> 'b -> monadS 'regs bool 'e*)
Definition write_memS {Regs E A B} wk (addr : mword A) sz (v : mword B) : monadS Regs bool E :=
 write_memtS wk addr sz v B0.

(*val read_regS : forall 'regs 'rv 'a 'e. register_ref 'regs 'rv 'a -> monadS 'regs 'a 'e*)
Definition read_regS {Regs RV A E} (reg : register_ref Regs RV A) : monadS Regs A E :=
 readS (fun s => reg.(read_from) s.(ss_regstate)).

(* TODO
let read_reg_range reg i j state =
  let v = slice (get_reg state (name_of_reg reg)) i j in
  [(Value (vec_to_bvec v),state)]
let read_reg_bit reg i state =
  let v = access (get_reg state (name_of_reg reg)) i in
  [(Value v,state)]
let read_reg_field reg regfield =
  let (i,j) = register_field_indices reg regfield in
  read_reg_range reg i j
let read_reg_bitfield reg regfield =
  let (i,_) = register_field_indices reg regfield in
  read_reg_bit reg i *)

(*val read_regvalS : forall 'regs 'rv 'e.
  register_accessors 'regs 'rv -> string -> monadS 'regs 'rv 'e*)
Definition read_regvalS {Regs RV E} (acc : register_accessors Regs RV) reg : monadS Regs RV E :=
  let '(read, _) := acc in
  readS (fun s => read reg s.(ss_regstate)) >>$= (fun v => match v with
      | Some v =>  returnS v
      | None => failS ("read_regvalS " ++ reg)
    end).

(*val write_regvalS : forall 'regs 'rv 'e.
  register_accessors 'regs 'rv -> string -> 'rv -> monadS 'regs unit 'e*)
Definition write_regvalS {Regs RV E} (acc : register_accessors Regs RV) reg (v : RV) : monadS Regs unit E :=
  let '(_, write) := acc in
  readS (fun s => write reg v s.(ss_regstate)) >>$= (fun x => match x with
      | Some rs' => updateS (fun s => {| ss_regstate := rs'; ss_memstate := s.(ss_memstate); ss_tagstate := s.(ss_tagstate) |})
      | None =>  failS ("write_regvalS " ++ reg)
    end).

(*val write_regS : forall 'regs 'rv 'a 'e. register_ref 'regs 'rv 'a -> 'a -> monadS 'regs unit 'e*)
Definition write_regS {Regs RV A E} (reg : register_ref Regs RV A) (v:A) : monadS Regs unit E :=
  updateS (fun s => {| ss_regstate := reg.(write_to) v s.(ss_regstate); ss_memstate := s.(ss_memstate); ss_tagstate := s.(ss_tagstate) |}).

(* TODO
val update_reg : forall 'regs 'rv 'a 'b 'e. register_ref 'regs 'rv 'a -> ('a -> 'b -> 'a) -> 'b -> monadS 'regs unit 'e
let update_reg reg f v state =
  let current_value = get_reg state reg in
  let new_value = f current_value v in
  [(Value (), set_reg state reg new_value)]

let write_reg_field reg regfield = update_reg reg regfield.set_field

val update_reg_range : forall 'regs 'rv 'a 'b. Bitvector 'a, Bitvector 'b => register_ref 'regs 'rv 'a -> integer -> integer -> 'a -> 'b -> 'a
let update_reg_range reg i j reg_val new_val = set_bits (reg.is_inc) reg_val i j (bits_of new_val)
let write_reg_range reg i j = update_reg reg (update_reg_range reg i j)

let update_reg_pos reg i reg_val x = update_list reg.is_inc reg_val i x
let write_reg_pos reg i = update_reg reg (update_reg_pos reg i)

let update_reg_bit reg i reg_val bit = set_bit (reg.is_inc) reg_val i (to_bitU bit)
let write_reg_bit reg i = update_reg reg (update_reg_bit reg i)

let update_reg_field_range regfield i j reg_val new_val =
  let current_field_value = regfield.get_field reg_val in
  let new_field_value = set_bits (regfield.field_is_inc) current_field_value i j (bits_of new_val) in
  regfield.set_field reg_val new_field_value
let write_reg_field_range reg regfield i j = update_reg reg (update_reg_field_range regfield i j)

let update_reg_field_pos regfield i reg_val x =
  let current_field_value = regfield.get_field reg_val in
  let new_field_value = update_list regfield.field_is_inc current_field_value i x in
  regfield.set_field reg_val new_field_value
let write_reg_field_pos reg regfield i = update_reg reg (update_reg_field_pos regfield i)

let update_reg_field_bit regfield i reg_val bit =
  let current_field_value = regfield.get_field reg_val in
  let new_field_value = set_bit (regfield.field_is_inc) current_field_value i (to_bitU bit) in
  regfield.set_field reg_val new_field_value
let write_reg_field_bit reg regfield i = update_reg reg (update_reg_field_bit regfield i)*)

(* TODO Add Show typeclass for value and exception type *)
(*val show_result : forall 'a 'e. result 'a 'e -> string*)
Definition show_result {A E} (x : result A E) : string := match x with
  | Value _ => "Value ()"
  | Ex (Failure msg) => "Failure " ++ msg
  | Ex (Throw _) => "Throw"
end.

(*val prerr_results : forall 'a 'e 's. SetType 's => set (result 'a 'e * 's) -> unit*)
Definition prerr_results {A E S} (rs : list (result A E * S)) : unit := tt.
(*  let _ = Set.map (fun (r, _) -> let _ = prerr_endline (show_result r) in ()) rs in
  ()*)

