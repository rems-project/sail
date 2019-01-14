Require Import Sail2_instr_kinds.
Require Import Sail2_values.
(*
(* 'a is result type *)

type memstate = map integer memory_byte
type tagstate = map integer bitU
(* type regstate = map string (vector bitU) *)

type sequential_state 'regs =
  <| regstate : 'regs;
     memstate : memstate;
     tagstate : tagstate;
     write_ea : maybe (write_kind * integer * integer);
     last_exclusive_operation_was_load : bool|>

val init_state : forall 'regs. 'regs -> sequential_state 'regs
let init_state regs =
  <| regstate = regs;
     memstate = Map.empty;
     tagstate = Map.empty;
     write_ea = Nothing;
     last_exclusive_operation_was_load = false |>

type ex 'e =
  | Failure of string
  | Throw of 'e

type result 'a 'e =
  | Value of 'a
  | Ex of (ex 'e)

(* State, nondeterminism and exception monad with result value type 'a
   and exception type 'e. *)
type monadS 'regs 'a 'e = sequential_state 'regs -> list (result 'a 'e * sequential_state 'regs)

val returnS : forall 'regs 'a 'e. 'a -> monadS 'regs 'a 'e
let returnS a s = [(Value a,s)]

val bindS : forall 'regs 'a 'b 'e. monadS 'regs 'a 'e -> ('a -> monadS 'regs 'b 'e) -> monadS 'regs 'b 'e
let bindS m f (s : sequential_state 'regs) =
  List.concatMap (function
                  | (Value a, s') -> f a s'
                  | (Ex e, s') -> [(Ex e, s')]
                  end) (m s)

val seqS: forall 'regs 'b 'e. monadS 'regs unit 'e -> monadS 'regs 'b 'e -> monadS 'regs 'b 'e
let seqS m n = bindS m (fun (_ : unit) -> n)

let inline (>>$=) = bindS
let inline (>>$) = seqS

val chooseS : forall 'regs 'a 'e. list 'a -> monadS 'regs 'a 'e
let chooseS xs s = List.map (fun x -> (Value x, s)) xs

val readS : forall 'regs 'a 'e. (sequential_state 'regs -> 'a) -> monadS 'regs 'a 'e
let readS f = (fun s -> returnS (f s) s)

val updateS : forall 'regs 'e. (sequential_state 'regs -> sequential_state 'regs) -> monadS 'regs unit 'e
let updateS f = (fun s -> returnS () (f s))

val failS : forall 'regs 'a 'e. string -> monadS 'regs 'a 'e
let failS msg s = [(Ex (Failure msg), s)]

val exitS : forall 'regs 'e 'a. unit -> monadS 'regs 'a 'e
let exitS () = failS "exit"

val throwS : forall 'regs 'a 'e. 'e -> monadS 'regs 'a 'e
let throwS e s = [(Ex (Throw e), s)]

val try_catchS : forall 'regs 'a 'e1 'e2. monadS 'regs 'a 'e1 -> ('e1 -> monadS 'regs 'a 'e2) ->  monadS 'regs 'a 'e2
let try_catchS m h s =
  List.concatMap (function
                  | (Value a, s') -> returnS a s'
                  | (Ex (Throw e), s') -> h e s'
                  | (Ex (Failure msg), s') -> [(Ex (Failure msg), s')]
                  end) (m s)

val assert_expS : forall 'regs 'e. bool -> string -> monadS 'regs unit 'e
let assert_expS exp msg = if exp then returnS () else failS msg

(* For early return, we abuse exceptions by throwing and catching
   the return value. The exception type is "either 'r 'e", where "Right e"
   represents a proper exception and "Left r" an early return of value "r". *)
type monadSR 'regs 'a 'r 'e = monadS 'regs 'a (either 'r 'e)

val early_returnS : forall 'regs 'a 'r 'e. 'r -> monadSR 'regs 'a 'r 'e
let early_returnS r = throwS (Left r)

val catch_early_returnS : forall 'regs 'a 'e. monadSR 'regs 'a 'a 'e -> monadS 'regs 'a 'e
let catch_early_returnS m =
  try_catchS m
    (function
      | Left a -> returnS a
      | Right e -> throwS e
     end)

(* Lift to monad with early return by wrapping exceptions *)
val liftSR : forall 'a 'r 'regs 'e. monadS 'regs 'a 'e -> monadSR 'regs 'a 'r 'e
let liftSR m = try_catchS m (fun e -> throwS (Right e))

(* Catch exceptions in the presence of early returns *)
val try_catchSR : forall 'regs 'a 'r 'e1 'e2. monadSR 'regs 'a 'r 'e1 -> ('e1 -> monadSR 'regs 'a 'r 'e2) ->  monadSR 'regs 'a 'r 'e2
let try_catchSR m h =
  try_catchS m
    (function
      | Left r -> throwS (Left r)
      | Right e -> h e
     end)

val read_tagS : forall 'regs 'a 'e. Bitvector 'a => 'a -> monadS 'regs bitU 'e
let read_tagS addr =
  readS (fun s -> fromMaybe B0 (Map.lookup (unsigned addr) s.tagstate))

(* Read bytes from memory and return in little endian order *)
val read_mem_bytesS : forall 'regs 'e 'a. Bitvector 'a => read_kind -> 'a -> nat -> monadS 'regs (list memory_byte) 'e
let read_mem_bytesS read_kind addr sz =
  let addr = unsigned addr in
  let sz = integerFromNat sz in
  let addrs = index_list addr (addr+sz-1) 1 in
  let read_byte s addr = Map.lookup addr s.memstate in
  readS (fun s -> just_list (List.map (read_byte s) addrs)) >>$= (function
    | Just mem_val ->
       updateS (fun s ->
         if read_is_exclusive read_kind
         then <| s with last_exclusive_operation_was_load = true |>
         else s) >>$
       returnS mem_val
    | Nothing -> failS "read_memS"
  end)

val read_memS : forall 'regs 'e 'a 'b. Bitvector 'a, Bitvector 'b => read_kind -> 'a -> integer -> monadS 'regs 'b 'e
let read_memS rk a sz =
  read_mem_bytesS rk a (natFromInteger sz) >>$= (fun bytes ->
  returnS (bits_of_mem_bytes bytes))

val excl_resultS : forall 'regs 'e. unit -> monadS 'regs bool 'e
let excl_resultS () =
  readS (fun s -> s.last_exclusive_operation_was_load) >>$= (fun excl_load ->
  updateS (fun s -> <| s with last_exclusive_operation_was_load = false |>) >>$
  chooseS (if excl_load then [false; true] else [false]))

val write_mem_eaS : forall 'regs 'e 'a. Bitvector 'a => write_kind -> 'a -> nat -> monadS 'regs unit 'e
let write_mem_eaS write_kind addr sz =
  let addr = unsigned addr in
  let sz = integerFromNat sz in
  updateS (fun s -> <| s with write_ea = Just (write_kind, addr, sz) |>)

(* Write little-endian list of bytes to previously announced address *)
val write_mem_bytesS : forall 'regs 'e. list memory_byte -> monadS 'regs bool 'e
let write_mem_bytesS v =
  readS (fun s -> s.write_ea) >>$= (function
      | Nothing -> failS "write ea has not been announced yet"
      | Just (_, addr, sz) ->
         let addrs = index_list addr (addr+sz-1) 1 in
         (*let v = external_mem_value (bits_of v) in*)
         let a_v = List.zip addrs v in
         let write_byte mem (addr, v) = Map.insert addr v mem in
         updateS (fun s ->
           <| s with memstate = List.foldl write_byte s.memstate a_v |>) >>$
         returnS true
    end)

val write_mem_valS : forall 'regs 'e 'a. Bitvector 'a => 'a -> monadS 'regs bool 'e
let write_mem_valS v = match mem_bytes_of_bits v with
  | Just v -> write_mem_bytesS v
  | Nothing -> failS "write_mem_val"
end

val write_tagS : forall 'regs 'e. bitU -> monadS 'regs bool 'e
let write_tagS t =
  readS (fun s -> s.write_ea) >>$= (function
      | Nothing -> failS "write ea has not been announced yet"
      | Just (_, addr, _) ->
         (*let taddr = addr / cap_alignment in*)
         updateS (fun s -> <| s with tagstate = Map.insert addr t s.tagstate |>) >>$
         returnS true
    end)

val read_regS : forall 'regs 'rv 'a 'e. register_ref 'regs 'rv 'a -> monadS 'regs 'a 'e
let read_regS reg = readS (fun s -> reg.read_from s.regstate)

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

val read_regvalS : forall 'regs 'rv 'e.
  register_accessors 'regs 'rv -> string -> monadS 'regs 'rv 'e
let read_regvalS (read, _) reg =
  readS (fun s -> read reg s.regstate) >>$= (function
      | Just v ->  returnS v
      | Nothing -> failS ("read_regvalS " ^ reg)
    end)

val write_regvalS : forall 'regs 'rv 'e.
  register_accessors 'regs 'rv -> string -> 'rv -> monadS 'regs unit 'e
let write_regvalS (_, write) reg v =
  readS (fun s -> write reg v s.regstate) >>$= (function
      | Just rs' -> updateS (fun s -> <| s with regstate = rs' |>)
      | Nothing ->  failS ("write_regvalS " ^ reg)
    end)

val write_regS : forall 'regs 'rv 'a 'e. register_ref 'regs 'rv 'a -> 'a -> monadS 'regs unit 'e
let write_regS reg v =
  updateS (fun s -> <| s with regstate = reg.write_to v s.regstate |>)

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
*)
