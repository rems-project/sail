(****************************************************************************)
(*     Sail                                                                 *)
(*                                                                          *)
(*  Sail and the Sail architecture models here, comprising all files and    *)
(*  directories except the ASL-derived Sail code in the aarch64 directory,  *)
(*  are subject to the BSD two-clause licence below.                        *)
(*                                                                          *)
(*  The ASL derived parts of the ARMv8.3 specification in                   *)
(*  aarch64/no_vector and aarch64/full are copyright ARM Ltd.               *)
(*                                                                          *)
(*  Copyright (c) 2013-2021                                                 *)
(*    Kathyrn Gray                                                          *)
(*    Shaked Flur                                                           *)
(*    Stephen Kell                                                          *)
(*    Gabriel Kerneis                                                       *)
(*    Robert Norton-Wright                                                  *)
(*    Christopher Pulte                                                     *)
(*    Peter Sewell                                                          *)
(*    Alasdair Armstrong                                                    *)
(*    Brian Campbell                                                        *)
(*    Thomas Bauereiss                                                      *)
(*    Anthony Fox                                                           *)
(*    Jon French                                                            *)
(*    Dominic Mulligan                                                      *)
(*    Stephen Kell                                                          *)
(*    Mark Wassell                                                          *)
(*    Alastair Reid (Arm Ltd)                                               *)
(*                                                                          *)
(*  All rights reserved.                                                    *)
(*                                                                          *)
(*  This work was partially supported by EPSRC grant EP/K008528/1 <a        *)
(*  href="http://www.cl.cam.ac.uk/users/pes20/rems">REMS: Rigorous          *)
(*  Engineering for Mainstream Systems</a>, an ARM iCASE award, EPSRC IAA   *)
(*  KTF funding, and donations from Arm.  This project has received         *)
(*  funding from the European Research Council (ERC) under the European     *)
(*  Union’s Horizon 2020 research and innovation programme (grant           *)
(*  agreement No 789108, ELVER).                                            *)
(*                                                                          *)
(*  This software was developed by SRI International and the University of  *)
(*  Cambridge Computer Laboratory (Department of Computer Science and       *)
(*  Technology) under DARPA/AFRL contracts FA8650-18-C-7809 ("CIFV")        *)
(*  and FA8750-10-C-0237 ("CTSRD").                                         *)
(*                                                                          *)
(*  SPDX-License-Identifier: BSD-2-Clause                                   *)
(****************************************************************************)

open Ast.Bit

type bits = Extraction.Definitions.bvn

type 'a return = { return : 'b. 'a -> 'b }

let opt_trace = ref false

let trace_depth = ref 0
let random = ref false

let opt_cycle_limit = ref 0
let cycle_count_var = ref 0

let get_cycle_count () = Z.of_int !cycle_count_var

let cycle_count () = incr cycle_count_var

let sail_call (type t) (f : _ -> t) =
  let module M = struct
    exception Return of t
  end in
  let return = { return = (fun x -> raise (M.Return x)) } in
  try f return with M.Return x -> x

let trace str =
  if !opt_trace then (
    if !trace_depth < 0 then trace_depth := 0 else ();
    prerr_endline (String.make (!trace_depth * 2) ' ' ^ str)
  )
  else ()

let trace_write name str = trace ("Write: " ^ name ^ " " ^ str)

let trace_read name str = trace ("Read: " ^ name ^ " " ^ str)

let sail_trace_call (type t) (name : string) (in_string : string) (string_of_out : t -> string) (f : _ -> t) =
  let module M = struct
    exception Return of t
  end in
  let return = { return = (fun x -> raise (M.Return x)) } in
  trace ("Call: " ^ name ^ " " ^ in_string);
  incr trace_depth;
  let result = try f return with M.Return x -> x in
  decr trace_depth;
  trace ("Return: " ^ string_of_out result);
  result

exception Runtime_type_error of string

let eq_anything a b = a = b

let require_width name = function
  | Some r -> r
  | None -> raise (Runtime_type_error (name ^ ": bitvector width mismatch"))

let and_bits xs ys = require_width "and_bits" (Extraction.PrimBits.and_bits xs ys)

let and_bool = Extraction.PrimBits.and_bool

let or_bits xs ys = require_width "or_bits" (Extraction.PrimBits.or_bits xs ys)

let or_bool = Extraction.PrimBits.or_bool

let xor_bits xs ys = require_width "xor_bits" (Extraction.PrimBits.xor_bits xs ys)

let undefined_bit () = Extraction.PrimBits.of_bit_list [(if !random then if Random.bool () then B0 else B1 else B0)]

let undefined_bool () = if !random then Random.bool () else false

let rec undefined_vector len item =
  if Z.equal len Z.zero then [] else item :: undefined_vector (Z.sub len (Z.of_int 1)) item

let undefined_list _ = []

let undefined_bitvector len = Extraction.PrimBits.zeros len

let undefined_string () = ""

let undefined_unit () = ()

let undefined_int () = if !random then Z.of_int (Random.int 0xFFFF) else Z.zero

let undefined_nat () = Z.zero

let undefined_range lo _ = lo

let internal_pick list = if !random then List.nth list (Random.int (List.length list)) else List.nth list 0

let eq_int = Extraction.PrimInt.eq_int

let eq_bool = Extraction.PrimBits.eq_bool

let count_leading_zeros = Extraction.PrimBits.count_leading_zeros

let count_trailing_zeros = Extraction.PrimBits.count_trailing_zeros

let subrange = Extraction.PrimBits.subrange

let subrange_inc = Extraction.PrimBits.subrange_inc

let slice = Extraction.PrimBits.slice

let subrange_list = Extraction.PrimVector.subrange

let slice_list = Extraction.PrimVector.slice

let slice_list_inc = Extraction.PrimVector.slice_inc

let slice_inc = Extraction.PrimBits.slice_inc

let eq_list = Extraction.PrimBits.eq_bits

let access = Extraction.PrimBits.access

let access_inc = Extraction.PrimBits.access_inc

let access_list xs n = List.nth (List.rev xs) (Z.to_int n)

let access_list_inc xs n = List.nth xs (Z.to_int n)

let append = Extraction.PrimBits.append

let update bits n b = Extraction.PrimBits.set_slice bits n b

let update_inc bits n b =
  let w = Extraction.PrimBits.width bits in
  Extraction.PrimBits.set_slice bits (Z.sub (Z.pred w) n) b

let update_list = Extraction.PrimVector.update_list

let update_list_inc = Extraction.PrimVector.update_list_inc

let update_subrange = Extraction.PrimBits.update_subrange

let update_subrange_inc xs n m ys =
  let w = Extraction.PrimBits.width xs in
  Extraction.PrimBits.update_subrange xs (Z.sub (Z.pred w) n) (Z.sub (Z.pred w) m) ys

let vector_init = Extraction.PrimVector.vector_init

let vector_truncate = Extraction.PrimBits.vector_truncate

let vector_truncateLSB = Extraction.PrimBits.vector_truncateLSB

let length = Extraction.PrimVector.length

let length_bits = Extraction.PrimBits.width

let uint = Extraction.PrimBits.uint

let sint = Extraction.PrimBits.sint

let add_int = Extraction.PrimInt.add_int
let sub_int = Extraction.PrimInt.sub_int
let sub_nat = Extraction.PrimInt.sub_nat

let mult = Extraction.PrimInt.mult

(* This is euclidian division from lem *)
let quotient = Extraction.PrimInt.quotient

(* This is the same as tdiv_int, kept for compatibility with old preludes *)
let quot_round_zero = Extraction.PrimInt.tdiv_int

(* The corresponding remainder function for above just respects the sign of x *)
let rem_round_zero = Extraction.PrimInt.tmod_int

(* Lem provides euclidian modulo by default *)
let modulus = Extraction.PrimInt.modulus

let negate = Extraction.PrimInt.negate

let tdiv_int = Extraction.PrimInt.tdiv_int

let tmod_int = Extraction.PrimInt.tmod_int

let not_bits = Extraction.PrimBits.not_bits

let add_bits xs ys = require_width "add_bits" (Extraction.PrimBits.add_bits xs ys)

let replicate_bits = Extraction.PrimBits.replicate_bits

let get_slice_int = Extraction.PrimBits.get_slice_int

let to_bits = Extraction.PrimBits.to_bits

let add_bits_int = Extraction.PrimBits.add_bits_int

let sub_bits xs ys = require_width "sub_bits" (Extraction.PrimBits.sub_bits xs ys)

let sub_bits_int = Extraction.PrimBits.sub_bits_int

(* Bitvector literals in the AST are still lists of bits, so the two
   conversions are needed where a literal becomes a value, and where a
   value is rendered back into a literal. *)
let bits_of_bit_list = Extraction.PrimBits.of_bit_list
let bit_list_of_bits = Extraction.PrimBits.to_bit_list

let hex_digit_value c =
  match c with
  | '0' .. '9' -> Char.code c - Char.code '0'
  | 'a' .. 'f' -> Char.code c - Char.code 'a' + 10
  | 'A' .. 'F' -> Char.code c - Char.code 'A' + 10
  | _ -> raise (Runtime_type_error "Invalid hex character")

let bits_of_string str =
  let v = ref Z.zero in
  String.iter (fun c -> v := Z.add (Z.shift_left !v 4) (Z.of_int (hex_digit_value c))) str;
  Extraction.PrimBits.to_bits (Z.of_int (4 * String.length str)) !v

let hex_char c = bits_of_string (String.make 1 c)

let concat_str str1 str2 = str1 ^ str2

let bit_of_bool = Extraction.PrimBits.bit_of_bool

let string_of_bits bits =
  let w = Z.to_int (Extraction.PrimBits.width bits) in
  let v = Extraction.PrimBits.uint bits in
  let digit shift mask = Z.to_int (Z.logand (Z.shift_right v shift) (Z.of_int mask)) in
  let buf = Buffer.create (2 + w) in
  if w mod 4 = 0 then (
    Buffer.add_string buf "0x";
    for i = (w / 4) - 1 downto 0 do
      let d = digit (4 * i) 15 in
      Buffer.add_char buf (if d < 10 then Char.chr (d + Char.code '0') else Char.chr (d - 10 + Char.code 'A'))
    done
  )
  else (
    Buffer.add_string buf "0b";
    for i = w - 1 downto 0 do
      Buffer.add_char buf (if digit i 1 = 1 then '1' else '0')
    done
  );
  Buffer.contents buf

let decimal_string_of_bits bits = Z.to_string (Extraction.PrimBits.uint bits)

let hex_slice str n m =
  let v = Extraction.PrimBits.uint (bits_of_string (String.sub str 2 (String.length str - 2))) in
  Extraction.PrimBits.to_bits n (Z.shift_right v (Z.to_int m))

let putchar n =
  print_char (char_of_int (Z.to_int n));
  flush stdout

module Mem = struct
  include Map.Make (struct
    type t = Z.t
    let compare = Z.compare
  end)
end

let mem_pages = (ref Mem.empty : Bytes.t Mem.t ref)

let page_shift_bits = 20 (* 1M page *)
let page_size_bytes = 1 lsl page_shift_bits

let page_no_of_addr a = Z.shift_right a page_shift_bits
let bottom_addr_of_page p = Z.shift_left p page_shift_bits
let top_addr_of_page p = Z.shift_left (Z.succ p) page_shift_bits
let get_mem_page p =
  try Mem.find p !mem_pages
  with Not_found ->
    let new_page = Bytes.make page_size_bytes '\000' in
    mem_pages := Mem.add p new_page !mem_pages;
    new_page

let rec add_mem_bytes addr buf off len =
  let page_no = page_no_of_addr addr in
  let page_bot = bottom_addr_of_page page_no in
  let page_top = top_addr_of_page page_no in
  let page_off = Z.to_int (Z.sub addr page_bot) in
  let page = get_mem_page page_no in
  let bytes_left_in_page = Z.sub page_top addr in
  let to_copy = min (Z.to_int bytes_left_in_page) len in
  Bytes.blit buf off page page_off to_copy;
  if to_copy < len then add_mem_bytes page_top buf (off + to_copy) (len - to_copy)

let rec read_mem_bytes addr len =
  let page_no = page_no_of_addr addr in
  let page_bot = bottom_addr_of_page page_no in
  let page_top = top_addr_of_page page_no in
  let page_off = Z.to_int (Z.sub addr page_bot) in
  let page = get_mem_page page_no in
  let bytes_left_in_page = Z.sub page_top addr in
  let to_get = min (Z.to_int bytes_left_in_page) len in
  let bytes = Bytes.sub page page_off to_get in
  if to_get >= len then bytes else Bytes.cat bytes (read_mem_bytes page_top (len - to_get))

let write_ram' data_size addr data =
  let len = Z.to_int data_size in
  let bytes = Bytes.create len in
  let v = Extraction.PrimBits.uint data in
  for i = 0 to len - 1 do
    let byte = Z.to_int (Z.logand (Z.shift_right v (8 * i)) (Z.of_int 255)) in
    Bytes.set bytes i (char_of_int byte)
  done;
  add_mem_bytes addr bytes 0 len

let write_ram _addr_size data_size _hex_ram addr data =
  write_ram' data_size (uint addr) data;
  true

let write_ram_byte addr byte =
  let bytes = Bytes.make 1 (char_of_int byte) in
  add_mem_bytes addr bytes 0 1

let read_mem_bits data_size addr =
  let len = Z.to_int data_size in
  let bytes = read_mem_bytes addr len in
  let v = ref Z.zero in
  Bytes.iteri (fun i byte -> v := Z.logor !v (Z.shift_left (Z.of_int (int_of_char byte)) (8 * i))) bytes;
  Extraction.PrimBits.to_bits (Z.mul (Z.of_int 8) data_size) !v

let read_ram _addr_size data_size _hex_ram addr = read_mem_bits data_size (uint addr)

let fast_read_ram data_size addr = read_mem_bits data_size (uint addr)

let tag_ram = (ref Mem.empty : bool Mem.t ref)

let write_tag_bool addr tag =
  let addri = uint addr in
  tag_ram := Mem.add addri tag !tag_ram

let read_tag_bool addr =
  let addri = uint addr in
  try Mem.find addri !tag_ram with Not_found -> false

let shl_int = Extraction.PrimInt.shl_int
let shr_int = Extraction.PrimInt.shr_int

let eq_string str1 str2 = String.compare str1 str2 == 0

let string_startswith str1 str2 =
  String.length str1 >= String.length str2 && String.compare (String.sub str1 0 (String.length str2)) str2 == 0

let string_drop str n =
  if Z.leq (Z.of_int (String.length str)) n then ""
  else (
    let n = Z.to_int n in
    String.sub str n (String.length str - n)
  )

let string_take str n =
  let n = Z.to_int n in
  if String.length str <= n then str else String.sub str 0 n

let string_length str = Z.of_int (String.length str)

let string_append s1 s2 = s1 ^ s2

let set_slice _out_len _slice_len out n slice = Extraction.PrimBits.set_slice out n slice

let set_slice_int = Extraction.PrimBits.set_slice_int

let eq_real x y = Q.equal x y
let lt_real x y = Q.lt x y
let gt_real x y = Q.gt x y
let lteq_real x y = Q.leq x y
let gteq_real x y = Q.geq x y
let to_real x = Q.of_bigint x
let neg_real x = Q.neg x

let string_of_real x = Q.to_string x

let print_real str r = print_endline (str ^ string_of_real r)
let prerr_real str r = prerr_endline (str ^ string_of_real r)

let round_down x = Z.fdiv (Q.num x) (Q.den x)
let round_up x = Z.cdiv (Q.num x) (Q.den x)
let div_real x y = Q.div x y
let mult_real x y = Q.mul x y
let real_power x n =
  let e = Z.to_int (Z.abs n) in
  let r = Q.make (Z.pow (Q.num x) e) (Z.pow (Q.den x) e) in
  if Z.lt n Z.zero then Q.inv r else r
let int_power = Extraction.PrimInt.int_power
let add_real x y = Q.add x y
let sub_real x y = Q.sub x y

let abs_real x = Q.abs x

let sqrt_real x =
  let precision = 30 in
  let s = Q.div (Q.of_bigint (Z.sqrt (Q.num x))) (Q.of_bigint (Z.sqrt (Q.den x))) in
  if Q.equal (Q.mul s s) x then s
  else (
    let p = ref s in
    let n = ref (Q.of_int 0) in
    let num_convergence = if Q.gt x (Q.of_int 1) then Q.of_int 1 else x in
    let convergence = ref (Q.div num_convergence (Q.of_bigint (Z.pow (Z.of_int 10) precision))) in
    let quit_loop = ref false in
    while not !quit_loop do
      n := Q.div (Q.add !p (Q.div x !p)) (Q.of_int 2);

      if Q.lt (Q.abs (Q.sub !p !n)) !convergence then quit_loop := true else p := !n
    done;
    !n
  )

let random_real () = Q.div (Q.of_int (Random.bits ())) (Q.of_int (Random.bits ()))

let lt = Extraction.PrimInt.lt
let gt = Extraction.PrimInt.gt
let lteq = Extraction.PrimInt.lteq
let gteq = Extraction.PrimInt.gteq

let pow2 = Extraction.PrimInt.pow2

let max_int = Extraction.PrimInt.max_int
let min_int = Extraction.PrimInt.min_int
let abs_int = Extraction.PrimInt.abs_int

let string_of_int x = Z.to_string x

let undefined_real () = Q.of_int 0

let real_of_string str = Q.of_string str

let print str = Stdlib.print_string str

let prerr str = Stdlib.prerr_string str

let print_int str x = print_endline (str ^ Z.to_string x)

let prerr_int str x = prerr_endline (str ^ Z.to_string x)

let print_bits str xs = print_endline (str ^ string_of_bits xs)

let prerr_bits str xs = prerr_endline (str ^ string_of_bits xs)

let reg_deref r = !r

let string_of_zbitvector bits = "0b" ^ Util.string_of_list "" (function B0 -> "0" | B1 -> "1") (bit_list_of_bits bits)
let string_of_znat n = Z.to_string n
let string_of_zint n = Z.to_string n
let string_of_zimplicit n = Z.to_string n
let string_of_zunit () = "()"
let string_of_zbool = function true -> "true" | false -> "false"
let string_of_zreal _ = "REAL"
let string_of_zstring str = "\"" ^ String.escaped str ^ "\""

let rec string_of_list sep string_of = function
  | [] -> ""
  | [x] -> string_of x
  | x :: ls -> string_of x ^ sep ^ string_of_list sep string_of ls

let zero_extend = Extraction.PrimBits.zero_extend

let sign_extend = Extraction.PrimBits.sign_extend

let zeros = Extraction.PrimBits.zeros
let ones = Extraction.PrimBits.ones

let shiftr = Extraction.PrimBits.shiftr

let arith_shiftr = Extraction.PrimBits.arith_shiftr

let shift_bits_right = Extraction.PrimBits.shift_bits_right

let shiftl = Extraction.PrimBits.shiftl

let shift_bits_left = Extraction.PrimBits.shift_bits_left

(* Return nanoseconds since epoch. Truncates to ocaml int but will be OK for next 100 years or so... *)
let get_time_ns () = Z.of_int (int_of_float (1e9 *. Unix.gettimeofday ()))

let dec_str x = Z.to_string x

let to_lower_hex_char n = if 10 <= n && n <= 15 then Char.chr (n + 87) else Char.chr (n + 48)

let to_upper_hex_char n = if 10 <= n && n <= 15 then Char.chr (n + 55) else Char.chr (n + 48)

let hex_str_helper to_char x =
  let x, negative = if Z.lt x Z.zero then (Z.abs x, "-") else (x, "") in
  if Z.equal x Z.zero then "0x0"
  else (
    let x = ref x in
    let s = ref "" in
    while not (Z.equal !x Z.zero) do
      let lower_4 = Z.to_int (Z.logand !x (Z.of_int 15)) in
      s := String.make 1 (to_char lower_4) ^ !s;
      x := Z.shift_right !x 4
    done;
    negative ^ "0x" ^ !s
  )

let hex_str = hex_str_helper to_lower_hex_char
let hex_str_upper = hex_str_helper to_upper_hex_char

let is_hex_char ch =
  let c = Char.code ch in
  (Char.code '0' <= c && c <= Char.code '9')
  || (Char.code 'a' <= c && c <= Char.code 'f')
  || (Char.code 'A' <= c && c <= Char.code 'F')

let hex_char_width c =
  if c = '0' then 0
  else if c = '1' then 1
  else if c = '2' || c = '3' then 2
  else if c = '4' || c = '5' || c = '6' || c = '7' then 3
  else 4

let valid_hex_bits n s =
  let len = String.length s in
  (* We must have at least the 0x prefix, then one character *)
  if len < 3 || String.sub s 0 2 <> "0x" then false
  else (
    let hex = String.sub s 2 (len - 2) in
    let is_valid = ref true in
    let actual_len = ref 0 in
    let seen_non_zero = ref false in
    String.iter
      (fun c ->
        if !seen_non_zero then actual_len := !actual_len + 4
        else if c <> '0' then (
          actual_len := !actual_len + hex_char_width c;
          seen_non_zero := true
        );
        is_valid := !is_valid && is_hex_char c
      )
      hex;
    !actual_len <= Z.to_int n && !is_valid
  )

let parse_hex_bits n s =
  if not (valid_hex_bits n s) then zeros n
  else Extraction.PrimBits.to_bits n (Extraction.PrimBits.uint (bits_of_string (String.sub s 2 (String.length s - 2))))

let valid_dec_bits n s =
  if String.length s > 0 && s.[0] = '-' then false
  else (
    let is_valid = ref true in
    String.iter (fun c -> is_valid := !is_valid && '0' <= c && c <= '9') s;
    if not !is_valid then false
    else (
      let rec count_bits n = if Z.equal n Z.zero then 0 else 1 + count_bits (Z.shift_right n 1) in
      let dec_value = Z.of_string s in
      count_bits dec_value <= Z.to_int n
    )
  )

let parse_dec_bits n s = if not (valid_dec_bits n s) then zeros n else Extraction.PrimBits.to_bits n (Z.of_string s)

let sleep_request () = ()
let wakeup_request () = ()
let reset_registers () = ()

let load_raw paddr file =
  let i = ref 0 in
  let paddr = uint paddr in
  let in_chan = open_in file in
  try
    while true do
      let byte = input_char in_chan |> Char.code in
      write_ram_byte (Z.add paddr (Z.of_int !i)) byte;
      incr i
    done
  with End_of_file -> ()

(* TODO range, atom, register(?), int, nat, bool, real(!), list, string, itself(?) *)
let rand_zvector (g : 'generators) (size : int) (_order : bool) (elem_gen : 'generators -> 'a) : 'a list =
  Util.list_init size (fun _ -> elem_gen g)

let rand_zbit (_ : 'generators) : bit = bit_of_bool (Random.bool ())

let rand_zbitvector (g : 'generators) (size : int) : bit list = Util.list_init size (fun _ -> rand_zbit g)

let rand_zbool (_ : 'generators) : bool = Random.bool ()

let rand_zunit (_ : 'generators) : unit = ()

let rand_choice l =
  let n = List.length l in
  List.nth l (Random.int n)

let emulator_read_mem _addrsize addr len = fast_read_ram len addr

let emulator_read_mem_ifetch _addrsize addr len = fast_read_ram len addr

let emulator_read_mem_exclusive _addrsize addr len = fast_read_ram len addr

let emulator_write_mem _addrsize addr len value =
  write_ram' len (uint addr) value;
  true

let emulator_write_mem_exclusive _addrsize addr len value =
  write_ram' len (uint addr) value;
  true

let emulator_read_tag _addrsize addr = read_tag_bool addr

let emulator_write_tag _addrsize addr tag = write_tag_bool addr tag
