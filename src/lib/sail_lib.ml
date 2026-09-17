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

module Big_int = Nat_big_num

type bits = Extraction.Definitions.bvn

(* for ToFromInterp_lib_foo *)
module type BitType = sig
  type t
  val b0 : t
  val b1 : t
end

type 'a return = { return : 'b. 'a -> 'b }
type 'za zoption = ZNone of unit | ZSome of 'za

let zint_forwards i = string_of_int (Big_int.to_int i)

let opt_trace = ref false

let trace_depth = ref 0
let random = ref false

let opt_cycle_limit = ref 0
let cycle_count_var = ref 0

let get_cycle_count () = Big_int.of_int !cycle_count_var

let cycle_count () = incr cycle_count_var

let cycle_limit_reached () =
  incr cycle_count_var;
  (not (Int.equal !opt_cycle_limit 0)) && !cycle_count_var >= !opt_cycle_limit

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

let trace_call str =
  trace str;
  incr trace_depth

exception Runtime_type_error of string

let eq_anything a b = a = b

let eq_bit a b = a = b

let and_bit = Extraction.PrimBits.and_bit

let or_bit = Extraction.PrimBits.or_bit

let xor_bit = Extraction.PrimBits.xor_bit

let require_width name = function
  | Some r -> r
  | None -> raise (Runtime_type_error (name ^ ": bitvector width mismatch"))

let and_vec xs ys = require_width "and_vec" (Extraction.PrimBits.and_vec xs ys)

let and_bool = Extraction.PrimBits.and_bool

let or_vec xs ys = require_width "or_vec" (Extraction.PrimBits.or_vec xs ys)

let or_bool = Extraction.PrimBits.or_bool

let xor_vec xs ys = require_width "xor_vec" (Extraction.PrimBits.xor_vec xs ys)

let xor_bool = Extraction.PrimBits.xor_bool

let undefined_bit () = if !random then if Random.bool () then B0 else B1 else B0

let undefined_bool () = if !random then Random.bool () else false

let rec undefined_vector len item =
  if Big_int.equal len Big_int.zero then [] else item :: undefined_vector (Big_int.sub len (Big_int.of_int 1)) item

let undefined_list _ = []

let undefined_bitvector len = Extraction.PrimBits.zeros len

let undefined_string () = ""

let undefined_unit () = ()

let undefined_int () = if !random then Big_int.of_int (Random.int 0xFFFF) else Big_int.zero

let undefined_nat () = Big_int.zero

let undefined_range lo _ = lo

let internal_pick list = if !random then List.nth list (Random.int (List.length list)) else List.nth list 0

let eq_int = Extraction.PrimInt.eq_int

let eq_bool = Extraction.PrimBits.eq_bool

let rec drop n xs = match (n, xs) with 0, xs -> xs | _, [] -> [] | n, _ :: xs -> drop (n - 1) xs

let rec take n xs = match (n, xs) with 0, _ -> [] | n, x :: xs -> x :: take (n - 1) xs | _, [] -> []

let count_leading_zeros = Extraction.PrimBits.count_leading_zeros

let count_trailing_zeros = Extraction.PrimBits.count_trailing_zeros

let subrange = Extraction.PrimBits.subrange

let subrange_inc = Extraction.PrimBits.subrange_inc

let slice = Extraction.PrimBits.slice

let subrange_list = Extraction.PrimVector.subrange

let subrange_list_inc = Extraction.PrimVector.subrange_inc

let slice_list = Extraction.PrimVector.slice

let slice_list_inc = Extraction.PrimVector.slice_inc

let slice_inc = Extraction.PrimBits.slice_inc

let eq_list = Extraction.PrimBits.eq_bits

let access = Extraction.PrimBits.access

let access_inc = Extraction.PrimBits.access_inc

let access_list xs n = List.nth (List.rev xs) (Big_int.to_int n)

let access_list_inc xs n = List.nth xs (Big_int.to_int n)

let append = Extraction.PrimBits.append

let update bits n b = Extraction.PrimBits.set_slice bits n b

let update_inc bits n b =
  let w = Extraction.PrimBits.width bits in
  Extraction.PrimBits.set_slice bits (Big_int.sub (Big_int.pred w) n) b

let update_list = Extraction.PrimVector.update_list

let update_list_inc = Extraction.PrimVector.update_list_inc

let update_subrange = Extraction.PrimBits.update_subrange

let update_subrange_inc xs n m ys =
  let w = Extraction.PrimBits.width xs in
  Extraction.PrimBits.update_subrange xs (Big_int.sub (Big_int.pred w) n) (Big_int.sub (Big_int.pred w) m) ys

let vector_init = Extraction.PrimVector.vector_init

let vector_truncate = Extraction.PrimBits.vector_truncate

let vector_truncateLSB = Extraction.PrimBits.vector_truncateLSB

let length = Extraction.PrimVector.length

let length_bits = Extraction.PrimBits.width

let big_int_of_bit = Extraction.PrimBits.bigint_of_bit

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

let add_bit_with_carry = Extraction.PrimBits.add_bit_with_carry

let sub_bit_with_carry = Extraction.PrimBits.sub_bit_with_carry

let not_bit = Extraction.PrimBits.not_bit

let not_vec = Extraction.PrimBits.not_vec

let add_vec_carry xs ys = require_width "add_vec_carry" (Extraction.PrimBits.add_vec_carry xs ys)

let add_vec xs ys = require_width "add_vec" (Extraction.PrimBits.add_vec xs ys)

let replicate_bits = Extraction.PrimBits.replicate_bits

let identity x = x

let get_slice_int' n m o = Extraction.PrimBits.get_slice_int (Big_int.of_int n) m (Big_int.of_int o)

let get_slice_int = Extraction.PrimBits.get_slice_int

let to_bits' len n = Extraction.PrimBits.to_bits (Big_int.of_int len) n

let to_bits = Extraction.PrimBits.to_bits

(* unsigned multiplication producing a list of 2n bits *)
let mult_vec = Extraction.PrimBits.mult_vec

(* signed multiplication bit lists producing a list of 2n bits. *)
let mults_vec = Extraction.PrimBits.mults_vec

let add_vec_int = Extraction.PrimBits.add_vec_int

let sub_vec xs ys = require_width "sub_vec" (Extraction.PrimBits.sub_vec xs ys)

let sub_vec_int = Extraction.PrimBits.sub_vec_int

let bin_char = function '0' -> B0 | '1' -> B1 | _ -> raise (Runtime_type_error "Invalid binary character")

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
  let v = ref Big_int.zero in
  String.iter (fun c -> v := Big_int.add (Big_int.shift_left !v 4) (Big_int.of_int (hex_digit_value c))) str;
  Extraction.PrimBits.to_bits (Big_int.of_int (4 * String.length str)) !v

let hex_char c = bits_of_string (String.make 1 c)

let list_of_string s =
  let rec aux i acc = if i < 0 then acc else aux (i - 1) (s.[i] :: acc) in
  aux (String.length s - 1) []

let concat_str str1 str2 = str1 ^ str2

let rec break n = function [] -> [] | _ :: _ as xs -> [take n xs] @ break n (drop n xs)

let string_of_bit = Extraction.PrimBits.string_of_bit

let char_of_bit = Extraction.PrimBits.char_of_bit

let int_of_bit = function B0 -> 0 | B1 -> 1

let bool_of_bit = Extraction.PrimBits.bool_of_bit

let bit_of_bool = Extraction.PrimBits.bit_of_bool

let bigint_of_bit = Extraction.PrimBits.bigint_of_bit

let string_of_bits bits =
  let w = Big_int.to_int (Extraction.PrimBits.width bits) in
  let v = Extraction.PrimBits.uint bits in
  let digit shift mask = Big_int.to_int (Big_int.bitwise_and (Big_int.shift_right v shift) (Big_int.of_int mask)) in
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

let string_of_hex bits = string_of_bits bits

let decimal_string_of_bits bits = Big_int.to_string (Extraction.PrimBits.uint bits)

let hex_slice str n m =
  let v = Extraction.PrimBits.uint (bits_of_string (String.sub str 2 (String.length str - 2))) in
  Extraction.PrimBits.to_bits n (Big_int.shift_right v (Big_int.to_int m))

let putchar n =
  print_char (char_of_int (Big_int.to_int n));
  flush stdout

let bits_of_int bit n =
  let rec width b acc = if b = 0 then acc else width (b / 2) (acc + 1) in
  Extraction.PrimBits.to_bits (Big_int.of_int (width bit 0)) (Big_int.of_int n)

let bits_of_big_int pow n = Extraction.PrimBits.to_bits (Big_int.of_int pow) n

let byte_of_int n = Extraction.PrimBits.to_bits (Big_int.of_int 8) (Big_int.of_int n)

module Mem = struct
  include Map.Make (struct
    type t = Big_int.num
    let compare = Big_int.compare
  end)
end

let mem_pages = (ref Mem.empty : Bytes.t Mem.t ref)

let page_shift_bits = 20 (* 1M page *)
let page_size_bytes = 1 lsl page_shift_bits

let page_no_of_addr a = Big_int.shift_right a page_shift_bits
let bottom_addr_of_page p = Big_int.shift_left p page_shift_bits
let top_addr_of_page p = Big_int.shift_left (Big_int.succ p) page_shift_bits
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
  let page_off = Big_int.to_int (Big_int.sub addr page_bot) in
  let page = get_mem_page page_no in
  let bytes_left_in_page = Big_int.sub page_top addr in
  let to_copy = min (Big_int.to_int bytes_left_in_page) len in
  Bytes.blit buf off page page_off to_copy;
  if to_copy < len then add_mem_bytes page_top buf (off + to_copy) (len - to_copy)

let rec read_mem_bytes addr len =
  let page_no = page_no_of_addr addr in
  let page_bot = bottom_addr_of_page page_no in
  let page_top = top_addr_of_page page_no in
  let page_off = Big_int.to_int (Big_int.sub addr page_bot) in
  let page = get_mem_page page_no in
  let bytes_left_in_page = Big_int.sub page_top addr in
  let to_get = min (Big_int.to_int bytes_left_in_page) len in
  let bytes = Bytes.sub page page_off to_get in
  if to_get >= len then bytes else Bytes.cat bytes (read_mem_bytes page_top (len - to_get))

let write_ram' data_size addr data =
  let len = Big_int.to_int data_size in
  let bytes = Bytes.create len in
  let v = Extraction.PrimBits.uint data in
  for i = 0 to len - 1 do
    let byte = Big_int.to_int (Big_int.bitwise_and (Big_int.shift_right v (8 * i)) (Big_int.of_int 255)) in
    Bytes.set bytes i (char_of_int byte)
  done;
  add_mem_bytes addr bytes 0 len

let write_ram _addr_size data_size _hex_ram addr data =
  write_ram' data_size (uint addr) data;
  true

let wram addr byte =
  let bytes = Bytes.make 1 (char_of_int byte) in
  add_mem_bytes addr bytes 0 1

let read_mem_bits data_size addr =
  let len = Big_int.to_int data_size in
  let bytes = read_mem_bytes addr len in
  let v = ref Big_int.zero in
  Bytes.iteri
    (fun i byte -> v := Big_int.bitwise_or !v (Big_int.shift_left (Big_int.of_int (int_of_char byte)) (8 * i)))
    bytes;
  Extraction.PrimBits.to_bits (Big_int.mul (Big_int.of_int 8) data_size) !v

let read_ram _addr_size data_size _hex_ram addr = read_mem_bits data_size (uint addr)

let fast_read_ram data_size addr = read_mem_bits data_size (uint addr)

let tag_ram = (ref Mem.empty : bool Mem.t ref)

let write_tag_bool addr tag =
  let addri = uint addr in
  tag_ram := Mem.add addri tag !tag_ram

let read_tag_bool addr =
  let addri = uint addr in
  try Mem.find addri !tag_ram with Not_found -> false

let reverse_endianness = Extraction.PrimBits.reverse_endianness

let shl_int = Extraction.PrimInt.shl_int
let shr_int = Extraction.PrimInt.shr_int
let lor_int = Extraction.PrimInt.lor_int
let land_int = Extraction.PrimInt.land_int
let lxor_int = Extraction.PrimInt.lxor_int

let debug str1 n str2 v = prerr_endline (str1 ^ Big_int.to_string n ^ str2 ^ string_of_bits v)

let eq_string str1 str2 = String.compare str1 str2 == 0

let string_startswith str1 str2 =
  String.length str1 >= String.length str2 && String.compare (String.sub str1 0 (String.length str2)) str2 == 0

let string_drop str n =
  if Big_int.less_equal (Big_int.of_int (String.length str)) n then ""
  else (
    let n = Big_int.to_int n in
    String.sub str n (String.length str - n)
  )

let string_take str n =
  let n = Big_int.to_int n in
  if String.length str <= n then str else String.sub str 0 n

let string_length str = Big_int.of_int (String.length str)

let string_append s1 s2 = s1 ^ s2

let int_of_string_opt s = try Some (Big_int.of_string s) with Invalid_argument _ -> None

(* highly inefficient recursive implementation *)
let rec maybe_int_of_prefix = function
  | "" -> ZNone ()
  | str -> (
      let len = String.length str in
      match int_of_string_opt str with
      | Some n -> ZSome (n, Big_int.of_int len)
      | None -> maybe_int_of_prefix (String.sub str 0 (len - 1))
    )

let maybe_int_of_string str = match int_of_string_opt str with None -> ZNone () | Some n -> ZSome n

let lt_int = Extraction.PrimInt.lt

let set_slice _out_len _slice_len out n slice = Extraction.PrimBits.set_slice out n slice

let set_slice_int = Extraction.PrimBits.set_slice_int

let eq_real x y = Q.equal x y
let lt_real x y = Q.lt x y
let gt_real x y = Q.gt x y
let lteq_real x y = Q.leq x y
let gteq_real x y = Q.geq x y
let to_real x = Q.of_bigint x
let negate_real x = Q.neg x
let neg_real x = Q.neg x

let string_of_real x = Q.to_string x

let print_real str r = print_endline (str ^ string_of_real r)
let prerr_real str r = prerr_endline (str ^ string_of_real r)

let round_down x = Z.fdiv (Q.num x) (Q.den x)
let round_up x = Z.cdiv (Q.num x) (Q.den x)
let quotient_real x y = Q.div x y
let div_real x y = Q.div x y
let mult_real x y = Q.mul x y
let real_power _ _ = failwith "real_power"
let int_power = Extraction.PrimInt.int_power
let add_real x y = Q.add x y
let sub_real x y = Q.sub x y

let abs_real x = Q.abs x

let sqrt_real x =
  let precision = 30 in
  let s = Q.div (Q.of_bigint (Big_int.sqrt (Q.num x))) (Q.of_bigint (Big_int.sqrt (Q.den x))) in
  if Q.equal (Q.mul s s) x then s
  else (
    let p = ref s in
    let n = ref (Q.of_int 0) in
    let num_convergence = if Q.gt x (Q.of_int 1) then Q.of_int 1 else x in
    let convergence = ref (Q.div num_convergence (Q.of_bigint (Big_int.pow_int_positive 10 precision))) in
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

let string_of_int x = Big_int.to_string x

let undefined_real () = Q.of_int 0

let rec pow x = function 0 -> 1 | n -> x * pow x (n - 1)

let real_of_string str = Q.of_string str

let print str = Stdlib.print_string str

let prerr str = Stdlib.prerr_string str

let print_int str x = print_endline (str ^ Big_int.to_string x)

let prerr_int str x = prerr_endline (str ^ Big_int.to_string x)

let print_bits str xs = print_endline (str ^ string_of_bits xs)

let prerr_bits str xs = prerr_endline (str ^ string_of_bits xs)

let print_string str msg = print_endline (str ^ msg)

let prerr_string str msg = prerr_endline (str ^ msg)

let reg_deref r = !r

let string_of_zbitvector bits = "0b" ^ Util.string_of_list "" (function B0 -> "0" | B1 -> "1") (bit_list_of_bits bits)
let string_of_znat n = Big_int.to_string n
let string_of_zint n = Big_int.to_string n
let string_of_zimplicit n = Big_int.to_string n
let string_of_zunit () = "()"
let string_of_zbool = function true -> "true" | false -> "false"
let string_of_zreal _ = "REAL"
let string_of_zstring str = "\"" ^ String.escaped str ^ "\""

let rec string_of_list sep string_of = function
  | [] -> ""
  | [x] -> string_of x
  | x :: ls -> string_of x ^ sep ^ string_of_list sep string_of ls

let skip () = ()

let memea _ _ = ()

let zero_extend = Extraction.PrimBits.zero_extend

let sign_extend = Extraction.PrimBits.sign_extend

let zeros = Extraction.PrimBits.zeros
let ones = Extraction.PrimBits.ones

let shift_bits_right_arith = Extraction.PrimBits.shift_bits_right_arith

let shiftr = Extraction.PrimBits.shiftr

let arith_shiftr = Extraction.PrimBits.arith_shiftr

let shift_bits_right = Extraction.PrimBits.shift_bits_right

let shiftl = Extraction.PrimBits.shiftl

let shift_bits_left = Extraction.PrimBits.shift_bits_left

let speculate_conditional_success () = true

(* Return nanoseconds since epoch. Truncates to ocaml int but will be OK for next 100 years or so... *)
let get_time_ns () = Big_int.of_int (int_of_float (1e9 *. Unix.gettimeofday ()))

let string_of_bool = function true -> "true" | false -> "false"

let dec_str x = Big_int.to_string x

let to_lower_hex_char n = if 10 <= n && n <= 15 then Char.chr (n + 87) else Char.chr (n + 48)

let to_upper_hex_char n = if 10 <= n && n <= 15 then Char.chr (n + 55) else Char.chr (n + 48)

let hex_str_helper to_char x =
  let x, negative = if Big_int.less x Big_int.zero then (Big_int.abs x, "-") else (x, "") in
  if Big_int.equal x Big_int.zero then "0x0"
  else (
    let x = ref x in
    let s = ref "" in
    while not (Big_int.equal !x Big_int.zero) do
      let lower_4 = Big_int.to_int (Big_int.bitwise_and !x (Big_int.of_int 15)) in
      s := String.make 1 (to_char lower_4) ^ !s;
      x := Big_int.shift_right !x 4
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
    !actual_len <= Big_int.to_int n && !is_valid
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
      let rec count_bits n = if Big_int.equal n Big_int.zero then 0 else 1 + count_bits (Big_int.shift_right n 1) in
      let dec_value = Big_int.of_string s in
      count_bits dec_value <= Big_int.to_int n
    )
  )

let parse_dec_bits n s =
  if not (valid_dec_bits n s) then zeros n else Extraction.PrimBits.to_bits n (Big_int.of_string s)

let trace_memory_write _ _ _ = ()
let trace_memory_read _ _ _ = ()

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
      wram (Big_int.add paddr (Big_int.of_int !i)) byte;
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
