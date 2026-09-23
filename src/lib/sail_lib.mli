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
module type BitType = sig
  type t
  val b0 : t
  val b1 : t
end
type 'a return = { return : 'b. 'a -> 'b }
type 'za zoption = ZNone of unit | ZSome of 'za
val zint_forwards : Big_int.num -> string
val opt_trace : bool ref
val trace_depth : int ref
val random : bool ref
val opt_cycle_limit : int ref
val cycle_count_var : int ref
val get_cycle_count : unit -> Big_int.num
val cycle_count : unit -> unit
val cycle_limit_reached : unit -> bool
val sail_call : ('t return -> 't) -> 't
val trace : string -> unit
val trace_write : string -> string -> unit
val trace_read : string -> string -> unit
val sail_trace_call : string -> string -> ('t -> string) -> ('t return -> 't) -> 't
val trace_call : string -> unit
val eq_anything : 'a -> 'a -> bool
val require_width : string -> 'a option -> 'a
val and_vec : bits -> bits -> bits
val and_bool : bool -> bool -> bool
val or_vec : bits -> bits -> bits
val or_bool : bool -> bool -> bool
val xor_vec : bits -> bits -> bits
val xor_bool : bool -> bool -> bool
val undefined_bit : unit -> bit
val undefined_bool : unit -> bool
val undefined_vector : Big_int.num -> 'a -> 'a list
val undefined_list : 'a -> 'b list
val undefined_bitvector : Big_int_Z.big_int -> bits
val undefined_string : unit -> string
val undefined_unit : unit -> unit
val undefined_int : unit -> Big_int.num
val undefined_nat : unit -> Big_int.num
val undefined_range : 'a -> 'b -> 'a
val internal_pick : 'a list -> 'a
val eq_int : Big_int_Z.big_int -> Big_int_Z.big_int -> bool
val eq_bool : bool -> bool -> bool
val drop : int -> 'a list -> 'a list
val take : int -> 'a list -> 'a list
val count_leading_zeros : bits -> Big_int_Z.big_int
val count_trailing_zeros : bits -> Big_int_Z.big_int
val subrange : bits -> Big_int_Z.big_int -> Big_int_Z.big_int -> bits
val subrange_inc : bits -> Big_int_Z.big_int -> Big_int_Z.big_int -> bits
val slice : bits -> Big_int_Z.big_int -> Big_int_Z.big_int -> bits
val subrange_list : 'a list -> Big_int_Z.big_int -> Big_int_Z.big_int -> 'a list
val subrange_list_inc : 'a list -> Big_int_Z.big_int -> Big_int_Z.big_int -> 'a list
val slice_list : 'a list -> Big_int_Z.big_int -> Big_int_Z.big_int -> 'a list
val slice_list_inc : 'a list -> Big_int_Z.big_int -> Big_int_Z.big_int -> 'a list
val slice_inc : bits -> Big_int_Z.big_int -> Big_int_Z.big_int -> bits
val eq_list : bits -> bits -> bool
val access : bits -> Big_int_Z.big_int -> bits
val access_inc : bits -> Big_int_Z.big_int -> bits
val access_list : 'a list -> Big_int.num -> 'a
val access_list_inc : 'a list -> Big_int.num -> 'a
val append : bits -> bits -> bits
val update : bits -> Big_int_Z.big_int -> bits -> bits
val update_inc : bits -> Big_int.num -> bits -> bits
val update_list : 'a list -> Big_int_Z.big_int -> 'a -> 'a list
val update_list_inc : 'a list -> Big_int_Z.big_int -> 'a -> 'a list
val update_subrange : bits -> Big_int_Z.big_int -> Big_int_Z.big_int -> bits -> bits
val update_subrange_inc : bits -> Big_int.num -> Big_int.num -> bits -> bits
val vector_init : Big_int_Z.big_int -> 'a -> 'a list
val vector_truncate : bits -> Big_int_Z.big_int -> bits
val vector_truncateLSB : bits -> Big_int_Z.big_int -> bits
val length : 'a list -> Big_int_Z.big_int
val length_bits : bits -> Big_int_Z.big_int
val big_int_of_bit : bit -> Big_int_Z.big_int
val uint : bits -> Big_int_Z.big_int
val sint : bits -> Big_int_Z.big_int
val add_int : Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int
val sub_int : Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int
val sub_nat : Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int
val mult : Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int
val quotient : Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int
val quot_round_zero : Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int
val rem_round_zero : Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int
val modulus : Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int
val negate : Big_int_Z.big_int -> Big_int_Z.big_int
val tdiv_int : Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int
val tmod_int : Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int
val add_bit_with_carry : bit -> bit -> bit -> bit * bit
val sub_bit_with_carry : bit -> bit -> bit -> bit * bit
val not_vec : bits -> bits
val add_vec_carry : bits -> bits -> bit * bits
val add_vec : bits -> bits -> bits
val replicate_bits : bits -> Big_int_Z.big_int -> bits
val identity : 'a -> 'a
val get_slice_int' : int -> Big_int_Z.big_int -> int -> bits
val get_slice_int : Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int -> bits
val to_bits' : int -> Big_int_Z.big_int -> bits
val to_bits : Big_int_Z.big_int -> Big_int_Z.big_int -> bits
val mult_vec : bits -> bits -> bits
val mults_vec : bits -> bits -> bits
val add_vec_int : bits -> Big_int_Z.big_int -> bits
val sub_vec : bits -> bits -> bits
val sub_vec_int : bits -> Big_int_Z.big_int -> bits
val bin_char : char -> bit
val bits_of_bit_list : bit list -> bits
val bit_list_of_bits : bits -> bit list
val hex_digit_value : char -> int
val bits_of_string : string -> bits
val hex_char : char -> bits
val list_of_string : string -> char list
val concat_str : string -> string -> string
val break : int -> 'a list -> 'a list list
val string_of_bit : bit -> string
val char_of_bit : bit -> char
val int_of_bit : bit -> int
val bool_of_bit : bit -> bool
val bit_of_bool : bool -> bit
val bigint_of_bit : bit -> Big_int_Z.big_int
val string_of_bits : bits -> string
val string_of_hex : bits -> string
val decimal_string_of_bits : bits -> string
val hex_slice : string -> Big_int_Z.big_int -> Big_int.num -> bits
val putchar : Big_int.num -> unit
val bits_of_int : int -> int -> bits
val bits_of_big_int : int -> Big_int_Z.big_int -> bits
val byte_of_int : int -> bits
module Mem : Map.S with type key = Big_int.num
val mem_pages : Bytes.t Mem.t ref
val page_shift_bits : int
val page_size_bytes : int
val page_no_of_addr : Big_int.num -> Big_int.num
val bottom_addr_of_page : Big_int.num -> Big_int.num
val top_addr_of_page : Big_int.num -> Big_int.num
val get_mem_page : Mem.key -> Bytes.t
val add_mem_bytes : Big_int.num -> bytes -> int -> int -> unit
val read_mem_bytes : Big_int.num -> int -> bytes
val write_ram' : Big_int.num -> Big_int.num -> bits -> unit
val write_ram : 'a -> Big_int.num -> 'b -> bits -> bits -> bool
val wram : Big_int.num -> int -> unit
val read_mem_bits : Big_int.num -> Big_int.num -> bits
val read_ram : 'a -> Big_int.num -> 'b -> bits -> bits
val fast_read_ram : Big_int.num -> bits -> bits
val tag_ram : bool Mem.t ref
val write_tag_bool : bits -> bool -> unit
val read_tag_bool : bits -> bool
val reverse_endianness : bits -> bits
val shl_int : Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int
val shr_int : Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int
val lor_int : Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int
val land_int : Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int
val lxor_int : Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int
val debug : string -> Big_int.num -> string -> bits -> unit
val eq_string : String.t -> String.t -> bool
val string_startswith : string -> String.t -> bool
val string_drop : string -> Big_int.num -> string
val string_take : string -> Big_int.num -> string
val string_length : string -> Big_int.num
val string_append : string -> string -> string
val int_of_string_opt : string -> Big_int.num option
val maybe_int_of_prefix : string -> (Big_int.num * Big_int.num) zoption
val maybe_int_of_string : string -> Big_int.num zoption
val lt_int : Big_int_Z.big_int -> Big_int_Z.big_int -> bool
val set_slice : 'a -> 'b -> bits -> Big_int_Z.big_int -> bits -> bits
val set_slice_int : Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int -> bits -> Big_int_Z.big_int
val eq_real : Q.t -> Q.t -> bool
val lt_real : Q.t -> Q.t -> bool
val gt_real : Q.t -> Q.t -> bool
val lteq_real : Q.t -> Q.t -> bool
val gteq_real : Q.t -> Q.t -> bool
val to_real : Z.t -> Q.t
val negate_real : Q.t -> Q.t
val neg_real : Q.t -> Q.t
val string_of_real : Q.t -> string
val print_real : string -> Q.t -> unit
val prerr_real : string -> Q.t -> unit
val round_down : Q.t -> Z.t
val round_up : Q.t -> Z.t
val quotient_real : Q.t -> Q.t -> Q.t
val div_real : Q.t -> Q.t -> Q.t
val mult_real : Q.t -> Q.t -> Q.t
val real_power : 'a -> 'b -> 'c
val int_power : Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int
val add_real : Q.t -> Q.t -> Q.t
val sub_real : Q.t -> Q.t -> Q.t
val abs_real : Q.t -> Q.t
val sqrt_real : Q.t -> Q.t
val random_real : unit -> Q.t
val lt : Big_int_Z.big_int -> Big_int_Z.big_int -> bool
val gt : Big_int_Z.big_int -> Big_int_Z.big_int -> bool
val lteq : Big_int_Z.big_int -> Big_int_Z.big_int -> bool
val gteq : Big_int_Z.big_int -> Big_int_Z.big_int -> bool
val pow2 : Big_int_Z.big_int -> Big_int_Z.big_int
val max_int : Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int
val min_int : Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int
val abs_int : Big_int_Z.big_int -> Big_int_Z.big_int
val string_of_int : Big_int.num -> string
val undefined_real : unit -> Q.t
val pow : int -> int -> int
val real_of_string : string -> Q.t
val print : string -> unit
val prerr : string -> unit
val print_int : string -> Big_int.num -> unit
val prerr_int : string -> Big_int.num -> unit
val print_bits : string -> bits -> unit
val prerr_bits : string -> bits -> unit
val print_string : string -> string -> unit
val prerr_string : string -> string -> unit
val reg_deref : 'a ref -> 'a
val string_of_zbitvector : bits -> string
val string_of_znat : Big_int.num -> string
val string_of_zint : Big_int.num -> string
val string_of_zimplicit : Big_int.num -> string
val string_of_zunit : unit -> string
val string_of_zbool : bool -> string
val string_of_zreal : 'a -> string
val string_of_zstring : string -> string
val string_of_list : string -> ('a -> string) -> 'a list -> string
val skip : unit -> unit
val memea : 'a -> 'b -> unit
val zero_extend : bits -> Big_int_Z.big_int -> bits
val sign_extend : bits -> Big_int_Z.big_int -> bits
val zeros : Big_int_Z.big_int -> bits
val ones : Big_int_Z.big_int -> bits
val shift_bits_right_arith : bits -> bits -> bits
val shiftr : bits -> Big_int_Z.big_int -> bits
val arith_shiftr : bits -> Big_int_Z.big_int -> bits
val shift_bits_right : bits -> bits -> bits
val shiftl : bits -> Big_int_Z.big_int -> bits
val shift_bits_left : bits -> bits -> bits
val speculate_conditional_success : unit -> bool
val get_time_ns : unit -> Big_int.num
val string_of_bool : bool -> string
val dec_str : Big_int.num -> string
val to_lower_hex_char : int -> char
val to_upper_hex_char : int -> char
val hex_str_helper : (int -> char) -> Big_int.num -> string
val hex_str : Big_int.num -> string
val hex_str_upper : Big_int.num -> string
val is_hex_char : char -> bool
val hex_char_width : char -> int
val valid_hex_bits : Big_int.num -> string -> bool
val parse_hex_bits : Big_int.num -> string -> bits
val valid_dec_bits : Big_int.num -> string -> bool
val parse_dec_bits : Big_int.num -> string -> bits
val trace_memory_write : 'a -> 'b -> 'c -> unit
val trace_memory_read : 'a -> 'b -> 'c -> unit
val sleep_request : unit -> unit
val wakeup_request : unit -> unit
val reset_registers : unit -> unit
val load_raw : bits -> string -> unit
val rand_zvector : 'generators -> int -> bool -> ('generators -> 'a) -> 'a list
val rand_zbit : 'generators -> bit
val rand_zbitvector : 'generators -> int -> bit list
val rand_zbool : 'generators -> bool
val rand_zunit : 'generators -> unit
val rand_choice : 'a list -> 'a
val emulator_read_mem : 'a -> bits -> Big_int.num -> bits
val emulator_read_mem_ifetch : 'a -> bits -> Big_int.num -> bits
val emulator_read_mem_exclusive : 'a -> bits -> Big_int.num -> bits
val emulator_write_mem : 'a -> bits -> Big_int.num -> bits -> bool
val emulator_write_mem_exclusive : 'a -> bits -> Big_int.num -> bits -> bool
val emulator_read_tag : 'a -> bits -> bool
val emulator_write_tag : 'a -> bits -> bool -> unit
