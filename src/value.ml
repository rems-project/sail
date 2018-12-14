(**************************************************************************)
(*     Sail                                                               *)
(*                                                                        *)
(*  Copyright (c) 2013-2017                                               *)
(*    Kathyrn Gray                                                        *)
(*    Shaked Flur                                                         *)
(*    Stephen Kell                                                        *)
(*    Gabriel Kerneis                                                     *)
(*    Robert Norton-Wright                                                *)
(*    Christopher Pulte                                                   *)
(*    Peter Sewell                                                        *)
(*    Alasdair Armstrong                                                  *)
(*    Brian Campbell                                                      *)
(*    Thomas Bauereiss                                                    *)
(*    Anthony Fox                                                         *)
(*    Jon French                                                          *)
(*    Dominic Mulligan                                                    *)
(*    Stephen Kell                                                        *)
(*    Mark Wassell                                                        *)
(*                                                                        *)
(*  All rights reserved.                                                  *)
(*                                                                        *)
(*  This software was developed by the University of Cambridge Computer   *)
(*  Laboratory as part of the Rigorous Engineering of Mainstream Systems  *)
(*  (REMS) project, funded by EPSRC grant EP/K008528/1.                   *)
(*                                                                        *)
(*  Redistribution and use in source and binary forms, with or without    *)
(*  modification, are permitted provided that the following conditions    *)
(*  are met:                                                              *)
(*  1. Redistributions of source code must retain the above copyright     *)
(*     notice, this list of conditions and the following disclaimer.      *)
(*  2. Redistributions in binary form must reproduce the above copyright  *)
(*     notice, this list of conditions and the following disclaimer in    *)
(*     the documentation and/or other materials provided with the         *)
(*     distribution.                                                      *)
(*                                                                        *)
(*  THIS SOFTWARE IS PROVIDED BY THE AUTHOR AND CONTRIBUTORS ``AS IS''    *)
(*  AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED     *)
(*  TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A       *)
(*  PARTICULAR PURPOSE ARE DISCLAIMED.  IN NO EVENT SHALL THE AUTHOR OR   *)
(*  CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,          *)
(*  SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT      *)
(*  LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF      *)
(*  USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND   *)
(*  ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,    *)
(*  OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT    *)
(*  OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF    *)
(*  SUCH DAMAGE.                                                          *)
(**************************************************************************)

module Big_int = Nat_big_num

module StringMap = Map.Make(String)

let print_chan = ref stdout
let print_redirected = ref false

let output_redirect chan =
  print_chan := chan;
  print_redirected := true

let output_close () =
  if !print_redirected then
    close_out !print_chan
  else
    ()

let output str =
  output_string !print_chan str;
  flush !print_chan

let output_endline str =
  output_string !print_chan (str ^ "\n");
  flush !print_chan

type value =
  | V_vector of value list
  | V_list of value list
  | V_int of Big_int.num
  | V_real of Rational.t
  | V_bool of bool
  | V_bit of Sail_lib.bit
  | V_tuple of value list
  | V_unit
  | V_string of string
  | V_ref of string
  | V_ctor of string * value list
  | V_record of value StringMap.t
  (* When constant folding we disable reading registers, so a register
     read will return a V_attempted_read value. If we try to do
     anything with this value, we'll get an exception - but if all we
     do is return it then we can replace the expression we are folding
     with a direct register read. *)
  | V_attempted_read of string

let rec eq_value v1 v2 =
  match v1, v2 with
  | V_vector v1s, V_vector v2s when List.length v1s = List.length v2s -> List.for_all2 eq_value v1s v2s
  | V_list v1s, V_vector v2s when List.length v1s = List.length v2s -> List.for_all2 eq_value v1s v2s
  | V_int n, V_int m -> Big_int.equal n m
  | V_real n, V_real m -> Rational.equal n m
  | V_bool b1, V_bool b2 -> b1 = b2
  | V_bit b1, V_bit b2 -> b1 = b2
  | V_tuple v1s, V_tuple v2s when List.length v1s = List.length v2s -> List.for_all2 eq_value v1s v2s
  | V_unit, V_unit -> true
  | V_string str1, V_string str2 -> str1 = str2
  | V_ref str1, V_ref str2 -> str1 = str2
  | V_ctor (name1, fields1), V_ctor (name2, fields2) when List.length fields1 = List.length fields2 ->
     name1 = name2 && List.for_all2 eq_value fields1 fields2
  | V_record fields1, V_record fields2 ->
     StringMap.equal eq_value fields1 fields2
  | _, _ -> false

let coerce_bit = function
  | V_bit b -> b
  | _ -> assert false

let coerce_ctor = function
  | V_ctor (str, [V_tuple vals]) -> (str, vals)
  | V_ctor (str, vals) -> (str, vals)
  | _ -> assert false

let coerce_bool = function
  | V_bool b -> b
  | _ -> assert false

let coerce_record = function
  | V_record record -> record
  | _ -> assert false

let and_bool = function
  | [v1; v2] -> V_bool (coerce_bool v1 && coerce_bool v2)
  | _ -> assert false

let or_bool = function
  | [v1; v2] -> V_bool (coerce_bool v1 || coerce_bool v2)
  | _ -> assert false

let tuple_value (vs : value list) : value = V_tuple vs

let mk_vector (bits : Sail_lib.bit list) : value = V_vector (List.map (fun bit -> V_bit bit) bits)

let coerce_bit = function
  | V_bit b -> b
  | _ -> assert false

let coerce_tuple = function
  | V_tuple vs -> vs
  | _ -> assert false

let coerce_listlike = function
  | V_tuple vs -> vs
  | V_list vs -> vs
  | V_unit -> []
  | _ -> assert false

let coerce_int = function
  | V_int i -> i
  | _ -> assert false

let coerce_real = function
  | V_real r -> r
  | _ -> assert false

let coerce_cons = function
  | V_list (v :: vs) -> Some (v, vs)
  | V_list [] -> None
  | _ -> assert false

let coerce_gv = function
  | V_vector vs -> vs
  | _ -> assert false

let coerce_bv = function
  | V_vector vs -> List.map coerce_bit vs
  | _ -> assert false

let coerce_string = function
  | V_string str -> str
  | _ -> assert false

let coerce_ref = function
  | V_ref str -> str
  | _ -> assert false

let unit_value = V_unit

let value_eq_int = function
  | [v1; v2] -> V_bool (Sail_lib.eq_int (coerce_int v1, coerce_int v2))
  | _ -> failwith "value eq_int"

let value_eq_bool = function
  | [v1; v2] -> V_bool (Sail_lib.eq_bool (coerce_bool v1, coerce_bool v2))
  | _ -> failwith "value eq_bool"

let value_lteq = function
  | [v1; v2] -> V_bool (Sail_lib.lteq (coerce_int v1, coerce_int v2))
  | _ -> failwith "value lteq"

let value_gteq = function
  | [v1; v2] -> V_bool (Sail_lib.gteq (coerce_int v1, coerce_int v2))
  | _ -> failwith "value gteq"

let value_lt = function
  | [v1; v2] -> V_bool (Sail_lib.lt (coerce_int v1, coerce_int v2))
  | _ -> failwith "value lt"

let value_gt = function
  | [v1; v2] -> V_bool (Sail_lib.gt (coerce_int v1, coerce_int v2))
  | _ -> failwith "value gt"

let value_eq_list = function
  | [v1; v2] -> V_bool (Sail_lib.eq_list (coerce_bv v1, coerce_bv v2))
  | _ -> failwith "value eq_list"

let value_eq_string = function
  | [v1; v2] -> V_bool (Sail_lib.eq_string (coerce_string v1, coerce_string v2))
  | _ -> failwith "value eq_string"

let value_string_startswith = function
  | [v1; v2] -> V_bool (Sail_lib.string_startswith (coerce_string v1, coerce_string v2))
  | _ -> failwith "value string_startswith"

let value_string_drop = function
  | [v1; v2] -> V_string (Sail_lib.string_drop (coerce_string v1, coerce_int v2))
  | _ -> failwith "value string_drop"

let value_string_take = function
  | [v1; v2] -> V_string (Sail_lib.string_take (coerce_string v1, coerce_int v2))
  | _ -> failwith "value string_take"

let value_string_length = function
  | [v] -> V_int (coerce_string v |> Sail_lib.string_length)
  | _ -> failwith "value string_length"
let value_eq_bit = function
  | [v1; v2] -> V_bool (Sail_lib.eq_bit (coerce_bit v1, coerce_bit v2))
  | _ -> failwith "value eq_bit"

let value_length = function
  | [v] -> V_int (coerce_gv v |> List.length |> Big_int.of_int)
  | _ -> failwith "value length"

let value_subrange = function
  | [v1; v2; v3] -> mk_vector (Sail_lib.subrange (coerce_bv v1, coerce_int v2, coerce_int v3))
  | _ -> failwith "value subrange"

let value_access = function
  | [v1; v2] -> Sail_lib.access (coerce_gv v1, coerce_int v2)
  | _ -> failwith "value access"

let value_update = function
  | [v1; v2; v3] -> V_vector (Sail_lib.update (coerce_gv v1, coerce_int v2, v3))
  | _ -> failwith "value update"

let value_update_subrange = function
  | [v1; v2; v3; v4] -> mk_vector (Sail_lib.update_subrange (coerce_bv v1, coerce_int v2, coerce_int v3, coerce_bv v4))
  | _ -> failwith "value update_subrange"

let value_append = function
  | [v1; v2] -> V_vector (coerce_gv v1 @ coerce_gv v2)
  | _ -> failwith "value append"

let value_slice = function
  | [v1; v2; v3] -> V_vector (Sail_lib.slice (coerce_gv v1, coerce_int v2, coerce_int v3))
  | _ -> failwith "value slice"

let value_not = function
  | [v] -> V_bool (not (coerce_bool v))
  | _ -> failwith "value not"

let value_not_vec = function
  | [v] -> mk_vector (Sail_lib.not_vec (coerce_bv v))
  | _ -> failwith "value not_vec"

let value_and_vec = function
  | [v1; v2] -> mk_vector (Sail_lib.and_vec (coerce_bv v1, coerce_bv v2))
  | _ -> failwith "value not_vec"

let value_or_vec = function
  | [v1; v2] -> mk_vector (Sail_lib.or_vec (coerce_bv v1, coerce_bv v2))
  | _ -> failwith "value not_vec"

let value_uint = function
  | [v] -> V_int (Sail_lib.uint (coerce_bv v))
  | _ -> failwith "value uint"

let value_sint = function
  | [v] -> V_int (Sail_lib.sint (coerce_bv v))
  | _ -> failwith "value sint"

let value_get_slice_int = function
  | [v1; v2; v3] -> mk_vector (Sail_lib.get_slice_int (coerce_int v1, coerce_int v2, coerce_int v3))
  | _ -> failwith "value get_slice_int"

let value_set_slice_int = function
  | [v1; v2; v3; v4] ->
     V_int (Sail_lib.set_slice_int (coerce_int v1, coerce_int v2, coerce_int v3, coerce_bv v4))
  | _ -> failwith "value set_slice_int"

let value_set_slice = function
  | [v1; v2; v3; v4; v5] ->
     mk_vector (Sail_lib.set_slice (coerce_int v1, coerce_int v2, coerce_bv v3, coerce_int v4, coerce_bv v5))
  | _ -> failwith "value set_slice"

let value_hex_slice = function
  | [v1; v2; v3] ->
     mk_vector (Sail_lib.hex_slice (coerce_string v1, coerce_int v2, coerce_int v3))
  | _ -> failwith "value hex_slice"

let value_add_int = function
  | [v1; v2] -> V_int (Sail_lib.add_int (coerce_int v1, coerce_int v2))
  | _ -> failwith "value add"

let value_sub_int = function
  | [v1; v2] -> V_int (Sail_lib.sub_int (coerce_int v1, coerce_int v2))
  | _ -> failwith "value sub"

let value_negate = function
  | [v1] -> V_int (Sail_lib.negate (coerce_int v1))
  | _ -> failwith "value negate"

let value_mult = function
  | [v1; v2] -> V_int (Sail_lib.mult (coerce_int v1, coerce_int v2))
  | _ -> failwith "value mult"

let value_quotient = function
  | [v1; v2] -> V_int (Sail_lib.quotient (coerce_int v1, coerce_int v2))
  | _ -> failwith "value quotient"

let value_modulus = function
  | [v1; v2] -> V_int (Sail_lib.modulus (coerce_int v1, coerce_int v2))
  | _ -> failwith "value modulus"

let value_add_vec_int = function
  | [v1; v2] -> mk_vector (Sail_lib.add_vec_int (coerce_bv v1, coerce_int v2))
  | _ -> failwith "value add_vec_int"

let value_sub_vec_int = function
  | [v1; v2] -> mk_vector (Sail_lib.sub_vec_int (coerce_bv v1, coerce_int v2))
  | _ -> failwith "value add_vec_int"

let value_add_vec = function
  | [v1; v2] -> mk_vector (Sail_lib.add_vec (coerce_bv v1, coerce_bv v2))
  | _ -> failwith "value add_vec"

let value_sub_vec = function
  | [v1; v2] -> mk_vector (Sail_lib.sub_vec (coerce_bv v1, coerce_bv v2))
  | _ -> failwith "value sub_vec"

let value_shl_int = function
  | [v1; v2] -> V_int (Sail_lib.shl_int (coerce_int v1, coerce_int v2))
  | _ -> failwith "value shl_int"

let value_shr_int = function
  | [v1; v2] -> V_int (Sail_lib.shr_int (coerce_int v1, coerce_int v2))
  | _ -> failwith "value shr_int"

let value_max_int = function
  | [v1; v2] -> V_int (Sail_lib.max_int (coerce_int v1, coerce_int v2))
  | _ -> failwith "value max_int"

let value_min_int = function
  | [v1; v2] -> V_int (Sail_lib.min_int (coerce_int v1, coerce_int v2))
  | _ -> failwith "value min_int"

let value_replicate_bits = function
  | [v1; v2] -> mk_vector (Sail_lib.replicate_bits (coerce_bv v1, coerce_int v2))
  | _ -> failwith "value replicate_bits"

let is_bit = function
  | V_bit _ -> true
  | _ -> false

let is_ctor = function
  | V_ctor _ -> true
  | _ -> false

let rec string_of_value = function
  | V_vector vs when List.for_all is_bit vs -> Sail_lib.string_of_bits (List.map coerce_bit vs)
  | V_vector vs -> "[" ^ Util.string_of_list ", " string_of_value vs ^ "]"
  | V_bool true -> "true"
  | V_bool false -> "false"
  | V_bit Sail_lib.B0 -> "bitzero"
  | V_bit Sail_lib.B1 -> "bitone"
  | V_int n -> Big_int.to_string n
  | V_tuple vals -> "(" ^ Util.string_of_list ", " string_of_value vals ^ ")"
  | V_list vals -> "[|" ^ Util.string_of_list ", " string_of_value vals ^ "|]"
  | V_unit -> "()"
  | V_string str -> "\"" ^ str ^ "\""
  | V_ref str -> "ref " ^ str
  | V_real r -> Sail_lib.string_of_real r
  | V_ctor (str, vals) -> str ^ "(" ^ Util.string_of_list ", " string_of_value vals ^ ")"
  | V_record record ->
     "{" ^ Util.string_of_list ", " (fun (field, v) -> field ^ "=" ^ string_of_value v) (StringMap.bindings record) ^ "}"
  | V_attempted_read _ -> assert false

let value_sign_extend = function
  | [v1; v2] -> mk_vector (Sail_lib.sign_extend (coerce_bv v1, coerce_int v2))
  | _ -> failwith "value sign_extend"

let value_zero_extend = function
  | [v1; v2] -> mk_vector (Sail_lib.zero_extend (coerce_bv v1, coerce_int v2))
  | _ -> failwith "value zero_extend"

let value_zeros = function
  | [v] -> mk_vector (Sail_lib.zeros (coerce_int v))
  | _ -> failwith "value zeros"

let value_shiftl = function
  | [v1; v2] -> mk_vector (Sail_lib.shiftl (coerce_bv v1, coerce_int v2))
  | _ -> failwith "value shiftl"

let value_shiftr = function
  | [v1; v2] -> mk_vector (Sail_lib.shiftr (coerce_bv v1, coerce_int v2))
  | _ -> failwith "value shiftr"

let value_vector_truncate = function
  | [v1; v2] -> mk_vector (Sail_lib.vector_truncate (coerce_bv v1, coerce_int v2))
  | _ -> failwith "value vector_truncate"

let value_eq_anything = function
  | [v1; v2] -> V_bool (eq_value v1 v2)
  | _ -> failwith "value eq_anything"

let value_print = function
  | [V_string str] -> output str; V_unit
  | [v] -> output (string_of_value v |> Util.red |> Util.clear); V_unit
  | _ -> assert false

let value_print_endline = function
  | [V_string str] -> output_endline str; V_unit
  | [v] -> output_endline (string_of_value v |> Util.red |> Util.clear); V_unit
  | _ -> assert false

let value_internal_pick = function
  | [v1] -> List.hd (coerce_listlike v1);
  | _ -> failwith "value internal_pick"

let value_undefined_vector = function
  | [v1; v2] -> V_vector (Sail_lib.undefined_vector (coerce_int v1, v2))
  | _ -> failwith "value undefined_vector"

let value_read_ram = function
  | [v1; v2; v3; v4] -> mk_vector (Sail_lib.read_ram (coerce_int v1, coerce_int v2, coerce_bv v3, coerce_bv v4))
  | _ -> failwith "value read_ram"

let value_write_ram = function
  | [v1; v2; v3; v4; v5] ->
     let b = Sail_lib.write_ram (coerce_int v1, coerce_int v2, coerce_bv v3, coerce_bv v4, coerce_bv v5) in
     V_bool(b)
  | _ -> failwith "value write_ram"

let value_load_raw = function
  | [v1; v2] -> Sail_lib.load_raw (coerce_bv v1, coerce_string v2) ; V_unit
  | _ -> failwith "value load_raw"

let value_putchar = function
  | [v] ->
     output_char !print_chan (char_of_int (Big_int.to_int (coerce_int v)));
     flush !print_chan;
     V_unit
  | _ -> failwith "value putchar"

let value_print_bits = function
  | [msg; bits] -> output_endline (coerce_string msg ^ string_of_value bits); V_unit
  | _ -> failwith "value print_bits"

let value_print_int = function
  | [msg; n] -> output_endline (coerce_string msg ^ string_of_value n); V_unit
  | _ -> failwith "value print_int"

let value_print_string = function
  | [msg; str] -> output_endline (coerce_string msg ^ coerce_string str); V_unit
  | _ -> failwith "value print_string"

let value_prerr_bits = function
  | [msg; bits] -> prerr_endline (coerce_string msg ^ string_of_value bits); V_unit
  | _ -> failwith "value prerr_bits"

let value_prerr_int = function
  | [msg; n] -> prerr_endline (coerce_string msg ^ string_of_value n); V_unit
  | _ -> failwith "value prerr_int"

let value_prerr_string = function
  | [msg; str] -> output_endline (coerce_string msg ^ coerce_string str); V_unit
  | _ -> failwith "value print_string"

let value_concat_str = function
  | [v1; v2] -> V_string (Sail_lib.concat_str (coerce_string v1, coerce_string v2))
  | _ -> failwith "value concat_str"

let value_to_real = function
  | [v] -> V_real (Sail_lib.to_real (coerce_int v))
  | _ -> failwith "value to_real"

let value_print_real = function
  | [v1; v2] -> output_endline (coerce_string v1 ^ string_of_value v2); V_unit
  | _ -> failwith "value print_real"

let value_random_real = function
  | [_] -> V_real (Sail_lib.random_real ())
  | _ -> failwith "value random_real"

let value_sqrt_real = function
  | [v] -> V_real (Sail_lib.sqrt_real (coerce_real v))
  | _ -> failwith "value sqrt_real"

let value_quotient_real = function
  | [v1; v2] -> V_real (Sail_lib.quotient_real (coerce_real v1, coerce_real v2))
  | _ -> failwith "value quotient_real"

let value_round_up = function
  | [v] -> V_int (Sail_lib.round_up (coerce_real v))
  | _ -> failwith "value round_up"

let value_round_down = function
  | [v] -> V_int (Sail_lib.round_down (coerce_real v))
  | _ -> failwith "value round_down"

let value_add_real = function
  | [v1; v2] -> V_real (Sail_lib.add_real (coerce_real v1, coerce_real v2))
  | _ -> failwith "value add_real"

let value_sub_real = function
  | [v1; v2] -> V_real (Sail_lib.sub_real (coerce_real v1, coerce_real v2))
  | _ -> failwith "value sub_real"

let value_mult_real = function
  | [v1; v2] -> V_real (Sail_lib.mult_real (coerce_real v1, coerce_real v2))
  | _ -> failwith "value mult_real"

let value_div_real = function
  | [v1; v2] -> V_real (Sail_lib.div_real (coerce_real v1, coerce_real v2))
  | _ -> failwith "value div_real"

let value_abs_real = function
  | [v] -> V_real (Sail_lib.abs_real (coerce_real v))
  | _ -> failwith "value abs_real"

let value_eq_real = function
  | [v1; v2] -> V_bool (Sail_lib.eq_real (coerce_real v1, coerce_real v2))
  | _ -> failwith "value eq_real"

let value_lt_real = function
  | [v1; v2] -> V_bool (Sail_lib.lt_real (coerce_real v1, coerce_real v2))
  | _ -> failwith "value lt_real"

let value_gt_real = function
  | [v1; v2] -> V_bool (Sail_lib.gt_real (coerce_real v1, coerce_real v2))
  | _ -> failwith "value gt_real"

let value_lteq_real = function
  | [v1; v2] -> V_bool (Sail_lib.lteq_real (coerce_real v1, coerce_real v2))
  | _ -> failwith "value lteq_real"

let value_gteq_real = function
  | [v1; v2] -> V_bool (Sail_lib.gteq_real (coerce_real v1, coerce_real v2))
  | _ -> failwith "value gteq_real"

let value_string_append = function
  | [v1; v2] -> V_string (Sail_lib.string_append (coerce_string v1, coerce_string v2))
  | _ -> failwith "value string_append"

let primops =
  List.fold_left
    (fun r (x, y) -> StringMap.add x y r)
    StringMap.empty
    [ ("and_bool", and_bool);
      ("or_bool", or_bool);
      ("print", value_print);
      ("prerr", fun vs -> (prerr_string (string_of_value (List.hd vs)); V_unit));
      ("dec_str", fun _ -> V_string "X");
      ("print_endline", value_print_endline);
      ("prerr_endline", fun vs -> (prerr_endline (string_of_value (List.hd vs)); V_unit));
      ("putchar", value_putchar);
      ("string_of_int", fun vs -> V_string (string_of_value (List.hd vs)));
      ("string_of_bits", fun vs -> V_string (string_of_value (List.hd vs)));
      ("print_bits", value_print_bits);
      ("print_int", value_print_int);
      ("print_string", value_print_string);
      ("prerr_bits", value_print_bits);
      ("prerr_int", value_print_int);
      ("prerr_string", value_prerr_string);
      ("concat_str", value_concat_str);
      ("eq_int", value_eq_int);
      ("lteq", value_lteq);
      ("gteq", value_gteq);
      ("lt", value_lt);
      ("gt", value_gt);
      ("eq_list", value_eq_list);
      ("eq_bool", value_eq_bool);
      ("eq_string", value_eq_string);
      ("string_startswith", value_string_startswith);
      ("string_drop", value_string_drop);
      ("string_take", value_string_take);
      ("string_length", value_string_length);
      ("eq_bit", value_eq_bit);
      ("eq_anything", value_eq_anything);
      ("length", value_length);
      ("subrange", value_subrange);
      ("access", value_access);
      ("update", value_update);
      ("update_subrange", value_update_subrange);
      ("slice", value_slice);
      ("append", value_append);
      ("not", value_not);
      ("not_vec", value_not_vec);
      ("and_vec", value_and_vec);
      ("or_vec", value_or_vec);
      ("uint", value_uint);
      ("sint", value_sint);
      ("get_slice_int", value_get_slice_int);
      ("set_slice_int", value_set_slice_int);
      ("set_slice", value_set_slice);
      ("hex_slice", value_hex_slice);
      ("zero_extend", value_zero_extend);
      ("sign_extend", value_sign_extend);
      ("zeros", value_zeros);
      ("shiftr", value_shiftr);
      ("shiftl", value_shiftl);
      ("add_int", value_add_int);
      ("sub_int", value_sub_int);
      ("div_int", value_quotient);
      ("mult_int", value_mult);
      ("mult", value_mult);
      ("quotient", value_quotient);
      ("modulus", value_modulus);
      ("negate", value_negate);
      ("shr_int", value_shr_int);
      ("shl_int", value_shl_int);
      ("max_int", value_max_int);
      ("min_int", value_min_int);
      ("add_vec_int", value_add_vec_int);
      ("sub_vec_int", value_sub_vec_int);
      ("add_vec", value_add_vec);
      ("sub_vec", value_sub_vec);
      ("vector_truncate", value_vector_truncate);
      ("read_ram", value_read_ram);
      ("write_ram", value_write_ram);
      ("trace_memory_read", fun _ -> V_unit);
      ("trace_memory_write", fun _ -> V_unit);
      ("get_time_ns", fun _ -> V_int (Sail_lib.get_time_ns()));
      ("load_raw", value_load_raw);
      ("to_real", value_to_real);
      ("eq_real", value_eq_real);
      ("lt_real", value_lt_real);
      ("gt_real", value_gt_real);
      ("lteq_real", value_lteq_real);
      ("gteq_real", value_gteq_real);
      ("add_real", value_add_real);
      ("sub_real", value_sub_real);
      ("mult_real", value_mult_real);
      ("round_up", value_round_up);
      ("round_down", value_round_down);
      ("quotient_real", value_div_real);
      ("abs_real", value_abs_real);
      ("div_real", value_div_real);
      ("sqrt_real", value_sqrt_real);
      ("print_real", value_print_real);
      ("random_real", value_random_real);
      ("undefined_unit", fun _ -> V_unit);
      ("undefined_bit", fun _ -> V_bit Sail_lib.B0);
      ("undefined_int", fun _ -> V_int Big_int.zero);
      ("undefined_bool", fun _ -> V_bool false);
      ("undefined_vector", value_undefined_vector);
      ("undefined_string", fun _ -> V_string "");
      ("internal_pick", value_internal_pick);
      ("replicate_bits", value_replicate_bits);
      ("Elf_loader.elf_entry", fun _ -> V_int (!Elf_loader.opt_elf_entry));
      ("Elf_loader.elf_tohost", fun _ -> V_int (!Elf_loader.opt_elf_tohost));
      ("string_append", value_string_append);
      ("string_length", value_string_length);
      ("string_startswith", value_string_startswith);
      ("string_drop", value_string_drop);
    ]
