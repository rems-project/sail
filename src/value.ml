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

type value =
  | V_vector of value list
  | V_list of value list
  | V_int of Big_int.num
  | V_bool of bool
  | V_bit of Sail_lib.bit
  | V_tuple of value list
  | V_unit
  | V_string of string
  | V_ctor of string * value list
  | V_record of value StringMap.t

let coerce_bit = function
  | V_bit b -> b
  | _ -> assert false

let coerce_ctor = function
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

let unit_value = V_unit

let value_eq_int = function
  | [v1; v2] -> V_bool (Sail_lib.eq_int (coerce_int v1, coerce_int v2))
  | _ -> failwith "value eq_int"

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

let value_add = function
  | [v1; v2] -> V_int (Sail_lib.add (coerce_int v1, coerce_int v2))
  | _ -> failwith "value add"

let value_sub = function
  | [v1; v2] -> V_int (Sail_lib.sub (coerce_int v1, coerce_int v2))
  | _ -> failwith "value sub"

let value_replicate_bits = function
  | [v1; v2] -> mk_vector (Sail_lib.replicate_bits (coerce_bv v1, coerce_int v2))
  | _ -> failwith "value replicate_bits"

let rec string_of_value = function
  | V_vector vs -> Sail_lib.string_of_bits (List.map coerce_bit vs)
  | V_bool true -> "true"
  | V_bool false -> "false"
  | V_bit B0 -> "bitzero"
  | V_bit B1 -> "bitone"
  | V_int n -> Big_int.to_string n
  | V_tuple vals -> "(" ^ Util.string_of_list ", " string_of_value vals ^ ")"
  | V_list vals -> "[" ^ Util.string_of_list ", " string_of_value vals ^ "]"
  | V_unit -> "()"
  | V_string str -> "\"" ^ str ^ "\""
  | V_ctor (str, vals) -> str ^ "(" ^ Util.string_of_list ", " string_of_value vals ^ ")"
  | V_record record ->
     "{" ^ Util.string_of_list ", " (fun (field, v) -> field ^ "=" ^ string_of_value v) (StringMap.bindings record) ^ "}"

let eq_value v1 v2 = string_of_value v1 = string_of_value v2

let value_eq_anything = function
  | [v1; v2] -> V_bool (eq_value v1 v2)
  | _ -> failwith "value eq_anything"

let value_print = function
  | [v] -> print_endline (string_of_value v |> Util.red |> Util.clear); V_unit
  | _ -> assert false

let value_undefined_vector = function
  | [v1; v2; v3] -> V_vector (Sail_lib.undefined_vector (coerce_int v1, coerce_int v2, v3))
  | _ -> failwith "value undefined_vector"

let primops =
  List.fold_left
    (fun r (x, y) -> StringMap.add x y r)
    StringMap.empty
    [ ("and_bool", and_bool);
      ("or_bool", or_bool);
      ("print_endline", value_print);
      ("prerr_endline", value_print);
      ("string_of_bits", fun vs -> V_string (string_of_value (List.hd vs)));
      ("print_bits", fun [msg; bits] -> print_endline (coerce_string msg ^ string_of_value bits); V_unit);
      ("eq_int", value_eq_int);
      ("lteq", value_lteq);
      ("gteq", value_gteq);
      ("lt", value_lt);
      ("gt", value_gt);
      ("eq_list", value_eq_list);
      ("eq_string", value_eq_string);
      ("eq_anything", value_eq_anything);
      ("length", value_length);
      ("subrange", value_subrange);
      ("access", value_access);
      ("update", value_update);
      ("update_subrange", value_update_subrange);
      ("append", value_append);
      ("not", value_not);
      ("not_vec", value_not_vec);
      ("and_vec", value_and_vec);
      ("or_vec", value_or_vec);
      ("uint", value_uint);
      ("sint", value_sint);
      ("get_slice_int", value_get_slice_int);
      ("add", value_add);
      ("sub", value_sub);
      ("undefined_bit", fun _ -> V_bit Sail_lib.B0);
      ("undefined_vector", value_undefined_vector);
      ("replicate_bits", value_replicate_bits);
      ("Elf_loader.elf_entry", fun _ -> V_int (Big_int.of_int 0));
    ]
