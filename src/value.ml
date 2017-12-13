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

type bit = B0 | B1

type value =
  | V_vector of value list
  | V_list of value list
  | V_int of Big_int.num
  | V_bool of bool
  | V_bit of bit
  | V_tuple of value list
  | V_unit
  | V_string of string
  | V_ctor of string * value list

let rec string_of_value = function
  | V_vector _ -> "VEC"
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

let eq_value v1 v2 = string_of_value v1 = string_of_value v2

let coerce_bit = function
  | V_bit b -> b
  | _ -> assert false

let coerce_ctor = function
  | V_ctor (str, vals) -> (str, vals)
  | _ -> assert false

let coerce_bool = function
  | V_bool b -> b
  | _ -> assert false

let and_bool = function
  | [v1; v2] -> V_bool (coerce_bool v1 && coerce_bool v2)
  | _ -> assert false

let or_bool = function
  | [v1; v2] -> V_bool (coerce_bool v1 || coerce_bool v2)
  | _ -> assert false

let print = function
  | [v] -> print_endline (string_of_value v |> Util.red |> Util.clear); V_unit
  | _ -> assert false

let tuple_value (vs : value list) : value = V_tuple vs

let coerce_tuple = function
  | V_tuple vs -> vs
  | _ -> assert false

let coerce_listlike = function
  | V_tuple vs -> vs
  | V_list vs -> vs
  | _ -> assert false

let coerce_cons = function
  | V_list (v :: vs) -> Some (v, vs)
  | V_list [] -> None
  | _ -> assert false

let unit_value = V_unit

module StringMap = Map.Make(String)

let primops =
  List.fold_left
    (fun r (x, y) -> StringMap.add x y r)
    StringMap.empty
    [ ("and_bool", and_bool);
      ("or_bool", or_bool);
      ("print_endline", print);
    ]
