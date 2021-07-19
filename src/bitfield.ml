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

open Initial_check
open Ast
open Ast_defs
open Ast_util

let bitvec size order =
  Printf.sprintf "bitvector(%i, %s)" size (string_of_order order)

let constructor name order start stop =
  let size = if start > stop then start - (stop - 1) else stop - (start - 1) in
  let constructor_val = Printf.sprintf "val Mk_%s : %s -> %s" name (bitvec size order) name in
  let constructor_fun = Printf.sprintf "function Mk_%s v = struct { bits = v }" name in
  List.concat [defs_of_string constructor_val; defs_of_string constructor_fun]

(* For every index range, create a getter and setter *)
let index_range_getter name field order start stop =
  let size = if start > stop then start - (stop - 1) else stop - (start - 1) in
  let irg_val = Printf.sprintf "val _get_%s_%s : %s -> %s" name field name (bitvec size order) in
  let body (chunk, start, stop) =
    Printf.sprintf "v.%s_chunk_%i[%i .. %i]" name chunk start stop
  in
  let irg_function = Printf.sprintf "function _get_%s_%s v = v.bits[%i .. %i]" name field start stop in
  List.concat [defs_of_string irg_val; defs_of_string irg_function]

let index_range_setter name field order start stop =
  let size = if start > stop then start - (stop - 1) else stop - (start - 1) in
  let irs_val = Printf.sprintf "val _set_%s_%s : (register(%s), %s) -> unit effect {wreg}" name field name (bitvec size order) in
  (* Read-modify-write using an internal _reg_deref function without rreg effect *)
  let irs_function = String.concat "\n"
    [ Printf.sprintf "function _set_%s_%s (r_ref, v) = {" name field;
                     "  r = __bitfield_deref(r_ref);";
      Printf.sprintf "  r.bits = [r.bits with %i .. %i = v];" start stop;
                     "  (*r_ref) = r";
                     "}"
    ]
  in
  List.concat [defs_of_string irs_val; defs_of_string irs_function]

let index_range_update name field order start stop =
  let size = if start > stop then start - (stop - 1) else stop - (start - 1) in
  let iru_val = Printf.sprintf "val _update_%s_%s : (%s, %s) -> %s" name field name (bitvec size order) name in
  let iru_function =
    Printf.sprintf "function _update_%s_%s (v, x) = { v with bits = [ v.bits with %i .. %i = x] }"
      name field start stop
  in
  let iru_overload = Printf.sprintf "overload update_%s = {_update_%s_%s}" field name field in
  List.concat [defs_of_string iru_val; defs_of_string iru_function; defs_of_string iru_overload]

let index_range_overload name field order =
  defs_of_string (Printf.sprintf "overload _mod_%s = {_get_%s_%s, _set_%s_%s}" field name field name field)

let index_range_accessor name field order (n, m) =
  let getter n m = index_range_getter name field order (Big_int.to_int n) (Big_int.to_int m) in
  let setter n m = index_range_setter name field order (Big_int.to_int n) (Big_int.to_int m) in
  let update n m = index_range_update name field order (Big_int.to_int n) (Big_int.to_int m) in
  let overload = index_range_overload name field order in
  List.concat [getter n m; setter n m; update n m; overload]

let field_accessor name order (id, ir) =
  index_range_accessor name (string_of_id id) order ir

let macro id size order ranges =
  let name = string_of_id id in
  let ranges = (mk_id "bits", (Big_int.of_int (size - 1), Big_int.of_int 0)) :: Bindings.bindings ranges in
  List.concat ([constructor name order (size - 1) 0]
               @ List.map (field_accessor name order) ranges)
