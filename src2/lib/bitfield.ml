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
(*  Redistribution and use in source and binary forms, with or without      *)
(*  modification, are permitted provided that the following conditions      *)
(*  are met:                                                                *)
(*  1. Redistributions of source code must retain the above copyright       *)
(*     notice, this list of conditions and the following disclaimer.        *)
(*  2. Redistributions in binary form must reproduce the above copyright    *)
(*     notice, this list of conditions and the following disclaimer in      *)
(*     the documentation and/or other materials provided with the           *)
(*     distribution.                                                        *)
(*                                                                          *)
(*  THIS SOFTWARE IS PROVIDED BY THE AUTHOR AND CONTRIBUTORS ``AS IS''      *)
(*  AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED       *)
(*  TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A         *)
(*  PARTICULAR PURPOSE ARE DISCLAIMED.  IN NO EVENT SHALL THE AUTHOR OR     *)
(*  CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,            *)
(*  SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT        *)
(*  LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF        *)
(*  USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND     *)
(*  ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,      *)
(*  OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT      *)
(*  OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF      *)
(*  SUCH DAMAGE.                                                            *)
(****************************************************************************)

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
  List.concat [defs_of_string __POS__ constructor_val; defs_of_string __POS__ constructor_fun]

(* For every index range, create a getter and setter *)
let index_range_getter name field order start stop =
  let size = if start > stop then start - (stop - 1) else stop - (start - 1) in
  let irg_val = Printf.sprintf "val _get_%s_%s : %s -> %s" name field name (bitvec size order) in
  let irg_function = Printf.sprintf "function _get_%s_%s v = v.bits[%i .. %i]" name field start stop in
  List.concat [defs_of_string __POS__ irg_val; defs_of_string __POS__ irg_function]

let index_range_setter name field order start stop =
  let size = if start > stop then start - (stop - 1) else stop - (start - 1) in
  let irs_val = Printf.sprintf "val _set_%s_%s : (register(%s), %s) -> unit" name field name (bitvec size order) in
  (* Read-modify-write using an internal _reg_deref function without rreg effect *)
  let irs_function = String.concat "\n"
    [ Printf.sprintf "function _set_%s_%s (r_ref, v) = {" name field;
                     "  r = __deref(r_ref);";
      Printf.sprintf "  r.bits = [r.bits with %i .. %i = v];" start stop;
                     "  (*r_ref) = r";
                     "}"
    ]
  in
  List.concat [defs_of_string __POS__ irs_val; defs_of_string __POS__ irs_function]

let index_range_update name field order start stop =
  let size = if start > stop then start - (stop - 1) else stop - (start - 1) in
  let iru_val = Printf.sprintf "val _update_%s_%s : (%s, %s) -> %s" name field name (bitvec size order) name in
  let iru_function =
    Printf.sprintf "function _update_%s_%s (v, x) = { v with bits = [ v.bits with %i .. %i = x] }"
      name field start stop
  in
  let iru_overload = Printf.sprintf "overload update_%s = {_update_%s_%s}" field name field in
  List.concat [defs_of_string __POS__ iru_val; defs_of_string __POS__ iru_function; defs_of_string __POS__ iru_overload]

let index_range_overload name field order =
  defs_of_string __POS__ (Printf.sprintf "overload _mod_%s = {_get_%s_%s, _set_%s_%s}" field name field name field)

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
