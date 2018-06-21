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
open Ast_util

let bitvec size order =
  Printf.sprintf "vector(%i, %s, bit)" size (string_of_order order)

let rec combine = function
  | [] -> Defs []
  | (Defs defs) :: ast ->
     let (Defs defs') = combine ast in
     Defs (defs @ defs')

let newtype name size order =
  let chunks_64 =
    Util.list_init (size / 64) (fun i -> Printf.sprintf "%s_chunk_%i : vector(64, %s, bit)" name i (string_of_order order))
  in
  let chunks =
    if size mod 64 = 0 then chunks_64 else
      let chunk_rem =
        Printf.sprintf "%s_chunk_%i : vector(%i, %s, bit)" name (List.length chunks_64) (size mod 64) (string_of_order order)
      in
      chunk_rem :: List.rev chunks_64
  in
  let nt = Printf.sprintf "struct %s = {\n  %s }" name (Util.string_of_list ",\n  " (fun x -> x) chunks) in
  ast_of_def_string order nt

let rec translate_indices hi lo =
  if hi / 64 = lo / 64 then
    [(hi / 64, hi mod 64, lo mod 64)]
  else
    (hi / 64, hi mod 64, 0) :: translate_indices (hi - (hi mod 64 + 1)) lo

let constructor name order start stop =
  let indices = translate_indices start stop in
  let size = if start > stop then start - (stop - 1) else stop - (start - 1) in
  let constructor_val = Printf.sprintf "val Mk_%s : %s -> %s" name (bitvec size order) name in
  let body (chunk, hi, lo) =
    Printf.sprintf "%s_chunk_%i = v[%i .. %i]"
                   name chunk ((hi + chunk * 64) - stop) ((lo + chunk * 64) - stop)
  in
  let constructor_function = String.concat "\n"
    [ Printf.sprintf "function Mk_%s v = struct {" name;
      Printf.sprintf "  %s" (Util.string_of_list ",\n  " body indices);
                     "}"
    ]
  in
  combine [ast_of_def_string order constructor_val; ast_of_def_string order constructor_function]

(* For every index range, create a getter and setter *)
let index_range_getter name field order start stop =
  let indices = translate_indices start stop in
  let size = if start > stop then start - (stop - 1) else stop - (start - 1) in
  let irg_val = Printf.sprintf "val _get_%s_%s : %s -> %s" name field name (bitvec size order) in
  let body (chunk, start, stop) =
    Printf.sprintf "v.%s_chunk_%i[%i .. %i]" name chunk start stop
  in
  let irg_function = Printf.sprintf "function _get_%s_%s v = %s" name field (Util.string_of_list " @ " body indices) in
  combine [ast_of_def_string order irg_val; ast_of_def_string order irg_function]

let index_range_setter name field order start stop =
  let indices = translate_indices start stop in
  let size = if start > stop then start - (stop - 1) else stop - (start - 1) in
  let irs_val = Printf.sprintf "val _set_%s_%s : (register(%s), %s) -> unit effect {wreg}" name field name (bitvec size order) in
  (* Read-modify-write using an internal _reg_deref function without rreg effect *)
  let body (chunk, hi, lo) =
    Printf.sprintf "r.%s_chunk_%i = [ r.%s_chunk_%i with %i .. %i = v[%i .. %i]]"
                   name chunk name chunk hi lo ((hi + chunk * 64) - stop) ((lo + chunk * 64) - stop)
  in
  let irs_function = String.concat "\n"
    [ Printf.sprintf "function _set_%s_%s (r_ref, v) = {" name field;
                     "  r = _reg_deref(r_ref);";
      Printf.sprintf "  %s;" (Util.string_of_list ";\n  " body indices);
                     "  (*r_ref) = r";
                     "}"
    ]
  in
  combine [ast_of_def_string order irs_val; ast_of_def_string order irs_function]

let index_range_update name field order start stop =
  let indices = translate_indices start stop in
  let size = if start > stop then start - (stop - 1) else stop - (start - 1) in
  let iru_val = Printf.sprintf "val _update_%s_%s : (%s, %s) -> %s" name field name (bitvec size order) name in
  (* Read-modify-write using an internal _reg_deref function without rreg effect *)
  let body (chunk, hi, lo) =
    Printf.sprintf "let v = { v with %s_chunk_%i = [ v.%s_chunk_%i with %i .. %i = x[%i .. %i]] }"
                   name chunk name chunk hi lo ((hi + chunk * 64) - stop) ((lo + chunk * 64) - stop)
  in
  let iru_function = String.concat "\n"
    [ Printf.sprintf "function _update_%s_%s (v, x) =" name field;
      Printf.sprintf "  %s in" (Util.string_of_list " in\n  " body indices);
                     "  v"
    ]
  in
  let iru_overload = Printf.sprintf "overload update_%s = {_update_%s_%s}" field name field in
  combine [ast_of_def_string order iru_val; ast_of_def_string order iru_function; ast_of_def_string order iru_overload]

let index_range_overload name field order =
  ast_of_def_string order (Printf.sprintf "overload _mod_%s = {_get_%s_%s, _set_%s_%s}" field name field name field)

let index_range_accessor name field order (BF_aux (bf_aux, l)) =
  let getter n m = index_range_getter name field order (Big_int.to_int n) (Big_int.to_int m) in
  let setter n m = index_range_setter name field order (Big_int.to_int n) (Big_int.to_int m) in
  let update n m = index_range_update name field order (Big_int.to_int n) (Big_int.to_int m) in
  let overload = index_range_overload name field order in
  match bf_aux with
  | BF_single n -> combine [getter n n; setter n n; update n n; overload]
  | BF_range (n, m) -> combine [getter n m; setter n m; update n m; overload]
  | BF_concat _ -> failwith "Unimplemented"

let field_accessor name order (id, ir) = index_range_accessor name (string_of_id id) order ir

let macro id size order ranges =
  let name = string_of_id id in
  let ranges = (mk_id "bits", BF_aux (BF_range (Big_int.of_int (size - 1), Big_int.of_int 0), Parse_ast.Unknown)) :: ranges in
  combine ([newtype name size order; constructor name order (size - 1) 0] @ List.map (field_accessor name order) ranges)
