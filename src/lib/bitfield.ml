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

let constant_bitvector_typ size = bitvector_typ (nconstant size)
let fun_typschm arg_typs ret_typ = mk_typschm (mk_typquant []) (function_typ arg_typs ret_typ)

let index_of_nexp nexp =
  match int_of_nexp_opt (nexp_simp nexp) with
  | Some i -> i
  | None -> raise (Reporting.err_typ (nexp_loc nexp) "non-constant bitfield index")

let mk_num_exp i = mk_lit_exp (L_num i)
let mk_id_exp id = mk_exp (E_id id)
let mk_id_pat id = mk_pat (P_id id)

let rec indices_of_range = function
  | BF_aux (BF_single i, _) -> [(index_of_nexp i, index_of_nexp i)]
  | BF_aux (BF_range (i, j), _) -> [(index_of_nexp i, index_of_nexp j)]
  | BF_aux (BF_concat (l, r), _) -> indices_of_range l @ indices_of_range r

let slice_width (i, j) = Big_int.succ (Big_int.abs (Big_int.sub i j))
let range_width r = List.map slice_width (indices_of_range r) |> List.fold_left Big_int.add Big_int.zero

(* Generate a constructor function for a bitfield type *)
let constructor name size =
  let typschm = fun_typschm [constant_bitvector_typ size] (mk_id_typ name) in
  let constructor_val = mk_val_spec (VS_val_spec (typschm, prepend_id "Mk_" name, None)) in
  let constructor_fun = Printf.sprintf "function Mk_%s v = struct { bits = v }" (string_of_id name) in
  constructor_val :: defs_of_string __POS__ constructor_fun

(* Helper functions to generate different kinds of field accessor exps and lexps *)
let get_field_exp range inner_exp =
  let mk_slice (i, j) = mk_exp (E_vector_subrange (inner_exp, mk_num_exp i, mk_num_exp j)) in
  let rec aux = function
    | [e] -> e
    | e :: es -> mk_exp (E_vector_append (e, aux es))
    | [] -> assert false (* unreachable *)
  in
  aux (List.map mk_slice (indices_of_range range))

let construct_bitfield_struct _ exp = mk_exp (E_struct [mk_fexp (mk_id "bits") exp])

let construct_bitfield_exp name exp = mk_exp (E_app (prepend_id "Mk_" name, [exp]))

let set_field_lexp range inner_lexp =
  let mk_slice (i, j) = mk_lexp (LE_vector_range (inner_lexp, mk_num_exp i, mk_num_exp j)) in
  match List.map mk_slice (indices_of_range range) with [e] -> e | es -> mk_lexp (LE_vector_concat es)

let set_bits_field_lexp inner_lexp = mk_lexp (LE_field (inner_lexp, mk_id "bits"))

let get_bits_field exp = mk_exp (E_field (exp, mk_id "bits"))

let set_bits_field exp value = mk_exp (E_struct_update (exp, [mk_fexp (mk_id "bits") value]))

let update_field_exp range order inner_exp new_value =
  let single = List.length (indices_of_range range) == 1 in
  let rec aux e vi = function
    | (i, j) :: is ->
        let w = slice_width (i, j) in
        let vi' = if is_order_inc order then Big_int.add vi w else Big_int.sub vi w in
        let rhs =
          if single then new_value
          else begin
            let vj = if is_order_inc order then Big_int.pred vi' else Big_int.succ vi' in
            mk_exp (E_vector_subrange (new_value, mk_num_exp vi, mk_num_exp vj))
          end
        in
        let update = mk_exp (E_vector_update_subrange (e, mk_num_exp i, mk_num_exp j, rhs)) in
        aux update vi' is
    | [] -> e
  in
  let vi = if is_order_inc order then Big_int.zero else Big_int.pred (range_width range) in
  aux inner_exp vi (indices_of_range range)

(* For every field, create getter and setter functions *)
type field_accessor_ids = { get : id; set : id; update : id; overload : id }

let field_accessor_ids type_name field =
  let type_name = string_of_id type_name in
  let field = string_of_id field in
  {
    get = mk_id (Printf.sprintf "_get_%s_%s" type_name field);
    set = mk_id (Printf.sprintf "_set_%s_%s" type_name field);
    update = mk_id (Printf.sprintf "_update_%s_%s" type_name field);
    overload = mk_id (Printf.sprintf "_mod_%s" field);
  }

let field_getter typ_name field order range =
  let size = range_width range in
  let typschm = fun_typschm [mk_id_typ typ_name] (constant_bitvector_typ size) in
  let fun_id = (field_accessor_ids typ_name field).get in
  let spec = mk_val_spec (VS_val_spec (typschm, fun_id, None)) in
  let body = get_field_exp range (get_bits_field (mk_exp (E_id (mk_id "v")))) in
  let funcl = mk_funcl fun_id (mk_pat (P_id (mk_id "v"))) body in
  [spec; mk_fundef [funcl]]

let field_updater typ_name field order range =
  let size = range_width range in
  let typ = mk_id_typ typ_name in
  let typschm = fun_typschm [typ; constant_bitvector_typ size] typ in
  let fun_id = (field_accessor_ids typ_name field).update in
  let spec = mk_val_spec (VS_val_spec (typschm, fun_id, None)) in
  let orig_var = mk_id "v" in
  let new_val_var = mk_id "x" in
  let bits_exp = get_bits_field (mk_id_exp orig_var) in
  let new_bits = update_field_exp range order bits_exp (mk_id_exp new_val_var) in
  let body = set_bits_field (mk_id_exp orig_var) new_bits in
  let funcl = mk_funcl fun_id (mk_pat (P_tuple [mk_id_pat orig_var; mk_id_pat new_val_var])) body in
  let overload =
    defs_of_string __POS__ (Printf.sprintf "overload update_%s = {%s}" (string_of_id field) (string_of_id fun_id))
  in
  [spec; mk_fundef [funcl]] @ overload

let register_field_setter typ_name field order range =
  let size = range_width range in
  let fun_id = string_of_id (field_accessor_ids typ_name field).set in
  let update_fun_id = string_of_id (field_accessor_ids typ_name field).update in
  let typ_name = string_of_id typ_name in
  let field_typ = string_of_typ (constant_bitvector_typ size) in
  let rfs_val = Printf.sprintf "val %s : (register(%s), %s) -> unit" fun_id typ_name field_typ in
  (* Read-modify-write using an internal _reg_deref function without rreg effect *)
  let rfs_function =
    String.concat "\n"
      [
        Printf.sprintf "function %s (r_ref, v) = {" fun_id;
        "  r = __deref(r_ref);";
        Printf.sprintf "  (*r_ref) = %s(r, v)" update_fun_id;
        "}";
      ]
  in
  List.concat [defs_of_string __POS__ rfs_val; defs_of_string __POS__ rfs_function]

let field_overload name field =
  let fun_id = string_of_id (field_accessor_ids name field).overload in
  let get_id = string_of_id (field_accessor_ids name field).get in
  let set_id = string_of_id (field_accessor_ids name field).set in
  defs_of_string __POS__ (Printf.sprintf "overload %s = {%s, %s}" fun_id get_id set_id)

let field_accessors typ_name field order range =
  List.concat
    [
      field_getter typ_name field order range;
      field_updater typ_name field order range;
      register_field_setter typ_name field order range;
      field_overload typ_name field;
    ]

(* Generate all accessor functions for a given bitfield type *)
let macro id size order ranges =
  let full_range = BF_aux (BF_range (nconstant (Big_int.pred size), nconstant Big_int.zero), Parse_ast.Unknown) in
  let ranges = (mk_id "bits", full_range) :: Bindings.bindings ranges in
  let accessors = List.map (fun (field, range) -> field_accessors id field order range) ranges in
  List.concat ([constructor id size] @ accessors)
