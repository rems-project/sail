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

open Libsail

open Printf
open Ast
open Value
open Value_type

module Big_int = Nat_big_num
module StringMap = Map.Make (String)

let json_of_string s =
  sprintf "\"%s\"" (String.escaped s)

let json_of_int i =
  sprintf "%d" i

let json_of_bool b =
  if b then "true" else "false"

let json_of_list json_of_elem lst =
  let elems = List.map json_of_elem lst in
  sprintf "[%s]" (String.concat "," elems)

let json_of_dict_items json_of_dict_key json_of_dict_value (key,value) = 
  sprintf "%s:%s" (json_of_dict_key key) (json_of_dict_value value)

let json_of_dict json_of_dict_key json_of_dict_value lst =
  let items = List.map (json_of_dict_items json_of_dict_key json_of_dict_value) lst in
  sprintf "{%s}" (String.concat "," items)

let json_of_big_int num =
  sprintf "%s" (Big_int.to_string num)

let json_of_option json_of_elem = function
  | None -> "null"
  | Some x -> json_of_elem x

let json_of_loop = function
  | While -> json_of_string "While"
  | Until -> json_of_string "Until"

let json_of_visibility = function
  | Public -> json_of_string "Public"
  | Private loc -> json_of_string "Private"

let rec json_of_value = function
  | V_vector values -> sprintf "{\"V_vector\":%s}" (json_of_list json_of_value values)
  | V_bit bit -> sprintf "{\"V_bit\":\"%s\"}" (Sail_lib.string_of_bit bit)
  | V_list values -> sprintf "{\"V_list\":%s}" (json_of_list json_of_value values)
  | V_int num -> sprintf "{\"V_int\":%s}" (json_of_big_int num)
  | V_real real -> sprintf "{\"V_real\":[%s,%s]}" (Big_int.to_string (Rational.num real)) (Big_int.to_string (Rational.den real))
  | V_bool b -> sprintf "{\"V_bool\":%s}" (json_of_bool b)
  | V_tuple values -> sprintf "{\"V_tuple\":%s}" (json_of_list json_of_value values)
  | V_unit -> "\"V_unit\""
  | V_string s -> sprintf "{\"V_string\":%s}" (json_of_string s)
  | V_ref s -> sprintf "{\"V_ref\":%s}" (json_of_string s)
  | V_member s -> sprintf "{\"V_member\":%s}" (json_of_string s)
  | V_ctor (s,values) -> sprintf "{\"V_ctor\":[%s,%s]}" (json_of_string s) (json_of_list json_of_value values)
  | V_record fields ->
      let elems = List.fold_left (fun acc (key, value) ->
        let elem = sprintf "\"%s\":%s" key (json_of_value value) in
        elem ::acc
      ) [] fields in
      sprintf "{\"V_record\":{%s}}" (String.concat "," (List.rev elems))
  | V_attempted_read s -> sprintf "{\"V_attempted_read\":%s}" (json_of_string s)

let json_of_extern (ext: extern) =
  let bindings_json = json_of_list (fun (k,v) -> sprintf "[%s,%s]" (json_of_string k) (json_of_string v)) ext.bindings in
  sprintf "{\"pure\":%s,\"bindings\":%s}" (json_of_bool ext.pure) bindings_json

let rec json_of_kid_aux = function
  | Var x -> sprintf "{\"Var\":%s}" (json_of_string x)

and json_of_kid = function
  | Kid_aux (kid_aux,_) -> (json_of_kid_aux kid_aux)

let rec json_of_kind_aux = function
  | K_type -> json_of_string "K_type"
  | K_int -> json_of_string "K_int"
  | K_bool -> json_of_string "K_bool"

and json_of_kind = function
  | K_aux (kind_aux,_) -> (json_of_kind_aux kind_aux)

let rec json_of_id_aux = function
  | Id x -> sprintf "{\"Id\":%s}" (json_of_string x)
  | Operator x -> sprintf "{\"Operator\":%s}" (json_of_string x)
  | And_bool -> sprintf "[\"And_Bool\"]"
  | Or_bool -> sprintf "[\"Or_Bool\"]"

and json_of_id = function
  | Id_aux (id_aux,_) -> (json_of_id_aux id_aux)

let rec json_of_kinded_id_aux = function
  | KOpt_kind (k,kid) -> sprintf "{\"KOpt_kind\":[%s,%s]}" (json_of_kind k) (json_of_kid kid)

and json_of_kinded_id = function
  | KOpt_aux (kinded_id_aux,_) -> (json_of_kinded_id_aux kinded_id_aux)

let rec hex_digit_to_char = function
  | Hex_0 -> '0'
  | Hex_1 -> '1'
  | Hex_2 -> '2'
  | Hex_3 -> '3'
  | Hex_4 -> '4'
  | Hex_5 -> '5'
  | Hex_6 -> '6'
  | Hex_7 -> '7'
  | Hex_8 -> '8'
  | Hex_9 -> '9'
  | Hex_A -> 'A'
  | Hex_B -> 'B'
  | Hex_C -> 'C'
  | Hex_D -> 'D'
  | Hex_E -> 'E'
  | Hex_F -> 'F'

and bin_digit_to_char = function
  | Bin_0 -> '0'
  | Bin_1 -> '1'

and string_of_hex_non_empty (Non_empty (h, t)) =
  let chars = hex_digit_to_char h :: List.map hex_digit_to_char t in
  String.of_seq (List.to_seq chars)

and string_of_hex_non_empty_list lst =
  lst
  |> List.map string_of_hex_non_empty
  |> String.concat ""

and string_of_bin_non_empty (Non_empty (h, t)) =
  let chars = bin_digit_to_char h :: List.map bin_digit_to_char t in
  String.of_seq (List.to_seq chars)

and string_of_bin_non_empty_list lst =
  lst
  |> List.map string_of_bin_non_empty
  |> String.concat ""

let rec json_of_lit_aux = function
  | L_unit -> json_of_string "L_unit"
  | L_zero -> json_of_string "L_zero"
  | L_one -> json_of_string "L_one"
  | L_true -> json_of_string "L_true"
  | L_false -> json_of_string "L_false"
  | L_num num -> sprintf "{\"L_num\":%s}" (json_of_big_int num)
  | L_hex hex_list -> sprintf "{\"L_hex\":%s}" (json_of_string (string_of_hex_non_empty_list hex_list))
  | L_bin bin_list -> sprintf "{\"L_bin\":%s}" (json_of_string (string_of_bin_non_empty_list bin_list))
  | L_string s -> sprintf "{\"L_string\":%s}" (json_of_string s)
  | L_undef -> json_of_string "L_undef"
  | L_real s -> sprintf "{\"L_real\":%s}" (json_of_string s)

and json_of_lit = function
  | L_aux (l_aux,_) -> (json_of_lit_aux l_aux)

let json_of_field_pat_wildcard = function
  | FP_wild (_) -> sprintf "{\"FP_wild\":[]}"
  | FP_no_wild -> "{\"FP_no_wild\":[]}"

let rec json_of_typ_pat_aux = function
  | TP_wild -> "{\"TP_wild\":[]}"
  | TP_var kid -> sprintf "{\"TP_var\":[%s]}" (json_of_kid kid)
  | TP_app (id,typ_pat_list) -> sprintf "{\"TP_app\":[%s,%s]}" (json_of_id id) (json_of_list json_of_typ_pat typ_pat_list)

and json_of_typ_pat = function
  | TP_aux (aux,_) -> (json_of_typ_pat_aux aux)

let rec json_of_typ_aux = function
    | Typ_internal_unknown -> "{\"Typ_internal_unknown\":[]}"
  | Typ_id id -> sprintf "{\"Typ_id\":[%s]}" (json_of_id id)
  | Typ_var kid -> sprintf "{\"Typ_var\":[%s]}" (json_of_kid kid)
  | Typ_fn (typ_list,typ) -> sprintf "{\"Typ_fn\":[%s,%s]}" (json_of_list json_of_typ typ_list) (json_of_typ typ)
  | Typ_bidir (typ1,typ2) -> sprintf "{\"Typ_bidir\":[%s,%s]}" (json_of_typ typ1) (json_of_typ typ2)
  | Typ_tuple typ_list -> sprintf "{\"Typ_tuple\":[%s]}" (json_of_list json_of_typ typ_list)
  | Typ_app (id,typ_arg_list) -> sprintf "{\"Typ_app\":[%s,%s]}" (json_of_id id) (json_of_list json_of_typ_arg typ_arg_list)
  | Typ_exist (kinded_id_list,n_constraint,typ) -> sprintf "{\"Typ_exist\":[%s,%s,%s]}" (json_of_list json_of_kinded_id kinded_id_list) (json_of_n_constraint n_constraint) (json_of_typ typ)

and json_of_typ = function
  | Typ_aux (typ_aux,_) -> (json_of_typ_aux typ_aux)

and json_of_typ_arg_aux = function
  | A_nexp nexp -> sprintf "{\"A_nexp\":[%s]}" (json_of_nexp nexp)
  | A_typ typ -> sprintf "{\"A_typ\":[%s]}" (json_of_typ typ)
  | A_bool n_constraint -> sprintf "{\"A_bool\":[%s]}" (json_of_n_constraint n_constraint)

and json_of_typ_arg = function
  | A_aux (typ_arg_aux,_) -> (json_of_typ_arg_aux typ_arg_aux)

and json_of_nexp_aux = function
  | Nexp_id id -> sprintf "{\"Nexp_id\":[%s]}" (json_of_id id)
  | Nexp_var kid -> sprintf "{\"Nexp_var\":[%s]}" (json_of_kid kid)
  | Nexp_constant num -> sprintf "{\"Nexp_constant\":[%s]}" (json_of_big_int num)
  | Nexp_app (id,nexp_list) -> sprintf "{\"Nexp_app\":[%s,%s]}" (json_of_id id) (json_of_list json_of_nexp nexp_list)
  | Nexp_if (n_constraint,nexp1,nexp2) -> sprintf "{\"Nexp_if\":[%s,%s,%s]}" (json_of_n_constraint n_constraint) (json_of_nexp nexp1) (json_of_nexp nexp2)
  | Nexp_times (nexp1,nexp2) -> sprintf "{\"Nexp_times\":[%s,%s]}" (json_of_nexp nexp1) (json_of_nexp nexp2)
  | Nexp_sum (nexp1,nexp2) -> sprintf "{\"Nexp_sum\":[%s,%s]}" (json_of_nexp nexp1) (json_of_nexp nexp2)
  | Nexp_minus (nexp1,nexp2) -> sprintf "{\"Nexp_minus\":[%s,%s]}" (json_of_nexp nexp1) (json_of_nexp nexp2)
  | Nexp_exp nexp -> sprintf "{\"Nexp_exp\":[%s]}" (json_of_nexp nexp)
  | Nexp_neg nexp -> sprintf "{\"Nexp_neg\":[%s]}" (json_of_nexp nexp)

and json_of_nexp = function
  | Nexp_aux (nexp_aux,_) -> (json_of_nexp_aux nexp_aux)

and json_of_n_constraint_aux = function
  | NC_equal (arg1,arg2) -> sprintf "{\"NC_equal\":[%s,%s]}" (json_of_typ_arg arg1) (json_of_typ_arg arg2)
  | NC_not_equal (arg1,arg2) -> sprintf "{\"NC_not_equal\":[%s,%s]}" (json_of_typ_arg arg1) (json_of_typ_arg arg2)
  | NC_ge (nexp1,nexp2) -> sprintf "{\"NC_ge\":[%s,%s]}" (json_of_nexp nexp1) (json_of_nexp nexp2)
  | NC_gt (nexp1,nexp2) -> sprintf "{\"NC_gt\":[%s,%s]}" (json_of_nexp nexp1) (json_of_nexp nexp2)
  | NC_le (nexp1,nexp2) -> sprintf "{\"NC_le\":[%s,%s]}" (json_of_nexp nexp1) (json_of_nexp nexp2)
  | NC_lt (nexp1,nexp2) -> sprintf "{\"NC_lt\":[%s,%s]}" (json_of_nexp nexp1) (json_of_nexp nexp2)
  | NC_set (nexp,num_list) -> sprintf "{\"NC_set\":[%s,%s]}" (json_of_nexp nexp) (json_of_list json_of_big_int num_list)
  | NC_and (n_constraint1,n_constraint2) -> sprintf "{\"NC_and\":[%s,%s]}" (json_of_n_constraint n_constraint1) (json_of_n_constraint n_constraint2)
  | NC_or (n_constraint1,n_constraint2) -> sprintf "{\"NC_or\":[%s,%s]}" (json_of_n_constraint n_constraint1) (json_of_n_constraint n_constraint2)
  | NC_app (id,typ_arg_list) -> sprintf "{\"NC_app\":[%s,%s]}" (json_of_id id) (json_of_list json_of_typ_arg typ_arg_list)
  | NC_id (id) -> sprintf "{\"NC_id\":[%s]}" (json_of_id id)
  | NC_var (kid) -> sprintf "{\"NC_var\":[%s]}" (json_of_kid kid)
  | NC_true -> json_of_string "NC_true"
  | NC_false -> json_of_string "NC_false"

and json_of_n_constraint = function
  | NC_aux (n_constraint_aux,_) -> (json_of_n_constraint_aux n_constraint_aux)

let rec json_of_order_aux = function
  | Ord_inc -> json_of_string "Ord_inc"
  | Ord_dec -> json_of_string "Ord_dec"

and json_of_order = function
  | Ord_aux (order_aux,_) -> (json_of_order_aux order_aux)

let rec json_of_struct (id,pat) =
  sprintf "[%s,%s]" (json_of_id id) (json_of_pat pat)

and json_of_pat_aux = function
  | P_lit lit -> sprintf "{\"P_lit\":[%s]}" (json_of_lit lit)
  | P_wild -> "{\"P_wild\":[]}"
  | P_or (pat1,pat2) -> sprintf "{\"P_or\":[%s,%s]}" (json_of_pat pat1) (json_of_pat pat2)
  | P_not (pat) -> sprintf "{\"P_not\":[%s]}" (json_of_pat pat)
  | P_as (pat,id) -> sprintf "{\"P_as\":[%s,%s]}" (json_of_pat pat) (json_of_id id)
  | P_typ (typ,pat) -> sprintf "{\"P_typ\":[%s,%s]}" (json_of_typ typ) (json_of_pat pat)
  | P_id id -> sprintf "{\"P_id\":[%s]}" (json_of_id id)
  | P_var (pat,typ_pat) -> sprintf "{\"P_var\":[%s,%s]}" (json_of_pat pat) (json_of_typ_pat typ_pat)
  | P_app (id,pats) -> sprintf "{\"P_app\":[%s,%s]}" (json_of_id id) (json_of_list json_of_pat pats)
  | P_vector pats -> sprintf "{\"P_vector\":[%s]}" (json_of_list json_of_pat pats)
  | P_vector_concat pats -> sprintf "{\"P_vector_concat\":[%s]}" (json_of_list json_of_pat pats)
  | P_vector_subrange (id,big_int1,big_int2) ->
      sprintf "{\"P_vector_subrange\":[%s,%s,%s]}" (json_of_id id) (json_of_big_int big_int1) (json_of_big_int big_int2)
  | P_tuple pats -> sprintf "{\"P_tuple\":[%s]}" (json_of_list json_of_pat pats)
  | P_list pats -> sprintf "{\"P_list\":[%s]}" (json_of_list json_of_pat pats)
  | P_cons (pat1,pat2) -> sprintf "{\"P_cons\":[%s,%s]}" (json_of_pat pat1) (json_of_pat pat2)
  | P_string_append pats -> sprintf "{\"P_string_append\":%s}" (json_of_list json_of_pat pats)
  | P_struct (_,struct_list,field_pat_wildcard) ->
      sprintf "{\"P_struct\":[%s,%s]}"
      (json_of_list json_of_struct struct_list)
      (json_of_field_pat_wildcard field_pat_wildcard)

and json_of_pat = function
  | P_aux (pat_aux,(_,_)) -> (json_of_pat_aux pat_aux)

let rec json_of_typquant_aux = function
  | TypQ_tq quant_items -> sprintf "{\"TypQ_tq\":[%s]}" (json_of_list json_of_quant_item quant_items)
  | TypQ_no_forall -> "{\"TypQ_no_forall\":[]}"

and json_of_typquant = function
  | TypQ_aux (typquant_aux,_) -> (json_of_typquant_aux typquant_aux)

and json_of_quant_item_aux = function
  | QI_id kinded_id -> sprintf "{\"QI_id\":[%s]}" (json_of_kinded_id kinded_id)
  | QI_constraint n_constraint -> sprintf "{\"QI_constraint\":[%s]}" (json_of_n_constraint n_constraint)

and json_of_quant_item = function
  | QI_aux (quant_item_aux,_) -> (json_of_quant_item_aux quant_item_aux)

let rec json_of_exp_aux = function
  | E_block exps -> sprintf "{\"E_block\":[%s]}" (json_of_list json_of_exp exps)
  | E_id id -> sprintf "{\"E_id\":[%s]}" (json_of_id id)
  | E_lit lit -> sprintf "{\"E_lit\":[%s]}" (json_of_lit lit)
  | E_typ (typ,exp) -> sprintf "{\"E_typ\":[%s,%s]}" (json_of_typ typ) (json_of_exp exp)
  | E_app (id,exps) -> sprintf "{\"E_app\":[%s,%s]}" (json_of_id id) (json_of_list json_of_exp exps)
  | E_tuple exps -> sprintf "{\"E_tuple\":[%s]}" (json_of_list json_of_exp exps)
  | E_if (cond,then_exp,else_exp) -> sprintf "{\"E_if\":[%s,%s,%s]}" (json_of_exp cond) (json_of_exp then_exp) (json_of_exp else_exp)
  | E_loop (loop,internal_loop_measure,cond,body) ->
      sprintf "{\"E_loop\":[%s,%s,%s,%s]}" (json_of_loop loop) (json_of_internal_loop_measure internal_loop_measure) (json_of_exp cond) (json_of_exp body)
  | E_for (id,exp1,exp2,exp3,order,body) -> sprintf "{\"E_for\":[%s,%s,%s,%s,%s,%s]}" (json_of_id id) (json_of_exp exp1) (json_of_exp exp2) (json_of_exp exp3) (json_of_order order) (json_of_exp body)
  | E_vector exps -> sprintf "{\"E_vector\":[%s]}" (json_of_list json_of_exp exps)
  | E_vector_append (exp1,exp2) -> sprintf "{\"E_vector_append\":[%s,%s]}" (json_of_exp exp1) (json_of_exp exp2)
  | E_list exps -> sprintf "{\"E_list\":[%s]}" (json_of_list json_of_exp exps)
  | E_cons (hd,tl) -> sprintf "{\"E_cons\":[%s,%s]}" (json_of_exp hd) (json_of_exp tl)
  | E_struct (_,fields) -> sprintf "{\"E_struct\":[%s]}" (json_of_list json_of_fexp fields)
  | E_struct_update (exp,fields) -> sprintf "{\"E_struct_update\":[%s,%s]}" (json_of_exp exp) (json_of_list json_of_fexp fields)
  | E_field (exp,field) -> sprintf "{\"E_field\":[%s,%s]}" (json_of_exp exp) (json_of_id field)
  | E_match (exp,cases) -> sprintf "{\"E_match\":[%s,%s]}" (json_of_exp exp) (json_of_list json_of_pexp cases)
  | E_let (letbind,exp) -> sprintf "{\"E_let\":[%s,%s]}" (json_of_letbind letbind) (json_of_exp exp)
  | E_assign (lexp,exp) -> sprintf "{\"E_assign\":[%s,%s]}" (json_of_lexp lexp) (json_of_exp exp)
  | E_sizeof nexp -> sprintf "{\"E_sizeof\":[%s]}" (json_of_nexp nexp)
  | E_return exp -> sprintf "{\"E_return\":[%s]}" (json_of_exp exp)
  | E_exit exp -> sprintf "{\"E_exit\":[%s]}" (json_of_exp exp)
  | E_config config -> sprintf "{\"E_config\":[%s]}" (json_of_list json_of_string config)
  | E_ref id -> sprintf "{\"E_ref\":[%s]}" (json_of_id id)
  | E_throw exp -> sprintf "{\"E_throw\":[%s]}" (json_of_exp exp)
  | E_try (exp,cases) -> sprintf "{\"E_try\":[%s,%s]}" (json_of_exp exp) (json_of_list json_of_pexp cases)
  | E_assert (exp1,exp2) -> sprintf "{\"E_assert\":[%s,%s]}" (json_of_exp exp1) (json_of_exp exp2)
  | E_var (lexp,exp1,exp2) -> sprintf "{\"E_var\":[%s,%s,%s]}" (json_of_lexp lexp) (json_of_exp exp1) (json_of_exp exp2)
  | E_internal_plet (pat,exp1,exp2) -> sprintf "{\"E_internal_plet\":[%s,%s,%s]}" (json_of_pat pat) (json_of_exp exp1) (json_of_exp exp2)
  | E_internal_return exp -> sprintf "{\"E_internal_return\":[%s]}" (json_of_exp exp)
  | E_internal_value value -> sprintf "{\"E_internal_value\":[%s]}" (json_of_value value)
  | E_internal_assume (n_constraint,exp) -> sprintf "{\"E_internal_value\":[%s,%s]}" (json_of_n_constraint n_constraint) (json_of_exp exp)
  | E_constraint n_constraint -> sprintf "{\"E_constraint\":[%s]}" (json_of_n_constraint n_constraint)

and json_of_exp = function
  | E_aux (exp_aux,(_,_)) -> (json_of_exp_aux exp_aux)

and json_of_lexp_aux = function
  | LE_id id -> sprintf "{\"LE_id\":[%s]}" (json_of_id id)
  | LE_deref exp -> sprintf "{\"LE_deref\":[%s]}" (json_of_exp exp)
  | LE_app (id,exps) -> sprintf "{\"LE_app\":[%s,%s]}" (json_of_id id) (json_of_list json_of_exp exps)
  | LE_typ (typ,id) -> sprintf "{\"LE_typ\":[%s,%s]}" (json_of_typ typ) (json_of_id id)
  | LE_tuple lexps -> sprintf "{\"LE_tuple\":[%s]}" (json_of_list json_of_lexp lexps)
  | LE_vector_concat lexps -> sprintf "{\"LE_vector_concat\":[%s]}" (json_of_list json_of_lexp lexps)
  | LE_vector (lexp,exp) -> sprintf "{\"LE_vector\":[%s,%s]}" (json_of_lexp lexp) (json_of_exp exp)
  | LE_vector_range (lexp,exp1,exp2) -> sprintf "{\"LE_vector_range\":[%s,%s,%s]}" (json_of_lexp lexp) (json_of_exp exp1) (json_of_exp exp2)
  | LE_field (lexp,id) -> sprintf "{\"LE_field\":[%s,%s]}" (json_of_lexp lexp) (json_of_id id)

and json_of_lexp = function
  | LE_aux (lexp,(_,_)) -> (json_of_lexp_aux lexp)

and json_of_fexp_aux = function
  | FE_fexp (id,exp) -> sprintf "{\"FE_fexp\":[%s,%s]}" (json_of_id id) (json_of_exp exp)

and json_of_fexp = function
  | FE_aux (fexp,(_,_)) -> (json_of_fexp_aux fexp)

and json_of_pexp_aux = function
  | Pat_exp (pat,exp) -> sprintf "{\"Pat_exp\":[%s,%s]}" (json_of_pat pat) (json_of_exp exp)
  | Pat_when (pat,exp1,exp2) -> sprintf "{\"Pat_when\":[%s,%s,%s]}" (json_of_pat pat) (json_of_exp exp1) (json_of_exp exp2)

and json_of_pexp = function
  | Pat_aux (pexp,(_,_)) -> (json_of_pexp_aux pexp)

and json_of_letbind_aux = function
  | LB_val (pat,exp) -> sprintf "{\"LB_val\":[%s,%s]}" (json_of_pat pat) (json_of_exp exp)

and json_of_letbind = function
  | LB_aux (letbind_aux,(_,_)) -> (json_of_letbind_aux letbind_aux)

and json_of_internal_loop_measure_aux = function
  | Measure_none -> "{\"Measure_none\":[]}"
  | Measure_some (exp) -> sprintf "{\"Measure_some\":[%s]}" (json_of_exp exp) 

and json_of_internal_loop_measure = function
  | Measure_aux (measure,_) -> (json_of_internal_loop_measure_aux measure)

let rec json_of_mpat_aux = function
  | MP_lit lit -> sprintf "{\"MP_lit\":[%s]}" (json_of_lit lit)
  | MP_id id -> sprintf "{\"MP_id\":[%s]}" (json_of_id id)
  | MP_app (id,mpats) -> sprintf "{\"MP_app\":[%s,%s]}" (json_of_id id) (json_of_list json_of_mpat mpats)
  | MP_vector mpats -> sprintf "{\"MP_vector\":[%s]}" (json_of_list json_of_mpat mpats)
  | MP_vector_concat mpats -> sprintf "{\"MP_vector_concat\":[%s]}" (json_of_list json_of_mpat mpats)
  | MP_vector_subrange (id,n1,n2) -> sprintf "{\"MP_vector_subrange\":[%s,%s,%s]}" (json_of_id id) (json_of_big_int n1) (json_of_big_int n2)
  | MP_tuple mpats -> sprintf "{\"MP_tuple\":[%s]}" (json_of_list json_of_mpat mpats)
  | MP_list mpats -> sprintf "{\"MP_list\":[%s]}" (json_of_list json_of_mpat mpats)
  | MP_cons (mpat1,mpat2) -> sprintf "{\"MP_cons\":[%s,%s]}" (json_of_mpat mpat1) (json_of_mpat mpat2)
  | MP_string_append mpats -> sprintf "{\"MP_string_append\":[%s]}" (json_of_list json_of_mpat mpats)
  | MP_typ (mpat,typ) -> sprintf "{\"MP_typ\":[%s,%s]}" (json_of_mpat mpat) (json_of_typ typ)
  | MP_as (mpat,id) -> sprintf "{\"MP_as\":[%s,%s]}" (json_of_mpat mpat) (json_of_id id)
  | MP_struct (_,fexps) -> sprintf "{\"MP_struct\":[%s]}" (json_of_list (fun (id,mpat) -> sprintf "[%s,%s]" (json_of_id id) (json_of_mpat mpat)) fexps)

and json_of_mpat = function
  | MP_aux (mpat_aux,(_,_)) -> (json_of_mpat_aux mpat_aux)

let rec json_of_mpexp_aux = function
  | MPat_pat mpat -> sprintf "{\"MPat_pat\":[%s]}" (json_of_mpat mpat)
  | MPat_when (mpat,exp) -> sprintf "{\"MPat_when\":[%s,%s]}" (json_of_mpat mpat) (json_of_exp exp)

and json_of_mpexp = function
  | MPat_aux (mpexp_aux,(_,_)) -> (json_of_mpexp_aux mpexp_aux)

let rec json_of_mapcl_aux = function
  | MCL_bidir (mpexp1,mpexp2) -> sprintf "{\"MCL_bidir\":[%s,%s]}" (json_of_mpexp mpexp1) (json_of_mpexp mpexp2)
  | MCL_forwards pexp -> sprintf "{\"MCL_forwards\":[%s]}" (json_of_pexp pexp)
  | MCL_backwards pexp -> sprintf "{\"MCL_backwards\":[%s]}" (json_of_pexp pexp)

and json_of_mapcl = function
  | MCL_aux (mapcl_aux,(_,_)) -> (json_of_mapcl_aux mapcl_aux)

let rec json_of_funcl_aux = function
  | FCL_funcl (id,pexp) -> sprintf "{\"FCL_funcl\":[%s,%s]}" (json_of_id id) (json_of_pexp pexp)

and json_of_funcl = function
  | FCL_aux (funcl_aux,(_,_)) -> (json_of_funcl_aux funcl_aux)

let rec json_of_rec_opt_aux = function
  | Rec_nonrec -> "{\"Rec_nonrec\":[]}"
  | Rec_rec -> "{\"Rec_rec\":[]}"
  | Rec_measure (pat,exp) -> sprintf "{\"Rec_measure\":[%s,%s]}" (json_of_pat pat) (json_of_exp exp)

and json_of_rec_opt = function
  | Rec_aux (rec_opt_aux,_) -> (json_of_rec_opt_aux rec_opt_aux)

let rec json_of_tannot_opt_aux = function
  | Typ_annot_opt_none -> "{\"Typ_annot_opt_none\":[]}"
  | Typ_annot_opt_some (typquant,typ) -> sprintf "{\"Typ_annot_opt_some\":[%s,%s]}" (json_of_typquant typquant) (json_of_typ typ)

and json_of_tannot_opt = function
  | Typ_annot_opt_aux (tannot_opt_aux,_) -> (json_of_tannot_opt_aux tannot_opt_aux)

let rec json_of_type_union_aux = function
  | Tu_ty_id (typ,id) -> sprintf "{\"Tu_ty_id\":[%s,%s]}" (json_of_typ typ) (json_of_id id)

and json_of_type_union = function
  | Tu_aux (type_union_aux,_) -> (json_of_type_union_aux type_union_aux)

let rec json_of_typschm_aux = function
  | TypSchm_ts (typquant,typ) -> sprintf "{\"TypSchm_ts\":[%s,%s]}" (json_of_typquant typquant) (json_of_typ typ)

and json_of_typschm = function
  | TypSchm_aux (typschm_aux,_) -> (json_of_typschm_aux typschm_aux)

let rec json_of_index_range_aux = function
  | BF_single nexp -> sprintf "{\"BF_single\":%s}" (json_of_nexp nexp)
  | BF_range (nexp1,nexp2) -> sprintf "{\"BF_range\":[%s,%s]}" (json_of_nexp nexp1) (json_of_nexp nexp2)
  | BF_concat (index_range1,index_range2) -> sprintf "{\"BF_concat\":[%s,%s]}" (json_of_index_range index_range1) (json_of_index_range index_range2)

and json_of_index_range = function
  | BF_aux (index_range_aux,_) -> (json_of_index_range_aux index_range_aux)

let rec json_of_dec_spec_aux = function
  | DEC_reg (typ,id,exp_opt) -> sprintf "{\"DEC_reg\":[%s,%s,%s]}" (json_of_typ typ) (json_of_id id) (json_of_option json_of_exp exp_opt)

and json_of_dec_spec = function
  | DEC_aux (dec_spec_aux,(_,_)) -> (json_of_dec_spec_aux dec_spec_aux)

let rec json_of_scattered_def_aux = function
  | SD_function (id,tannot_opt) -> sprintf "{\"SD_function\":[%s,%s]}" (json_of_id id) (json_of_tannot_opt tannot_opt)
  | SD_funcl funcl -> sprintf "{\"SD_funcl\":%s}" (json_of_funcl funcl)
  | SD_variant (id,typquant) -> sprintf "{\"SD_variant\":[%s,%s]}" (json_of_id id) (json_of_typquant typquant)
  | SD_unioncl (id,type_union) -> sprintf "{\"SD_unioncl\":[%s,%s]}" (json_of_id id) (json_of_type_union type_union)
  | SD_internal_unioncl_record (id1,id2,typquant,typs) -> sprintf "{\"SD_internal_unioncl_record\":[%s,%s,%s,%s]}" (json_of_id id1) (json_of_id id2) (json_of_typquant typquant) (json_of_list (fun ((id, typ), _def_annot) -> sprintf "[%s,%s]" (json_of_typ typ) (json_of_id id)) typs)
  | SD_mapping (id,tannot_opt) -> sprintf "{\"SD_mapping\":[%s,%s]}" (json_of_id id) (json_of_tannot_opt tannot_opt)
  | SD_mapcl (id,mapcl) -> sprintf "{\"SD_mapcl\":[%s,%s]}" (json_of_id id) (json_of_mapcl mapcl)
  | SD_enum id -> sprintf "{\"SD_enum\":%s}" (json_of_id id)
  | SD_enumcl (id1,id2) -> sprintf "{\"SD_enumcl\":[%s,%s]}" (json_of_id id1) (json_of_id id2)
  | SD_end id -> sprintf "{\"SD_end\":%s}" (json_of_id id)

and json_of_scattered_def = function
  | SD_aux (scattered_def_aux,(_,_)) -> (json_of_scattered_def_aux scattered_def_aux)

let rec json_of_default_spec_aux = function
  | DT_order order -> sprintf "{\"DT_order\":%s}" (json_of_order order)

and json_of_default_spec = function
  | DT_aux (default_spec_aux,_) -> (json_of_default_spec_aux default_spec_aux)

let rec json_of_val_spec_aux = function
  | VS_val_spec (typschm,id,extern_opt) -> sprintf "{\"VS_val_spec\":[%s,%s,%s]}" (json_of_typschm typschm) (json_of_id id) (json_of_option json_of_extern extern_opt)

and json_of_val_spec = function
  | VS_aux (val_spec_aux,(_,_)) -> (json_of_val_spec_aux val_spec_aux)

let rec json_of_instantiation_spec_aux = function
  | IN_id id -> sprintf "{\"IN_id\":%s}" (json_of_id id)

and json_of_instantiation_spec = function
  | IN_aux (instantiation_spec_aux,(_,_)) -> (json_of_instantiation_spec_aux instantiation_spec_aux)

let rec json_of_outcome_spec_aux = function
  | OV_outcome (id,typschm,outcome_defs) -> sprintf "{\"OV_outcome\":[%s,%s,%s]}" (json_of_id id) (json_of_typschm typschm) (json_of_typquant outcome_defs)

and json_of_outcome_spec = function
  | OV_aux (outcome_spec_aux,_) -> (json_of_outcome_spec_aux outcome_spec_aux)

let rec json_of_subst_aux = function
  | IS_typ (kid,typ) -> sprintf "{\"IS_typ\":[%s,%s]}" (json_of_kid kid) (json_of_typ_arg typ)
  | IS_id (id1,id2) -> sprintf "{\"IS_id\":[%s,%s]}" (json_of_id id1) (json_of_id id2)

and json_of_subst = function
  | IS_aux (subst_aux,_) -> (json_of_subst_aux subst_aux)

let rec json_of_mapdef_aux = function
  | MD_mapping (id,tannot_opt,mapcls) -> sprintf "{\"MD_mapping\":[%s,%s,%s]}" (json_of_id id) (json_of_tannot_opt tannot_opt) (json_of_list json_of_mapcl mapcls)

and json_of_mapdef = function
  | MD_aux (mapdef_aux,(_,_)) -> (json_of_mapdef_aux mapdef_aux)

let rec json_of_fundef_aux = function
  | FD_function (rec_opt,tannot_opt,funcls) -> sprintf "{\"FD_function\":[%s,%s,%s]}" (json_of_rec_opt rec_opt) (json_of_tannot_opt tannot_opt) (json_of_list json_of_funcl funcls)

and json_of_fundef = function
  | FD_aux (fundef_aux,(_,_)) -> (json_of_fundef_aux fundef_aux)

let rec json_of_fundef_aux = function
  | FD_function (rec_opt,tannot_opt,funcls) -> sprintf "{\"FD_function\":[%s,%s,%s]}" (json_of_rec_opt rec_opt) (json_of_tannot_opt tannot_opt) (json_of_list json_of_funcl funcls)

and json_of_fundef = function
  | FD_aux (fundef_aux,(_,_)) -> (json_of_fundef_aux fundef_aux)

let rec json_of_type_def_aux = function
  | TD_abbrev (id,typquant,typ_arg) -> sprintf "{\"TD_abbrev\":[%s,%s,%s]}" (json_of_id id) (json_of_typquant typquant) (json_of_typ_arg typ_arg)
  | TD_record (id,typquant,typs_ids,bool) -> sprintf "{\"TD_record\":[%s,%s,%s,%b]}" (json_of_id id) (json_of_typquant typquant) (json_of_list (fun ((id, typ), _) -> sprintf "[%s,%s]" (json_of_typ typ) (json_of_id id)) typs_ids) bool
  | TD_variant (id,typquant,type_unions,bool) -> sprintf "{\"TD_variant\":[%s,%s,%s,%b]}" (json_of_id id) (json_of_typquant typquant) (json_of_list json_of_type_union type_unions) bool
  | TD_enum (id,ids,bool) -> sprintf "{\"TD_enum\":[%s,%s,%b]}" (json_of_id id) (json_of_list json_of_id ids) bool
  | TD_abstract (id,kind,_) -> sprintf "{\"TD_abstract\":[%s,%s]}" (json_of_id id) (json_of_kind kind)
  | TD_bitfield (id,typ,id_ranges) -> sprintf "{\"TD_bitfield\":[%s,%s,%s]}" (json_of_id id) (json_of_typ typ) ((json_of_list (fun ((id, range), _) -> sprintf "[%s,%s]" (json_of_id id) (json_of_index_range range)) id_ranges))

and json_of_type_def = function
  | TD_aux (type_def_aux,(_,_)) -> (json_of_type_def_aux type_def_aux)

let rec json_of_impldef_aux = function
  | Impl_impl funcl -> sprintf "{\"Impl_impl\":%s}" (json_of_funcl funcl)

and json_of_impldef = function
  | Impl_aux (impldef_aux,_) -> (json_of_impldef_aux impldef_aux)

let rec json_of_opt_default_aux = function
  | Def_val_empty -> "\"Def_val_empty\""
  | Def_val_dec exp -> sprintf "{\"Def_val_dec\":%s}" (json_of_exp exp)

and json_of_opt_default = function
  | Def_val_aux (opt_default_aux,(_,_)) -> (json_of_opt_default_aux opt_default_aux)

let json_of_loop_measure (loop,exp) =
  sprintf "[%s,%s]" (json_of_loop loop) (json_of_exp exp)

let json_of_prec = function
  | Infix -> json_of_string "Infix"
  | InfixL -> json_of_string "InfixL"
  | InfixR -> json_of_string "InfixR"

let rec json_of_def_aux = function
  | DEF_type type_def -> sprintf "{\"DEF_type\":%s}" (json_of_type_def type_def)
  | DEF_constraint n_constraint -> sprintf "{\"DEF_constraint\":%s}" (json_of_n_constraint n_constraint)
  | DEF_fundef fundef -> sprintf "{\"DEF_fundef\":%s}" (json_of_fundef fundef)
  | DEF_mapdef mapdef -> sprintf "{\"DEF_mapdef\":%s}" (json_of_mapdef mapdef)
  | DEF_impl funcl -> sprintf "{\"DEF_impl\":%s}" (json_of_funcl funcl)
  | DEF_let letbind -> sprintf "{\"DEF_let\":%s}" (json_of_letbind letbind)
  | DEF_val val_spec -> sprintf "{\"DEF_val\":%s}" (json_of_val_spec val_spec)
  | DEF_outcome (outcome_spec,defs) ->
      sprintf "{\"DEF_outcome\":[%s,%s]}" 
        (json_of_outcome_spec outcome_spec) (json_of_list json_of_def defs)
  | DEF_instantiation (instantiation_spec,substs) ->
      sprintf "{\"DEF_instantiation\":[%s,%s]}" 
        (json_of_instantiation_spec instantiation_spec) (json_of_list json_of_subst substs)
  | DEF_fixity (prec,num,id) ->
      sprintf "{\"DEF_fixity\":[%s,%s,%s]}" (json_of_prec prec) (json_of_big_int num) (json_of_id id)
  | DEF_overload (id,ids) ->
      sprintf "{\"DEF_overload\":[%s,%s]}" (json_of_id id) (json_of_list json_of_id ids)
  | DEF_default default_spec ->
      sprintf "{\"DEF_default\":%s}" (json_of_default_spec default_spec)
  | DEF_scattered scattered_def ->
      sprintf "{\"DEF_scattered\":%s}" (json_of_scattered_def scattered_def)
  | DEF_measure (id,pat,exp) ->
      sprintf "{\"DEF_measure\":[%s,%s,%s]}" (json_of_id id) (json_of_pat pat) (json_of_exp exp)
  | DEF_loop_measures (id,loop_measures) ->
      sprintf "{\"DEF_loop_measures\":[%s,%s]}" (json_of_id id) (json_of_list json_of_loop_measure loop_measures)
  | DEF_register dec_spec ->
      sprintf "{\"DEF_register\":%s}" (json_of_dec_spec dec_spec)
  | DEF_internal_mutrec fundefs ->
      sprintf "{\"DEF_internal_mutrec\":%s}" (json_of_list (json_of_fundef) fundefs)
  | DEF_pragma (pragma, Pragma_line (arg, _)) ->
      sprintf "{\"DEF_pragma\":[%s,%s]}" (json_of_string pragma) (json_of_string arg)
  | DEF_pragma (pragma, Pragma_structured data) ->
      let open Parse_ast.Attribute_data in
      sprintf "{\"DEF_pragma\":[%s]}" (json_of_string pragma)

and json_of_def = function
  | DEF_aux (def_aux,_) -> json_of_def_aux def_aux

let pp_ast_json defs =
  sprintf "{\"ast\":[%s]}" (String.concat "," (List.map json_of_def defs))
