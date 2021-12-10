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

(* generated by Ott 0.30 from: ../language/sail.ott *)
open PPrintEngine
open PPrintCombinators
open 

let rec pp_raw_l_default 

and pp_raw_id_aux x = match x with
| Id_aux_aux(Id(x),ott_menhir_loc) ->  string "[" ^^ string (pp_raw_l ott_menhir_loc) ^^ string "]" ^^ string "Id" ^^ string "(" ^^  string "\"" ^^ string x ^^ string "\"" ^^ string ")"
| Id_aux_aux(Operator(x),ott_menhir_loc) ->  string "[" ^^ string (pp_raw_l ott_menhir_loc) ^^ string "]" ^^ string "Operator" ^^ string "(" ^^  string "\"" ^^ string x ^^ string "\"" ^^ string ")"

and pp_raw_id x = match x with
| Id_aux(id_aux,l) -> string "Id_aux" ^^ string "(" ^^ pp_raw_id_aux id_aux ^^ string "," ^^ pp_raw_l l ^^ string ")"

and pp_raw_kid_aux x = match x with
| Kid_aux_aux(Var(x),ott_menhir_loc) ->  string "[" ^^ string (pp_raw_l ott_menhir_loc) ^^ string "]" ^^ string "Var" ^^ string "(" ^^  string "\"" ^^ string x ^^ string "\"" ^^ string ")"

and pp_raw_kid x = match x with
| Kid_aux(kid_aux,l) -> string "Kid_aux" ^^ string "(" ^^ pp_raw_kid_aux kid_aux ^^ string "," ^^ pp_raw_l l ^^ string ")"

and pp_raw_kind_aux x = match x with
| K_aux(K_type,ott_menhir_loc) ->  string "[" ^^ string (pp_raw_l ott_menhir_loc) ^^ string "]" ^^ string "K_type"
| K_aux(K_int,ott_menhir_loc) ->  string "[" ^^ string (pp_raw_l ott_menhir_loc) ^^ string "]" ^^ string "K_int"
| K_aux(K_order,ott_menhir_loc) ->  string "[" ^^ string (pp_raw_l ott_menhir_loc) ^^ string "]" ^^ string "K_order"
| K_aux(K_bool,ott_menhir_loc) ->  string "[" ^^ string (pp_raw_l ott_menhir_loc) ^^ string "]" ^^ string "K_bool"

and pp_raw_kind x = match x with
| K_aux(kind_aux,l) -> string "K_aux" ^^ string "(" ^^ pp_raw_kind_aux kind_aux ^^ string "," ^^ pp_raw_l l ^^ string ")"

and pp_raw_nexp_aux x = match x with
| Nexp_aux(Nexp_id(id),ott_menhir_loc) ->  string "[" ^^ string (pp_raw_l ott_menhir_loc) ^^ string "]" ^^ string "Nexp_id" ^^ string "(" ^^ pp_raw_id id ^^ string ")"
| Nexp_aux(Nexp_var(kid),ott_menhir_loc) ->  string "[" ^^ string (pp_raw_l ott_menhir_loc) ^^ string "]" ^^ string "Nexp_var" ^^ string "(" ^^ pp_raw_kid kid ^^ string ")"
| Nexp_aux(Nexp_constant(num),ott_menhir_loc) ->  string "[" ^^ string (pp_raw_l ott_menhir_loc) ^^ string "]" ^^ string "Nexp_constant" ^^ string "(" ^^  string "\"" ^^ string num ^^ string "\"" ^^ string ")"
| Nexp_aux(Nexp_app(id,nexp0),ott_menhir_loc) ->  string "[" ^^ string (pp_raw_l ott_menhir_loc) ^^ string "]" ^^ string "Nexp_app" ^^ string "(" ^^ pp_raw_id id ^^ string "," ^^ string "[" ^^ separate  (string ";") (List.map (function (nexp0) -> string "(" ^^ pp_raw_nexp nexp0 ^^ string ")") nexp0) ^^ string "]" ^^ string ")"
| Nexp_aux(Nexp_times(nexp1,nexp2),ott_menhir_loc) ->  string "[" ^^ string (pp_raw_l ott_menhir_loc) ^^ string "]" ^^ string "Nexp_times" ^^ string "(" ^^ pp_raw_nexp nexp1 ^^ string "," ^^ pp_raw_nexp nexp2 ^^ string ")"
| Nexp_aux(Nexp_sum(nexp1,nexp2),ott_menhir_loc) ->  string "[" ^^ string (pp_raw_l ott_menhir_loc) ^^ string "]" ^^ string "Nexp_sum" ^^ string "(" ^^ pp_raw_nexp nexp1 ^^ string "," ^^ pp_raw_nexp nexp2 ^^ string ")"
| Nexp_aux(Nexp_minus(nexp1,nexp2),ott_menhir_loc) ->  string "[" ^^ string (pp_raw_l ott_menhir_loc) ^^ string "]" ^^ string "Nexp_minus" ^^ string "(" ^^ pp_raw_nexp nexp1 ^^ string "," ^^ pp_raw_nexp nexp2 ^^ string ")"
| Nexp_aux(Nexp_exp(nexp),ott_menhir_loc) ->  string "[" ^^ string (pp_raw_l ott_menhir_loc) ^^ string "]" ^^ string "Nexp_exp" ^^ string "(" ^^ pp_raw_nexp nexp ^^ string ")"
| Nexp_aux(Nexp_neg(nexp),ott_menhir_loc) ->  string "[" ^^ string (pp_raw_l ott_menhir_loc) ^^ string "]" ^^ string "Nexp_neg" ^^ string "(" ^^ pp_raw_nexp nexp ^^ string ")"

and pp_raw_nexp x = match x with
| Nexp_aux(nexp_aux,l) -> string "Nexp_aux" ^^ string "(" ^^ pp_raw_nexp_aux nexp_aux ^^ string "," ^^ pp_raw_l l ^^ string ")"

and pp_raw_order_aux x = match x with
| Ord_aux(Ord_var(kid),ott_menhir_loc) ->  string "[" ^^ string (pp_raw_l ott_menhir_loc) ^^ string "]" ^^ string "Ord_var" ^^ string "(" ^^ pp_raw_kid kid ^^ string ")"
| Ord_aux(Ord_inc,ott_menhir_loc) ->  string "[" ^^ string (pp_raw_l ott_menhir_loc) ^^ string "]" ^^ string "Ord_inc"
| Ord_aux(Ord_dec,ott_menhir_loc) ->  string "[" ^^ string (pp_raw_l ott_menhir_loc) ^^ string "]" ^^ string "Ord_dec"

and pp_raw_order x = match x with
| Ord_aux(order_aux,l) -> string "Ord_aux" ^^ string "(" ^^ pp_raw_order_aux order_aux ^^ string "," ^^ pp_raw_l l ^^ string ")"

and pp_raw_base_effect_aux x = match x with
| BE_aux(BE_rreg,ott_menhir_loc) ->  string "[" ^^ string (pp_raw_l ott_menhir_loc) ^^ string "]" ^^ string "BE_rreg"
| BE_aux(BE_wreg,ott_menhir_loc) ->  string "[" ^^ string (pp_raw_l ott_menhir_loc) ^^ string "]" ^^ string "BE_wreg"
| BE_aux(BE_rmem,ott_menhir_loc) ->  string "[" ^^ string (pp_raw_l ott_menhir_loc) ^^ string "]" ^^ string "BE_rmem"
| BE_aux(BE_wmem,ott_menhir_loc) ->  string "[" ^^ string (pp_raw_l ott_menhir_loc) ^^ string "]" ^^ string "BE_wmem"
| BE_aux(BE_eamem,ott_menhir_loc) ->  string "[" ^^ string (pp_raw_l ott_menhir_loc) ^^ string "]" ^^ string "BE_eamem"
| BE_aux(BE_exmem,ott_menhir_loc) ->  string "[" ^^ string (pp_raw_l ott_menhir_loc) ^^ string "]" ^^ string "BE_exmem"
| BE_aux(BE_wmv,ott_menhir_loc) ->  string "[" ^^ string (pp_raw_l ott_menhir_loc) ^^ string "]" ^^ string "BE_wmv"
| BE_aux(BE_barr,ott_menhir_loc) ->  string "[" ^^ string (pp_raw_l ott_menhir_loc) ^^ string "]" ^^ string "BE_barr"
| BE_aux(BE_depend,ott_menhir_loc) ->  string "[" ^^ string (pp_raw_l ott_menhir_loc) ^^ string "]" ^^ string "BE_depend"
| BE_aux(BE_undef,ott_menhir_loc) ->  string "[" ^^ string (pp_raw_l ott_menhir_loc) ^^ string "]" ^^ string "BE_undef"
| BE_aux(BE_unspec,ott_menhir_loc) ->  string "[" ^^ string (pp_raw_l ott_menhir_loc) ^^ string "]" ^^ string "BE_unspec"
| BE_aux(BE_nondet,ott_menhir_loc) ->  string "[" ^^ string (pp_raw_l ott_menhir_loc) ^^ string "]" ^^ string "BE_nondet"
| BE_aux(BE_escape,ott_menhir_loc) ->  string "[" ^^ string (pp_raw_l ott_menhir_loc) ^^ string "]" ^^ string "BE_escape"
| BE_aux(BE_config,ott_menhir_loc) ->  string "[" ^^ string (pp_raw_l ott_menhir_loc) ^^ string "]" ^^ string "BE_config"

and pp_raw_base_effect x = match x with
| BE_aux(base_effect_aux,l) -> string "BE_aux" ^^ string "(" ^^ pp_raw_base_effect_aux base_effect_aux ^^ string "," ^^ pp_raw_l l ^^ string ")"

and pp_raw_effect_aux x = match x with
| Effect_aux(Effect_set(base_effect0),ott_menhir_loc) ->  string "[" ^^ string (pp_raw_l ott_menhir_loc) ^^ string "]" ^^ string "Effect_set" ^^ string "(" ^^ string "[" ^^ separate  (string ";") (List.map (function (base_effect0) -> string "(" ^^ pp_raw_base_effect base_effect0 ^^ string ")") base_effect0) ^^ string "]" ^^ string ")"

and pp_raw_effect x = match x with
| Effect_aux(effect_aux,l) -> string "Effect_aux" ^^ string "(" ^^ pp_raw_effect_aux effect_aux ^^ string "," ^^ pp_raw_l l ^^ string ")"

and pp_raw_typ_aux x = match x with
| Typ_aux(Typ_internal_unknown,ott_menhir_loc) ->  string "[" ^^ string (pp_raw_l ott_menhir_loc) ^^ string "]" ^^ string "Typ_internal_unknown"
| Typ_aux(Typ_id(id),ott_menhir_loc) ->  string "[" ^^ string (pp_raw_l ott_menhir_loc) ^^ string "]" ^^ string "Typ_id" ^^ string "(" ^^ pp_raw_id id ^^ string ")"
| Typ_aux(Typ_var(kid),ott_menhir_loc) ->  string "[" ^^ string (pp_raw_l ott_menhir_loc) ^^ string "]" ^^ string "Typ_var" ^^ string "(" ^^ pp_raw_kid kid ^^ string ")"
| Typ_aux(Typ_fn(typ0,typ2,effect),ott_menhir_loc) ->  string "[" ^^ string (pp_raw_l ott_menhir_loc) ^^ string "]" ^^ string "Typ_fn" ^^ string "(" ^^ string "[" ^^ separate  (string ";") (List.map (function (typ0) -> string "(" ^^ pp_raw_typ typ0 ^^ string ")") typ0) ^^ string "]" ^^ string "," ^^ pp_raw_typ typ2 ^^ string "," ^^ pp_raw_effect effect ^^ string ")"
| Typ_aux(Typ_bidir(typ1,typ2),ott_menhir_loc) ->  string "[" ^^ string (pp_raw_l ott_menhir_loc) ^^ string "]" ^^ string "Typ_bidir" ^^ string "(" ^^ pp_raw_typ typ1 ^^ string "," ^^ pp_raw_typ typ2 ^^ string ")"
| Typ_aux(Typ_tup(typ0),ott_menhir_loc) ->  string "[" ^^ string (pp_raw_l ott_menhir_loc) ^^ string "]" ^^ string "Typ_tup" ^^ string "(" ^^ string "[" ^^ separate  (string ";") (List.map (function (typ0) -> string "(" ^^ pp_raw_typ typ0 ^^ string ")") typ0) ^^ string "]" ^^ string ")"
| Typ_aux(Typ_app(id,typ_arg0),ott_menhir_loc) ->  string "[" ^^ string (pp_raw_l ott_menhir_loc) ^^ string "]" ^^ string "Typ_app" ^^ string "(" ^^ pp_raw_id id ^^ string "," ^^ string "[" ^^ separate  (string ";") (List.map (function (typ_arg0) -> string "(" ^^ pp_raw_typ_arg typ_arg0 ^^ string ")") typ_arg0) ^^ string "]" ^^ string ")"
| Typ_aux(Typ_exist(kinded_id0,n_constraint,typ),ott_menhir_loc) ->  string "[" ^^ string (pp_raw_l ott_menhir_loc) ^^ string "]" ^^ string "Typ_exist" ^^ string "(" ^^ string "[" ^^ separate  (string ";") (List.map (function (kinded_id0) -> string "(" ^^ pp_raw_kinded_id kinded_id0 ^^ string ")") kinded_id0) ^^ string "]" ^^ string "," ^^ pp_raw_n_constraint n_constraint ^^ string "," ^^ pp_raw_typ typ ^^ string ")"

and pp_raw_typ x = match x with
| Typ_aux(typ_aux,l) -> string "Typ_aux" ^^ string "(" ^^ pp_raw_typ_aux typ_aux ^^ string "," ^^ pp_raw_l l ^^ string ")"

and pp_raw_typ_arg_aux x = match x with
| A_aux(A_nexp(nexp),ott_menhir_loc) ->  string "[" ^^ string (pp_raw_l ott_menhir_loc) ^^ string "]" ^^ string "A_nexp" ^^ string "(" ^^ pp_raw_nexp nexp ^^ string ")"
| A_aux(A_typ(typ),ott_menhir_loc) ->  string "[" ^^ string (pp_raw_l ott_menhir_loc) ^^ string "]" ^^ string "A_typ" ^^ string "(" ^^ pp_raw_typ typ ^^ string ")"
| A_aux(A_order(order),ott_menhir_loc) ->  string "[" ^^ string (pp_raw_l ott_menhir_loc) ^^ string "]" ^^ string "A_order" ^^ string "(" ^^ pp_raw_order order ^^ string ")"
| A_aux(A_bool(n_constraint),ott_menhir_loc) ->  string "[" ^^ string (pp_raw_l ott_menhir_loc) ^^ string "]" ^^ string "A_bool" ^^ string "(" ^^ pp_raw_n_constraint n_constraint ^^ string ")"

and pp_raw_typ_arg x = match x with
| A_aux(typ_arg_aux,l) -> string "A_aux" ^^ string "(" ^^ pp_raw_typ_arg_aux typ_arg_aux ^^ string "," ^^ pp_raw_l l ^^ string ")"

and pp_raw_n_constraint_aux x = match x with
| NC_aux(NC_equal(nexp,nexp_prime),ott_menhir_loc) ->  string "[" ^^ string (pp_raw_l ott_menhir_loc) ^^ string "]" ^^ string "NC_equal" ^^ string "(" ^^ pp_raw_nexp nexp ^^ string "," ^^ pp_raw_nexp nexp_prime ^^ string ")"
| NC_aux(NC_bounded_ge(nexp,nexp_prime),ott_menhir_loc) ->  string "[" ^^ string (pp_raw_l ott_menhir_loc) ^^ string "]" ^^ string "NC_bounded_ge" ^^ string "(" ^^ pp_raw_nexp nexp ^^ string "," ^^ pp_raw_nexp nexp_prime ^^ string ")"
| NC_aux(NC_bounded_gt(nexp,nexp_prime),ott_menhir_loc) ->  string "[" ^^ string (pp_raw_l ott_menhir_loc) ^^ string "]" ^^ string "NC_bounded_gt" ^^ string "(" ^^ pp_raw_nexp nexp ^^ string "," ^^ pp_raw_nexp nexp_prime ^^ string ")"
| NC_aux(NC_bounded_le(nexp,nexp_prime),ott_menhir_loc) ->  string "[" ^^ string (pp_raw_l ott_menhir_loc) ^^ string "]" ^^ string "NC_bounded_le" ^^ string "(" ^^ pp_raw_nexp nexp ^^ string "," ^^ pp_raw_nexp nexp_prime ^^ string ")"
| NC_aux(NC_bounded_lt(nexp,nexp_prime),ott_menhir_loc) ->  string "[" ^^ string (pp_raw_l ott_menhir_loc) ^^ string "]" ^^ string "NC_bounded_lt" ^^ string "(" ^^ pp_raw_nexp nexp ^^ string "," ^^ pp_raw_nexp nexp_prime ^^ string ")"
| NC_aux(NC_not_equal(nexp,nexp_prime),ott_menhir_loc) ->  string "[" ^^ string (pp_raw_l ott_menhir_loc) ^^ string "]" ^^ string "NC_not_equal" ^^ string "(" ^^ pp_raw_nexp nexp ^^ string "," ^^ pp_raw_nexp nexp_prime ^^ string ")"
| NC_aux(NC_set(kid,num0),ott_menhir_loc) ->  string "[" ^^ string (pp_raw_l ott_menhir_loc) ^^ string "]" ^^ string "NC_set" ^^ string "(" ^^ pp_raw_kid kid ^^ string "," ^^ string "[" ^^ separate  (string ";") (List.map (function (num0) -> string "(" ^^  string "\"" ^^ string num0 ^^ string "\"" ^^ string ")") num0) ^^ string "]" ^^ string ")"
| NC_aux(NC_or(n_constraint,n_constraint_prime),ott_menhir_loc) ->  string "[" ^^ string (pp_raw_l ott_menhir_loc) ^^ string "]" ^^ string "NC_or" ^^ string "(" ^^ pp_raw_n_constraint n_constraint ^^ string "," ^^ pp_raw_n_constraint n_constraint_prime ^^ string ")"
| NC_aux(NC_and(n_constraint,n_constraint_prime),ott_menhir_loc) ->  string "[" ^^ string (pp_raw_l ott_menhir_loc) ^^ string "]" ^^ string "NC_and" ^^ string "(" ^^ pp_raw_n_constraint n_constraint ^^ string "," ^^ pp_raw_n_constraint n_constraint_prime ^^ string ")"
| NC_aux(NC_app(id,typ_arg0),ott_menhir_loc) ->  string "[" ^^ string (pp_raw_l ott_menhir_loc) ^^ string "]" ^^ string "NC_app" ^^ string "(" ^^ pp_raw_id id ^^ string "," ^^ string "[" ^^ separate  (string ";") (List.map (function (typ_arg0) -> string "(" ^^ pp_raw_typ_arg typ_arg0 ^^ string ")") typ_arg0) ^^ string "]" ^^ string ")"
| NC_aux(NC_var(kid),ott_menhir_loc) ->  string "[" ^^ string (pp_raw_l ott_menhir_loc) ^^ string "]" ^^ string "NC_var" ^^ string "(" ^^ pp_raw_kid kid ^^ string ")"
| NC_aux(NC_true,ott_menhir_loc) ->  string "[" ^^ string (pp_raw_l ott_menhir_loc) ^^ string "]" ^^ string "NC_true"
| NC_aux(NC_false,ott_menhir_loc) ->  string "[" ^^ string (pp_raw_l ott_menhir_loc) ^^ string "]" ^^ string "NC_false"

and pp_raw_n_constraint x = match x with
| NC_aux(n_constraint_aux,l) -> string "NC_aux" ^^ string "(" ^^ pp_raw_n_constraint_aux n_constraint_aux ^^ string "," ^^ pp_raw_l l ^^ string ")"

and pp_raw_kinded_id_aux x = match x with
| KOpt_aux(KOpt_kind(kind,kid),ott_menhir_loc) ->  string "[" ^^ string (pp_raw_l ott_menhir_loc) ^^ string "]" ^^ string "KOpt_kind" ^^ string "(" ^^ pp_raw_kind kind ^^ string "," ^^ pp_raw_kid kid ^^ string ")"

and pp_raw_kinded_id x = match x with
| KOpt_aux(kinded_id_aux,l) -> string "KOpt_aux" ^^ string "(" ^^ pp_raw_kinded_id_aux kinded_id_aux ^^ string "," ^^ pp_raw_l l ^^ string ")"

and pp_raw_quant_item_aux x = match x with
| QI_aux(QI_id(kinded_id),ott_menhir_loc) ->  string "[" ^^ string (pp_raw_l ott_menhir_loc) ^^ string "]" ^^ string "QI_id" ^^ string "(" ^^ pp_raw_kinded_id kinded_id ^^ string ")"
| QI_aux(QI_constraint(n_constraint),ott_menhir_loc) ->  string "[" ^^ string (pp_raw_l ott_menhir_loc) ^^ string "]" ^^ string "QI_constraint" ^^ string "(" ^^ pp_raw_n_constraint n_constraint ^^ string ")"
| QI_aux(QI_constant(kinded_id0),ott_menhir_loc) ->  string "[" ^^ string (pp_raw_l ott_menhir_loc) ^^ string "]" ^^ string "QI_constant" ^^ string "(" ^^ string "[" ^^ separate  (string ";") (List.map (function (kinded_id0) -> string "(" ^^ pp_raw_kinded_id kinded_id0 ^^ string ")") kinded_id0) ^^ string "]" ^^ string ")"

and pp_raw_quant_item x = match x with
| QI_aux(quant_item_aux,l) -> string "QI_aux" ^^ string "(" ^^ pp_raw_quant_item_aux quant_item_aux ^^ string "," ^^ pp_raw_l l ^^ string ")"

and pp_raw_typquant_aux x = match x with
| TypQ_aux(TypQ_tq(quant_item0),ott_menhir_loc) ->  string "[" ^^ string (pp_raw_l ott_menhir_loc) ^^ string "]" ^^ string "TypQ_tq" ^^ string "(" ^^ string "[" ^^ separate  (string ";") (List.map (function (quant_item0) -> string "(" ^^ pp_raw_quant_item quant_item0 ^^ string ")") quant_item0) ^^ string "]" ^^ string ")"
| TypQ_aux(TypQ_no_forall,ott_menhir_loc) ->  string "[" ^^ string (pp_raw_l ott_menhir_loc) ^^ string "]" ^^ string "TypQ_no_forall"

and pp_raw_typquant x = match x with
| TypQ_aux(typquant_aux,l) -> string "TypQ_aux" ^^ string "(" ^^ pp_raw_typquant_aux typquant_aux ^^ string "," ^^ pp_raw_l l ^^ string ")"

and pp_raw_typschm_aux x = match x with
| TypSchm_aux(TypSchm_ts(typquant,typ),ott_menhir_loc) ->  string "[" ^^ string (pp_raw_l ott_menhir_loc) ^^ string "]" ^^ string "TypSchm_ts" ^^ string "(" ^^ pp_raw_typquant typquant ^^ string "," ^^ pp_raw_typ typ ^^ string ")"

and pp_raw_typschm x = match x with
| TypSchm_aux(typschm_aux,l) -> string "TypSchm_aux" ^^ string "(" ^^ pp_raw_typschm_aux typschm_aux ^^ string "," ^^ pp_raw_l l ^^ string ")"

and pp_raw_type_def x = match x with
| TD_aux(type_def_aux) -> string "TD_aux" ^^ string "(" ^^ pp_raw_type_def_aux type_def_aux ^^ string ")"

and pp_raw_type_def_aux x = match x with
| TD_abbrev(id,typquant,typ_arg) -> string "TD_abbrev" ^^ string "(" ^^ pp_raw_id id ^^ string "," ^^ pp_raw_typquant typquant ^^ string "," ^^ pp_raw_typ_arg typ_arg ^^ string ")"
| TD_record(id,typquant,typ0_id0,semi_opt) -> string "TD_record" ^^ string "(" ^^ pp_raw_id id ^^ string "," ^^ pp_raw_typquant typquant ^^ string "," ^^ string "[" ^^ separate  (string ";") (List.map (function (typ0,id0) -> string "(" ^^ pp_raw_typ typ0 ^^ string "," ^^ pp_raw_id id0 ^^ string ")") typ0_id0) ^^ string "]" ^^ string "," ^^ pp_raw_semi_opt semi_opt ^^ string ")"
| TD_variant(id,typquant,type_union0,semi_opt) -> string "TD_variant" ^^ string "(" ^^ pp_raw_id id ^^ string "," ^^ pp_raw_typquant typquant ^^ string "," ^^ string "[" ^^ separate  (string ";") (List.map (function (type_union0) -> string "(" ^^ pp_raw_type_union type_union0 ^^ string ")") type_union0) ^^ string "]" ^^ string "," ^^ pp_raw_semi_opt semi_opt ^^ string ")"
| TD_enum(id,id0,semi_opt) -> string "TD_enum" ^^ string "(" ^^ pp_raw_id id ^^ string "," ^^ string "[" ^^ separate  (string ";") (List.map (function (id0) -> string "(" ^^ pp_raw_id id0 ^^ string ")") id0) ^^ string "]" ^^ string "," ^^ pp_raw_semi_opt semi_opt ^^ string ")"
| TD_bitfield(id,typ,id0_index_range0) -> string "TD_bitfield" ^^ string "(" ^^ pp_raw_id id ^^ string "," ^^ pp_raw_typ typ ^^ string "," ^^ string "[" ^^ separate  (string ";") (List.map (function (id0,index_range0) -> string "(" ^^ pp_raw_id id0 ^^ string "," ^^ pp_raw_index_range index_range0 ^^ string ")") id0_index_range0) ^^ string "]" ^^ string ")"

and pp_raw_type_union_aux x = match x with
| Tu_aux(Tu_ty_id(typ,id),ott_menhir_loc) ->  string "[" ^^ string (pp_raw_l ott_menhir_loc) ^^ string "]" ^^ string "Tu_ty_id" ^^ string "(" ^^ pp_raw_typ typ ^^ string "," ^^ pp_raw_id id ^^ string ")"

and pp_raw_type_union x = match x with
| Tu_aux(type_union_aux,l) -> string "Tu_aux" ^^ string "(" ^^ pp_raw_type_union_aux type_union_aux ^^ string "," ^^ pp_raw_l l ^^ string ")"

and pp_raw_index_range_aux x = match x with
| BF_aux(BF_single(nexp),ott_menhir_loc) ->  string "[" ^^ string (pp_raw_l ott_menhir_loc) ^^ string "]" ^^ string "BF_single" ^^ string "(" ^^ pp_raw_nexp nexp ^^ string ")"
| BF_aux(BF_range(nexp1,nexp2),ott_menhir_loc) ->  string "[" ^^ string (pp_raw_l ott_menhir_loc) ^^ string "]" ^^ string "BF_range" ^^ string "(" ^^ pp_raw_nexp nexp1 ^^ string "," ^^ pp_raw_nexp nexp2 ^^ string ")"
| BF_aux(BF_concat(index_range1,index_range2),ott_menhir_loc) ->  string "[" ^^ string (pp_raw_l ott_menhir_loc) ^^ string "]" ^^ string "BF_concat" ^^ string "(" ^^ pp_raw_index_range index_range1 ^^ string "," ^^ pp_raw_index_range index_range2 ^^ string ")"

and pp_raw_index_range x = match x with
| BF_aux(index_range_aux,l) -> string "BF_aux" ^^ string "(" ^^ pp_raw_index_range_aux index_range_aux ^^ string "," ^^ pp_raw_l l ^^ string ")"

and pp_raw_lit_aux x = match x with
| L_aux(L_unit,ott_menhir_loc) ->  string "[" ^^ string (pp_raw_l ott_menhir_loc) ^^ string "]" ^^ string "L_unit"
| L_aux(L_zero,ott_menhir_loc) ->  string "[" ^^ string (pp_raw_l ott_menhir_loc) ^^ string "]" ^^ string "L_zero"
| L_aux(L_one,ott_menhir_loc) ->  string "[" ^^ string (pp_raw_l ott_menhir_loc) ^^ string "]" ^^ string "L_one"
| L_aux(L_true,ott_menhir_loc) ->  string "[" ^^ string (pp_raw_l ott_menhir_loc) ^^ string "]" ^^ string "L_true"
| L_aux(L_false,ott_menhir_loc) ->  string "[" ^^ string (pp_raw_l ott_menhir_loc) ^^ string "]" ^^ string "L_false"
| L_aux(L_num(num),ott_menhir_loc) ->  string "[" ^^ string (pp_raw_l ott_menhir_loc) ^^ string "]" ^^ string "L_num" ^^ string "(" ^^  string "\"" ^^ string num ^^ string "\"" ^^ string ")"
| L_aux(L_hex(hex),ott_menhir_loc) ->  string "[" ^^ string (pp_raw_l ott_menhir_loc) ^^ string "]" ^^ string "L_hex" ^^ string "(" ^^  string "\"" ^^ string hex ^^ string "\"" ^^ string ")"
| L_aux(L_bin(bin),ott_menhir_loc) ->  string "[" ^^ string (pp_raw_l ott_menhir_loc) ^^ string "]" ^^ string "L_bin" ^^ string "(" ^^  string "\"" ^^ string bin ^^ string "\"" ^^ string ")"
| L_aux(L_string(string),ott_menhir_loc) ->  string "[" ^^ string (pp_raw_l ott_menhir_loc) ^^ string "]" ^^ string "L_string" ^^ string "(" ^^  string "\"" ^^ string string ^^ string "\"" ^^ string ")"
| L_aux(L_undef,ott_menhir_loc) ->  string "[" ^^ string (pp_raw_l ott_menhir_loc) ^^ string "]" ^^ string "L_undef"
| L_aux(L_real(real),ott_menhir_loc) ->  string "[" ^^ string (pp_raw_l ott_menhir_loc) ^^ string "]" ^^ string "L_real" ^^ string "(" ^^  string "\"" ^^ string real ^^ string "\"" ^^ string ")"

and pp_raw_lit x = match x with
| L_aux(lit_aux,l) -> string "L_aux" ^^ string "(" ^^ pp_raw_lit_aux lit_aux ^^ string "," ^^ pp_raw_l l ^^ string ")"

and pp_raw_semi_opt_default 

and pp_raw_typ_pat_aux x = match x with
| TP_aux(TP_wild,ott_menhir_loc) ->  string "[" ^^ string (pp_raw_l ott_menhir_loc) ^^ string "]" ^^ string "TP_wild"
| TP_aux(TP_var(kid),ott_menhir_loc) ->  string "[" ^^ string (pp_raw_l ott_menhir_loc) ^^ string "]" ^^ string "TP_var" ^^ string "(" ^^ pp_raw_kid kid ^^ string ")"
| TP_aux(TP_app(id,typ_pat0),ott_menhir_loc) ->  string "[" ^^ string (pp_raw_l ott_menhir_loc) ^^ string "]" ^^ string "TP_app" ^^ string "(" ^^ pp_raw_id id ^^ string "," ^^ string "[" ^^ separate  (string ";") (List.map (function (typ_pat0) -> string "(" ^^ pp_raw_typ_pat typ_pat0 ^^ string ")") typ_pat0) ^^ string "]" ^^ string ")"

and pp_raw_typ_pat x = match x with
| TP_aux(typ_pat_aux,l) -> string "TP_aux" ^^ string "(" ^^ pp_raw_typ_pat_aux typ_pat_aux ^^ string "," ^^ pp_raw_l l ^^ string ")"

and pp_raw_pat_aux x = match x with
| P_aux(P_lit(lit),ott_menhir_loc) ->  string "[" ^^ string (pp_raw_l ott_menhir_loc) ^^ string "]" ^^ string "P_lit" ^^ string "(" ^^ pp_raw_lit lit ^^ string ")"
| P_aux(P_wild,ott_menhir_loc) ->  string "[" ^^ string (pp_raw_l ott_menhir_loc) ^^ string "]" ^^ string "P_wild"
| P_aux(P_or(pat1,pat2),ott_menhir_loc) ->  string "[" ^^ string (pp_raw_l ott_menhir_loc) ^^ string "]" ^^ string "P_or" ^^ string "(" ^^ pp_raw_pat pat1 ^^ string "," ^^ pp_raw_pat pat2 ^^ string ")"
| P_aux(P_not(pat),ott_menhir_loc) ->  string "[" ^^ string (pp_raw_l ott_menhir_loc) ^^ string "]" ^^ string "P_not" ^^ string "(" ^^ pp_raw_pat pat ^^ string ")"
| P_aux(P_as(pat,id),ott_menhir_loc) ->  string "[" ^^ string (pp_raw_l ott_menhir_loc) ^^ string "]" ^^ string "P_as" ^^ string "(" ^^ pp_raw_pat pat ^^ string "," ^^ pp_raw_id id ^^ string ")"
| P_aux(P_typ(typ,pat),ott_menhir_loc) ->  string "[" ^^ string (pp_raw_l ott_menhir_loc) ^^ string "]" ^^ string "P_typ" ^^ string "(" ^^ pp_raw_typ typ ^^ string "," ^^ pp_raw_pat pat ^^ string ")"
| P_aux(P_id(id),ott_menhir_loc) ->  string "[" ^^ string (pp_raw_l ott_menhir_loc) ^^ string "]" ^^ string "P_id" ^^ string "(" ^^ pp_raw_id id ^^ string ")"
| P_aux(P_var(pat,typ_pat),ott_menhir_loc) ->  string "[" ^^ string (pp_raw_l ott_menhir_loc) ^^ string "]" ^^ string "P_var" ^^ string "(" ^^ pp_raw_pat pat ^^ string "," ^^ pp_raw_typ_pat typ_pat ^^ string ")"
| P_aux(P_app(id,pat0),ott_menhir_loc) ->  string "[" ^^ string (pp_raw_l ott_menhir_loc) ^^ string "]" ^^ string "P_app" ^^ string "(" ^^ pp_raw_id id ^^ string "," ^^ string "[" ^^ separate  (string ";") (List.map (function (pat0) -> string "(" ^^ pp_raw_pat pat0 ^^ string ")") pat0) ^^ string "]" ^^ string ")"
| P_aux(P_vector(pat0),ott_menhir_loc) ->  string "[" ^^ string (pp_raw_l ott_menhir_loc) ^^ string "]" ^^ string "P_vector" ^^ string "(" ^^ string "[" ^^ separate  (string ";") (List.map (function (pat0) -> string "(" ^^ pp_raw_pat pat0 ^^ string ")") pat0) ^^ string "]" ^^ string ")"
| P_aux(P_vector_concat(pat0),ott_menhir_loc) ->  string "[" ^^ string (pp_raw_l ott_menhir_loc) ^^ string "]" ^^ string "P_vector_concat" ^^ string "(" ^^ string "[" ^^ separate  (string ";") (List.map (function (pat0) -> string "(" ^^ pp_raw_pat pat0 ^^ string ")") pat0) ^^ string "]" ^^ string ")"
| P_aux(P_tup(pat0),ott_menhir_loc) ->  string "[" ^^ string (pp_raw_l ott_menhir_loc) ^^ string "]" ^^ string "P_tup" ^^ string "(" ^^ string "[" ^^ separate  (string ";") (List.map (function (pat0) -> string "(" ^^ pp_raw_pat pat0 ^^ string ")") pat0) ^^ string "]" ^^ string ")"
| P_aux(P_list(pat0),ott_menhir_loc) ->  string "[" ^^ string (pp_raw_l ott_menhir_loc) ^^ string "]" ^^ string "P_list" ^^ string "(" ^^ string "[" ^^ separate  (string ";") (List.map (function (pat0) -> string "(" ^^ pp_raw_pat pat0 ^^ string ")") pat0) ^^ string "]" ^^ string ")"
| P_aux(P_cons(pat1,pat2),ott_menhir_loc) ->  string "[" ^^ string (pp_raw_l ott_menhir_loc) ^^ string "]" ^^ string "P_cons" ^^ string "(" ^^ pp_raw_pat pat1 ^^ string "," ^^ pp_raw_pat pat2 ^^ string ")"
| P_aux(P_string_append(pat0),ott_menhir_loc) ->  string "[" ^^ string (pp_raw_l ott_menhir_loc) ^^ string "]" ^^ string "P_string_append" ^^ string "(" ^^ string "[" ^^ separate  (string ";") (List.map (function (pat0) -> string "(" ^^ pp_raw_pat pat0 ^^ string ")") pat0) ^^ string "]" ^^ string ")"

and pp_raw_pat x = match x with
| P_aux(pat_aux,annot) -> string "P_aux" ^^ string "(" ^^ pp_raw_pat_aux pat_aux ^^ string "," ^^ pp_raw_annot annot ^^ string ")"

and pp_raw_loop_default 

and pp_raw_internal_loop_measure_aux x = match x with
| Measure_aux(Measure_none,ott_menhir_loc) ->  string "[" ^^ string (pp_raw_l ott_menhir_loc) ^^ string "]" ^^ string "Measure_none"
| Measure_aux(Measure_some(exp),ott_menhir_loc) ->  string "[" ^^ string (pp_raw_l ott_menhir_loc) ^^ string "]" ^^ string "Measure_some" ^^ string "(" ^^ pp_raw_exp exp ^^ string ")"

and pp_raw_internal_loop_measure x = match x with
| Measure_aux(internal_loop_measure_aux,l) -> string "Measure_aux" ^^ string "(" ^^ pp_raw_internal_loop_measure_aux internal_loop_measure_aux ^^ string "," ^^ pp_raw_l l ^^ string ")"

and pp_raw_exp_aux x = match x with
| E_aux(E_block(exp0),ott_menhir_loc) ->  string "[" ^^ string (pp_raw_l ott_menhir_loc) ^^ string "]" ^^ string "E_block" ^^ string "(" ^^ string "[" ^^ separate  (string ";") (List.map (function (exp0) -> string "(" ^^ pp_raw_exp exp0 ^^ string ")") exp0) ^^ string "]" ^^ string ")"
| E_aux(E_id(id),ott_menhir_loc) ->  string "[" ^^ string (pp_raw_l ott_menhir_loc) ^^ string "]" ^^ string "E_id" ^^ string "(" ^^ pp_raw_id id ^^ string ")"
| E_aux(E_lit(lit),ott_menhir_loc) ->  string "[" ^^ string (pp_raw_l ott_menhir_loc) ^^ string "]" ^^ string "E_lit" ^^ string "(" ^^ pp_raw_lit lit ^^ string ")"
| E_aux(E_cast(typ,exp),ott_menhir_loc) ->  string "[" ^^ string (pp_raw_l ott_menhir_loc) ^^ string "]" ^^ string "E_cast" ^^ string "(" ^^ pp_raw_typ typ ^^ string "," ^^ pp_raw_exp exp ^^ string ")"
| E_aux(E_app(id,exp0),ott_menhir_loc) ->  string "[" ^^ string (pp_raw_l ott_menhir_loc) ^^ string "]" ^^ string "E_app" ^^ string "(" ^^ pp_raw_id id ^^ string "," ^^ string "[" ^^ separate  (string ";") (List.map (function (exp0) -> string "(" ^^ pp_raw_exp exp0 ^^ string ")") exp0) ^^ string "]" ^^ string ")"
| E_aux(E_app_infix(exp1,id,exp2),ott_menhir_loc) ->  string "[" ^^ string (pp_raw_l ott_menhir_loc) ^^ string "]" ^^ string "E_app_infix" ^^ string "(" ^^ pp_raw_exp exp1 ^^ string "," ^^ pp_raw_id id ^^ string "," ^^ pp_raw_exp exp2 ^^ string ")"
| E_aux(E_tuple(exp0),ott_menhir_loc) ->  string "[" ^^ string (pp_raw_l ott_menhir_loc) ^^ string "]" ^^ string "E_tuple" ^^ string "(" ^^ string "[" ^^ separate  (string ";") (List.map (function (exp0) -> string "(" ^^ pp_raw_exp exp0 ^^ string ")") exp0) ^^ string "]" ^^ string ")"
| E_aux(E_if(exp1,exp2,exp3),ott_menhir_loc) ->  string "[" ^^ string (pp_raw_l ott_menhir_loc) ^^ string "]" ^^ string "E_if" ^^ string "(" ^^ pp_raw_exp exp1 ^^ string "," ^^ pp_raw_exp exp2 ^^ string "," ^^ pp_raw_exp exp3 ^^ string ")"
| E_aux(E_loop(loop,internal_loop_measure,exp1,exp2),ott_menhir_loc) ->  string "[" ^^ string (pp_raw_l ott_menhir_loc) ^^ string "]" ^^ string "E_loop" ^^ string "(" ^^ pp_raw_loop loop ^^ string "," ^^ pp_raw_internal_loop_measure internal_loop_measure ^^ string "," ^^ pp_raw_exp exp1 ^^ string "," ^^ pp_raw_exp exp2 ^^ string ")"
| E_aux(E_for(id,exp1,exp2,exp3,order,exp4),ott_menhir_loc) ->  string "[" ^^ string (pp_raw_l ott_menhir_loc) ^^ string "]" ^^ string "E_for" ^^ string "(" ^^ pp_raw_id id ^^ string "," ^^ pp_raw_exp exp1 ^^ string "," ^^ pp_raw_exp exp2 ^^ string "," ^^ pp_raw_exp exp3 ^^ string "," ^^ pp_raw_order order ^^ string "," ^^ pp_raw_exp exp4 ^^ string ")"
| E_aux(E_vector(exp0),ott_menhir_loc) ->  string "[" ^^ string (pp_raw_l ott_menhir_loc) ^^ string "]" ^^ string "E_vector" ^^ string "(" ^^ string "[" ^^ separate  (string ";") (List.map (function (exp0) -> string "(" ^^ pp_raw_exp exp0 ^^ string ")") exp0) ^^ string "]" ^^ string ")"
| E_aux(E_vector_access(exp,exp_prime),ott_menhir_loc) ->  string "[" ^^ string (pp_raw_l ott_menhir_loc) ^^ string "]" ^^ string "E_vector_access" ^^ string "(" ^^ pp_raw_exp exp ^^ string "," ^^ pp_raw_exp exp_prime ^^ string ")"
| E_aux(E_vector_subrange(exp,exp1,exp2),ott_menhir_loc) ->  string "[" ^^ string (pp_raw_l ott_menhir_loc) ^^ string "]" ^^ string "E_vector_subrange" ^^ string "(" ^^ pp_raw_exp exp ^^ string "," ^^ pp_raw_exp exp1 ^^ string "," ^^ pp_raw_exp exp2 ^^ string ")"
| E_aux(E_vector_update(exp,exp1,exp2),ott_menhir_loc) ->  string "[" ^^ string (pp_raw_l ott_menhir_loc) ^^ string "]" ^^ string "E_vector_update" ^^ string "(" ^^ pp_raw_exp exp ^^ string "," ^^ pp_raw_exp exp1 ^^ string "," ^^ pp_raw_exp exp2 ^^ string ")"
| E_aux(E_vector_update_subrange(exp,exp1,exp2,exp3),ott_menhir_loc) ->  string "[" ^^ string (pp_raw_l ott_menhir_loc) ^^ string "]" ^^ string "E_vector_update_subrange" ^^ string "(" ^^ pp_raw_exp exp ^^ string "," ^^ pp_raw_exp exp1 ^^ string "," ^^ pp_raw_exp exp2 ^^ string "," ^^ pp_raw_exp exp3 ^^ string ")"
| E_aux(E_vector_append(exp1,exp2),ott_menhir_loc) ->  string "[" ^^ string (pp_raw_l ott_menhir_loc) ^^ string "]" ^^ string "E_vector_append" ^^ string "(" ^^ pp_raw_exp exp1 ^^ string "," ^^ pp_raw_exp exp2 ^^ string ")"
| E_aux(E_list(exp0),ott_menhir_loc) ->  string "[" ^^ string (pp_raw_l ott_menhir_loc) ^^ string "]" ^^ string "E_list" ^^ string "(" ^^ string "[" ^^ separate  (string ";") (List.map (function (exp0) -> string "(" ^^ pp_raw_exp exp0 ^^ string ")") exp0) ^^ string "]" ^^ string ")"
| E_aux(E_cons(exp1,exp2),ott_menhir_loc) ->  string "[" ^^ string (pp_raw_l ott_menhir_loc) ^^ string "]" ^^ string "E_cons" ^^ string "(" ^^ pp_raw_exp exp1 ^^ string "," ^^ pp_raw_exp exp2 ^^ string ")"
| E_aux(E_record(fexp0),ott_menhir_loc) ->  string "[" ^^ string (pp_raw_l ott_menhir_loc) ^^ string "]" ^^ string "E_record" ^^ string "(" ^^ string "[" ^^ separate  (string ";") (List.map (function (fexp0) -> string "(" ^^ pp_raw_fexp fexp0 ^^ string ")") fexp0) ^^ string "]" ^^ string ")"
| E_aux(E_record_update(exp,fexp0),ott_menhir_loc) ->  string "[" ^^ string (pp_raw_l ott_menhir_loc) ^^ string "]" ^^ string "E_record_update" ^^ string "(" ^^ pp_raw_exp exp ^^ string "," ^^ string "[" ^^ separate  (string ";") (List.map (function (fexp0) -> string "(" ^^ pp_raw_fexp fexp0 ^^ string ")") fexp0) ^^ string "]" ^^ string ")"
| E_aux(E_field(exp,id),ott_menhir_loc) ->  string "[" ^^ string (pp_raw_l ott_menhir_loc) ^^ string "]" ^^ string "E_field" ^^ string "(" ^^ pp_raw_exp exp ^^ string "," ^^ pp_raw_id id ^^ string ")"
| E_aux(E_case(exp,pexp0),ott_menhir_loc) ->  string "[" ^^ string (pp_raw_l ott_menhir_loc) ^^ string "]" ^^ string "E_case" ^^ string "(" ^^ pp_raw_exp exp ^^ string "," ^^ string "[" ^^ separate  (string ";") (List.map (function (pexp0) -> string "(" ^^ pp_raw_pexp pexp0 ^^ string ")") pexp0) ^^ string "]" ^^ string ")"
| E_aux(E_let(letbind,exp),ott_menhir_loc) ->  string "[" ^^ string (pp_raw_l ott_menhir_loc) ^^ string "]" ^^ string "E_let" ^^ string "(" ^^ pp_raw_letbind letbind ^^ string "," ^^ pp_raw_exp exp ^^ string ")"
| E_aux(E_assign(lexp,exp),ott_menhir_loc) ->  string "[" ^^ string (pp_raw_l ott_menhir_loc) ^^ string "]" ^^ string "E_assign" ^^ string "(" ^^ pp_raw_lexp lexp ^^ string "," ^^ pp_raw_exp exp ^^ string ")"
| E_aux(E_sizeof(nexp),ott_menhir_loc) ->  string "[" ^^ string (pp_raw_l ott_menhir_loc) ^^ string "]" ^^ string "E_sizeof" ^^ string "(" ^^ pp_raw_nexp nexp ^^ string ")"
| E_aux(E_return(exp),ott_menhir_loc) ->  string "[" ^^ string (pp_raw_l ott_menhir_loc) ^^ string "]" ^^ string "E_return" ^^ string "(" ^^ pp_raw_exp exp ^^ string ")"
| E_aux(E_exit(exp),ott_menhir_loc) ->  string "[" ^^ string (pp_raw_l ott_menhir_loc) ^^ string "]" ^^ string "E_exit" ^^ string "(" ^^ pp_raw_exp exp ^^ string ")"
| E_aux(E_ref(id),ott_menhir_loc) ->  string "[" ^^ string (pp_raw_l ott_menhir_loc) ^^ string "]" ^^ string "E_ref" ^^ string "(" ^^ pp_raw_id id ^^ string ")"
| E_aux(E_throw(exp),ott_menhir_loc) ->  string "[" ^^ string (pp_raw_l ott_menhir_loc) ^^ string "]" ^^ string "E_throw" ^^ string "(" ^^ pp_raw_exp exp ^^ string ")"
| E_aux(E_try(exp,pexp0),ott_menhir_loc) ->  string "[" ^^ string (pp_raw_l ott_menhir_loc) ^^ string "]" ^^ string "E_try" ^^ string "(" ^^ pp_raw_exp exp ^^ string "," ^^ string "[" ^^ separate  (string ";") (List.map (function (pexp0) -> string "(" ^^ pp_raw_pexp pexp0 ^^ string ")") pexp0) ^^ string "]" ^^ string ")"
| E_aux(E_assert(exp,exp_prime),ott_menhir_loc) ->  string "[" ^^ string (pp_raw_l ott_menhir_loc) ^^ string "]" ^^ string "E_assert" ^^ string "(" ^^ pp_raw_exp exp ^^ string "," ^^ pp_raw_exp exp_prime ^^ string ")"
| E_aux(E_var(lexp,exp,exp_prime),ott_menhir_loc) ->  string "[" ^^ string (pp_raw_l ott_menhir_loc) ^^ string "]" ^^ string "E_var" ^^ string "(" ^^ pp_raw_lexp lexp ^^ string "," ^^ pp_raw_exp exp ^^ string "," ^^ pp_raw_exp exp_prime ^^ string ")"
| E_aux(E_internal_plet(pat,exp,exp_prime),ott_menhir_loc) ->  string "[" ^^ string (pp_raw_l ott_menhir_loc) ^^ string "]" ^^ string "E_internal_plet" ^^ string "(" ^^ pp_raw_pat pat ^^ string "," ^^ pp_raw_exp exp ^^ string "," ^^ pp_raw_exp exp_prime ^^ string ")"
| E_aux(E_internal_return(exp),ott_menhir_loc) ->  string "[" ^^ string (pp_raw_l ott_menhir_loc) ^^ string "]" ^^ string "E_internal_return" ^^ string "(" ^^ pp_raw_exp exp ^^ string ")"
| E_aux(E_internal_value(value),ott_menhir_loc) ->  string "[" ^^ string (pp_raw_l ott_menhir_loc) ^^ string "]" ^^ string "E_internal_value" ^^ string "(" ^^  string "\"" ^^ string value ^^ string "\"" ^^ string ")"
| E_aux(E_constraint(n_constraint),ott_menhir_loc) ->  string "[" ^^ string (pp_raw_l ott_menhir_loc) ^^ string "]" ^^ string "E_constraint" ^^ string "(" ^^ pp_raw_n_constraint n_constraint ^^ string ")"

and pp_raw_exp x = match x with
| E_aux(exp_aux,annot) -> string "E_aux" ^^ string "(" ^^ pp_raw_exp_aux exp_aux ^^ string "," ^^ pp_raw_annot annot ^^ string ")"

and pp_raw_lexp_aux x = match x with
| LEXP_aux(LEXP_id(id),ott_menhir_loc) ->  string "[" ^^ string (pp_raw_l ott_menhir_loc) ^^ string "]" ^^ string "LEXP_id" ^^ string "(" ^^ pp_raw_id id ^^ string ")"
| LEXP_aux(LEXP_deref(exp),ott_menhir_loc) ->  string "[" ^^ string (pp_raw_l ott_menhir_loc) ^^ string "]" ^^ string "LEXP_deref" ^^ string "(" ^^ pp_raw_exp exp ^^ string ")"
| LEXP_aux(LEXP_memory(id,exp0),ott_menhir_loc) ->  string "[" ^^ string (pp_raw_l ott_menhir_loc) ^^ string "]" ^^ string "LEXP_memory" ^^ string "(" ^^ pp_raw_id id ^^ string "," ^^ string "[" ^^ separate  (string ";") (List.map (function (exp0) -> string "(" ^^ pp_raw_exp exp0 ^^ string ")") exp0) ^^ string "]" ^^ string ")"
| LEXP_aux(LEXP_cast(typ,id),ott_menhir_loc) ->  string "[" ^^ string (pp_raw_l ott_menhir_loc) ^^ string "]" ^^ string "LEXP_cast" ^^ string "(" ^^ pp_raw_typ typ ^^ string "," ^^ pp_raw_id id ^^ string ")"
| LEXP_aux(LEXP_tup(lexp0),ott_menhir_loc) ->  string "[" ^^ string (pp_raw_l ott_menhir_loc) ^^ string "]" ^^ string "LEXP_tup" ^^ string "(" ^^ string "[" ^^ separate  (string ";") (List.map (function (lexp0) -> string "(" ^^ pp_raw_lexp lexp0 ^^ string ")") lexp0) ^^ string "]" ^^ string ")"
| LEXP_aux(LEXP_vector_concat(lexp0),ott_menhir_loc) ->  string "[" ^^ string (pp_raw_l ott_menhir_loc) ^^ string "]" ^^ string "LEXP_vector_concat" ^^ string "(" ^^ string "[" ^^ separate  (string ";") (List.map (function (lexp0) -> string "(" ^^ pp_raw_lexp lexp0 ^^ string ")") lexp0) ^^ string "]" ^^ string ")"
| LEXP_aux(LEXP_vector(lexp,exp),ott_menhir_loc) ->  string "[" ^^ string (pp_raw_l ott_menhir_loc) ^^ string "]" ^^ string "LEXP_vector" ^^ string "(" ^^ pp_raw_lexp lexp ^^ string "," ^^ pp_raw_exp exp ^^ string ")"
| LEXP_aux(LEXP_vector_range(lexp,exp1,exp2),ott_menhir_loc) ->  string "[" ^^ string (pp_raw_l ott_menhir_loc) ^^ string "]" ^^ string "LEXP_vector_range" ^^ string "(" ^^ pp_raw_lexp lexp ^^ string "," ^^ pp_raw_exp exp1 ^^ string "," ^^ pp_raw_exp exp2 ^^ string ")"
| LEXP_aux(LEXP_field(lexp,id),ott_menhir_loc) ->  string "[" ^^ string (pp_raw_l ott_menhir_loc) ^^ string "]" ^^ string "LEXP_field" ^^ string "(" ^^ pp_raw_lexp lexp ^^ string "," ^^ pp_raw_id id ^^ string ")"

and pp_raw_lexp x = match x with
| LEXP_aux(lexp_aux,annot) -> string "LEXP_aux" ^^ string "(" ^^ pp_raw_lexp_aux lexp_aux ^^ string "," ^^ pp_raw_annot annot ^^ string ")"

and pp_raw_fexp_aux x = match x with
| FE_aux(FE_Fexp(id,exp),ott_menhir_loc) ->  string "[" ^^ string (pp_raw_l ott_menhir_loc) ^^ string "]" ^^ string "FE_Fexp" ^^ string "(" ^^ pp_raw_id id ^^ string "," ^^ pp_raw_exp exp ^^ string ")"

and pp_raw_fexp x = match x with
| FE_aux(fexp_aux,annot) -> string "FE_aux" ^^ string "(" ^^ pp_raw_fexp_aux fexp_aux ^^ string "," ^^ pp_raw_annot annot ^^ string ")"

and pp_raw_opt_default_aux x = match x with
| Def_val_aux(Def_val_empty,ott_menhir_loc) ->  string "[" ^^ string (pp_raw_l ott_menhir_loc) ^^ string "]" ^^ string "Def_val_empty"
| Def_val_aux(Def_val_dec(exp),ott_menhir_loc) ->  string "[" ^^ string (pp_raw_l ott_menhir_loc) ^^ string "]" ^^ string "Def_val_dec" ^^ string "(" ^^ pp_raw_exp exp ^^ string ")"

and pp_raw_opt_default x = match x with
| Def_val_aux(opt_default_aux,annot) -> string "Def_val_aux" ^^ string "(" ^^ pp_raw_opt_default_aux opt_default_aux ^^ string "," ^^ pp_raw_annot annot ^^ string ")"

and pp_raw_pexp_aux x = match x with
| Pat_aux(Pat_exp(pat,exp),ott_menhir_loc) ->  string "[" ^^ string (pp_raw_l ott_menhir_loc) ^^ string "]" ^^ string "Pat_exp" ^^ string "(" ^^ pp_raw_pat pat ^^ string "," ^^ pp_raw_exp exp ^^ string ")"
| Pat_aux(Pat_when(pat,exp1,exp),ott_menhir_loc) ->  string "[" ^^ string (pp_raw_l ott_menhir_loc) ^^ string "]" ^^ string "Pat_when" ^^ string "(" ^^ pp_raw_pat pat ^^ string "," ^^ pp_raw_exp exp1 ^^ string "," ^^ pp_raw_exp exp ^^ string ")"

and pp_raw_pexp x = match x with
| Pat_aux(pexp_aux,annot) -> string "Pat_aux" ^^ string "(" ^^ pp_raw_pexp_aux pexp_aux ^^ string "," ^^ pp_raw_annot annot ^^ string ")"

and pp_raw_tannot_opt_aux x = match x with
| Typ_annot_opt_aux(Typ_annot_opt_none,ott_menhir_loc) ->  string "[" ^^ string (pp_raw_l ott_menhir_loc) ^^ string "]" ^^ string "Typ_annot_opt_none"
| Typ_annot_opt_aux(Typ_annot_opt_some(typquant,typ),ott_menhir_loc) ->  string "[" ^^ string (pp_raw_l ott_menhir_loc) ^^ string "]" ^^ string "Typ_annot_opt_some" ^^ string "(" ^^ pp_raw_typquant typquant ^^ string "," ^^ pp_raw_typ typ ^^ string ")"

and pp_raw_tannot_opt x = match x with
| Typ_annot_opt_aux(tannot_opt_aux,l) -> string "Typ_annot_opt_aux" ^^ string "(" ^^ pp_raw_tannot_opt_aux tannot_opt_aux ^^ string "," ^^ pp_raw_l l ^^ string ")"

and pp_raw_rec_opt_aux x = match x with
| Rec_aux(Rec_nonrec,ott_menhir_loc) ->  string "[" ^^ string (pp_raw_l ott_menhir_loc) ^^ string "]" ^^ string "Rec_nonrec"
| Rec_aux(Rec_rec,ott_menhir_loc) ->  string "[" ^^ string (pp_raw_l ott_menhir_loc) ^^ string "]" ^^ string "Rec_rec"
| Rec_aux(Rec_measure(pat,exp),ott_menhir_loc) ->  string "[" ^^ string (pp_raw_l ott_menhir_loc) ^^ string "]" ^^ string "Rec_measure" ^^ string "(" ^^ pp_raw_pat pat ^^ string "," ^^ pp_raw_exp exp ^^ string ")"

and pp_raw_rec_opt x = match x with
| Rec_aux(rec_opt_aux,l) -> string "Rec_aux" ^^ string "(" ^^ pp_raw_rec_opt_aux rec_opt_aux ^^ string "," ^^ pp_raw_l l ^^ string ")"

and pp_raw_effect_opt_aux x = match x with
| Effect_opt_aux(Effect_opt_none,ott_menhir_loc) ->  string "[" ^^ string (pp_raw_l ott_menhir_loc) ^^ string "]" ^^ string "Effect_opt_none"
| Effect_opt_aux(Effect_opt_effect(effect),ott_menhir_loc) ->  string "[" ^^ string (pp_raw_l ott_menhir_loc) ^^ string "]" ^^ string "Effect_opt_effect" ^^ string "(" ^^ pp_raw_effect effect ^^ string ")"

and pp_raw_effect_opt x = match x with
| Effect_opt_aux(effect_opt_aux,l) -> string "Effect_opt_aux" ^^ string "(" ^^ pp_raw_effect_opt_aux effect_opt_aux ^^ string "," ^^ pp_raw_l l ^^ string ")"

and pp_raw_pexp_funcl x = match x with
| Pat_funcl_exp(pat,exp) -> string "Pat_funcl_exp" ^^ string "(" ^^ pp_raw_pat pat ^^ string "," ^^ pp_raw_exp exp ^^ string ")"
| Pat_funcl_when(pat,exp1,exp) -> string "Pat_funcl_when" ^^ string "(" ^^ pp_raw_pat pat ^^ string "," ^^ pp_raw_exp exp1 ^^ string "," ^^ pp_raw_exp exp ^^ string ")"

and pp_raw_funcl_aux x = match x with
| FCL_aux(FCL_Funcl(id,pexp_funcl),ott_menhir_loc) ->  string "[" ^^ string (pp_raw_l ott_menhir_loc) ^^ string "]" ^^ string "FCL_Funcl" ^^ string "(" ^^ pp_raw_id id ^^ string "," ^^ pp_raw_pexp_funcl pexp_funcl ^^ string ")"

and pp_raw_funcl x = match x with
| FCL_aux(funcl_aux,annot) -> string "FCL_aux" ^^ string "(" ^^ pp_raw_funcl_aux funcl_aux ^^ string "," ^^ pp_raw_annot annot ^^ string ")"

and pp_raw_fundef_aux x = match x with
| FD_aux(FD_function(rec_opt,tannot_opt,effect_opt,funcl0),ott_menhir_loc) ->  string "[" ^^ string (pp_raw_l ott_menhir_loc) ^^ string "]" ^^ string "FD_function" ^^ string "(" ^^ pp_raw_rec_opt rec_opt ^^ string "," ^^ pp_raw_tannot_opt tannot_opt ^^ string "," ^^ pp_raw_effect_opt effect_opt ^^ string "," ^^ string "[" ^^ separate  (string ";") (List.map (function (funcl0) -> string "(" ^^ pp_raw_funcl funcl0 ^^ string ")") funcl0) ^^ string "]" ^^ string ")"

and pp_raw_fundef x = match x with
| FD_aux(fundef_aux,annot) -> string "FD_aux" ^^ string "(" ^^ pp_raw_fundef_aux fundef_aux ^^ string "," ^^ pp_raw_annot annot ^^ string ")"

and pp_raw_mpat_aux x = match x with
| MP_aux(MP_lit(lit),ott_menhir_loc) ->  string "[" ^^ string (pp_raw_l ott_menhir_loc) ^^ string "]" ^^ string "MP_lit" ^^ string "(" ^^ pp_raw_lit lit ^^ string ")"
| MP_aux(MP_id(id),ott_menhir_loc) ->  string "[" ^^ string (pp_raw_l ott_menhir_loc) ^^ string "]" ^^ string "MP_id" ^^ string "(" ^^ pp_raw_id id ^^ string ")"
| MP_aux(MP_app(id,mpat0),ott_menhir_loc) ->  string "[" ^^ string (pp_raw_l ott_menhir_loc) ^^ string "]" ^^ string "MP_app" ^^ string "(" ^^ pp_raw_id id ^^ string "," ^^ string "[" ^^ separate  (string ";") (List.map (function (mpat0) -> string "(" ^^ pp_raw_mpat mpat0 ^^ string ")") mpat0) ^^ string "]" ^^ string ")"
| MP_aux(MP_vector(mpat0),ott_menhir_loc) ->  string "[" ^^ string (pp_raw_l ott_menhir_loc) ^^ string "]" ^^ string "MP_vector" ^^ string "(" ^^ string "[" ^^ separate  (string ";") (List.map (function (mpat0) -> string "(" ^^ pp_raw_mpat mpat0 ^^ string ")") mpat0) ^^ string "]" ^^ string ")"
| MP_aux(MP_vector_concat(mpat0),ott_menhir_loc) ->  string "[" ^^ string (pp_raw_l ott_menhir_loc) ^^ string "]" ^^ string "MP_vector_concat" ^^ string "(" ^^ string "[" ^^ separate  (string ";") (List.map (function (mpat0) -> string "(" ^^ pp_raw_mpat mpat0 ^^ string ")") mpat0) ^^ string "]" ^^ string ")"
| MP_aux(MP_tup(mpat0),ott_menhir_loc) ->  string "[" ^^ string (pp_raw_l ott_menhir_loc) ^^ string "]" ^^ string "MP_tup" ^^ string "(" ^^ string "[" ^^ separate  (string ";") (List.map (function (mpat0) -> string "(" ^^ pp_raw_mpat mpat0 ^^ string ")") mpat0) ^^ string "]" ^^ string ")"
| MP_aux(MP_list(mpat0),ott_menhir_loc) ->  string "[" ^^ string (pp_raw_l ott_menhir_loc) ^^ string "]" ^^ string "MP_list" ^^ string "(" ^^ string "[" ^^ separate  (string ";") (List.map (function (mpat0) -> string "(" ^^ pp_raw_mpat mpat0 ^^ string ")") mpat0) ^^ string "]" ^^ string ")"
| MP_aux(MP_cons(mpat1,mpat2),ott_menhir_loc) ->  string "[" ^^ string (pp_raw_l ott_menhir_loc) ^^ string "]" ^^ string "MP_cons" ^^ string "(" ^^ pp_raw_mpat mpat1 ^^ string "," ^^ pp_raw_mpat mpat2 ^^ string ")"
| MP_aux(MP_string_append(mpat0),ott_menhir_loc) ->  string "[" ^^ string (pp_raw_l ott_menhir_loc) ^^ string "]" ^^ string "MP_string_append" ^^ string "(" ^^ string "[" ^^ separate  (string ";") (List.map (function (mpat0) -> string "(" ^^ pp_raw_mpat mpat0 ^^ string ")") mpat0) ^^ string "]" ^^ string ")"
| MP_aux(MP_typ(mpat,typ),ott_menhir_loc) ->  string "[" ^^ string (pp_raw_l ott_menhir_loc) ^^ string "]" ^^ string "MP_typ" ^^ string "(" ^^ pp_raw_mpat mpat ^^ string "," ^^ pp_raw_typ typ ^^ string ")"
| MP_aux(MP_as(mpat,id),ott_menhir_loc) ->  string "[" ^^ string (pp_raw_l ott_menhir_loc) ^^ string "]" ^^ string "MP_as" ^^ string "(" ^^ pp_raw_mpat mpat ^^ string "," ^^ pp_raw_id id ^^ string ")"

and pp_raw_mpat x = match x with
| MP_aux(mpat_aux,annot) -> string "MP_aux" ^^ string "(" ^^ pp_raw_mpat_aux mpat_aux ^^ string "," ^^ pp_raw_annot annot ^^ string ")"

and pp_raw_mpexp_aux x = match x with
| MPat_aux(MPat_pat(mpat),ott_menhir_loc) ->  string "[" ^^ string (pp_raw_l ott_menhir_loc) ^^ string "]" ^^ string "MPat_pat" ^^ string "(" ^^ pp_raw_mpat mpat ^^ string ")"
| MPat_aux(MPat_when(mpat,exp),ott_menhir_loc) ->  string "[" ^^ string (pp_raw_l ott_menhir_loc) ^^ string "]" ^^ string "MPat_when" ^^ string "(" ^^ pp_raw_mpat mpat ^^ string "," ^^ pp_raw_exp exp ^^ string ")"

and pp_raw_mpexp x = match x with
| MPat_aux(mpexp_aux,annot) -> string "MPat_aux" ^^ string "(" ^^ pp_raw_mpexp_aux mpexp_aux ^^ string "," ^^ pp_raw_annot annot ^^ string ")"

and pp_raw_mapcl_aux x = match x with
| MCL_aux(MCL_bidir(mpexp1,mpexp2),ott_menhir_loc) ->  string "[" ^^ string (pp_raw_l ott_menhir_loc) ^^ string "]" ^^ string "MCL_bidir" ^^ string "(" ^^ pp_raw_mpexp mpexp1 ^^ string "," ^^ pp_raw_mpexp mpexp2 ^^ string ")"
| MCL_aux(MCL_forwards(mpexp,exp),ott_menhir_loc) ->  string "[" ^^ string (pp_raw_l ott_menhir_loc) ^^ string "]" ^^ string "MCL_forwards" ^^ string "(" ^^ pp_raw_mpexp mpexp ^^ string "," ^^ pp_raw_exp exp ^^ string ")"
| MCL_aux(MCL_backwards(mpexp,exp),ott_menhir_loc) ->  string "[" ^^ string (pp_raw_l ott_menhir_loc) ^^ string "]" ^^ string "MCL_backwards" ^^ string "(" ^^ pp_raw_mpexp mpexp ^^ string "," ^^ pp_raw_exp exp ^^ string ")"

and pp_raw_mapcl x = match x with
| MCL_aux(mapcl_aux,annot) -> string "MCL_aux" ^^ string "(" ^^ pp_raw_mapcl_aux mapcl_aux ^^ string "," ^^ pp_raw_annot annot ^^ string ")"

and pp_raw_mapdef_aux x = match x with
| MD_aux(MD_mapping(id,tannot_opt,mapcl0),ott_menhir_loc) ->  string "[" ^^ string (pp_raw_l ott_menhir_loc) ^^ string "]" ^^ string "MD_mapping" ^^ string "(" ^^ pp_raw_id id ^^ string "," ^^ pp_raw_tannot_opt tannot_opt ^^ string "," ^^ string "[" ^^ separate  (string ";") (List.map (function (mapcl0) -> string "(" ^^ pp_raw_mapcl mapcl0 ^^ string ")") mapcl0) ^^ string "]" ^^ string ")"

and pp_raw_mapdef x = match x with
| MD_aux(mapdef_aux,annot) -> string "MD_aux" ^^ string "(" ^^ pp_raw_mapdef_aux mapdef_aux ^^ string "," ^^ pp_raw_annot annot ^^ string ")"

and pp_raw_letbind_aux x = match x with
| LB_aux(LB_val(pat,exp),ott_menhir_loc) ->  string "[" ^^ string (pp_raw_l ott_menhir_loc) ^^ string "]" ^^ string "LB_val" ^^ string "(" ^^ pp_raw_pat pat ^^ string "," ^^ pp_raw_exp exp ^^ string ")"

and pp_raw_letbind x = match x with
| LB_aux(letbind_aux,annot) -> string "LB_aux" ^^ string "(" ^^ pp_raw_letbind_aux letbind_aux ^^ string "," ^^ pp_raw_annot annot ^^ string ")"

and pp_raw_val_spec x = match x with
| VS_aux(val_spec_aux) -> string "VS_aux" ^^ string "(" ^^ pp_raw_val_spec_aux val_spec_aux ^^ string ")"

and pp_raw_val_spec_aux x = match x with

and pp_raw_default_spec_aux x = match x with
| DT_aux(DT_order(order),ott_menhir_loc) ->  string "[" ^^ string (pp_raw_l ott_menhir_loc) ^^ string "]" ^^ string "DT_order" ^^ string "(" ^^ pp_raw_order order ^^ string ")"

and pp_raw_default_spec x = match x with
| DT_aux(default_spec_aux,l) -> string "DT_aux" ^^ string "(" ^^ pp_raw_default_spec_aux default_spec_aux ^^ string "," ^^ pp_raw_l l ^^ string ")"

and pp_raw_scattered_def_aux x = match x with
| SD_aux(SD_function(rec_opt,tannot_opt,effect_opt,id),ott_menhir_loc) ->  string "[" ^^ string (pp_raw_l ott_menhir_loc) ^^ string "]" ^^ string "SD_function" ^^ string "(" ^^ pp_raw_rec_opt rec_opt ^^ string "," ^^ pp_raw_tannot_opt tannot_opt ^^ string "," ^^ pp_raw_effect_opt effect_opt ^^ string "," ^^ pp_raw_id id ^^ string ")"
| SD_aux(SD_funcl(funcl),ott_menhir_loc) ->  string "[" ^^ string (pp_raw_l ott_menhir_loc) ^^ string "]" ^^ string "SD_funcl" ^^ string "(" ^^ pp_raw_funcl funcl ^^ string ")"
| SD_aux(SD_variant(id,typquant),ott_menhir_loc) ->  string "[" ^^ string (pp_raw_l ott_menhir_loc) ^^ string "]" ^^ string "SD_variant" ^^ string "(" ^^ pp_raw_id id ^^ string "," ^^ pp_raw_typquant typquant ^^ string ")"
| SD_aux(SD_unioncl(id,type_union),ott_menhir_loc) ->  string "[" ^^ string (pp_raw_l ott_menhir_loc) ^^ string "]" ^^ string "SD_unioncl" ^^ string "(" ^^ pp_raw_id id ^^ string "," ^^ pp_raw_type_union type_union ^^ string ")"
| SD_aux(SD_mapping(id,tannot_opt),ott_menhir_loc) ->  string "[" ^^ string (pp_raw_l ott_menhir_loc) ^^ string "]" ^^ string "SD_mapping" ^^ string "(" ^^ pp_raw_id id ^^ string "," ^^ pp_raw_tannot_opt tannot_opt ^^ string ")"
| SD_aux(SD_mapcl(id,mapcl),ott_menhir_loc) ->  string "[" ^^ string (pp_raw_l ott_menhir_loc) ^^ string "]" ^^ string "SD_mapcl" ^^ string "(" ^^ pp_raw_id id ^^ string "," ^^ pp_raw_mapcl mapcl ^^ string ")"
| SD_aux(SD_end(id),ott_menhir_loc) ->  string "[" ^^ string (pp_raw_l ott_menhir_loc) ^^ string "]" ^^ string "SD_end" ^^ string "(" ^^ pp_raw_id id ^^ string ")"

and pp_raw_scattered_def x = match x with
| SD_aux(scattered_def_aux,annot) -> string "SD_aux" ^^ string "(" ^^ pp_raw_scattered_def_aux scattered_def_aux ^^ string "," ^^ pp_raw_annot annot ^^ string ")"

and pp_raw_reg_id_aux x = match x with
| RI_aux(RI_id(id),ott_menhir_loc) ->  string "[" ^^ string (pp_raw_l ott_menhir_loc) ^^ string "]" ^^ string "RI_id" ^^ string "(" ^^ pp_raw_id id ^^ string ")"

and pp_raw_reg_id x = match x with
| RI_aux(reg_id_aux,annot) -> string "RI_aux" ^^ string "(" ^^ pp_raw_reg_id_aux reg_id_aux ^^ string "," ^^ pp_raw_annot annot ^^ string ")"

and pp_raw_alias_spec_aux x = match x with
| AL_aux(AL_subreg(reg_id,id),ott_menhir_loc) ->  string "[" ^^ string (pp_raw_l ott_menhir_loc) ^^ string "]" ^^ string "AL_subreg" ^^ string "(" ^^ pp_raw_reg_id reg_id ^^ string "," ^^ pp_raw_id id ^^ string ")"
| AL_aux(AL_bit(reg_id,exp),ott_menhir_loc) ->  string "[" ^^ string (pp_raw_l ott_menhir_loc) ^^ string "]" ^^ string "AL_bit" ^^ string "(" ^^ pp_raw_reg_id reg_id ^^ string "," ^^ pp_raw_exp exp ^^ string ")"
| AL_aux(AL_slice(reg_id,exp,exp_prime),ott_menhir_loc) ->  string "[" ^^ string (pp_raw_l ott_menhir_loc) ^^ string "]" ^^ string "AL_slice" ^^ string "(" ^^ pp_raw_reg_id reg_id ^^ string "," ^^ pp_raw_exp exp ^^ string "," ^^ pp_raw_exp exp_prime ^^ string ")"
| AL_aux(AL_concat(reg_id,reg_id_prime),ott_menhir_loc) ->  string "[" ^^ string (pp_raw_l ott_menhir_loc) ^^ string "]" ^^ string "AL_concat" ^^ string "(" ^^ pp_raw_reg_id reg_id ^^ string "," ^^ pp_raw_reg_id reg_id_prime ^^ string ")"

and pp_raw_alias_spec x = match x with
| AL_aux(alias_spec_aux,annot) -> string "AL_aux" ^^ string "(" ^^ pp_raw_alias_spec_aux alias_spec_aux ^^ string "," ^^ pp_raw_annot annot ^^ string ")"

and pp_raw_dec_spec_aux x = match x with
| DEC_aux(DEC_reg(effect,effect_prime,typ,id),ott_menhir_loc) ->  string "[" ^^ string (pp_raw_l ott_menhir_loc) ^^ string "]" ^^ string "DEC_reg" ^^ string "(" ^^ pp_raw_effect effect ^^ string "," ^^ pp_raw_effect effect_prime ^^ string "," ^^ pp_raw_typ typ ^^ string "," ^^ pp_raw_id id ^^ string ")"
| DEC_aux(DEC_config(id,typ,exp),ott_menhir_loc) ->  string "[" ^^ string (pp_raw_l ott_menhir_loc) ^^ string "]" ^^ string "DEC_config" ^^ string "(" ^^ pp_raw_id id ^^ string "," ^^ pp_raw_typ typ ^^ string "," ^^ pp_raw_exp exp ^^ string ")"
| DEC_aux(DEC_alias(id,alias_spec),ott_menhir_loc) ->  string "[" ^^ string (pp_raw_l ott_menhir_loc) ^^ string "]" ^^ string "DEC_alias" ^^ string "(" ^^ pp_raw_id id ^^ string "," ^^ pp_raw_alias_spec alias_spec ^^ string ")"
| DEC_aux(DEC_typ_alias(typ,id,alias_spec),ott_menhir_loc) ->  string "[" ^^ string (pp_raw_l ott_menhir_loc) ^^ string "]" ^^ string "DEC_typ_alias" ^^ string "(" ^^ pp_raw_typ typ ^^ string "," ^^ pp_raw_id id ^^ string "," ^^ pp_raw_alias_spec alias_spec ^^ string ")"

and pp_raw_dec_spec x = match x with
| DEC_aux(dec_spec_aux,annot) -> string "DEC_aux" ^^ string "(" ^^ pp_raw_dec_spec_aux dec_spec_aux ^^ string "," ^^ pp_raw_annot annot ^^ string ")"

and pp_raw_prec x = match x with
| Infix -> string "Infix"
| InfixL -> string "InfixL"
| InfixR -> string "InfixR"

and pp_raw_loop_measure x = match x with
| Loop(loop,exp) -> string "Loop" ^^ string "(" ^^ pp_raw_loop loop ^^ string "," ^^ pp_raw_exp exp ^^ string ")"

and pp_raw_def x = match x with
| DEF_type(type_def) -> string "DEF_type" ^^ string "(" ^^ pp_raw_type_def type_def ^^ string ")"
| DEF_fundef(fundef) -> string "DEF_fundef" ^^ string "(" ^^ pp_raw_fundef fundef ^^ string ")"
| DEF_mapdef(mapdef) -> string "DEF_mapdef" ^^ string "(" ^^ pp_raw_mapdef mapdef ^^ string ")"
| DEF_val(letbind) -> string "DEF_val" ^^ string "(" ^^ pp_raw_letbind letbind ^^ string ")"
| DEF_spec(val_spec) -> string "DEF_spec" ^^ string "(" ^^ pp_raw_val_spec val_spec ^^ string ")"
| DEF_fixity(prec,num,id) -> string "DEF_fixity" ^^ string "(" ^^ pp_raw_prec prec ^^ string "," ^^  string "\"" ^^ string num ^^ string "\"" ^^ string "," ^^ pp_raw_id id ^^ string ")"
| DEF_overload(id,id0) -> string "DEF_overload" ^^ string "(" ^^ pp_raw_id id ^^ string "," ^^ string "[" ^^ separate  (string ";") (List.map (function (id0) -> string "(" ^^ pp_raw_id id0 ^^ string ")") id0) ^^ string "]" ^^ string ")"
| DEF_default(default_spec) -> string "DEF_default" ^^ string "(" ^^ pp_raw_default_spec default_spec ^^ string ")"
| DEF_scattered(scattered_def) -> string "DEF_scattered" ^^ string "(" ^^ pp_raw_scattered_def scattered_def ^^ string ")"
| DEF_measure(id,pat,exp) -> string "DEF_measure" ^^ string "(" ^^ pp_raw_id id ^^ string "," ^^ pp_raw_pat pat ^^ string "," ^^ pp_raw_exp exp ^^ string ")"
| DEF_loop_measures(id,loop_measure0) -> string "DEF_loop_measures" ^^ string "(" ^^ pp_raw_id id ^^ string "," ^^ string "[" ^^ separate  (string ";") (List.map (function (loop_measure0) -> string "(" ^^ pp_raw_loop_measure loop_measure0 ^^ string ")") loop_measure0) ^^ string "]" ^^ string ")"
| DEF_reg_dec(dec_spec) -> string "DEF_reg_dec" ^^ string "(" ^^ pp_raw_dec_spec dec_spec ^^ string ")"
| DEF_internal_mutrec(fundef0) -> string "DEF_internal_mutrec" ^^ string "(" ^^ string "[" ^^ separate  (string ";") (List.map (function (fundef0) -> string "(" ^^ pp_raw_fundef fundef0 ^^ string ")") fundef0) ^^ string "]" ^^ string ")"
| DEF_pragma(string1,string2,l) -> string "DEF_pragma" ^^ string "(" ^^  string "\"" ^^ string string1 ^^ string "\"" ^^ string "," ^^  string "\"" ^^ string string2 ^^ string "\"" ^^ string "," ^^ pp_raw_l l ^^ string ")"

and pp_raw_defs x = match x with
| Defs(def0) -> string "Defs" ^^ string "(" ^^ string "[" ^^ separate  (string ";") (List.map (function (def0) -> string "(" ^^ pp_raw_def def0 ^^ string ")") def0) ^^ string "]" ^^ string ")"


let rec pp_l_default 

and pp_id_aux x = match x with
| Id_aux_aux(Id(x),ott_menhir_loc) -> string x
| Id_aux_aux(Operator(x),ott_menhir_loc) -> string "(" ^^ string "(" ^^ string " " ^^ string "operator" ^^ string " " ^^ string x ^^ string " " ^^ string ")" ^^ string ")"

and pp_id x = match x with
| Id_aux(id_aux,l) -> string "(" ^^ pp_id_aux id_aux ^^ string " " ^^ pp_l l ^^ string ")"

and pp_kid_aux x = match x with
| Kid_aux_aux(Var(x),ott_menhir_loc) -> string "(" ^^ string "'" ^^ string " " ^^ string x ^^ string ")"

and pp_kid x = match x with
| Kid_aux(kid_aux,l) -> string "(" ^^ pp_kid_aux kid_aux ^^ string " " ^^ pp_l l ^^ string ")"

and pp_kind_aux x = match x with
| K_aux(K_type,ott_menhir_loc) -> string "Type"
| K_aux(K_int,ott_menhir_loc) -> string "Int"
| K_aux(K_order,ott_menhir_loc) -> string "Order"
| K_aux(K_bool,ott_menhir_loc) -> string "Bool"

and pp_kind x = match x with
| K_aux(kind_aux,l) -> string "(" ^^ pp_kind_aux kind_aux ^^ string " " ^^ pp_l l ^^ string ")"

and pp_nexp_aux x = match x with
| Nexp_aux(Nexp_id(id),ott_menhir_loc) -> pp_id id
| Nexp_aux(Nexp_var(kid),ott_menhir_loc) -> pp_kid kid
| Nexp_aux(Nexp_constant(num),ott_menhir_loc) -> string num
| Nexp_aux(Nexp_app(id,nexp0),ott_menhir_loc) -> string "(" ^^ pp_id id ^^ string " " ^^ string "(" ^^ string " " ^^ separate (string ",") (List.map (function (nexp0) -> pp_nexp nexp0) nexp0) ^^ string " " ^^ string ")" ^^ string ")"
| Nexp_aux(Nexp_times(nexp1,nexp2),ott_menhir_loc) -> string "(" ^^ pp_nexp nexp1 ^^ string " " ^^ string "*" ^^ string " " ^^ pp_nexp nexp2 ^^ string ")"
| Nexp_aux(Nexp_sum(nexp1,nexp2),ott_menhir_loc) -> string "(" ^^ pp_nexp nexp1 ^^ string " " ^^ string "+" ^^ string " " ^^ pp_nexp nexp2 ^^ string ")"
| Nexp_aux(Nexp_minus(nexp1,nexp2),ott_menhir_loc) -> string "(" ^^ pp_nexp nexp1 ^^ string " " ^^ string "-" ^^ string " " ^^ pp_nexp nexp2 ^^ string ")"
| Nexp_aux(Nexp_exp(nexp),ott_menhir_loc) -> string "(" ^^ string "2" ^^ string " " ^^ string "^" ^^ string " " ^^ pp_nexp nexp ^^ string ")"
| Nexp_aux(Nexp_neg(nexp),ott_menhir_loc) -> string "(" ^^ string "-" ^^ string " " ^^ pp_nexp nexp ^^ string ")"

and pp_nexp x = match x with
| Nexp_aux(nexp_aux,l) -> string "(" ^^ pp_nexp_aux nexp_aux ^^ string " " ^^ pp_l l ^^ string ")"

and pp_order_aux x = match x with
| Ord_aux(Ord_var(kid),ott_menhir_loc) -> pp_kid kid
| Ord_aux(Ord_inc,ott_menhir_loc) -> string "inc"
| Ord_aux(Ord_dec,ott_menhir_loc) -> string "dec"

and pp_order x = match x with
| Ord_aux(order_aux,l) -> string "(" ^^ pp_order_aux order_aux ^^ string " " ^^ pp_l l ^^ string ")"

and pp_base_effect_aux x = match x with
| BE_aux(BE_rreg,ott_menhir_loc) -> string "rreg"
| BE_aux(BE_wreg,ott_menhir_loc) -> string "wreg"
| BE_aux(BE_rmem,ott_menhir_loc) -> string "rmem"
| BE_aux(BE_wmem,ott_menhir_loc) -> string "wmem"
| BE_aux(BE_eamem,ott_menhir_loc) -> string "wmea"
| BE_aux(BE_exmem,ott_menhir_loc) -> string "exmem"
| BE_aux(BE_wmv,ott_menhir_loc) -> string "wmv"
| BE_aux(BE_barr,ott_menhir_loc) -> string "barr"
| BE_aux(BE_depend,ott_menhir_loc) -> string "depend"
| BE_aux(BE_undef,ott_menhir_loc) -> string "undef"
| BE_aux(BE_unspec,ott_menhir_loc) -> string "unspec"
| BE_aux(BE_nondet,ott_menhir_loc) -> string "nondet"
| BE_aux(BE_escape,ott_menhir_loc) -> string "escape"
| BE_aux(BE_config,ott_menhir_loc) -> string "config"

and pp_base_effect x = match x with
| BE_aux(base_effect_aux,l) -> string "(" ^^ pp_base_effect_aux base_effect_aux ^^ string " " ^^ pp_l l ^^ string ")"

and pp_effect_aux x = match x with
| Effect_aux(Effect_set(base_effect0),ott_menhir_loc) -> string "(" ^^ string "{" ^^ string " " ^^ separate (string ",") (List.map (function (base_effect0) -> pp_base_effect base_effect0) base_effect0) ^^ string " " ^^ string "}" ^^ string ")"

and pp_effect x = match x with
| Effect_aux(effect_aux,l) -> string "(" ^^ pp_effect_aux effect_aux ^^ string " " ^^ pp_l l ^^ string ")"

and pp_typ_aux x = match x with
| Typ_aux(Typ_internal_unknown,ott_menhir_loc) -> string ""
| Typ_aux(Typ_id(id),ott_menhir_loc) -> pp_id id
| Typ_aux(Typ_var(kid),ott_menhir_loc) -> pp_kid kid
| Typ_aux(Typ_fn(typ0,typ2,effect),ott_menhir_loc) -> string "(" ^^ string "(" ^^ string " " ^^ separate (string ",") (List.map (function (typ0) -> pp_typ typ0) typ0) ^^ string " " ^^ string ")" ^^ string " " ^^ string "->" ^^ string " " ^^ pp_typ typ2 ^^ string " " ^^ string "effectkw" ^^ string " " ^^ pp_effect effect ^^ string ")"
| Typ_aux(Typ_bidir(typ1,typ2),ott_menhir_loc) -> string "(" ^^ pp_typ typ1 ^^ string " " ^^ string "<->" ^^ string " " ^^ pp_typ typ2 ^^ string ")"
| Typ_aux(Typ_tup(typ0),ott_menhir_loc) -> string "(" ^^ string "(" ^^ string " " ^^ separate (string ",") (List.map (function (typ0) -> pp_typ typ0) typ0) ^^ string " " ^^ string ")" ^^ string ")"
| Typ_aux(Typ_app(id,typ_arg0),ott_menhir_loc) -> string "(" ^^ pp_id id ^^ string " " ^^ string "(" ^^ string " " ^^ separate (string ",") (List.map (function (typ_arg0) -> pp_typ_arg typ_arg0) typ_arg0) ^^ string " " ^^ string ")" ^^ string ")"
| Typ_aux(Typ_exist(kinded_id0,n_constraint,typ),ott_menhir_loc) -> string "(" ^^ string "{" ^^ string " " ^^ separate (string " ") (List.map (function (kinded_id0) -> pp_kinded_id kinded_id0) kinded_id0) ^^ string " " ^^ string "," ^^ string " " ^^ pp_n_constraint n_constraint ^^ string " " ^^ string "." ^^ string " " ^^ pp_typ typ ^^ string " " ^^ string "}" ^^ string ")"

and pp_typ x = match x with
| Typ_aux(typ_aux,l) -> string "(" ^^ pp_typ_aux typ_aux ^^ string " " ^^ pp_l l ^^ string ")"

and pp_typ_arg_aux x = match x with
| A_aux(A_nexp(nexp),ott_menhir_loc) -> pp_nexp nexp
| A_aux(A_typ(typ),ott_menhir_loc) -> pp_typ typ
| A_aux(A_order(order),ott_menhir_loc) -> pp_order order
| A_aux(A_bool(n_constraint),ott_menhir_loc) -> pp_n_constraint n_constraint

and pp_typ_arg x = match x with
| A_aux(typ_arg_aux,l) -> string "(" ^^ pp_typ_arg_aux typ_arg_aux ^^ string " " ^^ pp_l l ^^ string ")"

and pp_n_constraint_aux x = match x with
| NC_aux(NC_equal(nexp,nexp_prime),ott_menhir_loc) -> string "(" ^^ pp_nexp nexp ^^ string " " ^^ string "==" ^^ string " " ^^ pp_nexp nexp_prime ^^ string ")"
| NC_aux(NC_bounded_ge(nexp,nexp_prime),ott_menhir_loc) -> string "(" ^^ pp_nexp nexp ^^ string " " ^^ string ">=" ^^ string " " ^^ pp_nexp nexp_prime ^^ string ")"
| NC_aux(NC_bounded_gt(nexp,nexp_prime),ott_menhir_loc) -> string "(" ^^ pp_nexp nexp ^^ string " " ^^ string ">" ^^ string " " ^^ pp_nexp nexp_prime ^^ string ")"
| NC_aux(NC_bounded_le(nexp,nexp_prime),ott_menhir_loc) -> string "(" ^^ pp_nexp nexp ^^ string " " ^^ string "<=" ^^ string " " ^^ pp_nexp nexp_prime ^^ string ")"
| NC_aux(NC_bounded_lt(nexp,nexp_prime),ott_menhir_loc) -> string "(" ^^ pp_nexp nexp ^^ string " " ^^ string "<" ^^ string " " ^^ pp_nexp nexp_prime ^^ string ")"
| NC_aux(NC_not_equal(nexp,nexp_prime),ott_menhir_loc) -> string "(" ^^ pp_nexp nexp ^^ string " " ^^ string "!=" ^^ string " " ^^ pp_nexp nexp_prime ^^ string ")"
| NC_aux(NC_set(kid,num0),ott_menhir_loc) -> string "(" ^^ pp_kid kid ^^ string " " ^^ string "IN" ^^ string " " ^^ string "{" ^^ string " " ^^ separate (string ",") (List.map (function (num0) -> string num0) num0) ^^ string " " ^^ string "}" ^^ string ")"
| NC_aux(NC_or(n_constraint,n_constraint_prime),ott_menhir_loc) -> string "(" ^^ pp_n_constraint n_constraint ^^ string " " ^^ string "&" ^^ string " " ^^ pp_n_constraint n_constraint_prime ^^ string ")"
| NC_aux(NC_and(n_constraint,n_constraint_prime),ott_menhir_loc) -> string "(" ^^ pp_n_constraint n_constraint ^^ string " " ^^ string "|" ^^ string " " ^^ pp_n_constraint n_constraint_prime ^^ string ")"
| NC_aux(NC_app(id,typ_arg0),ott_menhir_loc) -> string "(" ^^ pp_id id ^^ string " " ^^ string "(" ^^ string " " ^^ separate (string ",") (List.map (function (typ_arg0) -> pp_typ_arg typ_arg0) typ_arg0) ^^ string " " ^^ string ")" ^^ string ")"
| NC_aux(NC_var(kid),ott_menhir_loc) -> pp_kid kid
| NC_aux(NC_true,ott_menhir_loc) -> string "true"
| NC_aux(NC_false,ott_menhir_loc) -> string "false"

and pp_n_constraint x = match x with
| NC_aux(n_constraint_aux,l) -> string "(" ^^ pp_n_constraint_aux n_constraint_aux ^^ string " " ^^ pp_l l ^^ string ")"

and pp_kinded_id_aux x = match x with
| KOpt_aux(KOpt_kind(kind,kid),ott_menhir_loc) -> string "(" ^^ pp_kind kind ^^ string " " ^^ pp_kid kid ^^ string ")"

and pp_kinded_id x = match x with
| KOpt_aux(kinded_id_aux,l) -> string "(" ^^ pp_kinded_id_aux kinded_id_aux ^^ string " " ^^ pp_l l ^^ string ")"

and pp_quant_item_aux x = match x with
| QI_aux(QI_id(kinded_id),ott_menhir_loc) -> pp_kinded_id kinded_id
| QI_aux(QI_constraint(n_constraint),ott_menhir_loc) -> pp_n_constraint n_constraint
| QI_aux(QI_constant(kinded_id0),ott_menhir_loc) -> separate (string " ") (List.map (function (kinded_id0) -> pp_kinded_id kinded_id0) kinded_id0)

and pp_quant_item x = match x with
| QI_aux(quant_item_aux,l) -> string "(" ^^ pp_quant_item_aux quant_item_aux ^^ string " " ^^ pp_l l ^^ string ")"

and pp_typquant_aux x = match x with
| TypQ_aux(TypQ_tq(quant_item0),ott_menhir_loc) -> string "(" ^^ string "forall" ^^ string " " ^^ separate (string ",") (List.map (function (quant_item0) -> pp_quant_item quant_item0) quant_item0) ^^ string " " ^^ string "." ^^ string ")"
| TypQ_aux(TypQ_no_forall,ott_menhir_loc) -> string ""

and pp_typquant x = match x with
| TypQ_aux(typquant_aux,l) -> string "(" ^^ pp_typquant_aux typquant_aux ^^ string " " ^^ pp_l l ^^ string ")"

and pp_typschm_aux x = match x with
| TypSchm_aux(TypSchm_ts(typquant,typ),ott_menhir_loc) -> string "(" ^^ pp_typquant typquant ^^ string " " ^^ pp_typ typ ^^ string ")"

and pp_typschm x = match x with
| TypSchm_aux(typschm_aux,l) -> string "(" ^^ pp_typschm_aux typschm_aux ^^ string " " ^^ pp_l l ^^ string ")"

and pp_type_def x = match x with
| TD_aux(type_def_aux) -> pp_type_def_aux type_def_aux

and pp_type_def_aux x = match x with
| TD_abbrev(id,typquant,typ_arg) -> string "(" ^^ string "type" ^^ string " " ^^ pp_id id ^^ string " " ^^ pp_typquant typquant ^^ string " " ^^ string "=" ^^ string " " ^^ pp_typ_arg typ_arg ^^ string ")"
| TD_record(id,typquant,typ0_id0,semi_opt) -> string "(" ^^ string "typedef" ^^ string " " ^^ pp_id id ^^ string " " ^^ string "=" ^^ string " " ^^ string "const" ^^ string " " ^^ string "struct" ^^ string " " ^^ pp_typquant typquant ^^ string " " ^^ string "{" ^^ string " " ^^ separate (string ";") (List.map (function (typ0,id0) -> pp_typ typ0 ^^ string " " ^^ pp_id id0) typ0_id0) ^^ string " " ^^ pp_semi_opt semi_opt ^^ string " " ^^ string "}" ^^ string ")"
| TD_variant(id,typquant,type_union0,semi_opt) -> string "(" ^^ string "typedef" ^^ string " " ^^ pp_id id ^^ string " " ^^ string "=" ^^ string " " ^^ string "const" ^^ string " " ^^ string "union" ^^ string " " ^^ pp_typquant typquant ^^ string " " ^^ string "{" ^^ string " " ^^ separate (string ";") (List.map (function (type_union0) -> pp_type_union type_union0) type_union0) ^^ string " " ^^ pp_semi_opt semi_opt ^^ string " " ^^ string "}" ^^ string ")"
| TD_enum(id,id0,semi_opt) -> string "(" ^^ string "typedef" ^^ string " " ^^ pp_id id ^^ string " " ^^ string "=" ^^ string " " ^^ string "enumerate" ^^ string " " ^^ string "{" ^^ string " " ^^ separate (string ";") (List.map (function (id0) -> pp_id id0) id0) ^^ string " " ^^ pp_semi_opt semi_opt ^^ string " " ^^ string "}" ^^ string ")"
| TD_bitfield(id,typ,id0_index_range0) -> string "(" ^^ string "bitfield" ^^ string " " ^^ pp_id id ^^ string " " ^^ string ":" ^^ string " " ^^ pp_typ typ ^^ string " " ^^ string "=" ^^ string " " ^^ string "{" ^^ string " " ^^ separate (string ",") (List.map (function (id0,index_range0) -> pp_id id0 ^^ string " " ^^ string ":" ^^ string " " ^^ pp_index_range index_range0) id0_index_range0) ^^ string " " ^^ string "}" ^^ string ")"

and pp_type_union_aux x = match x with
| Tu_aux(Tu_ty_id(typ,id),ott_menhir_loc) -> string "(" ^^ pp_typ typ ^^ string " " ^^ pp_id id ^^ string ")"

and pp_type_union x = match x with
| Tu_aux(type_union_aux,l) -> string "(" ^^ pp_type_union_aux type_union_aux ^^ string " " ^^ pp_l l ^^ string ")"

and pp_index_range_aux x = match x with
| BF_aux(BF_single(nexp),ott_menhir_loc) -> pp_nexp nexp
| BF_aux(BF_range(nexp1,nexp2),ott_menhir_loc) -> string "(" ^^ pp_nexp nexp1 ^^ string " " ^^ string ".." ^^ string " " ^^ pp_nexp nexp2 ^^ string ")"
| BF_aux(BF_concat(index_range1,index_range2),ott_menhir_loc) -> string "(" ^^ pp_index_range index_range1 ^^ string " " ^^ string "," ^^ string " " ^^ pp_index_range index_range2 ^^ string ")"

and pp_index_range x = match x with
| BF_aux(index_range_aux,l) -> string "(" ^^ pp_index_range_aux index_range_aux ^^ string " " ^^ pp_l l ^^ string ")"

and pp_lit_aux x = match x with
| L_aux(L_unit,ott_menhir_loc) -> string "(" ^^ string "(" ^^ string " " ^^ string ")" ^^ string ")"
| L_aux(L_zero,ott_menhir_loc) -> string "bitzero"
| L_aux(L_one,ott_menhir_loc) -> string "bitone"
| L_aux(L_true,ott_menhir_loc) -> string "true"
| L_aux(L_false,ott_menhir_loc) -> string "false"
| L_aux(L_num(num),ott_menhir_loc) -> string num
| L_aux(L_hex(hex),ott_menhir_loc) -> string hex
| L_aux(L_bin(bin),ott_menhir_loc) -> string bin
| L_aux(L_string(string),ott_menhir_loc) -> string string
| L_aux(L_undef,ott_menhir_loc) -> string "undefined"
| L_aux(L_real(real),ott_menhir_loc) -> string real

and pp_lit x = match x with
| L_aux(lit_aux,l) -> string "(" ^^ pp_lit_aux lit_aux ^^ string " " ^^ pp_l l ^^ string ")"

and pp_semi_opt_default 

and pp_typ_pat_aux x = match x with
| TP_aux(TP_wild,ott_menhir_loc) -> string "_"
| TP_aux(TP_var(kid),ott_menhir_loc) -> pp_kid kid
| TP_aux(TP_app(id,typ_pat0),ott_menhir_loc) -> string "(" ^^ pp_id id ^^ string " " ^^ string "(" ^^ string " " ^^ separate (string ",") (List.map (function (typ_pat0) -> pp_typ_pat typ_pat0) typ_pat0) ^^ string " " ^^ string ")" ^^ string ")"

and pp_typ_pat x = match x with
| TP_aux(typ_pat_aux,l) -> string "(" ^^ pp_typ_pat_aux typ_pat_aux ^^ string " " ^^ pp_l l ^^ string ")"

and pp_pat_aux x = match x with
| P_aux(P_lit(lit),ott_menhir_loc) -> pp_lit lit
| P_aux(P_wild,ott_menhir_loc) -> string "_"
| P_aux(P_or(pat1,pat2),ott_menhir_loc) -> string "(" ^^ pp_pat pat1 ^^ string " " ^^ string "|" ^^ string " " ^^ pp_pat pat2 ^^ string ")"
| P_aux(P_not(pat),ott_menhir_loc) -> string "(" ^^ string "~" ^^ string " " ^^ pp_pat pat ^^ string ")"
| P_aux(P_as(pat,id),ott_menhir_loc) -> string "(" ^^ string "(" ^^ string " " ^^ pp_pat pat ^^ string " " ^^ string "as" ^^ string " " ^^ pp_id id ^^ string " " ^^ string ")" ^^ string ")"
| P_aux(P_typ(typ,pat),ott_menhir_loc) -> string "(" ^^ string "(" ^^ string " " ^^ pp_typ typ ^^ string " " ^^ string ")" ^^ string " " ^^ pp_pat pat ^^ string ")"
| P_aux(P_id(id),ott_menhir_loc) -> pp_id id
| P_aux(P_var(pat,typ_pat),ott_menhir_loc) -> string "(" ^^ pp_pat pat ^^ string " " ^^ pp_typ_pat typ_pat ^^ string ")"
| P_aux(P_app(id,pat0),ott_menhir_loc) -> string "(" ^^ pp_id id ^^ string " " ^^ string "(" ^^ string " " ^^ separate (string ",") (List.map (function (pat0) -> pp_pat pat0) pat0) ^^ string " " ^^ string ")" ^^ string ")"
| P_aux(P_vector(pat0),ott_menhir_loc) -> string "(" ^^ string "[" ^^ string " " ^^ separate (string ",") (List.map (function (pat0) -> pp_pat pat0) pat0) ^^ string " " ^^ string "]" ^^ string ")"
| P_aux(P_vector_concat(pat0),ott_menhir_loc) -> separate (string "@") (List.map (function (pat0) -> pp_pat pat0) pat0)
| P_aux(P_tup(pat0),ott_menhir_loc) -> string "(" ^^ string "(" ^^ string " " ^^ separate (string ",") (List.map (function (pat0) -> pp_pat pat0) pat0) ^^ string " " ^^ string ")" ^^ string ")"
| P_aux(P_list(pat0),ott_menhir_loc) -> string "(" ^^ string "[||" ^^ string " " ^^ separate (string ",") (List.map (function (pat0) -> pp_pat pat0) pat0) ^^ string " " ^^ string "||]" ^^ string ")"
| P_aux(P_cons(pat1,pat2),ott_menhir_loc) -> string "(" ^^ pp_pat pat1 ^^ string " " ^^ string "::" ^^ string " " ^^ pp_pat pat2 ^^ string ")"
| P_aux(P_string_append(pat0),ott_menhir_loc) -> separate (string "^^") (List.map (function (pat0) -> pp_pat pat0) pat0)

and pp_pat x = match x with
| P_aux(pat_aux,annot) -> string "(" ^^ pp_pat_aux pat_aux ^^ string " " ^^ pp_annot annot ^^ string ")"

and pp_loop_default 

and pp_internal_loop_measure_aux x = match x with
| Measure_aux(Measure_none,ott_menhir_loc) -> string ""
| Measure_aux(Measure_some(exp),ott_menhir_loc) -> string "(" ^^ string "termination_measure" ^^ string " " ^^ string "{" ^^ string " " ^^ pp_exp exp ^^ string " " ^^ string "}" ^^ string ")"

and pp_internal_loop_measure x = match x with
| Measure_aux(internal_loop_measure_aux,l) -> string "(" ^^ pp_internal_loop_measure_aux internal_loop_measure_aux ^^ string " " ^^ pp_l l ^^ string ")"

and pp_exp_aux x = match x with
| E_aux(E_block(exp0),ott_menhir_loc) -> string "(" ^^ string "{" ^^ string " " ^^ separate (string ";") (List.map (function (exp0) -> pp_exp exp0) exp0) ^^ string " " ^^ string "}" ^^ string ")"
| E_aux(E_id(id),ott_menhir_loc) -> pp_id id
| E_aux(E_lit(lit),ott_menhir_loc) -> pp_lit lit
| E_aux(E_cast(typ,exp),ott_menhir_loc) -> string "(" ^^ string "(" ^^ string " " ^^ pp_typ typ ^^ string " " ^^ string ")" ^^ string " " ^^ pp_exp exp ^^ string ")"
| E_aux(E_app(id,exp0),ott_menhir_loc) -> string "(" ^^ pp_id id ^^ string " " ^^ string "(" ^^ string " " ^^ separate (string ",") (List.map (function (exp0) -> pp_exp exp0) exp0) ^^ string " " ^^ string ")" ^^ string ")"
| E_aux(E_app_infix(exp1,id,exp2),ott_menhir_loc) -> string "(" ^^ pp_exp exp1 ^^ string " " ^^ pp_id id ^^ string " " ^^ pp_exp exp2 ^^ string ")"
| E_aux(E_tuple(exp0),ott_menhir_loc) -> string "(" ^^ string "(" ^^ string " " ^^ separate (string ",") (List.map (function (exp0) -> pp_exp exp0) exp0) ^^ string " " ^^ string ")" ^^ string ")"
| E_aux(E_if(exp1,exp2,exp3),ott_menhir_loc) -> string "(" ^^ string "if" ^^ string " " ^^ pp_exp exp1 ^^ string " " ^^ string "then" ^^ string " " ^^ pp_exp exp2 ^^ string " " ^^ string "else" ^^ string " " ^^ pp_exp exp3 ^^ string ")"
| E_aux(E_loop(loop,internal_loop_measure,exp1,exp2),ott_menhir_loc) -> string "(" ^^ pp_loop loop ^^ string " " ^^ pp_internal_loop_measure internal_loop_measure ^^ string " " ^^ pp_exp exp1 ^^ string " " ^^ pp_exp exp2 ^^ string ")"
| E_aux(E_for(id,exp1,exp2,exp3,order,exp4),ott_menhir_loc) -> string "(" ^^ string "foreach" ^^ string " " ^^ string "(" ^^ string " " ^^ pp_id id ^^ string " " ^^ string "from" ^^ string " " ^^ pp_exp exp1 ^^ string " " ^^ string "to" ^^ string " " ^^ pp_exp exp2 ^^ string " " ^^ string "by" ^^ string " " ^^ pp_exp exp3 ^^ string " " ^^ string "in" ^^ string " " ^^ pp_order order ^^ string " " ^^ string ")" ^^ string " " ^^ pp_exp exp4 ^^ string ")"
| E_aux(E_vector(exp0),ott_menhir_loc) -> string "(" ^^ string "[" ^^ string " " ^^ separate (string ",") (List.map (function (exp0) -> pp_exp exp0) exp0) ^^ string " " ^^ string "]" ^^ string ")"
| E_aux(E_vector_access(exp,exp_prime),ott_menhir_loc) -> string "(" ^^ pp_exp exp ^^ string " " ^^ string "[" ^^ string " " ^^ pp_exp exp_prime ^^ string " " ^^ string "]" ^^ string ")"
| E_aux(E_vector_subrange(exp,exp1,exp2),ott_menhir_loc) -> string "(" ^^ pp_exp exp ^^ string " " ^^ string "[" ^^ string " " ^^ pp_exp exp1 ^^ string " " ^^ string ".." ^^ string " " ^^ pp_exp exp2 ^^ string " " ^^ string "]" ^^ string ")"
| E_aux(E_vector_update(exp,exp1,exp2),ott_menhir_loc) -> string "(" ^^ string "[" ^^ string " " ^^ pp_exp exp ^^ string " " ^^ string "with" ^^ string " " ^^ pp_exp exp1 ^^ string " " ^^ string "=" ^^ string " " ^^ pp_exp exp2 ^^ string " " ^^ string "]" ^^ string ")"
| E_aux(E_vector_update_subrange(exp,exp1,exp2,exp3),ott_menhir_loc) -> string "(" ^^ string "[" ^^ string " " ^^ pp_exp exp ^^ string " " ^^ string "with" ^^ string " " ^^ pp_exp exp1 ^^ string " " ^^ string ".." ^^ string " " ^^ pp_exp exp2 ^^ string " " ^^ string "=" ^^ string " " ^^ pp_exp exp3 ^^ string " " ^^ string "]" ^^ string ")"
| E_aux(E_vector_append(exp1,exp2),ott_menhir_loc) -> string "(" ^^ pp_exp exp1 ^^ string " " ^^ string "@" ^^ string " " ^^ pp_exp exp2 ^^ string ")"
| E_aux(E_list(exp0),ott_menhir_loc) -> string "(" ^^ string "[|" ^^ string " " ^^ separate (string ",") (List.map (function (exp0) -> pp_exp exp0) exp0) ^^ string " " ^^ string "|]" ^^ string ")"
| E_aux(E_cons(exp1,exp2),ott_menhir_loc) -> string "(" ^^ pp_exp exp1 ^^ string " " ^^ string "::" ^^ string " " ^^ pp_exp exp2 ^^ string ")"
| E_aux(E_record(fexp0),ott_menhir_loc) -> string "(" ^^ string "struct" ^^ string " " ^^ string "{" ^^ string " " ^^ separate (string ",") (List.map (function (fexp0) -> pp_fexp fexp0) fexp0) ^^ string " " ^^ string "}" ^^ string ")"
| E_aux(E_record_update(exp,fexp0),ott_menhir_loc) -> string "(" ^^ string "{" ^^ string " " ^^ pp_exp exp ^^ string " " ^^ string "with" ^^ string " " ^^ separate (string ",") (List.map (function (fexp0) -> pp_fexp fexp0) fexp0) ^^ string " " ^^ string "}" ^^ string ")"
| E_aux(E_field(exp,id),ott_menhir_loc) -> string "(" ^^ pp_exp exp ^^ string " " ^^ string "." ^^ string " " ^^ pp_id id ^^ string ")"
| E_aux(E_case(exp,pexp0),ott_menhir_loc) -> string "(" ^^ string "match" ^^ string " " ^^ pp_exp exp ^^ string " " ^^ string "{" ^^ string " " ^^ separate (string ",") (List.map (function (pexp0) -> pp_pexp pexp0) pexp0) ^^ string " " ^^ string "}" ^^ string ")"
| E_aux(E_let(letbind,exp),ott_menhir_loc) -> string "(" ^^ pp_letbind letbind ^^ string " " ^^ string "in" ^^ string " " ^^ pp_exp exp ^^ string ")"
| E_aux(E_assign(lexp,exp),ott_menhir_loc) -> string "(" ^^ pp_lexp lexp ^^ string " " ^^ string "=" ^^ string " " ^^ pp_exp exp ^^ string ")"
| E_aux(E_sizeof(nexp),ott_menhir_loc) -> string "(" ^^ string "sizeof" ^^ string " " ^^ pp_nexp nexp ^^ string ")"
| E_aux(E_return(exp),ott_menhir_loc) -> string "(" ^^ string "return" ^^ string " " ^^ pp_exp exp ^^ string ")"
| E_aux(E_exit(exp),ott_menhir_loc) -> string "(" ^^ string "exit" ^^ string " " ^^ pp_exp exp ^^ string ")"
| E_aux(E_ref(id),ott_menhir_loc) -> string "(" ^^ string "ref" ^^ string " " ^^ pp_id id ^^ string ")"
| E_aux(E_throw(exp),ott_menhir_loc) -> string "(" ^^ string "throw" ^^ string " " ^^ pp_exp exp ^^ string ")"
| E_aux(E_try(exp,pexp0),ott_menhir_loc) -> string "(" ^^ string "try" ^^ string " " ^^ pp_exp exp ^^ string " " ^^ string "catch" ^^ string " " ^^ string "{" ^^ string " " ^^ separate (string ",") (List.map (function (pexp0) -> pp_pexp pexp0) pexp0) ^^ string " " ^^ string "}" ^^ string ")"
| E_aux(E_assert(exp,exp_prime),ott_menhir_loc) -> string "(" ^^ string "assert" ^^ string " " ^^ string "(" ^^ string " " ^^ pp_exp exp ^^ string " " ^^ string "," ^^ string " " ^^ pp_exp exp_prime ^^ string " " ^^ string ")" ^^ string ")"
| E_aux(E_var(lexp,exp,exp_prime),ott_menhir_loc) -> string "(" ^^ string "var" ^^ string " " ^^ pp_lexp lexp ^^ string " " ^^ string "=" ^^ string " " ^^ pp_exp exp ^^ string " " ^^ string "in" ^^ string " " ^^ pp_exp exp_prime ^^ string ")"
| E_aux(E_internal_plet(pat,exp,exp_prime),ott_menhir_loc) -> string "(" ^^ string "let" ^^ string " " ^^ pp_pat pat ^^ string " " ^^ string "=" ^^ string " " ^^ pp_exp exp ^^ string " " ^^ string "in" ^^ string " " ^^ pp_exp exp_prime ^^ string ")"
| E_aux(E_internal_return(exp),ott_menhir_loc) -> string "(" ^^ string "return_int" ^^ string " " ^^ string "(" ^^ string " " ^^ pp_exp exp ^^ string " " ^^ string ")" ^^ string ")"
| E_aux(E_internal_value(value),ott_menhir_loc) -> string value
| E_aux(E_constraint(n_constraint),ott_menhir_loc) -> string "(" ^^ string "constraint" ^^ string " " ^^ pp_n_constraint n_constraint ^^ string ")"

and pp_exp x = match x with
| E_aux(exp_aux,annot) -> string "(" ^^ pp_exp_aux exp_aux ^^ string " " ^^ pp_annot annot ^^ string ")"

and pp_lexp_aux x = match x with
| LEXP_aux(LEXP_id(id),ott_menhir_loc) -> pp_id id
| LEXP_aux(LEXP_deref(exp),ott_menhir_loc) -> string "(" ^^ string "deref" ^^ string " " ^^ pp_exp exp ^^ string ")"
| LEXP_aux(LEXP_memory(id,exp0),ott_menhir_loc) -> string "(" ^^ pp_id id ^^ string " " ^^ string "(" ^^ string " " ^^ separate (string ",") (List.map (function (exp0) -> pp_exp exp0) exp0) ^^ string " " ^^ string ")" ^^ string ")"
| LEXP_aux(LEXP_cast(typ,id),ott_menhir_loc) -> string "(" ^^ string "(" ^^ string " " ^^ pp_typ typ ^^ string " " ^^ string ")" ^^ string " " ^^ pp_id id ^^ string ")"
| LEXP_aux(LEXP_tup(lexp0),ott_menhir_loc) -> string "(" ^^ string "(" ^^ string " " ^^ separate (string ",") (List.map (function (lexp0) -> pp_lexp lexp0) lexp0) ^^ string " " ^^ string ")" ^^ string ")"
| LEXP_aux(LEXP_vector_concat(lexp0),ott_menhir_loc) -> separate (string "@") (List.map (function (lexp0) -> pp_lexp lexp0) lexp0)
| LEXP_aux(LEXP_vector(lexp,exp),ott_menhir_loc) -> string "(" ^^ pp_lexp lexp ^^ string " " ^^ string "[" ^^ string " " ^^ pp_exp exp ^^ string " " ^^ string "]" ^^ string ")"
| LEXP_aux(LEXP_vector_range(lexp,exp1,exp2),ott_menhir_loc) -> string "(" ^^ pp_lexp lexp ^^ string " " ^^ string "[" ^^ string " " ^^ pp_exp exp1 ^^ string " " ^^ string ".." ^^ string " " ^^ pp_exp exp2 ^^ string " " ^^ string "]" ^^ string ")"
| LEXP_aux(LEXP_field(lexp,id),ott_menhir_loc) -> string "(" ^^ pp_lexp lexp ^^ string " " ^^ string "." ^^ string " " ^^ pp_id id ^^ string ")"

and pp_lexp x = match x with
| LEXP_aux(lexp_aux,annot) -> string "(" ^^ pp_lexp_aux lexp_aux ^^ string " " ^^ pp_annot annot ^^ string ")"

and pp_fexp_aux x = match x with
| FE_aux(FE_Fexp(id,exp),ott_menhir_loc) -> string "(" ^^ pp_id id ^^ string " " ^^ string "=" ^^ string " " ^^ pp_exp exp ^^ string ")"

and pp_fexp x = match x with
| FE_aux(fexp_aux,annot) -> string "(" ^^ pp_fexp_aux fexp_aux ^^ string " " ^^ pp_annot annot ^^ string ")"

and pp_opt_default_aux x = match x with
| Def_val_aux(Def_val_empty,ott_menhir_loc) -> string ""
| Def_val_aux(Def_val_dec(exp),ott_menhir_loc) -> string "(" ^^ string ";" ^^ string " " ^^ string "default" ^^ string " " ^^ string "=" ^^ string " " ^^ pp_exp exp ^^ string ")"

and pp_opt_default x = match x with
| Def_val_aux(opt_default_aux,annot) -> string "(" ^^ pp_opt_default_aux opt_default_aux ^^ string " " ^^ pp_annot annot ^^ string ")"

and pp_pexp_aux x = match x with
| Pat_aux(Pat_exp(pat,exp),ott_menhir_loc) -> string "(" ^^ pp_pat pat ^^ string " " ^^ string "->" ^^ string " " ^^ pp_exp exp ^^ string ")"
| Pat_aux(Pat_when(pat,exp1,exp),ott_menhir_loc) -> string "(" ^^ pp_pat pat ^^ string " " ^^ string "when" ^^ string " " ^^ pp_exp exp1 ^^ string " " ^^ string "->" ^^ string " " ^^ pp_exp exp ^^ string ")"

and pp_pexp x = match x with
| Pat_aux(pexp_aux,annot) -> string "(" ^^ pp_pexp_aux pexp_aux ^^ string " " ^^ pp_annot annot ^^ string ")"

and pp_tannot_opt_aux x = match x with
| Typ_annot_opt_aux(Typ_annot_opt_none,ott_menhir_loc) -> string ""
| Typ_annot_opt_aux(Typ_annot_opt_some(typquant,typ),ott_menhir_loc) -> string "(" ^^ pp_typquant typquant ^^ string " " ^^ pp_typ typ ^^ string ")"

and pp_tannot_opt x = match x with
| Typ_annot_opt_aux(tannot_opt_aux,l) -> string "(" ^^ pp_tannot_opt_aux tannot_opt_aux ^^ string " " ^^ pp_l l ^^ string ")"

and pp_rec_opt_aux x = match x with
| Rec_aux(Rec_nonrec,ott_menhir_loc) -> string ""
| Rec_aux(Rec_rec,ott_menhir_loc) -> string "rec"
| Rec_aux(Rec_measure(pat,exp),ott_menhir_loc) -> string "(" ^^ string "{" ^^ string " " ^^ pp_pat pat ^^ string " " ^^ string "->" ^^ string " " ^^ pp_exp exp ^^ string " " ^^ string "}" ^^ string ")"

and pp_rec_opt x = match x with
| Rec_aux(rec_opt_aux,l) -> string "(" ^^ pp_rec_opt_aux rec_opt_aux ^^ string " " ^^ pp_l l ^^ string ")"

and pp_effect_opt_aux x = match x with
| Effect_opt_aux(Effect_opt_none,ott_menhir_loc) -> string ""
| Effect_opt_aux(Effect_opt_effect(effect),ott_menhir_loc) -> string "(" ^^ string "effectkw" ^^ string " " ^^ pp_effect effect ^^ string ")"

and pp_effect_opt x = match x with
| Effect_opt_aux(effect_opt_aux,l) -> string "(" ^^ pp_effect_opt_aux effect_opt_aux ^^ string " " ^^ pp_l l ^^ string ")"

and pp_pexp_funcl x = match x with
| Pat_funcl_exp(pat,exp) -> string "(" ^^ pp_pat pat ^^ string " " ^^ string "=" ^^ string " " ^^ pp_exp exp ^^ string ")"
| Pat_funcl_when(pat,exp1,exp) -> string "(" ^^ string "(" ^^ string " " ^^ pp_pat pat ^^ string " " ^^ string "when" ^^ string " " ^^ pp_exp exp1 ^^ string " " ^^ string ")" ^^ string " " ^^ string "=" ^^ string " " ^^ pp_exp exp ^^ string ")"

and pp_funcl_aux x = match x with
| FCL_aux(FCL_Funcl(id,pexp_funcl),ott_menhir_loc) -> string "(" ^^ pp_id id ^^ string " " ^^ pp_pexp_funcl pexp_funcl ^^ string ")"

and pp_funcl x = match x with
| FCL_aux(funcl_aux,annot) -> string "(" ^^ pp_funcl_aux funcl_aux ^^ string " " ^^ pp_annot annot ^^ string ")"

and pp_fundef_aux x = match x with
| FD_aux(FD_function(rec_opt,tannot_opt,effect_opt,funcl0),ott_menhir_loc) -> string "(" ^^ string "function" ^^ string " " ^^ pp_rec_opt rec_opt ^^ string " " ^^ pp_tannot_opt tannot_opt ^^ string " " ^^ pp_effect_opt effect_opt ^^ string " " ^^ separate (string "and") (List.map (function (funcl0) -> pp_funcl funcl0) funcl0) ^^ string ")"

and pp_fundef x = match x with
| FD_aux(fundef_aux,annot) -> string "(" ^^ pp_fundef_aux fundef_aux ^^ string " " ^^ pp_annot annot ^^ string ")"

and pp_mpat_aux x = match x with
| MP_aux(MP_lit(lit),ott_menhir_loc) -> pp_lit lit
| MP_aux(MP_id(id),ott_menhir_loc) -> pp_id id
| MP_aux(MP_app(id,mpat0),ott_menhir_loc) -> string "(" ^^ pp_id id ^^ string " " ^^ string "(" ^^ string " " ^^ separate (string ",") (List.map (function (mpat0) -> pp_mpat mpat0) mpat0) ^^ string " " ^^ string ")" ^^ string ")"
| MP_aux(MP_vector(mpat0),ott_menhir_loc) -> string "(" ^^ string "[" ^^ string " " ^^ separate (string ",") (List.map (function (mpat0) -> pp_mpat mpat0) mpat0) ^^ string " " ^^ string "]" ^^ string ")"
| MP_aux(MP_vector_concat(mpat0),ott_menhir_loc) -> separate (string "@") (List.map (function (mpat0) -> pp_mpat mpat0) mpat0)
| MP_aux(MP_tup(mpat0),ott_menhir_loc) -> string "(" ^^ string "(" ^^ string " " ^^ separate (string ",") (List.map (function (mpat0) -> pp_mpat mpat0) mpat0) ^^ string " " ^^ string ")" ^^ string ")"
| MP_aux(MP_list(mpat0),ott_menhir_loc) -> string "(" ^^ string "[||" ^^ string " " ^^ separate (string ",") (List.map (function (mpat0) -> pp_mpat mpat0) mpat0) ^^ string " " ^^ string "||]" ^^ string ")"
| MP_aux(MP_cons(mpat1,mpat2),ott_menhir_loc) -> string "(" ^^ pp_mpat mpat1 ^^ string " " ^^ string "::" ^^ string " " ^^ pp_mpat mpat2 ^^ string ")"
| MP_aux(MP_string_append(mpat0),ott_menhir_loc) -> separate (string "^^") (List.map (function (mpat0) -> pp_mpat mpat0) mpat0)
| MP_aux(MP_typ(mpat,typ),ott_menhir_loc) -> string "(" ^^ pp_mpat mpat ^^ string " " ^^ string ":" ^^ string " " ^^ pp_typ typ ^^ string ")"
| MP_aux(MP_as(mpat,id),ott_menhir_loc) -> string "(" ^^ pp_mpat mpat ^^ string " " ^^ string "as" ^^ string " " ^^ pp_id id ^^ string ")"

and pp_mpat x = match x with
| MP_aux(mpat_aux,annot) -> string "(" ^^ pp_mpat_aux mpat_aux ^^ string " " ^^ pp_annot annot ^^ string ")"

and pp_mpexp_aux x = match x with
| MPat_aux(MPat_pat(mpat),ott_menhir_loc) -> pp_mpat mpat
| MPat_aux(MPat_when(mpat,exp),ott_menhir_loc) -> string "(" ^^ pp_mpat mpat ^^ string " " ^^ string "when" ^^ string " " ^^ pp_exp exp ^^ string ")"

and pp_mpexp x = match x with
| MPat_aux(mpexp_aux,annot) -> string "(" ^^ pp_mpexp_aux mpexp_aux ^^ string " " ^^ pp_annot annot ^^ string ")"

and pp_mapcl_aux x = match x with
| MCL_aux(MCL_bidir(mpexp1,mpexp2),ott_menhir_loc) -> string "(" ^^ pp_mpexp mpexp1 ^^ string " " ^^ string "<->" ^^ string " " ^^ pp_mpexp mpexp2 ^^ string ")"
| MCL_aux(MCL_forwards(mpexp,exp),ott_menhir_loc) -> string "(" ^^ pp_mpexp mpexp ^^ string " " ^^ string "=>" ^^ string " " ^^ pp_exp exp ^^ string ")"
| MCL_aux(MCL_backwards(mpexp,exp),ott_menhir_loc) -> string "(" ^^ pp_mpexp mpexp ^^ string " " ^^ string "<-" ^^ string " " ^^ pp_exp exp ^^ string ")"

and pp_mapcl x = match x with
| MCL_aux(mapcl_aux,annot) -> string "(" ^^ pp_mapcl_aux mapcl_aux ^^ string " " ^^ pp_annot annot ^^ string ")"

and pp_mapdef_aux x = match x with
| MD_aux(MD_mapping(id,tannot_opt,mapcl0),ott_menhir_loc) -> string "(" ^^ string "mapping" ^^ string " " ^^ pp_id id ^^ string " " ^^ pp_tannot_opt tannot_opt ^^ string " " ^^ string "=" ^^ string " " ^^ string "{" ^^ string " " ^^ separate (string ",") (List.map (function (mapcl0) -> pp_mapcl mapcl0) mapcl0) ^^ string " " ^^ string "}" ^^ string ")"

and pp_mapdef x = match x with
| MD_aux(mapdef_aux,annot) -> string "(" ^^ pp_mapdef_aux mapdef_aux ^^ string " " ^^ pp_annot annot ^^ string ")"

and pp_letbind_aux x = match x with
| LB_aux(LB_val(pat,exp),ott_menhir_loc) -> string "(" ^^ string "let" ^^ string " " ^^ pp_pat pat ^^ string " " ^^ string "=" ^^ string " " ^^ pp_exp exp ^^ string ")"

and pp_letbind x = match x with
| LB_aux(letbind_aux,annot) -> string "(" ^^ pp_letbind_aux letbind_aux ^^ string " " ^^ pp_annot annot ^^ string ")"

and pp_val_spec x = match x with
| VS_aux(val_spec_aux) -> pp_val_spec_aux val_spec_aux

and pp_val_spec_aux x = match x with

and pp_default_spec_aux x = match x with
| DT_aux(DT_order(order),ott_menhir_loc) -> string "(" ^^ string "default" ^^ string " " ^^ string "Order" ^^ string " " ^^ pp_order order ^^ string ")"

and pp_default_spec x = match x with
| DT_aux(default_spec_aux,l) -> string "(" ^^ pp_default_spec_aux default_spec_aux ^^ string " " ^^ pp_l l ^^ string ")"

and pp_scattered_def_aux x = match x with
| SD_aux(SD_function(rec_opt,tannot_opt,effect_opt,id),ott_menhir_loc) -> string "(" ^^ string "scattered" ^^ string " " ^^ string "function" ^^ string " " ^^ pp_rec_opt rec_opt ^^ string " " ^^ pp_tannot_opt tannot_opt ^^ string " " ^^ pp_effect_opt effect_opt ^^ string " " ^^ pp_id id ^^ string ")"
| SD_aux(SD_funcl(funcl),ott_menhir_loc) -> string "(" ^^ string "function" ^^ string " " ^^ string "clause" ^^ string " " ^^ pp_funcl funcl ^^ string ")"
| SD_aux(SD_variant(id,typquant),ott_menhir_loc) -> string "(" ^^ string "scattered" ^^ string " " ^^ string "typedef" ^^ string " " ^^ pp_id id ^^ string " " ^^ string "=" ^^ string " " ^^ string "const" ^^ string " " ^^ string "union" ^^ string " " ^^ pp_typquant typquant ^^ string ")"
| SD_aux(SD_unioncl(id,type_union),ott_menhir_loc) -> string "(" ^^ string "union" ^^ string " " ^^ pp_id id ^^ string " " ^^ string "member" ^^ string " " ^^ pp_type_union type_union ^^ string ")"
| SD_aux(SD_mapping(id,tannot_opt),ott_menhir_loc) -> string "(" ^^ string "scattered" ^^ string " " ^^ string "mapping" ^^ string " " ^^ pp_id id ^^ string " " ^^ string ":" ^^ string " " ^^ pp_tannot_opt tannot_opt ^^ string ")"
| SD_aux(SD_mapcl(id,mapcl),ott_menhir_loc) -> string "(" ^^ string "mapping" ^^ string " " ^^ string "clause" ^^ string " " ^^ pp_id id ^^ string " " ^^ string "=" ^^ string " " ^^ pp_mapcl mapcl ^^ string ")"
| SD_aux(SD_end(id),ott_menhir_loc) -> string "(" ^^ string "end" ^^ string " " ^^ pp_id id ^^ string ")"

and pp_scattered_def x = match x with
| SD_aux(scattered_def_aux,annot) -> string "(" ^^ pp_scattered_def_aux scattered_def_aux ^^ string " " ^^ pp_annot annot ^^ string ")"

and pp_reg_id_aux x = match x with
| RI_aux(RI_id(id),ott_menhir_loc) -> pp_id id

and pp_reg_id x = match x with
| RI_aux(reg_id_aux,annot) -> string "(" ^^ pp_reg_id_aux reg_id_aux ^^ string " " ^^ pp_annot annot ^^ string ")"

and pp_alias_spec_aux x = match x with
| AL_aux(AL_subreg(reg_id,id),ott_menhir_loc) -> string "(" ^^ pp_reg_id reg_id ^^ string " " ^^ string "." ^^ string " " ^^ pp_id id ^^ string ")"
| AL_aux(AL_bit(reg_id,exp),ott_menhir_loc) -> string "(" ^^ pp_reg_id reg_id ^^ string " " ^^ string "[" ^^ string " " ^^ pp_exp exp ^^ string " " ^^ string "]" ^^ string ")"
| AL_aux(AL_slice(reg_id,exp,exp_prime),ott_menhir_loc) -> string "(" ^^ pp_reg_id reg_id ^^ string " " ^^ string "[" ^^ string " " ^^ pp_exp exp ^^ string " " ^^ string ".." ^^ string " " ^^ pp_exp exp_prime ^^ string " " ^^ string "]" ^^ string ")"
| AL_aux(AL_concat(reg_id,reg_id_prime),ott_menhir_loc) -> string "(" ^^ pp_reg_id reg_id ^^ string " " ^^ string ":" ^^ string " " ^^ pp_reg_id reg_id_prime ^^ string ")"

and pp_alias_spec x = match x with
| AL_aux(alias_spec_aux,annot) -> string "(" ^^ pp_alias_spec_aux alias_spec_aux ^^ string " " ^^ pp_annot annot ^^ string ")"

and pp_dec_spec_aux x = match x with
| DEC_aux(DEC_reg(effect,effect_prime,typ,id),ott_menhir_loc) -> string "(" ^^ string "register" ^^ string " " ^^ pp_effect effect ^^ string " " ^^ pp_effect effect_prime ^^ string " " ^^ pp_typ typ ^^ string " " ^^ pp_id id ^^ string ")"
| DEC_aux(DEC_config(id,typ,exp),ott_menhir_loc) -> string "(" ^^ string "register" ^^ string " " ^^ string "configuration" ^^ string " " ^^ pp_id id ^^ string " " ^^ string ":" ^^ string " " ^^ pp_typ typ ^^ string " " ^^ string "=" ^^ string " " ^^ pp_exp exp ^^ string ")"
| DEC_aux(DEC_alias(id,alias_spec),ott_menhir_loc) -> string "(" ^^ string "register" ^^ string " " ^^ string "alias" ^^ string " " ^^ pp_id id ^^ string " " ^^ string "=" ^^ string " " ^^ pp_alias_spec alias_spec ^^ string ")"
| DEC_aux(DEC_typ_alias(typ,id,alias_spec),ott_menhir_loc) -> string "(" ^^ string "register" ^^ string " " ^^ string "alias" ^^ string " " ^^ pp_typ typ ^^ string " " ^^ pp_id id ^^ string " " ^^ string "=" ^^ string " " ^^ pp_alias_spec alias_spec ^^ string ")"

and pp_dec_spec x = match x with
| DEC_aux(dec_spec_aux,annot) -> string "(" ^^ pp_dec_spec_aux dec_spec_aux ^^ string " " ^^ pp_annot annot ^^ string ")"

and pp_prec x = match x with
| Infix -> string "infix"
| InfixL -> string "infixl"
| InfixR -> string "infixr"

and pp_loop_measure x = match x with
| Loop(loop,exp) -> string "(" ^^ pp_loop loop ^^ string " " ^^ pp_exp exp ^^ string ")"

and pp_def x = match x with
| DEF_type(type_def) -> pp_type_def type_def
| DEF_fundef(fundef) -> pp_fundef fundef
| DEF_mapdef(mapdef) -> pp_mapdef mapdef
| DEF_val(letbind) -> pp_letbind letbind
| DEF_spec(val_spec) -> pp_val_spec val_spec
| DEF_fixity(prec,num,id) -> string "(" ^^ string "fix" ^^ string " " ^^ pp_prec prec ^^ string " " ^^ string num ^^ string " " ^^ pp_id id ^^ string ")"
| DEF_overload(id,id0) -> string "(" ^^ string "overload" ^^ string " " ^^ pp_id id ^^ string " " ^^ string "[" ^^ string " " ^^ separate (string ";") (List.map (function (id0) -> pp_id id0) id0) ^^ string " " ^^ string "]" ^^ string ")"
| DEF_default(default_spec) -> pp_default_spec default_spec
| DEF_scattered(scattered_def) -> pp_scattered_def scattered_def
| DEF_measure(id,pat,exp) -> string "(" ^^ string "termination_measure" ^^ string " " ^^ pp_id id ^^ string " " ^^ pp_pat pat ^^ string " " ^^ string "=" ^^ string " " ^^ pp_exp exp ^^ string ")"
| DEF_loop_measures(id,loop_measure0) -> string "(" ^^ string "termination_measure" ^^ string " " ^^ pp_id id ^^ string " " ^^ separate (string ",") (List.map (function (loop_measure0) -> pp_loop_measure loop_measure0) loop_measure0) ^^ string ")"
| DEF_reg_dec(dec_spec) -> pp_dec_spec dec_spec
| DEF_internal_mutrec(fundef0) -> separate (string " ") (List.map (function (fundef0) -> pp_fundef fundef0) fundef0)
| DEF_pragma(string1,string2,l) -> string "(" ^^ string "$" ^^ string " " ^^ string string1 ^^ string " " ^^ string string2 ^^ string " " ^^ pp_l l ^^ string ")"

and pp_defs x = match x with
| Defs(def0) -> separate (string " ") (List.map (function (def0) -> pp_def def0) def0)

