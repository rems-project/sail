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
(*    Thomas Bauereiss                                                    *)
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

open Ast
open Util
open Big_int

let mk_nc nc_aux = NC_aux (nc_aux, Parse_ast.Unknown)

let mk_nexp nexp_aux = Nexp_aux (nexp_aux, Parse_ast.Unknown)

let rec map_exp_annot f (E_aux (exp, annot)) = E_aux (map_exp_annot_aux f exp, f annot)
and map_exp_annot_aux f = function
  | E_block xs -> E_block (List.map (map_exp_annot f) xs)
  | E_nondet xs -> E_nondet (List.map (map_exp_annot f) xs)
  | E_id id -> E_id id
  | E_lit lit -> E_lit lit
  | E_cast (typ, exp) -> E_cast (typ, map_exp_annot f exp)
  | E_app (id, xs) -> E_app (id, List.map (map_exp_annot f) xs)
  | E_app_infix (x, op, y) -> E_app_infix (map_exp_annot f x, op, map_exp_annot f y)
  | E_tuple xs -> E_tuple (List.map (map_exp_annot f) xs)
  | E_if (cond, t, e) -> E_if (map_exp_annot f cond, map_exp_annot f t, map_exp_annot f e)
  | E_for (v, e1, e2, e3, o, e4) -> E_for (v, map_exp_annot f e1, map_exp_annot f e2, map_exp_annot f e3, o, map_exp_annot f e4)
  | E_vector exps -> E_vector (List.map (map_exp_annot f) exps)
  | E_vector_indexed (iexps, opt_default) ->
     E_vector_indexed (List.map (fun (i, exp) -> (i, map_exp_annot f exp)) iexps, map_opt_default_annot f opt_default)
  | E_vector_access (exp1, exp2) -> E_vector_access (map_exp_annot f exp1, map_exp_annot f exp2)
  | E_vector_subrange (exp1, exp2, exp3) -> E_vector_subrange (map_exp_annot f exp1, map_exp_annot f exp2, map_exp_annot f exp3)
  | E_vector_update (exp1, exp2, exp3) -> E_vector_update (map_exp_annot f exp1, map_exp_annot f exp2, map_exp_annot f exp3)
  | E_vector_update_subrange (exp1, exp2, exp3, exp4) ->
     E_vector_update_subrange (map_exp_annot f exp1, map_exp_annot f exp2, map_exp_annot f exp3, map_exp_annot f exp4)
  | E_vector_append (exp1, exp2) -> E_vector_append (map_exp_annot f exp1, map_exp_annot f exp2)
  | E_list xs -> E_list (List.map (map_exp_annot f) xs)
  | E_cons (exp1, exp2) -> E_cons (map_exp_annot f exp1, map_exp_annot f exp2)
  | E_record fexps -> E_record (map_fexps_annot f fexps)
  | E_record_update (exp, fexps) -> E_record_update (map_exp_annot f exp, map_fexps_annot f fexps)
  | E_field (exp, id) -> E_field (map_exp_annot f exp, id)
  | E_case (exp, cases) -> E_case (map_exp_annot f exp, List.map (map_pexp_annot f) cases)
  | E_let (letbind, exp) -> E_let (map_letbind_annot f letbind, map_exp_annot f exp)
  | E_assign (lexp, exp) -> E_assign (map_lexp_annot f lexp, map_exp_annot f exp)
  | E_sizeof nexp -> E_sizeof nexp
  | E_constraint nc -> E_constraint nc
  | E_exit exp -> E_exit (map_exp_annot f exp)
  | E_return exp -> E_return (map_exp_annot f exp)
  | E_assert (test, msg) -> E_assert (map_exp_annot f test, map_exp_annot f msg)
  | E_internal_cast (annot, exp) -> E_internal_cast (f annot, map_exp_annot f exp)
  | E_internal_exp annot -> E_internal_exp (f annot)
  | E_sizeof_internal annot -> E_sizeof_internal (f annot)
  | E_internal_exp_user (annot1, annot2) -> E_internal_exp_user (f annot1, f annot2)
  | E_comment str -> E_comment str
  | E_comment_struc exp -> E_comment_struc (map_exp_annot f exp)
  | E_internal_let (lexp, exp1, exp2) -> E_internal_let (map_lexp_annot f lexp, map_exp_annot f exp1, map_exp_annot f exp2)
  | E_internal_plet (pat, exp1, exp2) -> E_internal_plet (map_pat_annot f pat, map_exp_annot f exp1, map_exp_annot f exp2)
  | E_internal_return exp -> E_internal_return (map_exp_annot f exp)
and map_opt_default_annot f (Def_val_aux (df, annot)) = Def_val_aux (map_opt_default_annot_aux f df, f annot)
and map_opt_default_annot_aux f = function
  | Def_val_empty -> Def_val_empty
  | Def_val_dec exp -> Def_val_dec (map_exp_annot f exp)
and map_fexps_annot f (FES_aux (FES_Fexps (fexps, b), annot)) = FES_aux (FES_Fexps (List.map (map_fexp_annot f) fexps, b), f annot)
and map_fexp_annot f (FE_aux (FE_Fexp (id, exp), annot)) = FE_aux (FE_Fexp (id, map_exp_annot f exp), f annot)
and map_pexp_annot f (Pat_aux (pexp, annot)) = Pat_aux (map_pexp_annot_aux f pexp, f annot)
and map_pexp_annot_aux f = function
  | Pat_exp (pat, exp) -> Pat_exp (map_pat_annot f pat, map_exp_annot f exp)
  | Pat_when (pat, guard, exp) -> Pat_when (map_pat_annot f pat, map_exp_annot f guard, map_exp_annot f exp)
and map_pat_annot f (P_aux (pat, annot)) = P_aux (map_pat_annot_aux f pat, f annot)
and map_pat_annot_aux f = function
  | P_lit lit -> P_lit lit
  | P_wild -> P_wild
  | P_as (pat, id) -> P_as (map_pat_annot f pat, id)
  | P_typ (typ, pat) -> P_typ (typ, map_pat_annot f pat)
  | P_id id -> P_id id
  | P_app (id, pats) -> P_app (id, List.map (map_pat_annot f) pats)
  | P_record (fpats, b) -> P_record (List.map (map_fpat_annot f) fpats, b)
  | P_tup pats -> P_tup (List.map (map_pat_annot f) pats)
  | P_list pats -> P_list (List.map (map_pat_annot f) pats)
  | P_vector_concat pats -> P_vector_concat (List.map (map_pat_annot f) pats)
  | P_vector_indexed ipats -> P_vector_indexed (List.map (fun (i, pat) -> (i, map_pat_annot f pat)) ipats)
  | P_vector pats -> P_vector (List.map (map_pat_annot f) pats)
  | P_cons (pat1, pat2) -> P_cons (map_pat_annot f pat1, map_pat_annot f pat2)
and map_fpat_annot f (FP_aux (FP_Fpat (id, pat), annot)) = FP_aux (FP_Fpat (id, map_pat_annot f pat), f annot)
and map_letbind_annot f (LB_aux (lb, annot)) = LB_aux (map_letbind_annot_aux f lb, f annot)
and map_letbind_annot_aux f = function
  | LB_val_explicit (typschm, pat, exp) -> LB_val_explicit (typschm, map_pat_annot f pat, map_exp_annot f exp)
  | LB_val_implicit (pat, exp) -> LB_val_implicit (map_pat_annot f pat, map_exp_annot f exp)
and map_lexp_annot f (LEXP_aux (lexp, annot)) = LEXP_aux (map_lexp_annot_aux f lexp, f annot)
and map_lexp_annot_aux f = function
  | LEXP_id id -> LEXP_id id
  | LEXP_memory (id, exps) -> LEXP_memory (id, List.map (map_exp_annot f) exps)
  | LEXP_cast (typ, id) -> LEXP_cast (typ, id)
  | LEXP_tup lexps -> LEXP_tup (List.map (map_lexp_annot f) lexps)
  | LEXP_vector (lexp, exp) -> LEXP_vector (map_lexp_annot f lexp, map_exp_annot f exp)
  | LEXP_vector_range (lexp, exp1, exp2) -> LEXP_vector_range (map_lexp_annot f lexp, map_exp_annot f exp1, map_exp_annot f exp2)
  | LEXP_field (lexp, id) -> LEXP_field (map_lexp_annot f lexp, id)

let id_loc = function
  | Id_aux (_, l) -> l

let kid_loc = function
  | Kid_aux (_, l) -> l

let string_of_id = function
  | Id_aux (Id v, _) -> v
  | Id_aux (DeIid v, _) -> "(deinfix " ^ v ^ ")"

let string_of_kid = function
  | Kid_aux (Var v, _) -> v

let string_of_base_effect_aux = function
  | BE_rreg -> "rreg"
  | BE_wreg -> "wreg"
  | BE_rmem -> "rmem"
  | BE_rmemt -> "rmemt"
  | BE_wmem -> "wmem"
  | BE_eamem -> "eamem"
  | BE_exmem -> "exmem"
  | BE_wmv -> "wmv"
  | BE_wmvt -> "wmvt"
  | BE_barr -> "barr"
  | BE_depend -> "depend"
  | BE_undef -> "undef"
  | BE_unspec -> "unspec"
  | BE_nondet -> "nondet"
  | BE_escape -> "escape"
  | BE_lset -> "lset"
  | BE_lret -> "lret"

let string_of_base_kind_aux = function
  | BK_type -> "Type"
  | BK_nat -> "Nat"
  | BK_order -> "Order"
  | BK_effect -> "Effect"

let string_of_base_kind (BK_aux (bk, _)) = string_of_base_kind_aux bk

let string_of_kind (K_aux (K_kind bks, _)) = string_of_list " -> " string_of_base_kind bks

let string_of_base_effect = function
  | BE_aux (beff, _) -> string_of_base_effect_aux beff

let string_of_effect = function
  | Effect_aux (Effect_var kid, _) ->
     string_of_kid kid
  | Effect_aux (Effect_set [], _) -> "pure"
  | Effect_aux (Effect_set beffs, _) ->
     "{" ^ string_of_list ", " string_of_base_effect beffs ^ "}"

let string_of_order = function
  | Ord_aux (Ord_var kid, _) -> string_of_kid kid
  | Ord_aux (Ord_inc, _) -> "inc"
  | Ord_aux (Ord_dec, _) -> "dec"

let rec string_of_nexp = function
  | Nexp_aux (nexp, _) -> string_of_nexp_aux nexp
and string_of_nexp_aux = function
  | Nexp_id id -> string_of_id id
  | Nexp_var kid -> string_of_kid kid
  | Nexp_constant c -> string_of_int c
  | Nexp_times (n1, n2) -> "(" ^ string_of_nexp n1 ^ " * " ^ string_of_nexp n2 ^ ")"
  | Nexp_sum (n1, n2) -> "(" ^ string_of_nexp n1 ^ " + " ^ string_of_nexp n2 ^ ")"
  | Nexp_minus (n1, n2) -> "(" ^ string_of_nexp n1 ^ " - " ^ string_of_nexp n2 ^ ")"
  | Nexp_exp n -> "2 ^ " ^ string_of_nexp n
  | Nexp_neg n -> "- " ^ string_of_nexp n

let rec string_of_typ = function
  | Typ_aux (typ, l) -> string_of_typ_aux typ
and string_of_typ_aux = function
  | Typ_wild -> "_"
  | Typ_id id -> string_of_id id
  | Typ_var kid -> string_of_kid kid
  | Typ_tup typs -> "(" ^ string_of_list ", " string_of_typ typs ^ ")"
  | Typ_app (id, args) -> string_of_id id ^ "<" ^ string_of_list ", " string_of_typ_arg args ^ ">"
  | Typ_fn (typ_arg, typ_ret, eff) ->
     string_of_typ typ_arg ^ " -> " ^ string_of_typ typ_ret ^ " effect " ^ string_of_effect eff
and string_of_typ_arg = function
  | Typ_arg_aux (typ_arg, l) -> string_of_typ_arg_aux typ_arg
and string_of_typ_arg_aux = function
  | Typ_arg_nexp n -> string_of_nexp n
  | Typ_arg_typ typ -> string_of_typ typ
  | Typ_arg_order o -> string_of_order o
  | Typ_arg_effect eff -> string_of_effect eff

let rec string_of_n_constraint = function
  | NC_aux (NC_fixed (n1, n2), _) -> string_of_nexp n1 ^ " = " ^ string_of_nexp n2
  | NC_aux (NC_not_equal (n1, n2), _) -> string_of_nexp n1 ^ " != " ^ string_of_nexp n2
  | NC_aux (NC_bounded_ge (n1, n2), _) -> string_of_nexp n1 ^ " >= " ^ string_of_nexp n2
  | NC_aux (NC_bounded_le (n1, n2), _) -> string_of_nexp n1 ^ " <= " ^ string_of_nexp n2
  | NC_aux (NC_or (nc1, nc2), _) ->
     "(" ^ string_of_n_constraint nc1 ^ " | " ^ string_of_n_constraint nc2 ^ ")"
  | NC_aux (NC_and (nc1, nc2), _) ->
     "(" ^ string_of_n_constraint nc1 ^ " & " ^ string_of_n_constraint nc2 ^ ")"
  | NC_aux (NC_nat_set_bounded (kid, ns), _) ->
     string_of_kid kid ^ " IN {" ^ string_of_list ", " string_of_int ns ^ "}"
  | NC_aux (NC_true, _) -> "true"
  | NC_aux (NC_false, _) -> "false"

let string_of_quant_item_aux = function
  | QI_id (KOpt_aux (KOpt_none kid, _)) -> string_of_kid kid
  | QI_id (KOpt_aux (KOpt_kind (k, kid), _)) -> string_of_kind k ^ " " ^ string_of_kid kid
  | QI_const constr -> string_of_n_constraint constr

let string_of_quant_item = function
  | QI_aux (qi, _) -> string_of_quant_item_aux qi

let string_of_typquant_aux = function
  | TypQ_tq quants -> "forall " ^ string_of_list ", " string_of_quant_item quants
  | TypQ_no_forall -> ""

let string_of_typquant = function
  | TypQ_aux (quant, _) -> string_of_typquant_aux quant

let string_of_typschm (TypSchm_aux (TypSchm_ts (quant, typ), _)) =
  string_of_typquant quant ^ ". " ^ string_of_typ typ
let string_of_lit (L_aux (lit, _)) =
  match lit with
  | L_unit -> "()"
  | L_zero -> "bitzero"
  | L_one -> "bitone"
  | L_true -> "true"
  | L_false -> "false"
  | L_num n -> string_of_int n
  | L_hex n -> "0x" ^ n
  | L_bin n -> "0b" ^ n
  | L_undef -> "undefined"
  | L_real r -> r
  | L_string str -> "\"" ^ str ^ "\""

let rec string_of_exp (E_aux (exp, _)) =
  match exp with
  | E_block exps -> "{ " ^ string_of_list "; " string_of_exp exps ^ " }"
  | E_id v -> string_of_id v
  | E_sizeof nexp -> "sizeof " ^ string_of_nexp nexp
  | E_constraint nc -> "constraint(" ^ string_of_n_constraint nc ^ ")"
  | E_lit lit -> string_of_lit lit
  | E_return exp -> "return " ^ string_of_exp exp
  | E_app (f, args) -> string_of_id f ^ "(" ^ string_of_list ", " string_of_exp args ^ ")"
  | E_app_infix (x, op, y) -> "(" ^ string_of_exp x ^ " " ^ string_of_id op ^ " " ^ string_of_exp y ^ ")"
  | E_tuple exps -> "(" ^ string_of_list ", " string_of_exp exps ^ ")"
  | E_case (exp, cases) ->
     "switch " ^ string_of_exp exp ^ " { case " ^ string_of_list " case " string_of_pexp cases ^ "}"
  | E_let (letbind, exp) -> "let " ^ string_of_letbind letbind ^ " in " ^ string_of_exp exp
  | E_assign (lexp, bind) -> string_of_lexp lexp ^ " := " ^ string_of_exp bind
  | E_cast (typ, exp) -> "(" ^ string_of_typ typ ^ ") " ^ string_of_exp exp
  | E_vector vec -> "[" ^ string_of_list ", " string_of_exp vec ^ "]"
  | E_vector_access (v, n) -> string_of_exp v ^ "[" ^ string_of_exp n ^ "]"
  | E_vector_subrange (v, n1, n2) -> string_of_exp v ^ "[" ^ string_of_exp n1 ^ " .. " ^ string_of_exp n2 ^ "]"
  | E_vector_append (v1, v2) -> string_of_exp v1 ^ " : " ^ string_of_exp v2
  | E_if (cond, then_branch, else_branch) ->
     "if " ^ string_of_exp cond ^ " then " ^ string_of_exp then_branch ^ " else " ^ string_of_exp else_branch
  | E_field (exp, id) -> string_of_exp exp ^ "." ^ string_of_id id
  | E_for (id, f, t, u, ord, body) ->
     "foreach ("
     ^ string_of_id id ^ " from " ^ string_of_exp f ^ " to " ^ string_of_exp t
     ^ " by " ^ string_of_exp u ^ " order " ^ string_of_order ord
     ^ ") { "
     ^ string_of_exp body
  | E_assert (test, msg) -> "assert(" ^ string_of_exp test ^ ", " ^ string_of_exp msg ^ ")"
  | E_exit exp -> "exit " ^ string_of_exp exp
  | _ -> "INTERNAL"
and string_of_pexp (Pat_aux (pexp, _)) =
  match pexp with
  | Pat_exp (pat, exp) -> string_of_pat pat ^ " -> " ^ string_of_exp exp
  | Pat_when (pat, guard, exp) -> string_of_pat pat ^ " when " ^ string_of_exp guard ^ " -> " ^ string_of_exp exp
and string_of_pat (P_aux (pat, l)) =
  match pat with
  | P_lit lit -> string_of_lit lit
  | P_wild -> "_"
  | P_id v -> string_of_id v
  | P_typ (typ, pat) -> "(" ^ string_of_typ typ ^ ") " ^ string_of_pat pat
  | P_tup pats -> "(" ^ string_of_list ", " string_of_pat pats ^ ")"
  | P_app (f, pats) -> string_of_id f ^ "(" ^ string_of_list ", " string_of_pat pats ^ ")"
  | P_cons (pat1, pat2) -> string_of_pat pat1 ^ " :: " ^ string_of_pat pat2
  | P_list pats -> "[||" ^ string_of_list "," string_of_pat pats ^ "||]"
  | P_vector_concat pats -> string_of_list " : " string_of_pat pats
  | P_vector pats -> "[" ^ string_of_list ", " string_of_pat pats ^ "]"
  | P_as (pat, id) -> string_of_pat pat ^ " as " ^ string_of_id id
  | _ -> "PAT"
and string_of_lexp (LEXP_aux (lexp, _)) =
  match lexp with
  | LEXP_id v -> string_of_id v
  | LEXP_cast (typ, v) -> "(" ^ string_of_typ typ ^ ") " ^ string_of_id v
  | LEXP_tup lexps -> "(" ^ string_of_list ", " string_of_lexp lexps ^ ")"
  | LEXP_vector (lexp, exp) -> string_of_lexp lexp ^ "[" ^ string_of_exp exp ^ "]"
  | LEXP_field (lexp, id) -> string_of_lexp lexp ^ "." ^ string_of_id id
  | LEXP_memory (f, xs) -> string_of_id f ^ "(" ^ string_of_list ", " string_of_exp xs ^ ")"
  | _ -> "LEXP"
and string_of_letbind (LB_aux (lb, l)) =
  match lb with
  | LB_val_implicit (pat, exp) -> string_of_pat pat ^ " = " ^ string_of_exp exp
  | LB_val_explicit (typschm, pat, exp) ->
     string_of_typschm typschm ^ " " ^ string_of_pat pat ^ " = " ^ string_of_exp exp

let rec string_of_index_range (BF_aux (ir, _)) =
  match ir with
  | BF_single n -> string_of_int n
  | BF_range (n, m) -> string_of_int n ^ " .. " ^ string_of_int m
  | BF_concat (ir1, ir2) -> "(" ^ string_of_index_range ir1 ^ ") : (" ^ string_of_index_range ir2 ^ ")"

let id_of_fundef (FD_aux (FD_function (_, _, _, funcls), (l, _))) =
  match (List.fold_right
           (fun (FCL_aux (FCL_Funcl (id, _, _), _)) id' ->
             match id' with
             | Some id' -> if string_of_id id' = string_of_id id then Some id'
                           else raise (Reporting_basic.err_typ l
                             ("Function declaration expects all definitions to have the same name, "
                              ^ string_of_id id ^ " differs from other definitions of " ^ string_of_id id'))
             | None -> Some id) funcls None)
  with
  | Some id -> id
  | None -> raise (Reporting_basic.err_typ l "funcl list is empty")

module Kid = struct
  type t = kid
  let compare kid1 kid2 = String.compare (string_of_kid kid1) (string_of_kid kid2)
end

module BE = struct
  type t = base_effect
  let compare be1 be2 = String.compare (string_of_base_effect be1) (string_of_base_effect be2)
end

module Id = struct
  type t = id
  let compare id1 id2 =
    match (id1, id2) with
    | Id_aux (Id x, _), Id_aux (Id y, _) -> String.compare x y
    | Id_aux (DeIid x, _), Id_aux (DeIid y, _) -> String.compare x y
    | Id_aux (Id _, _), Id_aux (DeIid _, _) -> -1
    | Id_aux (DeIid _, _), Id_aux (Id _, _) -> 1
end

module Bindings = Map.Make(Id)
module IdSet = Set.Make(Id)
module KBindings = Map.Make(Kid)
module KidSet = Set.Make(Kid)

let rec nexp_frees (Nexp_aux (nexp, l)) =
  match nexp with
  | Nexp_id _ -> raise (Reporting_basic.err_typ l "Unimplemented Nexp_id in nexp_frees")
  | Nexp_var kid -> KidSet.singleton kid
  | Nexp_constant _ -> KidSet.empty
  | Nexp_times (n1, n2) -> KidSet.union (nexp_frees n1) (nexp_frees n2)
  | Nexp_sum (n1, n2) -> KidSet.union (nexp_frees n1) (nexp_frees n2)
  | Nexp_minus (n1, n2) -> KidSet.union (nexp_frees n1) (nexp_frees n2)
  | Nexp_exp n -> nexp_frees n
  | Nexp_neg n -> nexp_frees n

let rec nexp_identical (Nexp_aux (nexp1, _)) (Nexp_aux (nexp2, _)) =
  match nexp1, nexp2 with
  | Nexp_id v1, Nexp_id v2 -> Id.compare v1 v2 = 0
  | Nexp_var kid1, Nexp_var kid2 -> Kid.compare kid1 kid2 = 0
  | Nexp_constant c1, Nexp_constant c2 -> c1 = c2
  | Nexp_times (n1a, n1b), Nexp_times (n2a, n2b) -> nexp_identical n1a n2a && nexp_identical n1b n2b
  | Nexp_sum (n1a, n1b), Nexp_sum (n2a, n2b) -> nexp_identical n1a n2a && nexp_identical n1b n2b
  | Nexp_minus (n1a, n1b), Nexp_minus (n2a, n2b) -> nexp_identical n1a n2a && nexp_identical n1b n2b
  | Nexp_exp n1, Nexp_exp n2 -> nexp_identical n1 n2
  | Nexp_neg n1, Nexp_neg n2 -> nexp_identical n1 n2
  | _, _ -> false

let rec is_nexp_constant (Nexp_aux (nexp, _)) = match nexp with
| Nexp_id _ | Nexp_var _ -> false
| Nexp_constant _ -> true
| Nexp_times (n1, n2) | Nexp_sum (n1, n2) | Nexp_minus (n1, n2) ->
  is_nexp_constant n1 && is_nexp_constant n2
| Nexp_exp n | Nexp_neg n -> is_nexp_constant n

let rec is_number (Typ_aux (t,_)) =
  match t with
  | Typ_app (Id_aux (Id "range", _),_)
  | Typ_app (Id_aux (Id "implicit", _),_)
  | Typ_app (Id_aux (Id "atom", _),_) -> true
  | _ -> false

let rec is_vector_typ = function
  | Typ_aux (Typ_app (Id_aux (Id "vector",_), [_;_;_;_]), _) -> true
  | Typ_aux (Typ_app (Id_aux (Id "register",_), [Typ_arg_aux (Typ_arg_typ rtyp,_)]), _) ->
    is_vector_typ rtyp
  | _ -> false

let typ_app_args_of = function
  | Typ_aux (Typ_app (Id_aux (Id c,_), targs), l) ->
    (c, List.map (fun (Typ_arg_aux (a,_)) -> a) targs, l)
  | Typ_aux (_, l) -> raise (Reporting_basic.err_typ l "typ_app_args_of called on non-app type")

let rec vector_typ_args_of typ = match typ_app_args_of typ with
  | ("vector", [Typ_arg_nexp start; Typ_arg_nexp len; Typ_arg_order ord; Typ_arg_typ etyp], _) ->
    (start, len, ord, etyp)
  | ("register", [Typ_arg_typ rtyp], _) -> vector_typ_args_of rtyp
  | (_, _, l) -> raise (Reporting_basic.err_typ l "vector_typ_args_of called on non-vector type")

let is_order_inc = function
  | Ord_aux (Ord_inc, _) -> true
  | Ord_aux (Ord_dec, _) -> false
  | Ord_aux (Ord_var _, l) ->
    raise (Reporting_basic.err_unreachable l "is_order_inc called on vector with variable ordering")

let is_bit_typ = function
  | Typ_aux (Typ_id (Id_aux (Id "bit", _)), _) -> true
  | _ -> false

let is_bitvector_typ typ =
  if is_vector_typ typ then
    let (_,_,_,etyp) = vector_typ_args_of typ in
    is_bit_typ etyp
  else false

let has_effect (Effect_aux (eff,_)) searched_for = match eff with
  | Effect_set effs ->
    List.exists (fun (BE_aux (be,_)) -> be = searched_for) effs
  | Effect_var _ ->
    raise (Reporting_basic.err_unreachable Parse_ast.Unknown
      "has_effect called on effect variable")
