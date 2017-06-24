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

let debug = ref 1
let depth = ref 0

let rec indent n = match n with
  | 0 -> ""
  | n -> "|   " ^ indent (n - 1)

let typ_debug m = if !debug > 1 then prerr_endline (indent !depth ^ m) else ()

let typ_print m = if !debug > 0 then prerr_endline (indent !depth ^ m) else ()

exception Type_error of l * string;;

let typ_error l m = raise (Type_error (l, m))

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
  | E_list xs -> E_list (List.map (map_exp_annot f) xs)
  | E_case (exp, cases) -> E_case (map_exp_annot f exp, List.map (map_pexp_annot f) cases)
  | E_let (letbind, exp) -> E_let (map_letbind_annot f letbind, map_exp_annot f exp)
  | E_assign (lexp, exp) -> E_assign (map_lexp_annot f lexp, map_exp_annot f exp)
  | E_sizeof nexp -> E_sizeof nexp
  | E_exit exp -> E_exit (map_exp_annot f exp)
  | E_return exp -> E_return (map_exp_annot f exp)
  | _ -> typ_error Parse_ast.Unknown "Unimplemented: Cannot map annot in exp"
and map_pexp_annot f (Pat_aux (Pat_exp (pat, exp), annot)) = Pat_aux (Pat_exp (map_pat_annot f pat, map_exp_annot f exp), f annot)
and map_pat_annot f (P_aux (pat, annot)) = P_aux (map_pat_annot_aux f pat, f annot)
and map_pat_annot_aux f = function
  | P_lit lit -> P_lit lit
  | P_wild -> P_wild
  | P_as (pat, id) -> P_as (map_pat_annot f pat, id)
  | P_typ (typ, pat) -> P_typ (typ, map_pat_annot f pat)
  | P_id id -> P_id id
  | P_app (id, pats) -> P_app (id, List.map (map_pat_annot f) pats)
  | P_tup pats -> P_tup (List.map (map_pat_annot f) pats)
  | P_list pats -> P_list (List.map (map_pat_annot f) pats)
  | _ -> typ_error Parse_ast.Unknown "Unimplemented: Cannot map annot in pat"
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
  | _ -> typ_error Parse_ast.Unknown "Unimplemented: Cannot map annot in lexp"

let string_of_id = function
  | Id_aux (Id v, _) -> v
  | Id_aux (DeIid v, _) -> v

let string_of_kid = function
  | Kid_aux (Var v, _) -> v

let id_loc = function
  | Id_aux (_, l) -> l

let kid_loc = function
  | Kid_aux (_, l) -> l

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
     typ_debug "kid effect occured"; string_of_kid kid
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

let string_of_n_constraint = function
  | NC_aux (NC_fixed (n1, n2), _) -> string_of_nexp n1 ^ " = " ^ string_of_nexp n2
  | NC_aux (NC_bounded_ge (n1, n2), _) -> string_of_nexp n1 ^ " >= " ^ string_of_nexp n2
  | NC_aux (NC_bounded_le (n1, n2), _) -> string_of_nexp n1 ^ " <= " ^ string_of_nexp n2
  | NC_aux (NC_nat_set_bounded (kid, ns), _) ->
     string_of_kid kid ^ " IN {" ^ string_of_list ", " string_of_int ns ^ "}"

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

let string_of_bind (typquant, typ) = string_of_typquant typquant ^ ". " ^ string_of_typ typ

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
  | L_string str -> "\"" ^ str ^ "\""

let rec string_of_exp (E_aux (exp, _)) =
  match exp with
  | E_block exps -> "{ " ^ string_of_list "; " string_of_exp exps ^ " }"
  | E_id v -> string_of_id v
  | E_sizeof nexp -> "sizeof " ^ string_of_nexp nexp
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
  | E_if (cond, then_branch, else_branch) ->
     "if " ^ string_of_exp cond ^ " then " ^ string_of_exp then_branch ^ " else " ^ string_of_exp else_branch
  | _ -> "INTERNAL"
and string_of_pexp (Pat_aux (Pat_exp (pat, exp), _)) = string_of_pat pat ^ " -> " ^ string_of_exp exp
and string_of_pat (P_aux (pat, l)) =
  match pat with
  | P_lit lit -> string_of_lit lit
  | P_wild -> "_"
  | P_id v -> string_of_id v
  | P_typ (typ, pat) -> "(" ^ string_of_typ typ ^ ") " ^ string_of_pat pat
  | P_tup pats -> "(" ^ string_of_list ", " string_of_pat pats ^ ")"
  | _ -> "PAT"
and string_of_lexp (LEXP_aux (lexp, _)) =
  match lexp with
  | LEXP_id v -> string_of_id v
  | LEXP_cast (typ, v) -> "(" ^ string_of_typ typ ^ ") " ^ string_of_id v
  | LEXP_tup lexps -> "(" ^ string_of_list ", " string_of_lexp lexps ^ ")"
  | _ -> "LEXP"
and string_of_letbind (LB_aux (lb, l)) =
  match lb with
  | LB_val_implicit (pat, exp) -> string_of_pat pat ^ " = " ^ string_of_exp exp
  | LB_val_explicit (typschm, pat, exp) ->
     string_of_typschm typschm ^ " " ^ string_of_pat pat ^ " = " ^ string_of_exp exp

module Kid = struct
  type t = kid
  let compare kid1 kid2 = String.compare (string_of_kid kid1) (string_of_kid kid2)
end

let unaux_nexp (Nexp_aux (nexp, _)) = nexp
let unaux_order (Ord_aux (ord, _)) = ord
let unaux_typ (Typ_aux (typ, _)) = typ

let mk_typ typ = Typ_aux (typ, Parse_ast.Unknown)
let mk_typ_arg arg = Typ_arg_aux (arg, Parse_ast.Unknown)
let mk_id str = Id_aux (Id str, Parse_ast.Unknown)

let rec nexp_subst sv subst (Nexp_aux (nexp, l)) = Nexp_aux (nexp_subst_aux sv subst nexp, l)
and nexp_subst_aux sv subst = function
  | Nexp_id v -> Nexp_id v
  | Nexp_var kid -> if Kid.compare kid sv = 0 then subst else Nexp_var kid
  | Nexp_constant c -> Nexp_constant c
  | Nexp_times (nexp1, nexp2) -> Nexp_times (nexp_subst sv subst nexp1, nexp_subst sv subst nexp2)
  | Nexp_sum (nexp1, nexp2) -> Nexp_sum (nexp_subst sv subst nexp1, nexp_subst sv subst nexp2)
  | Nexp_minus (nexp1, nexp2) -> Nexp_minus (nexp_subst sv subst nexp1, nexp_subst sv subst nexp2)
  | Nexp_exp nexp -> Nexp_exp (nexp_subst sv subst nexp)
  | Nexp_neg nexp -> Nexp_neg (nexp_subst sv subst nexp)

let rec nc_subst_nexp sv subst (NC_aux (nc, l)) = NC_aux (nc_subst_nexp_aux l sv subst nc, l)
and nc_subst_nexp_aux l sv subst = function
  | NC_fixed (n1, n2) -> NC_fixed (nexp_subst sv subst n1, nexp_subst sv subst n2)
  | NC_bounded_ge (n1, n2) -> NC_bounded_ge (nexp_subst sv subst n1, nexp_subst sv subst n2)
  | NC_bounded_le (n1, n2) -> NC_bounded_le (nexp_subst sv subst n1, nexp_subst sv subst n2)
  | NC_nat_set_bounded (kid, ints) as set_nc ->
      if compare kid sv = 0
      then typ_error l ("Cannot substitute " ^ string_of_kid sv ^ " into set constraint " ^ string_of_n_constraint (NC_aux (set_nc, l)))
      else set_nc

let rec typ_subst_nexp sv subst (Typ_aux (typ, l)) = Typ_aux (typ_subst_nexp_aux sv subst typ, l)
and typ_subst_nexp_aux sv subst = function
  | Typ_wild -> Typ_wild
  | Typ_id v -> Typ_id v
  | Typ_var kid -> Typ_var kid
  | Typ_fn (typ1, typ2, effs) -> Typ_fn (typ_subst_nexp sv subst typ1, typ_subst_nexp sv subst typ2, effs)
  | Typ_tup typs -> Typ_tup (List.map (typ_subst_nexp sv subst) typs)
  | Typ_app (f, args) -> Typ_app (f, List.map (typ_subst_arg_nexp sv subst) args)
and typ_subst_arg_nexp sv subst (Typ_arg_aux (arg, l)) = Typ_arg_aux (typ_subst_arg_nexp_aux sv subst arg, l)
and typ_subst_arg_nexp_aux sv subst = function
  | Typ_arg_nexp nexp -> Typ_arg_nexp (nexp_subst sv subst nexp)
  | Typ_arg_typ typ -> Typ_arg_typ (typ_subst_nexp sv subst typ)
  | Typ_arg_order ord -> Typ_arg_order ord
  | Typ_arg_effect eff -> Typ_arg_effect eff

let rec typ_subst_typ sv subst (Typ_aux (typ, l)) = Typ_aux (typ_subst_typ_aux sv subst typ, l)
and typ_subst_typ_aux sv subst = function
  | Typ_wild -> Typ_wild
  | Typ_id v -> Typ_id v
  | Typ_var kid -> if Kid.compare kid sv = 0 then subst else Typ_var kid
  | Typ_fn (typ1, typ2, effs) -> Typ_fn (typ_subst_typ sv subst typ1, typ_subst_typ sv subst typ2, effs)
  | Typ_tup typs -> Typ_tup (List.map (typ_subst_typ sv subst) typs)
  | Typ_app (f, args) -> Typ_app (f, List.map (typ_subst_arg_typ sv subst) args)
and typ_subst_arg_typ sv subst (Typ_arg_aux (arg, l)) = Typ_arg_aux (typ_subst_arg_typ_aux sv subst arg, l)
and typ_subst_arg_typ_aux sv subst = function
  | Typ_arg_nexp nexp -> Typ_arg_nexp nexp
  | Typ_arg_typ typ -> Typ_arg_typ (typ_subst_typ sv subst typ)
  | Typ_arg_order ord -> Typ_arg_order ord
  | Typ_arg_effect eff -> Typ_arg_effect eff

let order_subst_aux sv subst = function
  | Ord_var kid -> if Kid.compare kid sv = 0 then subst else Ord_var kid
  | Ord_inc -> Ord_inc
  | Ord_dec -> Ord_dec

let order_subst sv subst (Ord_aux (ord, l)) = Ord_aux (order_subst_aux sv subst ord, l)

let rec typ_subst_order sv subst (Typ_aux (typ, l)) = Typ_aux (typ_subst_order_aux sv subst typ, l)
and typ_subst_order_aux sv subst = function
  | Typ_wild -> Typ_wild
  | Typ_id v -> Typ_id v
  | Typ_var kid -> Typ_var kid
  | Typ_fn (typ1, typ2, effs) -> Typ_fn (typ_subst_order sv subst typ1, typ_subst_order sv subst typ2, effs)
  | Typ_tup typs -> Typ_tup (List.map (typ_subst_order sv subst) typs)
  | Typ_app (f, args) -> Typ_app (f, List.map (typ_subst_arg_order sv subst) args)
and typ_subst_arg_order sv subst (Typ_arg_aux (arg, l)) = Typ_arg_aux (typ_subst_arg_order_aux sv subst arg, l)
and typ_subst_arg_order_aux sv subst = function
  | Typ_arg_nexp nexp -> Typ_arg_nexp nexp
  | Typ_arg_typ typ -> Typ_arg_typ (typ_subst_order sv subst typ)
  | Typ_arg_order ord -> Typ_arg_order (order_subst sv subst ord)
  | Typ_arg_effect eff -> Typ_arg_effect eff

let rec typ_subst_kid sv subst (Typ_aux (typ, l)) = Typ_aux (typ_subst_kid_aux sv subst typ, l)
and typ_subst_kid_aux sv subst = function
  | Typ_wild -> Typ_wild
  | Typ_id v -> Typ_id v
  | Typ_var kid -> if Kid.compare kid sv = 0 then Typ_var subst else Typ_var kid
  | Typ_fn (typ1, typ2, effs) -> Typ_fn (typ_subst_kid sv subst typ1, typ_subst_kid sv subst typ2, effs)
  | Typ_tup typs -> Typ_tup (List.map (typ_subst_kid sv subst) typs)
  | Typ_app (f, args) -> Typ_app (f, List.map (typ_subst_arg_kid sv subst) args)
and typ_subst_arg_kid sv subst (Typ_arg_aux (arg, l)) = Typ_arg_aux (typ_subst_arg_kid_aux sv subst arg, l)
and typ_subst_arg_kid_aux sv subst = function
  | Typ_arg_nexp nexp -> Typ_arg_nexp (nexp_subst sv (Nexp_var subst) nexp)
  | Typ_arg_typ typ -> Typ_arg_typ (typ_subst_kid sv subst typ)
  | Typ_arg_order ord -> Typ_arg_order (order_subst sv (Ord_var subst) ord)
  | Typ_arg_effect eff -> Typ_arg_effect eff

let quant_item_subst_kid_aux sv subst = function
  | QI_id (KOpt_aux (KOpt_none kid, l)) as qid ->
     if Kid.compare kid sv = 0 then QI_id (KOpt_aux (KOpt_none subst, l)) else qid
  | QI_id (KOpt_aux (KOpt_kind (k, kid), l)) as qid ->
     if Kid.compare kid sv = 0 then QI_id (KOpt_aux (KOpt_kind (k, subst), l)) else qid
  | QI_const nc -> QI_const (nc_subst_nexp sv (Nexp_var subst) nc)

let rec pow2 = function
  | 0 -> 1
  | n -> 2 * pow2 (n - 1)

let rec nexp_simp (Nexp_aux (nexp, l)) = Nexp_aux (nexp_simp_aux nexp, l)
and nexp_simp_aux = function
  | Nexp_sum (n1, n2) ->
     begin
       let (Nexp_aux (n1_simp, _) as n1) = nexp_simp n1 in
       let (Nexp_aux (n2_simp, _) as n2) = nexp_simp n2 in
       match n1_simp, n2_simp with
       | Nexp_constant c1, Nexp_constant c2 -> Nexp_constant (c1 + c2)
       | _, _ -> Nexp_sum (n1, n2)
     end
  | Nexp_times (n1, n2) ->
     begin
       let (Nexp_aux (n1_simp, _) as n1) = nexp_simp n1 in
       let (Nexp_aux (n2_simp, _) as n2) = nexp_simp n2 in
       match n1_simp, n2_simp with
       | Nexp_constant c1, Nexp_constant c2 -> Nexp_constant (c1 * c2)
       | _, _ -> Nexp_times (n1, n2)
     end
  | Nexp_minus (n1, n2) ->
     begin
       let (Nexp_aux (n1_simp, _) as n1) = nexp_simp n1 in
       let (Nexp_aux (n2_simp, _) as n2) = nexp_simp n2 in
       match n1_simp, n2_simp with
       | Nexp_constant c1, Nexp_constant c2 -> Nexp_constant (c1 - c2)
       | _, _ -> Nexp_minus (n1, n2)
     end
  | Nexp_exp n ->
     begin
       let (Nexp_aux (n_simp, _) as n) = nexp_simp n in
       match n_simp with
       | Nexp_constant c -> Nexp_constant (pow2 c)
       | _ -> Nexp_exp n
     end
  | nexp -> nexp

let quant_item_subst_kid sv subst (QI_aux (quant, l)) = QI_aux (quant_item_subst_kid_aux sv subst quant, l)

let typquant_subst_kid_aux sv subst = function
  | TypQ_tq quants -> TypQ_tq (List.map (quant_item_subst_kid sv subst) quants)
  | TypQ_no_forall -> TypQ_no_forall

let typquant_subst_kid sv subst (TypQ_aux (typq, l)) = TypQ_aux (typquant_subst_kid_aux sv subst typq, l)

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

type mut = Immutable | Mutable

type lvar = Register of typ | Local of mut * typ | Unbound

module Env : sig
  type t
  val get_val_spec : id -> t -> typquant * typ
  val add_val_spec : id -> typquant * typ -> t -> t
  val get_local : id -> t -> mut * typ
  val add_local : id -> mut * typ -> t -> t
  val get_register : id -> t -> typ
  val add_register : id -> typ -> t -> t
  val add_regtyp : id -> int -> int -> (index_range * id) list -> t -> t
  val is_mutable : id -> t -> bool
  val get_constraints : t -> n_constraint list
  val add_constraint : n_constraint -> t -> t
  val get_typ_var : kid -> t -> base_kind_aux
  val add_typ_var : kid -> base_kind_aux -> t -> t
  val get_ret_typ : t -> typ option
  val add_ret_typ : typ -> t -> t
  val add_typ_synonym : id -> (typ_arg list -> typ) -> t -> t
  val get_typ_synonym : id -> t -> typ_arg list -> typ
  val add_overloads : id -> id list -> t -> t
  val get_overloads : id -> t -> id list
  val get_default_order : t -> order
  val set_default_order_inc : t -> t
  val set_default_order_dec : t -> t
  val get_casts : t -> id list
  val allow_casts : t -> bool
  val no_casts : t -> t
  val lookup_id : id -> t -> lvar
  val fresh_kid : t -> kid
  val expand_synonyms : t -> typ -> typ
  val empty : t
end = struct
  type t =
    { top_val_specs : (typquant * typ) Bindings.t;
      locals : (mut * typ) Bindings.t;
      registers : typ Bindings.t;
      regtyps : (int * int * (index_range * id) list) Bindings.t;
      typ_vars : base_kind_aux KBindings.t;
      typ_synonyms : (typ_arg list -> typ) Bindings.t;
      overloads : (id list) Bindings.t;
      casts : id list;
      allow_casts : bool;
      constraints : n_constraint list;
      default_order : order option;
      ret_typ : typ option
    }

  let empty =
    { top_val_specs = Bindings.empty;
      locals = Bindings.empty;
      registers = Bindings.empty;
      regtyps = Bindings.empty;
      typ_vars = KBindings.empty;
      typ_synonyms = Bindings.empty;
      overloads = Bindings.empty;
      casts = [mk_id "cast_vec_to_range"; mk_id "cast_01_to_vec"; mk_id "reg_deref"];
      allow_casts = true;
      constraints = [];
      default_order = None;
      ret_typ = None;
    }

  let counter = ref 0

  let fresh_kid env =
    let fresh = Kid_aux (Var ("'fv" ^ string_of_int !counter), Parse_ast.Unknown) in
    incr counter; fresh

  let freshen_kid env kid (typq, typ) =
    let fresh = fresh_kid env in
    (typquant_subst_kid kid fresh typq, typ_subst_kid kid fresh typ)

  let get_val_spec id env =
    try
      let bind = Bindings.find id env.top_val_specs in
      typ_debug ("get_val_spec: Env has " ^ string_of_list ", " (fun (kid, bk) -> string_of_kid kid ^ " => " ^ string_of_base_kind_aux bk) (KBindings.bindings env.typ_vars));
      let bind' = List.fold_left (fun bind (kid, _) -> freshen_kid env kid bind) bind (KBindings.bindings env.typ_vars) in
      typ_debug ("get_val_spec: freshened to " ^ string_of_bind bind');
      bind'
    with
    | Not_found -> typ_error (id_loc id) ("No val spec found for " ^ string_of_id id)

  let add_val_spec id bind env =
    if Bindings.mem id env.top_val_specs
    then typ_error (id_loc id) ("Identifier " ^ string_of_id id ^ " is already bound")
    else
      begin
        typ_debug ("Adding val spec binding " ^ string_of_id id ^ " :: " ^ string_of_bind bind);
        { env with top_val_specs = Bindings.add id bind env.top_val_specs }
      end

  let get_local id env =
    try Bindings.find id env.locals with
    | Not_found -> typ_error (id_loc id) ("No local binding found for " ^ string_of_id id)

  let is_mutable id env =
    try
      let (mut, _) = Bindings.find id env.locals in
      match mut with
      | Mutable -> true
      | Immutable -> false
    with
    | Not_found -> typ_error (id_loc id) ("No local binding found for " ^ string_of_id id)

  let string_of_mtyp (mut, typ) = match mut with
    | Immutable -> string_of_typ typ
    | Mutable -> "ref<" ^ string_of_typ typ ^ ">"

  let add_local id mtyp env =
    begin
      typ_print ("Adding local binding " ^ string_of_id id ^ " :: " ^ string_of_mtyp mtyp);
      { env with locals = Bindings.add id mtyp env.locals }
    end

  let get_register id env =
    try Bindings.find id env.registers with
    | Not_found -> typ_error (id_loc id) ("No register binding found for " ^ string_of_id id)

  let get_overloads id env =
    try Bindings.find id env.overloads with
    | Not_found -> []

  let add_overloads id ids env =
    typ_print ("Adding overloads for " ^ string_of_id id ^ " [" ^ string_of_list ", " string_of_id ids ^ "]");
    { env with overloads = Bindings.add id ids env.overloads }

  let get_casts env = env.casts

  let check_index_range cmp f t (BF_aux (ir, l)) =
    match ir with
    | BF_single n ->
       if cmp f n && cmp n t
       then n
       else typ_error l ("Badly ordered index range: " ^ string_of_list ", " string_of_int [f; n; t])
    | BF_range (n1, n2) ->
       if cmp f n1 && cmp n1 n2 && cmp n2 t
       then n2
       else typ_error l ("Badly ordered index range: " ^ string_of_list ", " string_of_int [f; n1; n2; t])
    | BF_concat _ -> typ_error l "Index range concatenation currently unsupported"

  let rec check_index_ranges ids cmp base top = function
    | [] -> ()
    | ((range, id) :: ranges) ->
       if IdSet.mem id ids
       then typ_error (id_loc id) ("Duplicate id " ^ string_of_id id ^ " in register typedef")
       else
         begin
           let base' = check_index_range cmp base top range in
           check_index_ranges (IdSet.add id ids) cmp base' top ranges
         end

  let add_register id typ env =
    if Bindings.mem id env.registers
    then typ_error (id_loc id) ("Register " ^ string_of_id id ^ " is already bound")
    else
      begin
        typ_print ("Adding register binding " ^ string_of_id id ^ " :: " ^ string_of_typ typ);
        { env with registers = Bindings.add id typ env.registers }
      end

  let add_regtyp id base top ranges env =
    if Bindings.mem id env.regtyps
    then typ_error (id_loc id) ("Register typ " ^ string_of_id id ^ " is already bound")
    else
      begin
        typ_print ("Adding register type " ^ string_of_id id);
        if base > top
        then check_index_ranges IdSet.empty (fun x y -> x > y) (base + 1) (top - 1) ranges
        else check_index_ranges IdSet.empty (fun x y -> x < y) (base - 1) (top + 1) ranges;
        { env with regtyps = Bindings.add id (base, top, ranges) env.regtyps }
      end

  let lookup_id id env =
    try
      let (mut, typ) = Bindings.find id env.locals in
      Local (mut, typ)
    with
    | Not_found ->
       begin
         try Register (Bindings.find id env.registers) with
         | Not_found -> Unbound
       end

  let get_typ_var kid env =
    try KBindings.find kid env.typ_vars with
    | Not_found -> typ_error (kid_loc kid) ("No kind identifier " ^ string_of_kid kid)

  let add_typ_var kid k env =
    if KBindings.mem kid env.typ_vars
    then typ_error (kid_loc kid) ("Kind identifier " ^ string_of_kid kid ^ " is already bound")
    else
      begin
        typ_debug ("Adding kind identifier binding " ^ string_of_kid kid ^ " :: " ^ string_of_base_kind_aux k);
        { env with typ_vars = KBindings.add kid k env.typ_vars }
      end

  let rec wf_nexp env (Nexp_aux (nexp, l)) =
    match nexp with
    | Nexp_id _ -> typ_error l "Unimplemented: Nexp_id"
    | Nexp_var kid ->
       begin
         match get_typ_var kid env with
         | BK_nat -> ()
         | kind -> typ_error l ("Constraint is badly formed, "
                                ^ string_of_kid kid ^ " has kind "
                                ^ string_of_base_kind_aux kind ^ " but should have kind Nat")
       end
    | Nexp_constant _ -> ()
    | Nexp_times (nexp1, nexp2) -> wf_nexp env nexp1; wf_nexp env nexp2
    | Nexp_sum (nexp1, nexp2) -> wf_nexp env nexp1; wf_nexp env nexp2
    | Nexp_minus (nexp1, nexp2) -> wf_nexp env nexp1; wf_nexp env nexp2
    | Nexp_exp nexp -> wf_nexp env nexp (* MAYBE: Could put restrictions on what is allowed here *)
    | Nexp_neg nexp -> wf_nexp env nexp

  let wf_constraint env (NC_aux (nc, _)) =
    match nc with
    | NC_fixed (n1, n2) -> wf_nexp env n1; wf_nexp env n2
    | NC_bounded_ge (n1, n2) -> wf_nexp env n1; wf_nexp env n2
    | NC_bounded_le (n1, n2) -> wf_nexp env n1; wf_nexp env n2
    | NC_nat_set_bounded (kid, ints) -> () (* MAYBE: We could demand that ints are all unique here *)

  let get_constraints env = env.constraints

  let add_constraint (NC_aux (_, l) as constr) env =
    wf_constraint env constr;
    begin
      typ_debug ("Adding constraint " ^ string_of_n_constraint constr);
      { env with constraints = constr :: env.constraints }
    end

  let get_ret_typ env = env.ret_typ

  let add_ret_typ typ env = { env with ret_typ = Some typ }

  let allow_casts env = env.allow_casts

  let no_casts env = { env with allow_casts = false }

  let add_typ_synonym id synonym env =
    if Bindings.mem id env.typ_synonyms
    then typ_error (id_loc id) ("Type synonym " ^ string_of_id id ^ " already exists")
    else
      begin
        typ_debug ("Adding typ synonym " ^ string_of_id id);
        { env with typ_synonyms = Bindings.add id synonym env.typ_synonyms }
      end

  let get_typ_synonym id env = Bindings.find id env.typ_synonyms

  let rec expand_synonyms env (Typ_aux (typ, l)) =
    match typ with
    | Typ_tup typs -> Typ_aux (Typ_tup (List.map (expand_synonyms env) typs), l)
    | Typ_fn (typ1, typ2, effs) -> Typ_aux (Typ_fn (expand_synonyms env typ1, expand_synonyms env typ2, effs), l)
    | Typ_app (id, args) ->
       begin
         try
           let synonym = Bindings.find id env.typ_synonyms in
           expand_synonyms env (synonym args)
         with
       | Not_found -> Typ_aux (Typ_app (id, List.map (expand_synonyms_arg env) args), l)
       end
    | Typ_id id ->
       begin
         try
           let synonym = Bindings.find id env.typ_synonyms in
           expand_synonyms env (synonym [])
         with
         | Not_found -> Typ_aux (Typ_id id, l)
       end
    | typ -> Typ_aux (typ, l)
  and expand_synonyms_arg env (Typ_arg_aux (typ_arg, l)) =
    match typ_arg with
    | Typ_arg_typ typ -> Typ_arg_aux (Typ_arg_typ (expand_synonyms env typ), l)
    | arg -> Typ_arg_aux (arg, l)

  let get_default_order env =
    match env.default_order with
    | None -> typ_error Parse_ast.Unknown ("No default order has been set")
    | Some ord -> ord

  let set_default_order o env =
    match env.default_order with
    | None -> { env with default_order = Some (Ord_aux (o, Parse_ast.Unknown)) }
    | Some _ -> typ_error Parse_ast.Unknown ("Cannot change default order once already set")

  let set_default_order_inc = set_default_order Ord_inc
  let set_default_order_dec = set_default_order Ord_dec

end

type tannot = (Env.t * typ) option

let add_typquant (quant : typquant) (env : Env.t) : Env.t =
  let rec add_quant_item env = function
    | QI_aux (qi, _) -> add_quant_item_aux env qi
  and add_quant_item_aux env = function
    | QI_const constr -> Env.add_constraint constr env
    | QI_id (KOpt_aux (KOpt_none kid, _)) -> Env.add_typ_var kid BK_nat env
    | QI_id (KOpt_aux (KOpt_kind (K_aux (K_kind [BK_aux (k, _)], _), kid), _)) -> Env.add_typ_var kid k env
    | QI_id (KOpt_aux (_, l)) -> typ_error l "Type variable had non base kinds!"
  in
  match quant with
  | TypQ_aux (TypQ_no_forall, _) -> env
  | TypQ_aux (TypQ_tq quants, _) -> List.fold_left add_quant_item env quants

let nconstant c = Nexp_aux (Nexp_constant c, Parse_ast.Unknown)
let nminus n1 n2 = Nexp_aux (Nexp_minus (n1, n2), Parse_ast.Unknown)
let nsum n1 n2 = Nexp_aux (Nexp_sum (n1, n2), Parse_ast.Unknown)
let nvar kid = Nexp_aux (Nexp_var kid, Parse_ast.Unknown)

type index_sort =
  | IS_int
  | IS_prop of kid * (nexp * nexp) list

type tnf =
  | Tnf_wild
  | Tnf_id of id
  | Tnf_var of kid
  | Tnf_tup of tnf list
  | Tnf_index_sort of index_sort
  | Tnf_app of id * tnf_arg list
and tnf_arg =
  | Tnf_arg_nexp of nexp
  | Tnf_arg_typ of tnf
  | Tnf_arg_order of order
  | Tnf_arg_effect of effect

let rec string_of_tnf = function
  | Tnf_wild -> "_"
  | Tnf_id id -> string_of_id id
  | Tnf_var kid -> string_of_kid kid
  | Tnf_tup tnfs -> "(" ^ string_of_list ", " string_of_tnf tnfs ^ ")"
  | Tnf_app (id, args) -> string_of_id id ^ "<" ^ string_of_list ", " string_of_tnf_arg args ^ ">"
  | Tnf_index_sort IS_int -> "INT"
  | Tnf_index_sort (IS_prop (kid, props)) ->
     "{" ^ string_of_kid kid ^ " | " ^ string_of_list " & " (fun (n1, n2) -> string_of_nexp n1 ^ " <= " ^ string_of_nexp n2) props ^ "}"
and string_of_tnf_arg = function
  | Tnf_arg_nexp n -> string_of_nexp n
  | Tnf_arg_typ tnf -> string_of_tnf tnf
  | Tnf_arg_order o -> string_of_order o
  | Tnf_arg_effect eff -> string_of_effect eff

let rec normalize_typ env (Typ_aux (typ, l)) =
  match typ with
  | Typ_wild -> Tnf_wild
  | Typ_id (Id_aux (Id "int", _)) -> Tnf_index_sort IS_int
  | Typ_id (Id_aux (Id "nat", _)) ->
     let kid = Env.fresh_kid env in Tnf_index_sort (IS_prop (kid, [(nconstant 0, nvar kid)]))
  | Typ_id v ->
     begin
       try normalize_typ env (Env.get_typ_synonym v env []) with
       | Not_found -> Tnf_id v
     end
  | Typ_var kid -> Tnf_var kid
  | Typ_tup typs -> Tnf_tup (List.map (normalize_typ env) typs)
  | Typ_app (Id_aux (Id "range", _), [Typ_arg_aux (Typ_arg_nexp n1, _); Typ_arg_aux (Typ_arg_nexp n2, _)]) ->
     let kid = Env.fresh_kid env in
     Tnf_index_sort (IS_prop (kid, [(n1, nvar kid); (nvar kid, n2)]))
  | Typ_app ((Id_aux (Id "vector", _) as vector), args) ->
     Tnf_app (vector, List.map (normalize_typ_arg env) args)
  | Typ_app (id, args) ->
     begin
       try normalize_typ env (Env.get_typ_synonym id env args) with
       | Not_found -> Tnf_app (id, List.map (normalize_typ_arg env) args)
     end
  | Typ_fn _ -> typ_error l ("Cannot normalize function type " ^ string_of_typ (Typ_aux (typ, l)))
and normalize_typ_arg env (Typ_arg_aux (typ_arg, _)) =
  match typ_arg with
  | Typ_arg_nexp n -> Tnf_arg_nexp n
  | Typ_arg_typ typ -> Tnf_arg_typ (normalize_typ env typ)
  | Typ_arg_order o -> Tnf_arg_order o
  | Typ_arg_effect e -> Tnf_arg_effect e

(* Here's how the constraint generation works for subtyping

X(b,c...) --> {a. Y(a,b,c...)} \subseteq {a. Z(a,b,c...)}

this is equivalent to

\forall b c. X(b,c) --> \forall a. Y(a,b,c) --> Z(a,b,c)

\forall b c. X(b,c) --> \forall a. !Y(a,b,c) \/ !Z^-1(a,b,c)

\forall b c. X(b,c) --> !\exists a. Y(a,b,c) /\ Z^-1(a,b,c)

\forall b c. !X(b,c) \/ !\exists a. Y(a,b,c) /\ Z^-1(a,b,c)

!\exists b c. X(b,c) /\ \exists a. Y(a,b,c) /\ Z^-1(a,b,c)

!\exists a b c. X(b,c) /\ Y(a,b,c) /\ Z^-1(a,b,c)

which is then a problem we can feed to the constraint solver expecting unsat.
 *)

let order_eq (Ord_aux (ord_aux1, _)) (Ord_aux (ord_aux2, _)) =
  match ord_aux1, ord_aux2 with
  | Ord_inc, Ord_inc -> true
  | Ord_dec, Ord_dec -> true
  | Ord_var kid1, Ord_var kid2 -> Kid.compare kid1 kid2 = 0
  | _, _ -> false

let rec props_subst sv subst props =
  match props with
  | [] -> []
  | ((nexp1, nexp2) :: props) -> (nexp_subst sv subst nexp1, nexp_subst sv subst nexp2) :: props_subst sv subst props

let rec nexp_constraint var_of (Nexp_aux (nexp, l)) =
  match nexp with
  | Nexp_id v -> typ_error l "Unimplemented: Cannot generate constraint from Nexp_id"
  | Nexp_var kid -> Constraint.variable (var_of kid)
  | Nexp_constant c -> Constraint.constant (big_int_of_int c)
  | Nexp_times (nexp1, nexp2) -> Constraint.mult (nexp_constraint var_of nexp1) (nexp_constraint var_of nexp2)
  | Nexp_sum (nexp1, nexp2) -> Constraint.add (nexp_constraint var_of nexp1) (nexp_constraint var_of nexp2)
  | Nexp_minus (nexp1, nexp2) -> Constraint.sub (nexp_constraint var_of nexp1) (nexp_constraint var_of nexp2)
  | Nexp_exp nexp -> Constraint.pow2 (nexp_constraint var_of nexp)
  | Nexp_neg nexp -> Constraint.sub (Constraint.constant (big_int_of_int 0)) (nexp_constraint var_of nexp)

let nc_constraint var_of (NC_aux (nc, _)) =
  match nc with
  | NC_fixed (nexp1, nexp2) -> Constraint.eq (nexp_constraint var_of nexp1) (nexp_constraint var_of nexp2)
  | NC_bounded_ge (nexp1, nexp2) -> Constraint.gteq (nexp_constraint var_of nexp1) (nexp_constraint var_of nexp2)
  | NC_bounded_le (nexp1, nexp2) -> Constraint.lteq (nexp_constraint var_of nexp1) (nexp_constraint var_of nexp2)
  | NC_nat_set_bounded (_, []) -> Constraint.literal false
  | NC_nat_set_bounded (kid, (int :: ints)) ->
     List.fold_left Constraint.disj
                    (Constraint.eq (Constraint.variable (var_of kid)) (Constraint.constant (big_int_of_int int)))
                    (List.map (fun i -> Constraint.eq (Constraint.variable (var_of kid)) (Constraint.constant (big_int_of_int i))) ints)

let rec nc_constraints var_of ncs =
  match ncs with
  | [] -> Constraint.literal true
  | [nc] -> nc_constraint var_of nc
  | (nc :: ncs) ->
     Constraint.conj (nc_constraint var_of nc) (nc_constraints var_of ncs)

let prove env nc =
  typ_print ("Prove " ^ string_of_list ", " string_of_n_constraint (Env.get_constraints env) ^ " |- " ^ string_of_n_constraint nc);
  let module Bindings = Map.Make(Kid) in
  let bindings = ref Bindings.empty  in
  let fresh_var kid =
    let n = Bindings.cardinal !bindings in
    bindings := Bindings.add kid n !bindings;
    n
  in
  let var_of kid =
    try Bindings.find kid !bindings with
    | Not_found -> fresh_var kid
  in
  let constr = Constraint.conj (nc_constraints var_of (Env.get_constraints env)) (Constraint.negate (nc_constraint var_of nc)) in
  match Constraint.call_z3 constr with
  | Constraint.Unsat _ -> typ_debug "unsat"; true
  | Constraint.Unknown [] -> typ_debug "sat"; false
  | Constraint.Unknown _ -> typ_debug "unknown"; false

let rec subtyp_tnf env tnf1 tnf2 =
  typ_print ("Subset " ^ string_of_list ", " string_of_n_constraint (Env.get_constraints env) ^ " |- " ^ string_of_tnf tnf1 ^ " " ^ string_of_tnf tnf2);
  let module Bindings = Map.Make(Kid) in
  let bindings = ref Bindings.empty  in
  let fresh_var kid =
    let n = Bindings.cardinal !bindings in
    bindings := Bindings.add kid n !bindings;
    n
  in
  let var_of kid =
    try Bindings.find kid !bindings with
    | Not_found -> fresh_var kid
  in
  let rec neg_props props =
    match props with
    | [] -> Constraint.literal false
    | [(nexp1, nexp2)] -> Constraint.gt (nexp_constraint var_of nexp1) (nexp_constraint var_of nexp2)
    | ((nexp1, nexp2) :: props) ->
       Constraint.disj (Constraint.gt (nexp_constraint var_of nexp1) (nexp_constraint var_of nexp2)) (neg_props props)
  in
  let rec pos_props props =
    match props with
    | [] -> Constraint.literal true
    | [(nexp1, nexp2)] -> Constraint.lteq (nexp_constraint var_of nexp1) (nexp_constraint var_of nexp2)
    | ((nexp1, nexp2) :: props) ->
       Constraint.conj (Constraint.lteq (nexp_constraint var_of nexp1) (nexp_constraint var_of nexp2)) (pos_props props)
  in
  match (tnf1, tnf2) with
  | Tnf_wild, Tnf_wild -> true
  | Tnf_id v1, Tnf_id v2 -> Id.compare v1 v2 = 0
  | Tnf_var kid1, Tnf_var kid2 -> Kid.compare kid1 kid2 = 0
  | Tnf_tup tnfs1, Tnf_tup tnfs2 ->
     begin
       try List.for_all2 (subtyp_tnf env) tnfs1 tnfs2 with
       | Invalid_argument _ -> false
     end
  | Tnf_app (v1, args1), Tnf_app (v2, args2) -> Id.compare v1 v2 = 0 && List.for_all2 (tnf_args_eq env) args1 args2
  | Tnf_index_sort IS_int, Tnf_index_sort IS_int -> true
  | Tnf_index_sort (IS_prop _), Tnf_index_sort IS_int -> true
  | Tnf_index_sort (IS_prop (kid1, prop1)), Tnf_index_sort (IS_prop (kid2, prop2)) ->
     begin
       let kid3 = Env.fresh_kid env in
       let (prop1, prop2) = props_subst kid1 (Nexp_var kid3) prop1, props_subst kid2 (Nexp_var kid3) prop2 in
       let constr = Constraint.conj (nc_constraints var_of (Env.get_constraints env)) (Constraint.conj (pos_props prop1) (neg_props prop2)) in
       match Constraint.call_z3 constr with
       | Constraint.Unsat _ -> typ_debug "unsat"; true
       | Constraint.Unknown [] -> typ_debug "sat"; false
       | Constraint.Unknown _ -> typ_debug "unknown"; false
     end
  | _, _ -> false

and tnf_args_eq env arg1 arg2 =
  match arg1, arg2 with
  | Tnf_arg_nexp n1, Tnf_arg_nexp n2 -> prove env (NC_aux (NC_fixed (n1, n2), Parse_ast.Unknown))
  | Tnf_arg_order ord1, Tnf_arg_order ord2 -> order_eq ord1 ord2
  | Tnf_arg_typ tnf1, Tnf_arg_typ tnf2 -> subtyp_tnf env tnf1 tnf2 && subtyp_tnf env tnf2 tnf1
  | _, _ -> assert false

let subtyp l env typ1 typ2 =
  if subtyp_tnf env (normalize_typ env typ1) (normalize_typ env typ2)
  then ()
  else typ_error l (string_of_typ typ1
                    ^ " is not a subtype of " ^ string_of_typ typ2
                    ^ " in context " ^ string_of_list ", " string_of_n_constraint (Env.get_constraints env))

let rec nexp_frees (Nexp_aux (nexp, l)) =
  match nexp with
  | Nexp_id _ -> typ_error l "Unimplemented Nexp_id in nexp_frees"
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

exception Unification_error of l * string;;

let unify_error l str = raise (Unification_error (l, str))

let rec unify_nexps l (Nexp_aux (nexp_aux1, _) as nexp1) (Nexp_aux (nexp_aux2, _) as nexp2) =
  typ_debug ("UNIFYING NEXPS " ^ string_of_nexp nexp1 ^ " AND " ^ string_of_nexp nexp2);
  match nexp_aux1 with
  | Nexp_id v -> unify_error l "Unimplemented Nexp_id in unify nexp"
  | Nexp_var kid -> Some (kid, nexp2)
  | Nexp_constant c1 ->
     begin
       match nexp_aux2 with
       | Nexp_constant c2 -> if c1 = c2 then None else unify_error l "Constants are not the same"
       | _ -> unify_error l "Unification error"
     end
  | Nexp_sum (n1a, n1b) ->
     if KidSet.is_empty (nexp_frees n1b)
     then unify_nexps l n1a (nminus nexp2 n1b)
     else
       if KidSet.is_empty (nexp_frees n1a)
       then unify_nexps l n1b (nminus nexp2 n1a)
       else unify_error l ("Both sides of Nat expression " ^ string_of_nexp nexp1
                           ^ " contain free type variables so it cannot be unified with " ^ string_of_nexp nexp2)
  | Nexp_minus (n1a, n1b) ->
     if KidSet.is_empty (nexp_frees n1b)
     then unify_nexps l n1a (nsum nexp2 n1b)
     else  unify_error l ("Cannot unify minus Nat expression " ^ string_of_nexp nexp1 ^ " with " ^ string_of_nexp nexp2)

  | _ -> unify_error l ("Cannot unify Nat expression " ^ string_of_nexp nexp1 ^ " with " ^ string_of_nexp nexp2)

type uvar =
  | U_nexp of nexp
  | U_order of order
  | U_effect of effect
  | U_typ of typ

let string_of_uvar = function
  | U_nexp n -> string_of_nexp n
  | U_order o -> string_of_order o
  | U_effect eff -> string_of_effect eff
  | U_typ typ -> string_of_typ typ

let unify_order l (Ord_aux (ord_aux1, _) as ord1) (Ord_aux (ord_aux2, _) as ord2) =
  typ_debug ("UNIFYING ORDERS " ^ string_of_order ord1 ^ " AND " ^ string_of_order ord2);
  match ord_aux1, ord_aux2 with
  | Ord_var kid, _ -> KBindings.singleton kid (U_order ord2)
  | Ord_inc, Ord_inc -> KBindings.empty
  | Ord_dec, Ord_dec -> KBindings.empty
  | _, _ -> unify_error l (string_of_order ord1 ^ " cannot be unified with " ^ string_of_order ord2)

let subst_unifiers unifiers typ =
  let subst_unifier typ (kid, uvar) =
    match uvar with
    | U_nexp nexp -> typ_subst_nexp kid (unaux_nexp nexp) typ
    | U_order ord -> typ_subst_order kid (unaux_order ord) typ
    | U_typ subst -> typ_subst_typ kid (unaux_typ subst) typ
    | _ -> typ_error Parse_ast.Unknown "Cannot subst unifier"
  in
  List.fold_left subst_unifier typ (KBindings.bindings unifiers)

let subst_args_unifiers unifiers typ_args =
  let subst_unifier typ_args (kid, uvar) =
    match uvar with
    | U_nexp nexp -> List.map (typ_subst_arg_nexp kid (unaux_nexp nexp)) typ_args
    | U_order ord -> List.map (typ_subst_arg_order kid (unaux_order ord)) typ_args
    | U_typ subst -> List.map (typ_subst_arg_typ kid (unaux_typ subst)) typ_args
    | _ -> typ_error Parse_ast.Unknown "Cannot subst unifier"
  in
  List.fold_left subst_unifier typ_args (KBindings.bindings unifiers)

let unify l env typ1 typ2 =
  let merge_unifiers l kid uvar1 uvar2 =
    match uvar1, uvar2 with
    | Some (U_nexp n1), Some (U_nexp n2) ->
       if nexp_identical n1 n2 then Some (U_nexp n1)
       else unify_error l ("Multiple non-identical unifiers for " ^ string_of_kid kid
                           ^ ": " ^ string_of_nexp n1 ^ " and " ^ string_of_nexp n2)
    | Some _, Some _ -> unify_error l "Multiple non-identical non-nexp unifiers"
    | None, Some u2 -> Some u2
    | Some u1, None -> Some u1
    | None, None -> None
  in
  let rec unify_typ l (Typ_aux (typ1_aux, _) as typ1) (Typ_aux (typ2_aux, _) as typ2) =
    typ_debug ("UNIFYING TYPES " ^ string_of_typ typ1 ^ " AND " ^ string_of_typ typ2);
    match typ1_aux, typ2_aux with
    | Typ_wild, Typ_wild -> KBindings.empty
    | Typ_id v1, Typ_id v2 ->
       if Id.compare v1 v2 = 0 then KBindings.empty
       else unify_error l (string_of_typ typ1 ^ " cannot be unified with " ^ string_of_typ typ2)
    | Typ_var kid, _ -> KBindings.singleton kid (U_typ typ2)
    | Typ_tup typs1, Typ_tup typs2 ->
       begin
         try List.fold_left (KBindings.merge (merge_unifiers l)) KBindings.empty (List.map2 (unify_typ l) typs1 typs2) with
         | Invalid_argument _ -> unify_error l (string_of_typ typ1 ^ " cannot be unified with " ^ string_of_typ typ2
                                              ^ " tuple type is of different length")
       end
    | Typ_app (f1, args1), Typ_app (f2, args2) when Id.compare f1 f2 = 0 ->
       unify_typ_arg_list 0 KBindings.empty [] [] args1 args2
    | _, _ -> unify_error l (string_of_typ typ1 ^ " cannot be unified with " ^ string_of_typ typ2)

  and unify_typ_arg_list unified acc uargs1 uargs2 args1 args2 =
    match args1, args2 with
    | [], [] when unified = 0 && List.length uargs1 > 0 -> unify_error l ("Could not unify arg lists") (*FIXME improve error *)
    | [], [] when unified > 0 && List.length uargs1 > 0 -> unify_typ_arg_list 0 acc [] [] uargs1 uargs2
    | [], [] when List.length uargs1 = 0 -> acc
    | (a1 :: a1s), (a2 :: a2s) ->
       begin
         try
           let unifiers = unify_typ_args l a1 a2 in
           let a1s = subst_args_unifiers unifiers a1s in
           let a2s = subst_args_unifiers unifiers a2s in
           let uargs1 = subst_args_unifiers unifiers uargs1 in
           let uargs2 = subst_args_unifiers unifiers uargs2 in
           unify_typ_arg_list (unified + 1) (KBindings.merge (merge_unifiers l) unifiers acc) uargs1 uargs2 a1s a2s
         with
         | Unification_error _ -> unify_typ_arg_list unified acc (a1 :: uargs1) (a2 :: uargs2) a1s a2s
       end
    | _, _ -> unify_error l "Cannot unify type lists of different length"

  and unify_typ_args l (Typ_arg_aux (typ_arg_aux1, _) as typ_arg1) (Typ_arg_aux (typ_arg_aux2, _) as typ_arg2) =
    match typ_arg_aux1, typ_arg_aux2 with
    | Typ_arg_nexp n1, Typ_arg_nexp n2 ->
       begin
         match unify_nexps l (nexp_simp n1) (nexp_simp n2) with
         | Some (kid, unifier) -> KBindings.singleton kid (U_nexp unifier)
         | None -> KBindings.empty
       end
    | Typ_arg_typ typ1, Typ_arg_typ typ2 -> unify_typ l typ1 typ2
    | Typ_arg_order ord1, Typ_arg_order ord2 -> unify_order l ord1 ord2
    | Typ_arg_effect _, Typ_arg_effect _ -> assert false
    | _, _ -> unify_error l (string_of_typ_arg typ_arg1 ^ " cannot be unified with type argument " ^ string_of_typ_arg typ_arg2)
  in
  let typ1, typ2 = Env.expand_synonyms env typ1, Env.expand_synonyms env typ2 in
  unify_typ l typ1 typ2

(* FIXME: we need to unify lists of typ args better, consider:

unifying [|'n - 'l + 1:'n|] against [|0:31|] for example

we can only unify the first argument if we do the second first

*)

let infer_lit env (L_aux (lit_aux, l) as lit) =
  match lit_aux with
  | L_unit -> mk_typ (Typ_id (mk_id "unit"))
  | L_zero -> mk_typ (Typ_id (mk_id "bit"))
  | L_one -> mk_typ (Typ_id (mk_id "bit"))
  | L_num n -> mk_typ (Typ_app (mk_id "atom", [mk_typ_arg (Typ_arg_nexp (nconstant n))]))
  | L_true -> mk_typ (Typ_id (mk_id "bool"))
  | L_false -> mk_typ (Typ_id (mk_id "bool"))
  | L_string _ -> mk_typ (Typ_id (mk_id "string"))
  | L_bin str ->
     begin
       match Env.get_default_order env with
       | Ord_aux (Ord_inc, _) ->
          mk_typ (Typ_app (mk_id "vector",
                           [mk_typ_arg (Typ_arg_nexp (nconstant 0));
                            mk_typ_arg (Typ_arg_nexp (nconstant (String.length str)));
                            mk_typ_arg (Typ_arg_order (Env.get_default_order env));
                            mk_typ_arg (Typ_arg_typ (mk_typ (Typ_id (mk_id "bit"))))]))
       | Ord_aux (Ord_dec, _) ->
          mk_typ (Typ_app (mk_id "vector",
                           [mk_typ_arg (Typ_arg_nexp (nconstant (String.length str - 1)));
                            mk_typ_arg (Typ_arg_nexp (nconstant (String.length str)));
                            mk_typ_arg (Typ_arg_order (Env.get_default_order env));
                            mk_typ_arg (Typ_arg_typ (mk_typ (Typ_id (mk_id "bit"))))]))
     end
  | L_hex str ->
     begin
       match Env.get_default_order env with
       | Ord_aux (Ord_inc, _) ->
          mk_typ (Typ_app (mk_id "vector",
                           [mk_typ_arg (Typ_arg_nexp (nconstant 0));
                            mk_typ_arg (Typ_arg_nexp (nconstant (String.length str * 4)));
                            mk_typ_arg (Typ_arg_order (Env.get_default_order env));
                            mk_typ_arg (Typ_arg_typ (mk_typ (Typ_id (mk_id "bit"))))]))
       | Ord_aux (Ord_dec, _) ->
          mk_typ (Typ_app (mk_id "vector",
                           [mk_typ_arg (Typ_arg_nexp (nconstant (String.length str * 4 - 1)));
                            mk_typ_arg (Typ_arg_nexp (nconstant (String.length str * 4)));
                            mk_typ_arg (Typ_arg_order (Env.get_default_order env));
                            mk_typ_arg (Typ_arg_typ (mk_typ (Typ_id (mk_id "bit"))))]))
     end
  | L_undef -> typ_error l "Cannot infer the type of undefined"

let rec bind_pat env (P_aux (pat_aux, (l, _)) as pat) (Typ_aux (typ_aux, _) as typ) =
  let annot_pat pat typ = P_aux (pat, (l, Some (env, typ))) in
  match pat_aux with
  | P_id v -> annot_pat (P_id v) typ, Env.add_local v (Immutable, typ) env
  | P_wild -> annot_pat P_wild typ, env
  | P_typ (typ_annot, pat) ->
     begin
       subtyp l env typ_annot typ;
       let (typed_pat, env) = bind_pat env pat typ_annot in
       annot_pat (P_typ (typ_annot, typed_pat)) typ, env
     end
  | P_tup pats ->
     begin
       match typ_aux with
       | Typ_tup typs ->
          let bind_tuple_pat (tpats, env) pat typ =
            let tpat, env = bind_pat env pat typ in tpat :: tpats, env
          in
          let tpats, env =
            try List.fold_left2 bind_tuple_pat ([], env) pats typs with
            | Invalid_argument _ -> typ_error l "Tuple pattern and tuple type have different length"
          in
          annot_pat (P_tup tpats) typ, env
       | _ -> typ_error l "Cannot bind tuple pattern against non tuple type"
     end
  | P_lit lit ->
     begin
       let lit_typ = infer_lit env lit in
       subtyp l env lit_typ typ; (* CHECK: is the the correct way round? *)
       annot_pat (P_lit lit) typ, env
     end
  | _ -> typ_error l ("Unhandled pat " ^ string_of_pat pat)

and bind_lexp env (LEXP_aux (lexp_aux, (l, _))) typ =
  let annot_lexp lexp typ = LEXP_aux (lexp, (l, Some (env, typ))) in
  match lexp_aux with
  | LEXP_id v ->
     begin
       match Env.lookup_id v env with
       | Local (Immutable, _) -> typ_error l ("Cannot modify or shadow let-bound constant " ^ string_of_id v)
       | Local (Mutable, vtyp) -> subtyp l env typ vtyp; annot_lexp (LEXP_id v) typ, env
       | Register vtyp -> subtyp l env typ vtyp; annot_lexp (LEXP_id v) typ, env
       | Unbound -> annot_lexp (LEXP_id v) typ, Env.add_local v (Mutable, typ) env
     end
  | LEXP_cast (typ_annot, v) ->
     begin
       match Env.lookup_id v env with
       | Local (Immutable, _) -> typ_error l ("Cannot modify or shadow let-bound constant " ^ string_of_id v)
       | Local (Mutable, vtyp) ->
          begin
            subtyp l env typ typ_annot;
            subtyp l env typ_annot vtyp;
            annot_lexp (LEXP_cast (typ_annot, v)) typ, env
          end
       | Register vtyp ->
          begin
            subtyp l env typ typ_annot;
            subtyp l env typ_annot vtyp;
            annot_lexp (LEXP_cast (typ_annot, v)) typ, env
          end
       | Unbound ->
          begin
            subtyp l env typ typ_annot;
            annot_lexp (LEXP_cast (typ_annot, v)) typ, Env.add_local v (Mutable, typ_annot) env
          end
     end
  | LEXP_tup lexps ->
     begin
       let (Typ_aux (typ_aux, _)) = typ in
       match typ_aux with
       | Typ_tup typs ->
          let bind_tuple_lexp (tlexps, env) lexp typ =
            let tlexp, env = bind_lexp env lexp typ in tlexp :: tlexps, env
          in
          let tlexps, env =
            try List.fold_left2 bind_tuple_lexp ([], env) lexps typs with
            | Invalid_argument _ -> typ_error l "Tuple l-expression and tuple type have different length"
          in
          annot_lexp (LEXP_tup tlexps) typ, env
       | _ -> typ_error l "Cannot bind tuple l-expression against non tuple type"
     end
  | _ -> typ_error l ("Unhandled l-expression")

let quant_items : typquant -> quant_item list = function
  | TypQ_aux (TypQ_tq qis, _) -> qis
  | TypQ_aux (TypQ_no_forall, _) -> []

let is_nat_kid kid = function
  | KOpt_aux (KOpt_none kid', _) -> Kid.compare kid kid' = 0
  | KOpt_aux (KOpt_kind (K_aux (K_kind [BK_aux (BK_nat, _)], _), kid'), _) -> Kid.compare kid kid' = 0
  | _ -> false

let is_order_kid kid = function
  | KOpt_aux (KOpt_kind (K_aux (K_kind [BK_aux (BK_order, _)], _), kid'), _) -> Kid.compare kid kid' = 0
  | _ -> false

let is_typ_kid kid = function
  | KOpt_aux (KOpt_kind (K_aux (K_kind [BK_aux (BK_type, _)], _), kid'), _) -> Kid.compare kid kid' = 0
  | _ -> false

let rec instantiate_quants quants kid uvar = match quants with
  | [] -> []
  | ((QI_aux (QI_id kinded_id, _) as quant) :: quants) ->
     begin
       match uvar with
       | U_nexp nexp ->
          if is_nat_kid kid kinded_id
          then instantiate_quants quants kid uvar
          else quant :: instantiate_quants quants kid uvar
       | U_order ord ->
          if is_order_kid kid kinded_id
          then instantiate_quants quants kid uvar
          else quant :: instantiate_quants quants kid uvar
       | U_typ typ ->
          if is_typ_kid kid kinded_id
          then instantiate_quants quants kid uvar
          else quant :: instantiate_quants quants kid uvar
       | _ -> typ_error Parse_ast.Unknown "Cannot instantiate quantifier"
     end
  | ((QI_aux (QI_const nc, l)) :: quants) ->
     begin
       match uvar with
       | U_nexp nexp ->
          QI_aux (QI_const (nc_subst_nexp kid (unaux_nexp nexp) nc), l) :: instantiate_quants quants kid uvar
       | _ -> (QI_aux (QI_const nc, l)) :: instantiate_quants quants kid uvar
     end

let destructure_vec_typ l typ =
  match typ with
  | Typ_aux (Typ_app (id, [Typ_arg_aux (Typ_arg_nexp n1, _);
                           Typ_arg_aux (Typ_arg_nexp n2, _);
                           Typ_arg_aux (Typ_arg_order o, _);
                           Typ_arg_aux (Typ_arg_typ vtyp, _)]
                     ), _) ->
     if string_of_id id = "vector" then (n1, n2, o, vtyp)
     else typ_error l ("Expected vector type, got " ^ string_of_typ typ)
  | _ -> typ_error l ("Expected vector type, got " ^ string_of_typ typ)

let typ_of (E_aux (_, (_, tannot))) = match tannot with
  | Some (_, typ) -> typ
  | None -> assert false

let crule r env exp typ =
  incr depth;
  typ_print ("Check " ^ string_of_exp exp ^ " <= " ^ string_of_typ typ);
  try
    let checked_exp = r env exp typ in
    decr depth; checked_exp
  with
  | Type_error (l, m) -> decr depth; typ_error l m

let irule r env exp =
  incr depth;
  try
    let inferred_exp = r env exp in
    typ_print ("Infer " ^ string_of_exp exp ^ " => " ^ string_of_typ (typ_of inferred_exp));
    decr depth;
    inferred_exp
  with
  | Type_error (l, m) -> decr depth; typ_error l m

let rec check_exp env (E_aux (exp_aux, (l, annot)) as exp) (Typ_aux (typ_aux, _) as typ) =
  let annot_exp exp typ = E_aux (exp, (l, Some (env, typ))) in
  match (exp_aux, typ_aux) with
  | E_block exps, _ ->
     begin
       let rec check_block l env exps typ = match exps with
         | [] -> typ_error l "Empty block found"
         | [exp] -> [crule check_exp env exp typ]
         | (E_aux (E_assign (lexp, bind), _) :: exps) ->
            let texp, env = bind_assignment env lexp bind in
            texp :: check_block l env exps typ
         | (exp :: exps) ->
            let texp = crule check_exp env exp (mk_typ (Typ_id (mk_id "unit"))) in
            texp :: check_block l env exps typ
       in
       annot_exp (E_block (check_block l env exps typ)) typ
     end
  | E_case (exp, cases), _ ->
     let inferred_exp = irule infer_exp env exp in
     let check_case (Pat_aux (Pat_exp (pat, case), (l, _))) typ =
       let tpat, env = bind_pat env pat (typ_of inferred_exp) in
       Pat_aux (Pat_exp (tpat, crule check_exp env case typ), (l, None))
     in
     annot_exp (E_case (inferred_exp, List.map (fun case -> check_case case typ) cases)) typ
  | E_let (LB_aux (letbind, (let_loc, _)), exp), _ ->
     begin
       match letbind with
       | LB_val_explicit (typschm, pat, bind) -> assert false
       | LB_val_implicit (pat, bind) ->
          let inferred_bind = irule infer_exp env bind in
          let tpat, env = bind_pat env pat (typ_of inferred_bind) in
          annot_exp (E_let (LB_aux (LB_val_implicit (tpat, inferred_bind), (let_loc, None)), crule check_exp env exp typ)) typ
     end
  | E_app_infix (x, op, y), _ when List.length (Env.get_overloads op env) > 0 -> check_exp env (E_aux (E_app (op, [x; y]), (l, annot))) typ
  | E_app (f, xs), _ when List.length (Env.get_overloads f env) > 0 ->
     let rec try_overload m1 = function
       | [] -> typ_error l (m1 ^ "\nNo valid overloading for " ^ string_of_exp exp)
       | (f :: fs) -> begin
           typ_print ("Overload: " ^ string_of_id f ^ "(" ^ string_of_list ", " string_of_exp xs ^ ")");
           try crule check_exp env (E_aux (E_app (f, xs), (l, annot))) typ with
           | Type_error (_, m2) -> try_overload (m1 ^ "\nand " ^ m2) fs
         end
     in
     try_overload "Overloading error" (Env.get_overloads f env)
  | E_app (f, xs), _ ->
     let inferred_exp = infer_funapp l env f xs (Some typ)
     in (subtyp l env (typ_of inferred_exp) typ; inferred_exp)
  | E_if (cond, then_branch, else_branch), _ ->
     let cond' = crule check_exp env cond (mk_typ (Typ_id (mk_id "bool"))) in
     let then_branch' = crule check_exp env then_branch typ in
     let else_branch' = crule check_exp env else_branch typ in
     annot_exp (E_if (cond', then_branch', else_branch')) typ
  | E_exit exp, _ ->
     let checked_exp = crule check_exp env exp (mk_typ (Typ_id (mk_id "unit"))) in
     annot_exp (E_exit checked_exp) typ
  | E_vector vec, _ ->
     begin
       let (start, len, ord, vtyp) = destructure_vec_typ l typ in
       let checked_items = List.map (fun i -> crule check_exp env i vtyp) vec in
       match len with
       | Nexp_aux (Nexp_constant lenc, _) ->
          if List.length vec = lenc then annot_exp (E_vector checked_items) typ
          else typ_error l "List length didn't match" (* FIXME: improve error message *)
       | _ -> typ_error l "Cannot check list constant against non-constant length vector type"
     end
  | E_lit (L_aux (L_undef, _) as lit), _ ->
     annot_exp (E_lit lit) typ
  (* This rule allows registers of type t to be passed by name with type register<t>*)
  | E_id reg, Typ_app (id, [Typ_arg_aux (Typ_arg_typ typ, _)]) when string_of_id id = "register" ->
     let rtyp = Env.get_register reg env in
     subtyp l env rtyp typ; annot_exp (E_id reg) typ (* CHECK: is this subtyp the correct way around? *)
  | _, _ ->
     let inferred_exp = irule infer_exp env exp in
     let strip_annots exp = map_exp_annot (fun (l, _) -> (l, annot)) exp in
     let rec try_casts m = function
       | [] -> typ_error l ("No valid casts:\n" ^ m)
       | (cast :: casts) -> begin
           typ_print ("Casting with " ^ string_of_id cast ^ " expression " ^ string_of_exp inferred_exp ^ " to " ^ string_of_typ typ);
           try crule check_exp (Env.no_casts env) (strip_annots (annot_exp (E_app (cast, [inferred_exp])) typ)) typ with
           | Type_error (l, m) -> try_casts m casts
         end
     in
     begin
       try
         subtyp l env (typ_of inferred_exp) typ; inferred_exp
       with
       | Type_error (_, m) when Env.allow_casts env -> try_casts "" (Env.get_casts env)
       | Type_error (l, m) -> typ_error l ("Subtype error " ^ m)
     end

and bind_assignment env lexp (E_aux (_, (l, _)) as exp) =
  let inferred_exp = irule infer_exp env exp in
  let tlexp, env' = bind_lexp env lexp (typ_of inferred_exp) in
  E_aux (E_assign (tlexp, inferred_exp), (l, Some (env, mk_typ (Typ_id (mk_id "unit"))))), env'

and infer_exp env (E_aux (exp_aux, (l, annot)) as exp : 'a exp) =
  let annot_exp exp typ = E_aux (exp, (l, Some (env, typ))) in
  match exp_aux with
  | E_id v ->
     begin
       match Env.lookup_id v env with
       | Local (_, typ) -> annot_exp (E_id v) typ
       | Register typ -> annot_exp (E_id v) typ
       | Unbound -> typ_error l ("Identifier " ^ string_of_id v ^ " is unbound")
     end
  | E_lit lit -> annot_exp (E_lit lit) (infer_lit env lit)
  | E_sizeof nexp -> annot_exp (E_sizeof nexp) (mk_typ (Typ_app (mk_id "atom", [mk_typ_arg (Typ_arg_nexp nexp)])))
  | E_return exp ->
     begin
       match Env.get_ret_typ env with
       | Some typ -> annot_exp (E_return (crule check_exp env exp typ)) (mk_typ (Typ_id (mk_id "unit")))
       | None -> typ_error l "Return found in non-function environment"
     end
  | E_tuple exps ->
     let inferred_exps = List.map (irule infer_exp env) exps in
     annot_exp (E_tuple inferred_exps) (mk_typ (Typ_tup (List.map typ_of inferred_exps)))
  | E_assign (lexp, bind) ->
     fst (bind_assignment env lexp bind)
  | E_cast (typ, exp) ->
     let checked_exp = crule check_exp env exp typ in
     annot_exp (E_cast (typ, checked_exp)) typ
  | E_app_infix (x, op, y) when List.length (Env.get_overloads op env) > 0 -> infer_exp env (E_aux (E_app (op, [x; y]), (l, annot)))
  | E_app (f, xs) when List.length (Env.get_overloads f env) > 0 ->
     let rec try_overload m1 = function
       | [] -> typ_error l (m1 ^ "\nNo valid overloading for " ^ string_of_exp exp)
       | (f :: fs) -> begin
           typ_print ("Overload: " ^ string_of_id f ^ "(" ^ string_of_list ", " string_of_exp xs ^ ")");
           try irule infer_exp env (E_aux (E_app (f, xs), (l, annot))) with
           | Type_error (_, m2) -> try_overload (m1 ^ "\nand " ^ m2) fs
         end
     in
     try_overload "Overloading error" (Env.get_overloads f env)
  | E_app (f, xs) -> infer_funapp l env f xs None
  | E_vector_access (v, n) -> infer_exp env (E_aux (E_app (mk_id "vector_access", [v; n]), (l, annot)))
  | E_vector_append (v1, v2) -> infer_exp env (E_aux (E_app (mk_id "vector_append", [v1; v2]), (l, annot)))
  | E_vector_subrange (v, n, m) -> infer_exp env (E_aux (E_app (mk_id "vector_subrange", [v; n; m]), (l, annot)))
  | E_vector [] -> typ_error l "Cannot infer type of empty vector"
  | E_vector ((item :: items) as vec) ->
     let inferred_item = irule infer_exp env item in
     let checked_items = List.map (fun i -> crule check_exp env i (typ_of inferred_item)) items in
     let vec_typ = match Env.get_default_order env with
       | Ord_aux (Ord_inc, _) ->
          mk_typ (Typ_app (mk_id "vector",
                           [mk_typ_arg (Typ_arg_nexp (nconstant 0));
                            mk_typ_arg (Typ_arg_nexp (nconstant (List.length vec)));
                            mk_typ_arg (Typ_arg_order (Env.get_default_order env));
                            mk_typ_arg (Typ_arg_typ (typ_of inferred_item))]))
       | Ord_aux (Ord_dec, _) ->
          mk_typ (Typ_app (mk_id "vector",
                           [mk_typ_arg (Typ_arg_nexp (nconstant (List.length vec - 1)));
                            mk_typ_arg (Typ_arg_nexp (nconstant (List.length vec)));
                            mk_typ_arg (Typ_arg_order (Env.get_default_order env));
                            mk_typ_arg (Typ_arg_typ (typ_of inferred_item))]))
     in
     annot_exp (E_vector (inferred_item :: checked_items)) vec_typ
  | _ -> typ_error l "Unimplemented"

and infer_funapp l env f xs ret_ctx_typ =
  let annot_exp exp typ = E_aux (exp, (l, Some (env, typ))) in
  let rec number n = function
    | [] -> []
    | (x :: xs) -> (n, x) :: number (n + 1) xs
  in
  let solve_quant = function
    | QI_aux (QI_id _, _) -> false
    | QI_aux (QI_const nc, _) -> prove env nc
  in
  let rec instantiate quants typs ret_typ args =
    match typs, args with
    | (utyps, []), (uargs, []) ->
       begin
         let iuargs = List.map2 (fun utyp (n, uarg) -> (n, crule check_exp env uarg utyp)) utyps uargs in
         if List.for_all solve_quant quants
         then (iuargs, ret_typ)
         else typ_error l ("Quantifiers " ^ string_of_list ", " string_of_quant_item quants
                           ^ " not resolved during function application of " ^ string_of_id f)
       end
    | (utyps, (typ :: typs)), (uargs, ((n, arg) :: args)) ->
       begin
         typ_debug ("INSTANTIATE: " ^ string_of_exp arg ^ " with " ^ string_of_typ typ ^ " NF " ^ string_of_tnf (normalize_typ env typ));
         let iarg = irule infer_exp env arg in
         typ_debug ("INFER: " ^ string_of_exp arg ^ " type " ^ string_of_typ (typ_of iarg) ^ " NF " ^ string_of_tnf (normalize_typ env (typ_of iarg)));
         try
           let unifiers = unify l env typ (typ_of iarg) in
           typ_debug (string_of_list ", " (fun (kid, uvar) -> string_of_kid kid ^ " => " ^ string_of_uvar uvar) (KBindings.bindings unifiers));
           let utyps' = List.map (subst_unifiers unifiers) utyps in
           let typs' = List.map (subst_unifiers unifiers) typs in
           let quants' = List.fold_left (fun qs (kid, uvar) -> instantiate_quants qs kid uvar) quants (KBindings.bindings unifiers) in
           let ret_typ' = subst_unifiers unifiers ret_typ in
           let (iargs, ret_typ'') = instantiate quants' (utyps', typs') ret_typ' (uargs, args) in
           ((n, iarg) :: iargs, ret_typ'')
         with
         | Unification_error (l, str) ->
            typ_debug ("Unification error: " ^ str);
            instantiate quants (typ :: utyps, typs) ret_typ ((n, arg) :: uargs, args)
       end
    | (_, []), _ -> typ_error l ("Function " ^ string_of_id f ^ " applied to too many arguments")
    | _, (_, []) -> typ_error l ("Function " ^ string_of_id f ^ " not applied to enough arguments")
  in
  let instantiate_ret quants typs ret_typ =
    match ret_ctx_typ with
    | None -> (quants, typs, ret_typ)
    | Some rct ->
       begin
         try
           let unifiers = unify l env ret_typ rct in
           typ_debug (string_of_list ", " (fun (kid, uvar) -> string_of_kid kid ^ " => " ^ string_of_uvar uvar) (KBindings.bindings unifiers));
           let typs' = List.map (subst_unifiers unifiers) typs in
           let quants' = List.fold_left (fun qs (kid, uvar) -> instantiate_quants qs kid uvar) quants (KBindings.bindings unifiers) in
           let ret_typ' = subst_unifiers unifiers ret_typ in
           (quants', typs', ret_typ')
         with
         | Unification_error (_, str) ->
            typ_debug ("Unification error (function return): " ^ str);
            (quants, typs, ret_typ)
       end
  in
  let (typq, f_typ) = Env.get_val_spec f env in
  match f_typ with
  | Typ_aux (Typ_fn (Typ_aux (Typ_tup typ_args, _), typ_ret, effs), _) ->
     let (quants, typ_args, typ_ret) = instantiate_ret (quant_items typq) typ_args typ_ret in
     let (xs_instantiated, typ_ret) = instantiate quants ([], typ_args) typ_ret ([], number 0 xs) in
     let xs_reordered = List.map snd (List.sort (fun (n, _) (m, _) -> compare n m) xs_instantiated) in
     annot_exp (E_app (f, xs_reordered)) typ_ret
  | Typ_aux (Typ_fn (typ_arg, typ_ret, effs), _) ->
     let (quants, typ_args, typ_ret) = instantiate_ret (quant_items typq) [typ_arg] typ_ret in
     let (xs_instantiated, typ_ret) = instantiate quants ([], typ_args) typ_ret ([], number 0 xs) in
     let xs_reordered = List.map snd (List.sort (fun (n, _) (m, _) -> compare n m) xs_instantiated) in
     annot_exp (E_app (f, xs_reordered)) typ_ret
  | _ -> typ_error l (string_of_id f ^ " is not a function")

let check_letdef env (LB_aux (letbind, (l, _))) =
  begin
    match letbind with
    | LB_val_explicit (typschm, pat, bind) -> assert false
    | LB_val_implicit (P_aux (P_typ (typ_annot, pat), _), bind) ->
       let checked_bind = crule check_exp env bind typ_annot in
       let tpat, env = bind_pat env pat typ_annot in
       DEF_val (LB_aux (LB_val_implicit (tpat, checked_bind), (l, None))), env
    | LB_val_implicit (pat, bind) ->
       let inferred_bind = irule infer_exp env bind in
       let tpat, env = bind_pat env pat (typ_of inferred_bind) in
       DEF_val (LB_aux (LB_val_implicit (tpat, inferred_bind), (l, None))), env
  end

let check_funcl env (FCL_aux (FCL_Funcl (id, pat, exp), (l, _))) typ =
  match typ with
  | Typ_aux (Typ_fn (typ_arg, typ_ret, eff), _) ->
     begin
       let typed_pat, env = bind_pat env pat typ_arg in
       let env = Env.add_ret_typ typ_ret env in
       let exp = crule check_exp env exp typ_ret in
       FCL_aux (FCL_Funcl (id, typed_pat, exp), (l, Some (env, typ)))
     end
  | _ -> typ_error l ("Function clause must have function type: " ^ string_of_typ typ ^ " is not a function type")

let check_fundef env (FD_aux (FD_function (recopt, tannotopt, effectopt, funcls), (l, _)) as fd_aux : 'a fundef) : tannot def =
  let (Typ_annot_opt_aux (Typ_annot_opt_some (annot_quant, annot_typ1), _)) = tannotopt in
  let id =
    match (List.fold_right
             (fun (FCL_aux (FCL_Funcl (id, _, _), _)) id' ->
               match id' with
               | Some id' -> if string_of_id id' = string_of_id id then Some id'
                             else typ_error l ("Function declaration expects all definitions to have the same name, "
                                               ^ string_of_id id ^ " differs from other definitions of " ^ string_of_id id')
               | None -> Some id) funcls None)
    with
    | Some id -> id
    | None -> typ_error l "funcl list is empty"
  in
  typ_print ("\nChecking function " ^ string_of_id id);
  let (quant, typ) = Env.get_val_spec id env in
  typ_debug ("Checking fundef " ^ string_of_id id ^ " has type " ^ string_of_bind (quant, typ));
  typ_debug ("Annotation typ " ^ string_of_bind (annot_quant, annot_typ1));
  let funcl_env = add_typquant quant env in
  let funcls = List.map (fun funcl -> check_funcl funcl_env funcl typ) funcls in
  DEF_fundef (FD_aux (FD_function (recopt, tannotopt, effectopt, funcls), (l, None)))

(* Checking a val spec simply adds the type as a binding in the
   context. We have to destructure the various kinds of val specs, but
   the difference is irrelevant for the typechecker. *)
let check_val_spec env (VS_aux (vs, (l, _))) =
  let (id, quants, typ) = match vs with
    | VS_val_spec (TypSchm_aux (TypSchm_ts (quants, typ), _), id) -> (id, quants, typ)
    | VS_extern_no_rename (TypSchm_aux (TypSchm_ts (quants, typ), _), id) -> (id, quants, typ)
    | VS_extern_spec (TypSchm_aux (TypSchm_ts (quants, typ), _), id, _) -> (id, quants, typ) in
  DEF_spec (VS_aux (vs, (l, None))), Env.add_val_spec id (quants, typ) env

let check_default env (DT_aux (ds, l)) =
  match ds with
  | DT_kind _ -> DEF_default (DT_aux (ds,l)), env (* Check: Is this supposed to do nothing? *)
  | DT_order (Ord_aux (Ord_inc, _)) -> DEF_default (DT_aux (ds, l)), Env.set_default_order_inc env
  | DT_order (Ord_aux (Ord_dec, _)) -> DEF_default (DT_aux (ds, l)), Env.set_default_order_dec env
  | DT_order (Ord_aux (Ord_var _, _)) -> typ_error l "Cannot have variable default order"
  (* This branch allows us to write something like: default forall Nat 'n. [|'n|] name... what does this even mean?! *)
  | DT_typ (typschm, id) -> typ_error l ("Unsupported default construct")

let check_register env id base top ranges =
  match base, top with
  | Nexp_aux (Nexp_constant basec, _), Nexp_aux (Nexp_constant topc, _) -> Env.add_regtyp id basec topc ranges env
  | _, _ -> typ_error (id_loc id) "Num expressions in register type declaration do not evaluate to constants"

let check_typedef env (TD_aux (tdef, (l, _))) =
  let td_err () = raise (Reporting_basic.err_unreachable Parse_ast.Unknown "Unimplemented Typedef") in
  match tdef with
  | TD_abbrev(id, nmscm, (TypSchm_aux (TypSchm_ts (typq, typ), _))) ->
     DEF_type (TD_aux (tdef, (l, None))), Env.add_typ_synonym id (fun _ -> typ) env
  | TD_record(id, nmscm, typq, fields, _) -> td_err ()
  | TD_variant(id, nmscm, typq, arms, _) -> td_err ()
  | TD_enum(id, nmscm, ids, _) -> td_err ()
  | TD_register(id, base, top, ranges) -> DEF_type (TD_aux (tdef, (l, None))), check_register env id base top ranges

let rec check_def env def =
  let cd_err () = raise (Reporting_basic.err_unreachable Parse_ast.Unknown "Unimplemented Case") in
  match def with
  | DEF_kind kdef -> cd_err ()
  | DEF_type tdef -> check_typedef env tdef
  | DEF_fundef fdef -> check_fundef env fdef, env
  | DEF_val letdef -> check_letdef env letdef
  | DEF_spec vs -> check_val_spec env vs
  | DEF_default default -> check_default env default
  | DEF_reg_dec (DEC_aux (DEC_reg (typ, id), (l, _))) ->
     DEF_reg_dec (DEC_aux (DEC_reg (typ, id), (l, None))), Env.add_register id typ env
  | DEF_reg_dec (DEC_aux (DEC_alias (id, aspec), (l, annot))) -> cd_err ()
  | DEF_reg_dec (DEC_aux (DEC_typ_alias (typ, id, aspec), (l, tannot))) -> cd_err ()
  | DEF_scattered _ -> raise (Reporting_basic.err_unreachable Parse_ast.Unknown "Scattered given to type checker")
  | DEF_comm (DC_comm str) -> DEF_comm (DC_comm str), env
  | DEF_comm (DC_comm_struct def) ->
     let def, env = check_def env def
     in DEF_comm (DC_comm_struct def), env

let rec check' env (Defs defs) =
  match defs with
  | [] -> (Defs []), env
  | def :: defs ->
     let (def, env) = check_def env def in
     let (Defs defs, env) = check' env (Defs defs) in
     (Defs (def::defs)), env

let check env defs =
  try check' env defs with
  | Type_error (l, m) -> raise (Reporting_basic.err_typ l m)

let initial_env =
  Env.empty
  |> Env.add_typ_synonym (mk_id "atom") (fun args -> mk_typ (Typ_app (mk_id "range", args @ args)))
  |> Env.add_overloads (mk_id "^^") [mk_id "duplicate"; mk_id "duplicate_bits"]
  |> Env.add_overloads (mk_id "!=") [mk_id "neq_vec"]
  |> Env.add_overloads (mk_id "==") [mk_id "vec_eq_01_left"; mk_id "vec_eq_01_right"]
  |> Env.add_overloads (mk_id "vector_access") [mk_id "vector_access_inc"; mk_id "vector_access_dec"]
