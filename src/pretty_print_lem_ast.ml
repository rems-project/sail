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

open Type_check
open Ast
open Format
open Pretty_print_common

(****************************************************************************
 * annotated source to Lem ast pretty printer
****************************************************************************)

let rec list_pp i_format l_format =
  fun ppf l ->
    match l with
    | [] -> fprintf ppf ""
    | [i] -> fprintf ppf "%a" l_format i
    | i::is -> fprintf ppf "%a%a" i_format i (list_pp i_format l_format) is

let pp_option_lem some_format =
  fun ppf opt ->
    match opt with
    | Some a -> fprintf ppf "(Just %a)" some_format a
    | None -> fprintf ppf "Nothing"

let pp_bool_lem ppf b = fprintf ppf (if b then "true" else "false")

let kwd ppf s = fprintf ppf "%s" s
let base ppf s = fprintf ppf "%s" s
let quot_string ppf s = fprintf ppf "\"%s\"" s

let lemnum default n =
  if Big_int.less_equal Big_int.zero n && Big_int.less_equal n (Big_int.of_int 128) then
    "int" ^ Big_int.to_string n
  else if Big_int.greater_equal n Big_int.zero then
    default n
  else ("(int0 - " ^ (default (Big_int.abs n)) ^ ")")

let pp_format_id (Id_aux(i,_)) =
  match i with
  | Id(i) -> i
  | DeIid(x) -> "(deinfix " ^ x ^ ")"

let pp_format_var (Kid_aux(Var v,_)) = v

let rec pp_format_l_lem = function
  | Parse_ast.Unknown -> "Unknown"
  | _ -> "Unknown"(*
  | Parse_ast.Int(s,None) -> "(Int \"" ^ s ^ "\" Nothing)"
  | Parse_ast.Int(s,(Some l)) -> "(Int \"" ^  s ^ "\" (Just " ^ (pp_format_l_lem l) ^ "))"
  | Parse_ast.Range(p1,p2) -> "(Range \"" ^ p1.Lexing.pos_fname ^ "\" " ^
                               (string_of_int p1.Lexing.pos_lnum) ^ " " ^
                               (string_of_int (p1.Lexing.pos_cnum - p1.Lexing.pos_bol)) ^ " " ^
                               (string_of_int p2.Lexing.pos_lnum) ^ " " ^
                              (string_of_int (p2.Lexing.pos_cnum - p2.Lexing.pos_bol)) ^ ")"
  | Parse_ast.Generated l -> "(Generated " ^ (pp_format_l_lem l) ^ ")"
  | _ -> "Unknown"*)

let pp_lem_l ppf l = base ppf (pp_format_l_lem l)

let pp_format_id_lem (Id_aux(i,l)) =
  "(Id_aux " ^
    (match i with
      | Id(i) -> "(Id \"" ^ i ^ "\")"
      | DeIid(x) -> "(DeIid \"" ^ x ^ "\")") ^ " " ^
   (pp_format_l_lem l) ^ ")"

let pp_lem_id ppf id = base ppf (pp_format_id_lem id)

let pp_format_var_lem (Kid_aux(Var v,l)) = "(Kid_aux (Var \"" ^ v ^ "\") " ^ (pp_format_l_lem l) ^ ")"

let pp_lem_var ppf var = base ppf (pp_format_var_lem var)

let pp_format_bkind_lem (BK_aux(k,l)) =
  "(BK_aux " ^
  (match k with
    | BK_type -> "BK_type"
    | BK_nat -> "BK_nat"
    | BK_order -> "BK_order") ^ " " ^
  (pp_format_l_lem l) ^ ")"

let pp_lem_bkind ppf bk = base ppf (pp_format_bkind_lem bk)

let pp_format_kind_lem (K_aux(K_kind(klst),l)) =
  "(K_aux (K_kind [" ^ list_format "; " pp_format_bkind_lem klst ^ "]) " ^ (pp_format_l_lem l) ^ ")"

let pp_lem_kind ppf k = base ppf (pp_format_kind_lem k)

let rec pp_format_typ_lem (Typ_aux(t,l)) =
  "(Typ_aux " ^
  (match t with
    | Typ_id(id) -> "(Typ_id " ^ pp_format_id_lem id ^ ")"
    | Typ_var(var) -> "(Typ_var " ^ pp_format_var_lem var ^ ")"
    | Typ_fn(arg,ret,efct) -> "(Typ_fn " ^ pp_format_typ_lem arg ^ " " ^
                              pp_format_typ_lem ret ^ " " ^
                              (pp_format_effects_lem efct) ^ ")"
    | Typ_tup(typs) -> "(Typ_tup [" ^ (list_format "; " pp_format_typ_lem typs) ^ "])"
    | Typ_app(id,args) -> "(Typ_app " ^ (pp_format_id_lem id) ^ " [" ^ (list_format "; " pp_format_typ_arg_lem args) ^ "])"
    | Typ_exist(kids,nc,typ) -> "(Typ_exist [" ^ list_format ";" pp_format_var_lem kids ^ "] " ^ pp_format_nexp_constraint_lem nc ^ " " ^ pp_format_typ_lem typ ^ ")") ^ " " ^
    (pp_format_l_lem l) ^ ")"
and pp_format_nexp_lem (Nexp_aux(n,l)) =
  "(Nexp_aux " ^
  (match n with
   | Nexp_id(i) -> "(Nexp_id " ^ pp_format_id_lem i ^ ")"
   | Nexp_var(v) -> "(Nexp_var " ^ pp_format_var_lem v ^ ")"
   | Nexp_app(op,args) -> "(Nexp_app [" ^ Util.string_of_list ", " pp_format_nexp_lem args ^ "])"
   | Nexp_constant(i) -> "(Nexp_constant " ^ (lemnum Big_int.to_string i) ^ ")"
   | Nexp_sum(n1,n2) -> "(Nexp_sum " ^ (pp_format_nexp_lem n1) ^ " " ^ (pp_format_nexp_lem n2) ^ ")"
   | Nexp_minus(n1,n2) -> "(Nexp_minus " ^ (pp_format_nexp_lem n1)^ " " ^ (pp_format_nexp_lem n2) ^ ")"
   | Nexp_times(n1,n2) -> "(Nexp_times " ^  (pp_format_nexp_lem n1) ^ " " ^ (pp_format_nexp_lem n2) ^ ")"
   | Nexp_exp(n1) -> "(Nexp_exp " ^ (pp_format_nexp_lem n1) ^ ")"
   | Nexp_neg(n1) -> "(Nexp_neg " ^ (pp_format_nexp_lem n1) ^ ")") ^ " " ^
  (pp_format_l_lem l) ^ ")"
and pp_format_ord_lem (Ord_aux(o,l)) =
  "(Ord_aux " ^
  (match o with
    | Ord_var(v) -> "(Ord_var " ^ pp_format_var_lem v ^ ")"
    | Ord_inc -> "Ord_inc"
    | Ord_dec -> "Ord_dec") ^ " " ^
   (pp_format_l_lem l) ^ ")"
and pp_format_base_effect_lem (BE_aux(e,l)) =
  "(BE_aux " ^
  (match e with
    | BE_rreg -> "BE_rreg"
    | BE_wreg -> "BE_wreg"
    | BE_rmem -> "BE_rmem"
    | BE_rmemt -> "BE_rmemt"
    | BE_wmem -> "BE_wmem"
    | BE_wmv  -> "BE_wmv"
    | BE_wmvt  -> "BE_wmvt"
    | BE_eamem -> "BE_eamem"
    | BE_exmem -> "BE_exmem"
    | BE_barr -> "BE_barr"
    | BE_depend -> "BE_depend"
    | BE_undef -> "BE_undef"
    | BE_unspec -> "BE_unspec"
    | BE_nondet -> "BE_nondet"
    | BE_lset -> "BE_lset"
    | BE_lret -> "BE_lret"
    | BE_escape -> "BE_escape") ^ " " ^
  (pp_format_l_lem l) ^ ")"
and pp_format_effects_lem (Effect_aux(e,l)) =
  "(Effect_aux " ^
  (match e with
  | Effect_set(efcts) ->
    "(Effect_set [" ^
      (list_format "; " pp_format_base_effect_lem efcts) ^ " ])") ^ " " ^
  (pp_format_l_lem l) ^ ")"
and pp_format_typ_arg_lem (Typ_arg_aux(t,l)) =
  "(Typ_arg_aux " ^
  (match t with
   | Typ_arg_typ(t) -> "(Typ_arg_typ " ^ pp_format_typ_lem t ^ ")"
   | Typ_arg_nexp(n) -> "(Typ_arg_nexp " ^ pp_format_nexp_lem n ^ ")"
   | Typ_arg_order(o) -> "(Typ_arg_order " ^ pp_format_ord_lem o ^ ")") ^ " " ^
  (pp_format_l_lem l) ^ ")"
and pp_format_nexp_constraint_lem (NC_aux(nc,l)) =
  "(NC_aux " ^
  (match nc with
  | NC_equal(n1,n2) -> "(NC_equal " ^ pp_format_nexp_lem n1 ^ " " ^ pp_format_nexp_lem n2 ^ ")"
  | NC_bounded_ge(n1,n2) -> "(NC_bounded_ge " ^ pp_format_nexp_lem n1 ^ " " ^ pp_format_nexp_lem n2 ^ ")"
  | NC_bounded_le(n1,n2) -> "(NC_bounded_le " ^ pp_format_nexp_lem n1 ^ " " ^ pp_format_nexp_lem n2 ^ ")"
  | NC_not_equal(n1,n2) -> "(NC_not_equal " ^ pp_format_nexp_lem n1 ^ " " ^ pp_format_nexp_lem n2 ^ ")"
  | NC_or(nc1,nc2) -> "(NC_or " ^ pp_format_nexp_constraint_lem nc1 ^ " " ^ pp_format_nexp_constraint_lem nc2 ^ ")"
  | NC_and(nc1,nc2) -> "(NC_and " ^ pp_format_nexp_constraint_lem nc1 ^ " " ^ pp_format_nexp_constraint_lem nc2 ^ ")"
  | NC_true -> "NC_true"
  | NC_false -> "NC_false"
  | NC_set(id,bounds) -> "(NC_set " ^
    pp_format_var_lem id ^
      " [" ^
      list_format "; " Big_int.to_string bounds ^
      "])") ^ " " ^
  (pp_format_l_lem l) ^ ")"

let pp_lem_typ ppf t = base ppf (pp_format_typ_lem t)
let pp_lem_nexp ppf n = base ppf (pp_format_nexp_lem n)
let pp_lem_ord ppf o = base ppf (pp_format_ord_lem o)
let pp_lem_effects ppf e = base ppf (pp_format_effects_lem e)
let pp_lem_beffect ppf be = base ppf (pp_format_base_effect_lem be)
let pp_lem_loop ppf l =
  let l_str = match l with
  | While -> "While"
  | Until -> "Until" in
  base ppf l_str
let pp_lem_prec ppf p =
  let p_str = match p with
  | Infix -> "Infix"
  | InfixL -> "InfixL"
  | InfixR -> "InfixR" in
  base ppf p_str

let pp_lem_nexp_constraint ppf nc = base ppf (pp_format_nexp_constraint_lem nc)

let pp_format_qi_lem (QI_aux(qi,lq)) =
  "(QI_aux " ^
  (match qi with
  | QI_const(n_const) -> "(QI_const " ^ pp_format_nexp_constraint_lem n_const ^ ")"
  | QI_id(KOpt_aux(ki,lk)) ->
    "(QI_id (KOpt_aux " ^
    (match ki with
    | KOpt_none(var) -> "(KOpt_none " ^ pp_format_var_lem var ^ ")"
    | KOpt_kind(k,var) -> "(KOpt_kind " ^ pp_format_kind_lem k ^ " " ^ pp_format_var_lem var ^ ")") ^ " " ^
      (pp_format_l_lem lk) ^ "))") ^ " " ^
  (pp_format_l_lem lq) ^ ")"

let pp_lem_qi ppf qi = base ppf (pp_format_qi_lem qi)

let pp_format_typquant_lem (TypQ_aux(tq,l)) =
  "(TypQ_aux " ^
  (match tq with
  | TypQ_no_forall -> "TypQ_no_forall"
  | TypQ_tq(qlist) ->
    "(TypQ_tq [" ^
    (list_format "; " pp_format_qi_lem qlist) ^
    "])") ^ " " ^
  (pp_format_l_lem l) ^ ")"

let pp_lem_typquant ppf tq = base ppf (pp_format_typquant_lem tq)

let pp_format_typscm_lem (TypSchm_aux(TypSchm_ts(tq,t),l)) =
  "(TypSchm_aux (TypSchm_ts " ^ (pp_format_typquant_lem tq) ^ " " ^ pp_format_typ_lem t ^ ") " ^
                (pp_format_l_lem l) ^ ")"

let pp_lem_typscm ppf ts = base ppf (pp_format_typscm_lem ts)

let pp_format_lit_lem (L_aux(lit,l)) =
  "(L_aux " ^
  (match lit with
  | L_unit -> "L_unit"
  | L_zero -> "L_zero"
  | L_one -> "L_one"
  | L_true -> "L_true"
  | L_false -> "L_false"
  | L_num(i) -> "(L_num " ^ (lemnum Big_int.to_string i) ^ ")"
  | L_hex(n) -> "(L_hex \"" ^ n ^ "\")"
  | L_bin(n) -> "(L_bin \"" ^ n ^ "\")"
  | L_undef -> "L_undef"
  | L_string(s) -> "(L_string \"" ^ s ^ "\")"
  | L_real(s) -> "(L_real \"" ^ s ^ "\")") ^ " " ^
  (pp_format_l_lem l) ^ ")"

let pp_lem_lit ppf l = base ppf (pp_format_lit_lem l)


let tag_id id env =
  if Env.is_extern id env "lem_ast" then
    "Tag_extern (Just \"" ^ Ast_util.string_of_id id ^ "\")"
  else if Env.is_union_constructor id env then
    "Tag_ctor"
  else
    "Tag_empty"

let pp_format_annot ?tag:(t="Tag_empty") = function
  | None -> "Nothing"
  | Some (_, typ, eff) ->
     "(Just ("
     ^ pp_format_typ_lem typ ^ ", "
     ^ t ^ ", "
     ^ "[], "
     ^ pp_format_effects_lem eff ^ ", "
     ^ pp_format_effects_lem eff
     ^ "))"

let pp_annot ppf ant = base ppf (pp_format_annot ant)

let pp_annot_tag tag ppf ant = base ppf (pp_format_annot ~tag:tag ant)

let rec pp_format_pat_lem (P_aux(p,(l,annot))) =
  "(P_aux " ^
  (match p with
  | P_lit(lit) -> "(P_lit " ^ pp_format_lit_lem lit ^ ")"
  | P_wild -> "P_wild"
  | P_id(id) -> "(P_id " ^ pp_format_id_lem id ^ ")"
  | P_var(pat,_) -> "(P_var " ^ pp_format_pat_lem pat ^ ")" (* FIXME *)
  | P_as(pat,id) -> "(P_as " ^ pp_format_pat_lem pat ^ " " ^ pp_format_id_lem id ^ ")"
  | P_typ(typ,pat) -> "(P_typ " ^ pp_format_typ_lem typ ^ " " ^ pp_format_pat_lem pat ^ ")"
  | P_app(id,pats) -> "(P_app " ^ pp_format_id_lem id ^ " [" ^
                      list_format "; " pp_format_pat_lem pats ^ "])"
  | P_record(fpats,_) -> "(P_record [" ^
                       list_format "; " (fun (FP_aux(FP_Fpat(id,fpat),_)) ->
                                          "(FP_Fpat " ^ pp_format_id_lem id ^ " " ^ pp_format_pat_lem fpat ^ ")") fpats
                       ^ "])"
  | P_vector(pats) -> "(P_vector [" ^ list_format "; " pp_format_pat_lem pats ^ "])"
  | P_vector_concat(pats) -> "(P_vector_concat [" ^ list_format "; " pp_format_pat_lem pats ^ "])"
  | P_tup(pats) -> "(P_tup [" ^ (list_format "; " pp_format_pat_lem pats) ^ "])"
  | P_list(pats) -> "(P_list [" ^ (list_format "; " pp_format_pat_lem pats) ^ "])"
  | P_cons(pat,pat') -> "(P_cons " ^ pp_format_pat_lem pat ^ " " ^ pp_format_pat_lem pat' ^ ")") ^
  " (" ^ pp_format_l_lem l ^ ", " ^ pp_format_annot annot ^ "))"

let pp_lem_pat ppf p = base ppf (pp_format_pat_lem p)

let rec pp_lem_let ppf (LB_aux(lb,(l,annot))) =
  let print_lb ppf lb =
    match lb with
      | LB_val(pat,exp) ->
        fprintf ppf "@[<0>(%a %a %a)@]" kwd "LB_val" pp_lem_pat pat  pp_lem_exp exp in
  fprintf ppf "@[<0>(LB_aux %a (%a, %a))@]" print_lb lb pp_lem_l l pp_annot annot

and pp_lem_exp ppf (E_aux(e,(l,annot)) as exp) =
  let env = env_of exp in
  let print_e ppf e =
    match e with
    | E_block(exps) -> fprintf ppf "@[<0>(E_aux %a [%a] %a (%a, %a))@]"
      kwd "(E_block"
      (list_pp pp_semi_lem_exp pp_lem_exp) exps
      kwd ")" pp_lem_l l pp_annot annot
    | E_nondet(exps) -> fprintf ppf "@[<0>(E_aux %a [%a] %a (%a, %a))@]"
      kwd "(E_nondet"
      (list_pp pp_semi_lem_exp pp_lem_exp) exps
      kwd ")" pp_lem_l l pp_annot annot
    | E_id(id) -> fprintf ppf "(E_aux (%a %a) (%a, %a))" kwd "E_id" pp_lem_id id pp_lem_l l (pp_annot_tag (tag_id id env)) annot
    | E_ref(id) -> fprintf ppf "(E_aux (%a %a) (%a, %a))" kwd "E_ref" pp_lem_id id pp_lem_l l (pp_annot_tag (tag_id id env)) annot
    | E_lit(lit) -> fprintf ppf "(E_aux (%a %a) (%a, %a))" kwd "E_lit" pp_lem_lit lit pp_lem_l l pp_annot annot
    | E_cast(typ,exp) ->
      fprintf ppf "@[<0>(E_aux (E_cast %a %a) (%a, %a))@]" pp_lem_typ typ pp_lem_exp exp pp_lem_l l pp_annot annot
    | E_internal_cast((_,None),e) -> pp_lem_exp ppf e
    | E_app(f,args) -> fprintf ppf "@[<0>(E_aux (E_app %a [%a]) (%a, %a))@]"
                         pp_lem_id f (list_pp pp_semi_lem_exp pp_lem_exp) args pp_lem_l l (pp_annot_tag (tag_id f env)) annot
    | E_app_infix(l',op,r) -> fprintf ppf "@[<0>(E_aux (E_app_infix %a %a %a) (%a, %a))@]"
                                pp_lem_exp l' pp_lem_id op pp_lem_exp r pp_lem_l l pp_annot annot
    | E_tuple(exps) -> fprintf ppf "@[<0>(E_aux (E_tuple [%a]) (%a, %a))@]"
                         (list_pp pp_semi_lem_exp pp_lem_exp) exps pp_lem_l l pp_annot annot
    | E_if(c,t,e) -> fprintf ppf "@[<0>(E_aux (E_if %a @[<1>%a@] @[<1> %a@]) (%a, %a))@]"
                       pp_lem_exp c pp_lem_exp t pp_lem_exp e pp_lem_l l pp_annot annot
    | E_for(id,exp1,exp2,exp3,order,exp4) ->
      fprintf ppf "@[<0>(E_aux (E_for %a %a %a %a %a @ @[<1> %a @]) (%a, %a))@]"
        pp_lem_id id pp_lem_exp exp1 pp_lem_exp exp2 pp_lem_exp exp3
        pp_lem_ord order pp_lem_exp exp4 pp_lem_l l pp_annot annot
    | E_loop(loop,cond,body) ->
      fprintf ppf "@[<0>(E_aux (E_loop %a %a @ @[<1> %a @]) (%a, %a))@]"
        pp_lem_loop loop pp_lem_exp cond pp_lem_exp body pp_lem_l l pp_annot annot
    | E_vector(exps) -> fprintf ppf "@[<0>(E_aux (%a [%a]) (%a, %a))@]"
                          kwd "E_vector" (list_pp pp_semi_lem_exp pp_lem_exp) exps pp_lem_l l pp_annot annot
    | E_vector_access(v,e) ->
      fprintf ppf "@[<0>(E_aux (%a %a %a) (%a, %a))@]"
        kwd "E_vector_access" pp_lem_exp v pp_lem_exp e pp_lem_l l pp_annot annot
    | E_vector_subrange(v,e1,e2) ->
      fprintf ppf "@[<0>(E_aux (E_vector_subrange %a %a %a) (%a, %a))@]"
        pp_lem_exp v pp_lem_exp e1 pp_lem_exp e2 pp_lem_l l pp_annot annot
    | E_vector_update(v,e1,e2) ->
      fprintf ppf "@[<0>(E_aux (E_vector_update %a %a %a) (%a, %a))@]"
        pp_lem_exp v pp_lem_exp e1 pp_lem_exp e2 pp_lem_l l pp_annot annot
    | E_vector_update_subrange(v,e1,e2,e3) ->
      fprintf ppf "@[<0>(E_aux (E_vector_update_subrange %a %a %a %a) (%a, %a))@]"
        pp_lem_exp v pp_lem_exp e1 pp_lem_exp e2 pp_lem_exp e3 pp_lem_l l pp_annot annot
    | E_vector_append(v1,v2) ->
      fprintf ppf "@[<0>(E_aux (E_vector_append %a %a) (%a, %a))@]"
        pp_lem_exp v1 pp_lem_exp v2 pp_lem_l l pp_annot annot
    | E_list(exps) -> fprintf ppf "@[<0>(E_aux (E_list [%a]) (%a, %a))@]"
                        (list_pp pp_semi_lem_exp pp_lem_exp) exps pp_lem_l l pp_annot annot
    | E_cons(e1,e2) -> fprintf ppf "@[<0>(E_aux (E_cons %a %a) (%a, %a))@]"
                         pp_lem_exp e1 pp_lem_exp e2 pp_lem_l l pp_annot annot
    | E_record(FES_aux(FES_Fexps(fexps,_),(fl,fannot))) ->
      fprintf ppf "@[<0>(E_aux (E_record (FES_aux (FES_Fexps [%a] false) (%a,%a))) (%a, %a))@]"
        (list_pp pp_semi_lem_fexp pp_lem_fexp) fexps pp_lem_l fl pp_annot fannot pp_lem_l l pp_annot annot
    | E_record_update(exp,(FES_aux(FES_Fexps(fexps,_),(fl,fannot)))) ->
      fprintf ppf "@[<0>(E_aux (E_record_update %a (FES_aux (FES_Fexps [%a] false) (%a,%a))) (%a,%a))@]"
        pp_lem_exp exp (list_pp pp_semi_lem_fexp pp_lem_fexp) fexps
        pp_lem_l fl pp_annot fannot pp_lem_l l pp_annot annot
    | E_field(fexp,id) -> fprintf ppf "@[<0>(E_aux (E_field %a %a) (%a, %a))@]"
                            pp_lem_exp fexp pp_lem_id id pp_lem_l l pp_annot annot
    | E_case(exp,pexps) ->
      fprintf ppf "@[<0>(E_aux (E_case %a [%a]) (%a, %a))@]"
        pp_lem_exp exp (list_pp pp_semi_lem_case pp_lem_case) pexps pp_lem_l l pp_annot annot
    | E_try(exp,pexps) ->
      fprintf ppf "@[<0>(E_aux (E_try %a [%a]) (%a, %a))@]"
        pp_lem_exp exp (list_pp pp_semi_lem_case pp_lem_case) pexps pp_lem_l l pp_annot annot
    | E_let(leb,exp) -> fprintf ppf "@[<0>(E_aux (E_let %a %a) (%a, %a))@]"
                          pp_lem_let leb pp_lem_exp exp pp_lem_l l pp_annot annot
    | E_assign(lexp,exp) -> fprintf ppf "@[<0>(E_aux (E_assign %a %a) (%a, %a))@]"
                              pp_lem_lexp lexp pp_lem_exp exp pp_lem_l l pp_annot annot
    | E_sizeof nexp ->
      fprintf ppf "@[<0>(E_aux (E_sizeof %a) (%a, %a))@]" pp_lem_nexp nexp pp_lem_l l pp_annot annot
    | E_constraint nc ->
      fprintf ppf "@[<0>(E_aux (E_constraint %a) (%a, %a))@]" pp_lem_nexp_constraint nc pp_lem_l l pp_annot annot
    | E_exit exp ->
      fprintf ppf "@[<0>(E_aux (E_exit %a) (%a, %a))@]" pp_lem_exp exp pp_lem_l l pp_annot annot
    | E_throw exp ->
      fprintf ppf "@[<0>(E_aux (E_throw %a) (%a, %a))@]" pp_lem_exp exp pp_lem_l l pp_annot annot
    | E_return exp ->
      fprintf ppf "@[<0>(E_aux (E_return %a) (%a, %a))@]" pp_lem_exp exp pp_lem_l l pp_annot annot
    | E_assert(c,msg) ->
      fprintf ppf "@[<0>(E_aux (E_assert %a %a) (%a, %a))@]" pp_lem_exp c pp_lem_exp msg pp_lem_l l pp_annot annot
    | E_comment _ | E_comment_struc _ ->
      fprintf ppf "@[(E_aux (E_lit (L_aux L_unit %a)) (%a,%a))@]" pp_lem_l l pp_lem_l l pp_annot annot
    | E_internal_cast _ | E_internal_exp _ ->
      raise (Reporting_basic.err_unreachable l "Found internal cast or exp")
    | E_internal_exp_user _ -> (raise (Reporting_basic.err_unreachable l "Found non-rewritten internal_exp_user"))
    | E_sizeof_internal _ -> (raise (Reporting_basic.err_unreachable l "Internal sizeof not removed"))
    | E_var (lexp,exp1,exp2) ->
      fprintf ppf "@[<0>(E_aux (E_var %a %a %a) (%a, %a))@]"
        pp_lem_lexp lexp pp_lem_exp exp1 pp_lem_exp exp2 pp_lem_l l pp_annot annot
    | E_internal_return exp ->
      fprintf ppf "@[<0>(E_aux (E_internal_return %a) (%a, %a))@]"
        pp_lem_exp exp pp_lem_l l pp_annot annot
    | E_internal_plet (pat,exp1,exp2) ->
      fprintf ppf "@[<0>(E_aux (E_internal_plet %a %a %a) (%a, %a))@]"
        pp_lem_pat pat pp_lem_exp exp1 pp_lem_exp exp2 pp_lem_l l pp_annot annot
    | E_internal_value _ -> raise (Reporting_basic.err_unreachable l "Found internal_value")
  in
  print_e ppf e

and pp_semi_lem_exp ppf e = fprintf ppf "@[<1>%a%a@]" pp_lem_exp e kwd ";"

and pp_lem_fexp ppf (FE_aux(FE_Fexp(id,exp),(l,annot))) =
  fprintf ppf "@[<1>(FE_aux (FE_Fexp %a %a) (%a, %a))@]" pp_lem_id id pp_lem_exp exp pp_lem_l l pp_annot annot
and pp_semi_lem_fexp ppf fexp = fprintf ppf "@[<1>%a %a@]" pp_lem_fexp fexp kwd ";"

and pp_lem_case ppf = function
| Pat_aux(Pat_exp(pat,exp),(l,annot)) ->
  fprintf ppf "@[<1>(Pat_aux (Pat_exp %a@ %a) (%a, %a))@]" pp_lem_pat pat pp_lem_exp exp pp_lem_l l pp_annot annot
| Pat_aux(Pat_when(pat,guard,exp),(l,annot)) ->
  fprintf ppf "@[<1>(Pat_aux (Pat_when %a@ %a %a) (%a, %a))@]" pp_lem_pat pat pp_lem_exp guard pp_lem_exp exp pp_lem_l l pp_annot annot
and pp_semi_lem_case ppf case = fprintf ppf "@[<1>%a %a@]" pp_lem_case case kwd ";"

and pp_lem_lexp ppf (LEXP_aux(lexp,(l,annot))) =
  let print_le ppf lexp =
    match lexp with
    | LEXP_id(id) -> fprintf ppf "(%a %a)" kwd "LEXP_id" pp_lem_id id
    | LEXP_deref exp ->
       fprintf ppf "(LEXP_deref %a)" pp_lem_exp exp
    | LEXP_memory(id,args) ->
       fprintf ppf "(LEXP_memory %a [%a])" pp_lem_id id (list_pp pp_semi_lem_exp pp_lem_exp) args
    | LEXP_cast(typ,id) -> fprintf ppf "(LEXP_cast %a %a)" pp_lem_typ typ pp_lem_id id
    | LEXP_tup tups -> fprintf ppf "(LEXP_tup [%a])" (list_pp pp_semi_lem_lexp pp_lem_lexp) tups
    | LEXP_vector(v,exp) -> fprintf ppf "@[(%a %a %a)@]" kwd "LEXP_vector" pp_lem_lexp v pp_lem_exp exp
    | LEXP_vector_range(v,e1,e2) ->
       fprintf ppf "@[(%a %a %a %a)@]" kwd "LEXP_vector_range" pp_lem_lexp v  pp_lem_exp e1 pp_lem_exp e2
    | LEXP_field(v,id) -> fprintf ppf "@[(%a %a %a)@]" kwd "LEXP_field" pp_lem_lexp v pp_lem_id id
  in
  fprintf ppf "@[(LEXP_aux %a (%a, %a))@]" print_le lexp pp_lem_l l pp_annot annot
and pp_semi_lem_lexp ppf le = fprintf ppf "@[<1>%a%a@]" pp_lem_lexp le kwd ";"

let pp_semi_lem_id ppf id = fprintf ppf "@[<1>%a%a@]" pp_lem_id id kwd ";"

let pp_lem_default ppf (DT_aux(df,l)) =
  let print_de ppf df =
    match df with
      | DT_kind(bk,var) -> fprintf ppf "@[<0>(%a %a %a)@]" kwd "DT_kind" pp_lem_bkind bk pp_lem_var var
      | DT_typ(ts,id) -> fprintf ppf "@[<0>(%a %a %a)@]" kwd "DT_typ" pp_lem_typscm ts pp_lem_id id
      | DT_order(ord) -> fprintf ppf "@[<0>(DT_order %a)@]" pp_lem_ord ord
  in
  fprintf ppf "@[<0>(DT_aux %a %a)@]" print_de df pp_lem_l l

(* FIXME *)
let pp_lem_spec ppf (VS_aux(v,(l,annot))) =
  let print_spec ppf (VS_val_spec(ts, id, ext_opt, is_cast)) =
    fprintf ppf "@[<0>(%a %a %a %a %a)@]@\n" kwd "VS_val_spec" pp_lem_typscm ts pp_lem_id id (pp_option_lem quot_string) None pp_bool_lem is_cast
  in
  fprintf ppf "@[<0>(VS_aux %a (%a, %a))@]" print_spec v pp_lem_l l pp_annot annot

let pp_lem_namescm ppf (Name_sect_aux(ns,l)) =
  match ns with
  | Name_sect_none -> fprintf ppf "(Name_sect_aux Name_sect_none %a)" pp_lem_l l
  | Name_sect_some(s) -> fprintf ppf "(Name_sect_aux (Name_sect_some \"%s\") %a)" s pp_lem_l l

let rec pp_lem_range ppf (BF_aux(r,l)) =
  match r with
  | BF_single(i) -> fprintf ppf "(BF_aux (BF_single %i) %a)" (Big_int.to_int i) pp_lem_l l
  | BF_range(i1,i2) -> fprintf ppf "(BF_aux (BF_range %i %i) %a)" (Big_int.to_int i1) (Big_int.to_int i2) pp_lem_l l
  | BF_concat(ir1,ir2) -> fprintf ppf "(BF_aux (BF_concat %a %a) %a)" pp_lem_range ir1 pp_lem_range ir2 pp_lem_l l

let pp_lem_typdef ppf (TD_aux(td,(l,annot))) =
  let print_td ppf td =
    match td with
      | TD_abbrev(id,namescm,typschm) ->
        fprintf ppf "@[<0>(%a %a %a %a)@]" kwd "TD_abbrev" pp_lem_id id pp_lem_namescm namescm pp_lem_typscm typschm
      | TD_record(id,nm,typq,fs,_) ->
        let f_pp ppf (typ,id) =
          fprintf ppf "@[<1>(%a, %a)%a@]" pp_lem_typ typ pp_lem_id id kwd ";" in
        fprintf ppf "@[<0>(%a %a %a %a [%a] false)@]"
          kwd "TD_record" pp_lem_id id pp_lem_namescm nm pp_lem_typquant typq (list_pp f_pp f_pp) fs
      | TD_variant(id,nm,typq,ar,_) ->
        let a_pp ppf (Tu_aux(Tu_ty_id(typ,id),l)) =
          fprintf ppf "@[<1>(Tu_aux (Tu_ty_id %a %a) %a);@]"
                  pp_lem_typ typ pp_lem_id id pp_lem_l l
        in
        fprintf ppf "@[<0>(%a %a %a %a [%a] false)@]"
          kwd "TD_variant" pp_lem_id id pp_lem_namescm nm pp_lem_typquant typq (list_pp a_pp a_pp) ar
      | TD_enum(id,ns,enums,_) ->
        let pp_id_semi ppf id = fprintf ppf "%a%a " pp_lem_id id kwd ";" in
        fprintf ppf "@[<0>(%a %a %a [%a] false)@]"
          kwd "TD_enum" pp_lem_id id pp_lem_namescm ns (list_pp pp_id_semi pp_lem_id) enums
      | TD_bitfield(id,typ,rs) ->
        let pp_rid ppf (id, r) = fprintf ppf "(%a, %a)%a " pp_lem_range r pp_lem_id id kwd ";" in
        let pp_rids = (list_pp pp_rid pp_rid) in
        fprintf ppf "@[<0>(%a %a %a [%a])@]"
          kwd "TD_bitfield" pp_lem_id id pp_lem_typ typ pp_rids rs
  in
  fprintf ppf "@[<0>(TD_aux %a (%a, %a))@]" print_td td pp_lem_l l pp_annot annot

let pp_lem_kindef ppf (KD_aux(kd,(l,annot))) =
  let print_kd ppf kd =
    match kd with
    | KD_nabbrev(kind,id,namescm,n) ->
      fprintf ppf "@[<0>(KD_nabbrev %a %a %a %a)@]"
        pp_lem_kind kind pp_lem_id id pp_lem_namescm namescm pp_lem_nexp n
  in
  fprintf ppf "@[<0>(KD_aux %a (%a, %a))@]" print_kd kd pp_lem_l l pp_annot annot

let pp_lem_rec ppf (Rec_aux(r,l)) =
  match r with
  | Rec_nonrec -> fprintf ppf "(Rec_aux Rec_nonrec %a)" pp_lem_l l
  | Rec_rec -> fprintf ppf "(Rec_aux Rec_rec %a)" pp_lem_l l

let pp_lem_tannot_opt ppf (Typ_annot_opt_aux(t,l)) =
  match t with
  | Typ_annot_opt_some(tq,typ) ->
    fprintf ppf "(Typ_annot_opt_aux (Typ_annot_opt_some %a %a) %a)" pp_lem_typquant tq pp_lem_typ typ pp_lem_l l
  | Typ_annot_opt_none ->
    fprintf ppf "(Typ_annot_opt_aux (Typ_annot_opt_none) %a)" pp_lem_l l

let pp_lem_effects_opt ppf (Effect_opt_aux(e,l)) =
  match e with
  | Effect_opt_pure -> fprintf ppf "(Effect_opt_aux Effect_opt_pure %a)" pp_lem_l l
  | Effect_opt_effect e -> fprintf ppf "(Effect_opt_aux (Effect_opt_effect %a) %a)" pp_lem_effects e pp_lem_l l

let pp_lem_funcl ppf (FCL_aux(FCL_Funcl(id,pexp),(l,annot))) =
  fprintf ppf "@[<0>(FCL_aux (%a %a %a) (%a,%a))@]@\n"
    kwd "FCL_Funcl" pp_lem_id id pp_lem_case pexp pp_lem_l l pp_annot annot

let pp_lem_fundef ppf (FD_aux(FD_function(r, typa, efa, fcls),(l,annot))) =
  let pp_funcls ppf funcl = fprintf ppf "%a %a" pp_lem_funcl funcl kwd ";" in
  fprintf ppf "@[<0>(FD_aux (%a %a %a %a [%a]) (%a, %a))@]"
    kwd "FD_function" pp_lem_rec r pp_lem_tannot_opt typa pp_lem_effects_opt efa (list_pp pp_funcls pp_funcls) fcls
    pp_lem_l l pp_annot annot

let pp_lem_aspec ppf (AL_aux(aspec,(l,annot))) =
  let pp_reg_id ppf (RI_aux((RI_id ri),(l,annot))) =
    fprintf ppf "@[<0>(RI_aux (RI_id %a) (%a,%a))@]" pp_lem_id ri pp_lem_l l pp_annot annot in
  match aspec with
    | AL_subreg(reg,subreg) ->
      fprintf ppf "@[<0>(AL_aux (AL_subreg %a %a) (%a,%a))@]"
        pp_reg_id reg pp_lem_id subreg pp_lem_l l pp_annot annot
    | AL_bit(reg,ac) ->
      fprintf ppf "@[<0>(AL_aux (AL_bit %a %a) (%a,%a))@]" pp_reg_id reg pp_lem_exp ac pp_lem_l l pp_annot annot
    | AL_slice(reg,b,e) ->
      fprintf ppf "@[<0>(AL_aux (AL_slice %a %a %a) (%a,%a))@]"
        pp_reg_id reg pp_lem_exp b pp_lem_exp e pp_lem_l l pp_annot annot
    | AL_concat(f,s) ->
      fprintf ppf "@[<0>(AL_aux (AL_concat %a %a) (%a,%a))@]" pp_reg_id f pp_reg_id s pp_lem_l l pp_annot annot

let pp_lem_dec ppf (DEC_aux(reg,(l,annot))) =
  match reg with
  | DEC_reg(typ,id) ->
    fprintf ppf "@[<0>(DEC_aux (DEC_reg %a %a) (%a,%a))@]" pp_lem_typ typ pp_lem_id id pp_lem_l l pp_annot annot
  | DEC_alias(id,alias_spec) ->
    fprintf ppf "@[<0>(DEC_aux (DEC_alias %a %a) (%a, %a))@]"
      pp_lem_id id pp_lem_aspec alias_spec pp_lem_l l pp_annot annot
  | DEC_typ_alias(typ,id,alias_spec) ->
    fprintf ppf "@[<0>(DEC_aux (DEC_typ_alias %a %a %a) (%a, %a))@]"
      pp_lem_typ typ pp_lem_id id pp_lem_aspec alias_spec pp_lem_l l pp_annot annot

let rec pp_lem_def ppf d =
  match d with
  | DEF_default(df) -> fprintf ppf "(DEF_default %a);@\n" pp_lem_default df
  | DEF_spec(v_spec) -> fprintf ppf "(DEF_spec %a);@\n" pp_lem_spec v_spec
  | DEF_overload(id,ids) -> fprintf ppf "(DEF_overload %a [%a]);@\n" pp_lem_id id (list_pp pp_semi_lem_id pp_lem_id) ids
  | DEF_type(t_def) -> fprintf ppf "(DEF_type %a);@\n" pp_lem_typdef t_def
  | DEF_kind(k_def) -> fprintf ppf "(DEF_kind %a);@\n" pp_lem_kindef k_def
  | DEF_fundef(f_def) -> fprintf ppf "(DEF_fundef %a);@\n" pp_lem_fundef f_def
  | DEF_val(lbind) -> fprintf ppf "(DEF_val %a);@\n" pp_lem_let lbind
  | DEF_reg_dec(dec) -> fprintf ppf "(DEF_reg_dec %a);@\n" pp_lem_dec dec
  | DEF_comm d -> fprintf ppf ""
  | DEF_fixity (prec, n, id) -> fprintf ppf "(DEF_fixity %a %s %a);@\n" pp_lem_prec prec (lemnum Big_int.to_string n) pp_lem_id id
  | DEF_internal_mutrec f_defs -> List.iter (fun f_def -> pp_lem_def ppf (DEF_fundef f_def)) f_defs
  | _ -> raise (Reporting_basic.err_unreachable Parse_ast.Unknown "initial_check didn't remove all scattered Defs")

let pp_lem_defs ppf (Defs(defs)) =
  fprintf ppf "Defs [@[%a@]]@\n" (list_pp pp_lem_def pp_lem_def) defs
