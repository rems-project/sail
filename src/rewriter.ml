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
open Ast
open Ast_util
open Type_check
open Spec_analysis

type 'a rewriters = {
    rewrite_exp  : 'a rewriters -> 'a exp -> 'a exp;
    rewrite_lexp : 'a rewriters -> 'a lexp -> 'a lexp;
    rewrite_pat  : 'a rewriters -> 'a pat -> 'a pat;
    rewrite_let  : 'a rewriters -> 'a letbind -> 'a letbind;
    rewrite_fun  : 'a rewriters -> 'a fundef -> 'a fundef;
    rewrite_def  : 'a rewriters -> 'a def -> 'a def;
    rewrite_defs : 'a rewriters -> 'a defs -> 'a defs;
  }

let effect_of_fpat (FP_aux (_,(_,a))) = effect_of_annot a
let effect_of_lexp (LEXP_aux (_,(_,a))) = effect_of_annot a
let effect_of_fexp (FE_aux (_,(_,a))) = effect_of_annot a
let effect_of_fexps fexps =
  List.fold_left union_effects no_effect (List.map effect_of_fexp fexps)
let effect_of_opt_default (Def_val_aux (_,(_,a))) = effect_of_annot a
(* The typechecker does not seem to annotate pexps themselves *)
let effect_of_pexp (Pat_aux (pexp,(_,a))) =
  let eff = match pexp with
    | Pat_exp (p, e) -> union_effects (effect_of_pat p) (effect_of e)
    | Pat_when (p, g, e) ->
       union_effects (effect_of_pat p) (union_effects (effect_of g) (effect_of e))
  in
  union_effects eff (effect_of_annot a)
let effect_of_lb (LB_aux (_,(_,a))) = effect_of_annot a

let simple_annot l typ = (gen_loc l, mk_tannot initial_env typ no_effect)


let lookup_generated_kid env kid =
  let match_kid_nc kid = function
    | NC_aux (NC_equal (Nexp_aux (Nexp_var kid1, _), Nexp_aux (Nexp_var kid2, _)), _)
      when Kid.compare kid kid2 = 0 && not (is_kid_generated kid1) -> kid1
    | _ -> kid
  in
  List.fold_left match_kid_nc kid (Env.get_constraints env)

let generated_kids typ = KidSet.filter is_kid_generated (tyvars_of_typ typ)

let resolve_generated_kids env typ =
  let subst_kid kid typ = subst_kid typ_subst kid (lookup_generated_kid env kid) typ in
  KidSet.fold subst_kid (generated_kids typ) typ

let rec remove_p_typ = function
  | P_aux (P_typ (typ, pat), _) -> remove_p_typ pat
  | pat -> pat

let add_p_typ typ (P_aux (paux, annot) as pat) =
  let typ' = resolve_generated_kids (env_of_pat pat) typ in
  if KidSet.is_empty (generated_kids typ') then
    P_aux (P_typ (typ', remove_p_typ pat), annot)
  else pat

let rec remove_e_cast = function
  | E_aux (E_cast (_, exp), _) -> remove_e_cast exp
  | exp -> exp

let add_e_cast typ (E_aux (eaux, annot) as exp) =
  let typ' = resolve_generated_kids (env_of exp) typ in
  if KidSet.is_empty (generated_kids typ') then
    E_aux (E_cast (typ', remove_e_cast exp), annot)
  else exp

let rec small (E_aux (exp,_)) = match exp with
  | E_id _
  | E_lit _ -> true
  | E_cast (_,e) -> small e
  | E_list es -> List.for_all small es
  | E_cons (e1,e2) -> small e1 && small e2
  | E_sizeof _ -> true
  | _ -> false

let union_eff_exps es =
  List.fold_left union_effects no_effect (List.map effect_of es)

let fun_app_effects id env =
  try
    match Env.get_val_spec id env with
    | (_, Typ_aux (Typ_fn (_,_,feff), _)) -> feff
    | _ -> no_effect
  with
  | _ -> no_effect

let fix_eff_exp (E_aux (e,((l,_) as annot))) = match destruct_tannot (snd annot) with
| Some (env, typ, eff) ->
  let effsum = match e with
    | E_block es -> union_eff_exps es
    | E_nondet es -> union_eff_exps es
    | E_id _ | E_ref _
    | E_lit _ -> eff
    | E_cast (_,e) -> effect_of e
    | E_app (f,es) ->
      union_effects (fun_app_effects f env) (union_eff_exps es)
    | E_tuple es -> union_eff_exps es
    | E_app_infix (e1,f,e2) ->
      union_effects (fun_app_effects f env) (union_eff_exps [e1;e2])
    | E_if (e1,e2,e3) -> union_eff_exps [e1;e2;e3]
    | E_for (_,e1,e2,e3,_,e4) -> union_eff_exps [e1;e2;e3;e4]
    | E_loop (_,e1,e2) -> union_eff_exps [e1;e2]
    | E_vector es -> union_eff_exps es
    | E_vector_access (e1,e2) -> union_eff_exps [e1;e2]
    | E_vector_subrange (e1,e2,e3) -> union_eff_exps [e1;e2;e3]
    | E_vector_update (e1,e2,e3) -> union_eff_exps [e1;e2;e3]
    | E_vector_update_subrange (e1,e2,e3,e4) -> union_eff_exps [e1;e2;e3;e4]
    | E_vector_append (e1,e2) -> union_eff_exps [e1;e2]
    | E_list es -> union_eff_exps es
    | E_cons (e1,e2) -> union_eff_exps [e1;e2]
    | E_record fexps -> effect_of_fexps fexps
    | E_record_update(e,fexps) ->
      union_effects (effect_of e) (effect_of_fexps fexps)
    | E_field (e,_) -> effect_of e
    | E_case (e,pexps) | E_try (e,pexps) ->
      List.fold_left union_effects (effect_of e) (List.map effect_of_pexp pexps)
    | E_let (lb,e) -> union_effects (effect_of_lb lb) (effect_of e)
    | E_assign (lexp,e) -> union_effects (effect_of_lexp lexp) (effect_of e)
    | E_exit e | E_return e | E_throw e -> union_effects eff (effect_of e)
    | E_sizeof _ | E_constraint _ -> no_effect
    | E_assert (c,m) -> union_effects eff (union_eff_exps [c; m])
    | E_var (lexp,e1,e2) ->
      union_effects (effect_of_lexp lexp)
        (union_effects (effect_of e1) (effect_of e2))
    | E_internal_plet (_,e1,e2) -> union_effects (effect_of e1) (effect_of e2)
    | E_internal_return e1 -> effect_of e1
    | E_internal_value v -> no_effect
  in
  E_aux (e, (l, mk_tannot env typ effsum))
| None ->
  E_aux (e, (l, empty_tannot))

let fix_eff_lexp (LEXP_aux (lexp,((l,_) as annot))) = match destruct_tannot (snd annot) with
| Some (env, typ, eff) ->
  let effsum = union_effects eff (match lexp with
    | LEXP_id _ -> no_effect
    | LEXP_cast _ -> no_effect
    | LEXP_deref e -> effect_of e
    | LEXP_memory (_,es) -> union_eff_exps es
    | LEXP_tup les ->
      List.fold_left (fun eff le -> union_effects eff (effect_of_lexp le)) no_effect les
    | LEXP_vector_concat les ->
      List.fold_left (fun eff le -> union_effects eff (effect_of_lexp le)) no_effect les
    | LEXP_vector (lexp,e) -> union_effects (effect_of_lexp lexp) (effect_of e)
    | LEXP_vector_range (lexp,e1,e2) ->
      union_effects (effect_of_lexp lexp)
        (union_effects (effect_of e1) (effect_of e2))
    | LEXP_field (lexp,_) -> effect_of_lexp lexp) in
  LEXP_aux (lexp, (l, mk_tannot env typ effsum))
| None ->
  LEXP_aux (lexp, (l, empty_tannot))

let fix_eff_fexp (FE_aux (fexp,((l,_) as annot))) = match destruct_tannot (snd annot) with
| Some (env, typ, eff) ->
  let effsum = union_effects eff (match fexp with
    | FE_Fexp (_,e) -> effect_of e) in
  FE_aux (fexp, (l, mk_tannot env typ effsum))
| None ->
  FE_aux (fexp, (l, empty_tannot))

let fix_eff_fexps fexps = fexps (* FES_aux have no effect information *)

let fix_eff_opt_default (Def_val_aux (opt_default,((l,_) as annot))) = match destruct_tannot (snd annot) with
| Some (env, typ, eff) ->
  let effsum = union_effects eff (match opt_default with
    | Def_val_empty -> no_effect
    | Def_val_dec e -> effect_of e) in
  Def_val_aux (opt_default, (l, mk_tannot env typ effsum))
| None ->
  Def_val_aux (opt_default, (l, empty_tannot))

let fix_eff_pexp (Pat_aux (pexp,((l,_) as annot))) = match destruct_tannot (snd annot) with
| Some (env, typ, eff) ->
  let effsum = match pexp with
    | Pat_exp (_,e) -> effect_of e
    | Pat_when (_,e,e') -> union_effects (effect_of e) (effect_of e') in
  Pat_aux (pexp, (l, mk_tannot env typ effsum))
| None ->
  Pat_aux (pexp, (l, empty_tannot))

let fix_eff_lb (LB_aux (lb,((l,_) as annot))) = match destruct_tannot (snd annot) with
| Some (env, typ, eff) ->
  let effsum = match lb with
    | LB_val (_,e) -> effect_of e in
  LB_aux (lb, (l, mk_tannot env typ effsum))
| None ->
  LB_aux (lb, (l, empty_tannot))

let rewrite_pexp rewriters =
  let rewrite = rewriters.rewrite_exp rewriters in
  function
  | (Pat_aux (Pat_exp(p, e), pannot)) ->
     Pat_aux (Pat_exp(rewriters.rewrite_pat rewriters p, rewrite e), pannot)
  | (Pat_aux (Pat_when(p, e, e'), pannot)) ->
     Pat_aux (Pat_when(rewriters.rewrite_pat rewriters p, rewrite e, rewrite e'), pannot)

let rewrite_pat rewriters (P_aux (pat,(l,annot)) as orig_pat) =
  let rewrap p = P_aux (p,(l,annot)) in
  let rewrite = rewriters.rewrite_pat rewriters in
  match pat with
  | P_lit _ | P_wild | P_id _ | P_var _ -> rewrap pat
  | P_or(pat1, pat2) -> rewrap (P_or(rewrite pat1, rewrite pat2))
  | P_not(pat) -> rewrap (P_not(rewrite pat))
  | P_as(pat,id) -> rewrap (P_as(rewrite pat, id))
  | P_typ(typ,pat) -> rewrap (P_typ(typ, rewrite pat))
  | P_app(id ,pats) -> rewrap (P_app(id, List.map rewrite pats))
  | P_record(fpats,_) ->
    rewrap (P_record(List.map (fun (FP_aux(FP_Fpat(id,pat),pannot)) -> FP_aux(FP_Fpat(id, rewrite pat), pannot)) fpats,
                     false))
  | P_vector pats -> rewrap (P_vector(List.map rewrite pats))
  | P_vector_concat pats -> rewrap (P_vector_concat (List.map rewrite pats))
  | P_tup pats -> rewrap (P_tup (List.map rewrite pats))
  | P_list pats -> rewrap (P_list (List.map rewrite pats))
  | P_cons (pat1, pat2) -> rewrap (P_cons (rewrite pat1, rewrite pat2))
  | P_string_append pats -> rewrap (P_string_append (List.map rewrite pats))

let rewrite_exp rewriters (E_aux (exp,(l,annot)) as orig_exp) =
  let rewrap e = E_aux (e,(l,annot)) in
  let rewrite = rewriters.rewrite_exp rewriters in
  match exp with
  | E_block exps -> rewrap (E_block (List.map rewrite exps))
  | E_nondet exps -> rewrap (E_nondet (List.map rewrite exps))
  | E_id _ | E_lit _  -> rewrap exp
  | E_cast (typ, exp) -> rewrap (E_cast (typ, rewrite exp))
  | E_app (id,exps) -> rewrap (E_app (id,List.map rewrite exps))
  | E_app_infix(el,id,er) -> rewrap (E_app_infix(rewrite el,id,rewrite er))
  | E_tuple exps -> rewrap (E_tuple (List.map rewrite exps))
  | E_if (c,t,e) -> rewrap (E_if (rewrite c,rewrite t, rewrite e))
  | E_for (id, e1, e2, e3, o, body) ->
    rewrap (E_for (id, rewrite e1, rewrite e2, rewrite e3, o, rewrite body))
  | E_loop (loop, e1, e2) ->
    rewrap (E_loop (loop, rewrite e1, rewrite e2))
  | E_vector exps -> rewrap (E_vector (List.map rewrite exps))
  | E_vector_access (vec,index) -> rewrap (E_vector_access (rewrite vec,rewrite index))
  | E_vector_subrange (vec,i1,i2) ->
    rewrap (E_vector_subrange (rewrite vec,rewrite i1,rewrite i2))
  | E_vector_update (vec,index,new_v) ->
    rewrap (E_vector_update (rewrite vec,rewrite index,rewrite new_v))
  | E_vector_update_subrange (vec,i1,i2,new_v) ->
    rewrap (E_vector_update_subrange (rewrite vec,rewrite i1,rewrite i2,rewrite new_v))
  | E_vector_append (v1,v2) -> rewrap (E_vector_append (rewrite v1,rewrite v2))
  | E_list exps -> rewrap (E_list (List.map rewrite exps))
  | E_cons(h,t) -> rewrap (E_cons (rewrite h,rewrite t))
  | E_record fexps ->
    rewrap (E_record
              (List.map (fun (FE_aux(FE_Fexp(id,e),fannot)) ->
                   FE_aux(FE_Fexp(id,rewrite e),fannot)) fexps))
  | E_record_update (re, fexps) ->
    rewrap (E_record_update ((rewrite re),
                             (List.map (fun (FE_aux(FE_Fexp(id,e),fannot)) ->
                                  FE_aux(FE_Fexp(id,rewrite e),fannot)) fexps)))
  | E_field(exp,id) -> rewrap (E_field(rewrite exp,id))
  | E_case (exp,pexps) ->
    rewrap (E_case (rewrite exp, List.map (rewrite_pexp rewriters) pexps))
  | E_try (exp,pexps) ->
    rewrap (E_try (rewrite exp, List.map (rewrite_pexp rewriters) pexps))
  | E_let (letbind,body) -> rewrap (E_let(rewriters.rewrite_let rewriters letbind,rewrite body))
  | E_assign (lexp,exp) -> rewrap (E_assign(rewriters.rewrite_lexp rewriters lexp,rewrite exp))
  | E_sizeof n -> rewrap (E_sizeof n)
  | E_exit e -> rewrap (E_exit (rewrite e))
  | E_throw e -> rewrap (E_throw (rewrite e))
  | E_return e -> rewrap (E_return (rewrite e))
  | E_assert(e1,e2) -> rewrap (E_assert(rewrite e1,rewrite e2))
  | E_var (lexp, e1, e2) ->
     rewrap (E_var (rewriters.rewrite_lexp rewriters lexp, rewriters.rewrite_exp rewriters e1, rewriters.rewrite_exp rewriters e2))
  | E_internal_return _ -> raise (Reporting.err_unreachable l __POS__ "Internal return found before it should have been introduced")
  | E_internal_plet _ -> raise (Reporting.err_unreachable l __POS__ " Internal plet found before it should have been introduced")
  | _ -> rewrap exp

let rewrite_let rewriters (LB_aux(letbind,(l,annot))) =
  match letbind with
  | LB_val ( pat, exp) ->
    LB_aux(LB_val (rewriters.rewrite_pat rewriters pat,
                   rewriters.rewrite_exp rewriters exp),
           (l, annot))

let rewrite_lexp rewriters (LEXP_aux(lexp,(l,annot))) =
  let rewrap le = LEXP_aux(le,(l,annot)) in
  match lexp with
  | LEXP_id _ | LEXP_cast _ -> rewrap lexp
  | LEXP_deref exp -> rewrap (LEXP_deref (rewriters.rewrite_exp rewriters exp))
  | LEXP_tup tupls -> rewrap (LEXP_tup (List.map (rewriters.rewrite_lexp rewriters) tupls))
  | LEXP_memory (id,exps) -> rewrap (LEXP_memory(id,List.map (rewriters.rewrite_exp rewriters) exps))
  | LEXP_vector (lexp,exp) ->
    rewrap (LEXP_vector (rewriters.rewrite_lexp rewriters lexp,rewriters.rewrite_exp rewriters exp))
  | LEXP_vector_range (lexp,exp1,exp2) -> 
    rewrap (LEXP_vector_range (rewriters.rewrite_lexp rewriters lexp,
                               rewriters.rewrite_exp rewriters exp1,
                               rewriters.rewrite_exp rewriters exp2))
  | LEXP_vector_concat lexps -> rewrap (LEXP_vector_concat (List.map (rewriters.rewrite_lexp rewriters) lexps))
  | LEXP_field (lexp,id) -> rewrap (LEXP_field (rewriters.rewrite_lexp rewriters lexp,id))

let rewrite_fun rewriters (FD_aux (FD_function(recopt,tannotopt,effectopt,funcls),(l,fdannot))) = 
  let rewrite_funcl (FCL_aux (FCL_Funcl(id,pexp),(l,annot))) =
    (FCL_aux (FCL_Funcl (id, rewrite_pexp rewriters pexp),(l,annot)))
  in
  let recopt = match recopt with
    | Rec_aux (Rec_nonrec, l) -> Rec_aux (Rec_nonrec, l)
    | Rec_aux (Rec_rec, l) -> Rec_aux (Rec_rec, l)
    | Rec_aux (Rec_measure (pat,exp),l) ->
       Rec_aux (Rec_measure (rewrite_pat rewriters pat, rewrite_exp rewriters exp),l)
  in
  FD_aux (FD_function(recopt,tannotopt,effectopt,List.map rewrite_funcl funcls),(l,fdannot))

let rewrite_def rewriters d = match d with
  | DEF_reg_dec (DEC_aux (DEC_config (id, typ, exp), annot)) ->
     DEF_reg_dec (DEC_aux (DEC_config (id, typ, rewriters.rewrite_exp rewriters exp), annot))
  | DEF_type _ | DEF_mapdef _ | DEF_kind _ | DEF_spec _ | DEF_default _ | DEF_reg_dec _ | DEF_overload _ | DEF_fixity _ -> d
  | DEF_fundef fdef -> DEF_fundef (rewriters.rewrite_fun rewriters fdef)
  | DEF_internal_mutrec fdefs -> DEF_internal_mutrec (List.map (rewriters.rewrite_fun rewriters) fdefs)
  | DEF_val letbind -> DEF_val (rewriters.rewrite_let rewriters letbind)
  | DEF_pragma (pragma, arg, l) -> DEF_pragma (pragma, arg, l)
  | DEF_scattered _ -> raise (Reporting.err_unreachable Parse_ast.Unknown __POS__ "DEF_scattered survived to rewritter")
  | DEF_measure (id,pat,exp) -> DEF_measure (id,rewriters.rewrite_pat rewriters pat, rewriters.rewrite_exp rewriters exp)

let rewrite_defs_base rewriters (Defs defs) =
  let rec rewrite ds = match ds with
    | [] -> []
    | d::ds -> (rewriters.rewrite_def rewriters d)::(rewrite ds) in
  Defs (rewrite defs)

let rewriters_base =
  {rewrite_exp = rewrite_exp;
   rewrite_pat = rewrite_pat;
   rewrite_let = rewrite_let;
   rewrite_lexp = rewrite_lexp;
   rewrite_fun = rewrite_fun;
   rewrite_def = rewrite_def;
   rewrite_defs = rewrite_defs_base}

let rewrite_defs (Defs defs) = rewrite_defs_base rewriters_base (Defs defs)

module Envmap = Finite_map.Fmap_map(String)

(* TODO: This seems to only consider a single assignment (or possibly two, in
   separate branches of an if-expression). Hence, it seems the result is always
   at most one variable. Is this intended?
   It is only used below when pulling out local variables inside if-expressions
   into the outer scope, which seems dubious. I comment it out for now. *)
(*let rec introduced_variables (E_aux (exp,(l,annot))) =
  match exp with
  | E_cast (typ, exp) -> introduced_variables exp
  | E_if (c,t,e) -> Envmap.intersect (introduced_variables t) (introduced_variables e)
  | E_assign (lexp,exp) -> introduced_vars_le lexp exp
  | _ -> Envmap.empty

and introduced_vars_le (LEXP_aux(lexp,annot)) exp =
  match lexp with
  | LEXP_id (Id_aux (Id id,_))  | LEXP_cast(_,(Id_aux (Id id,_))) ->
    (match annot with
     | Base((_,t),Emp_intro,_,_,_,_) ->
       Envmap.insert Envmap.empty (id,(t,exp))
     | _ -> Envmap.empty)
  | _ -> Envmap.empty*)

type ('a,'pat,'pat_aux,'fpat,'fpat_aux) pat_alg =
  { p_lit            : lit -> 'pat_aux
  ; p_wild           : 'pat_aux
  ; p_or             : 'pat * 'pat -> 'pat_aux
  ; p_not            : 'pat        -> 'pat_aux
  ; p_as             : 'pat * id -> 'pat_aux
  ; p_typ            : Ast.typ * 'pat -> 'pat_aux
  ; p_id             : id -> 'pat_aux
  ; p_var            : 'pat * typ_pat -> 'pat_aux
  ; p_app            : id * 'pat list -> 'pat_aux
  ; p_record         : 'fpat list * bool -> 'pat_aux
  ; p_vector         : 'pat list -> 'pat_aux
  ; p_vector_concat  : 'pat list -> 'pat_aux
  ; p_tup            : 'pat list -> 'pat_aux
  ; p_list           : 'pat list -> 'pat_aux
  ; p_cons           : 'pat * 'pat -> 'pat_aux
  ; p_string_append  : 'pat list -> 'pat_aux
  ; p_aux            : 'pat_aux * 'a annot -> 'pat
  ; fP_aux           : 'fpat_aux * 'a annot -> 'fpat
  ; fP_Fpat          : id * 'pat -> 'fpat_aux
  }

let rec fold_pat_aux (alg : ('a,'pat,'pat_aux,'fpat,'fpat_aux) pat_alg) : 'a pat_aux -> 'pat_aux =
  function
  | P_lit lit           -> alg.p_lit lit
  | P_wild              -> alg.p_wild
  | P_or(p1, p2)        -> alg.p_or (fold_pat alg p1, fold_pat alg p2)
  | P_not(p)            -> alg.p_not (fold_pat alg p)
  | P_id id             -> alg.p_id id
  | P_var (p,tpat)      -> alg.p_var (fold_pat alg p, tpat)
  | P_as (p,id)         -> alg.p_as (fold_pat alg p, id)
  | P_typ (typ,p)       -> alg.p_typ (typ,fold_pat alg p)
  | P_app (id,ps)       -> alg.p_app (id,List.map (fold_pat alg) ps)
  | P_record (ps,b)     -> alg.p_record (List.map (fold_fpat alg) ps, b)
  | P_vector ps         -> alg.p_vector (List.map (fold_pat alg) ps)
  | P_vector_concat ps  -> alg.p_vector_concat (List.map (fold_pat alg) ps)
  | P_tup ps            -> alg.p_tup (List.map (fold_pat alg) ps)
  | P_list ps           -> alg.p_list (List.map (fold_pat alg) ps)
  | P_cons (ph,pt)      -> alg.p_cons (fold_pat alg ph, fold_pat alg pt)
  | P_string_append ps  -> alg.p_string_append (List.map (fold_pat alg) ps)

and fold_pat (alg : ('a,'pat,'pat_aux,'fpat,'fpat_aux) pat_alg) : 'a pat -> 'pat =
  function
  | P_aux (pat,annot)   -> alg.p_aux (fold_pat_aux alg pat,annot)
and fold_fpat_aux (alg : ('a,'pat,'pat_aux,'fpat,'fpat_aux) pat_alg) : 'a fpat_aux -> 'fpat_aux =
  function
  | FP_Fpat (id,pat)    -> alg.fP_Fpat (id,fold_pat alg pat)
and fold_fpat (alg : ('a,'pat,'pat_aux,'fpat,'fpat_aux) pat_alg) : 'a fpat -> 'fpat =
  function
  | FP_aux (fpat,annot) -> alg.fP_aux (fold_fpat_aux alg fpat,annot)

(* identity fold from term alg to term alg *)
let id_pat_alg : ('a,'a pat, 'a pat_aux, 'a fpat, 'a fpat_aux) pat_alg =
  { p_lit            = (fun lit -> P_lit lit)
  ; p_wild           = P_wild
  ; p_or             = (fun (pat1, pat2) -> P_or(pat1, pat2))
  ; p_not            = (fun pat -> P_not(pat))
  ; p_as             = (fun (pat,id) -> P_as (pat,id))
  ; p_typ            = (fun (typ,pat) -> P_typ (typ,pat))
  ; p_id             = (fun id -> P_id id)
  ; p_var            = (fun (pat,tpat) -> P_var (pat,tpat))
  ; p_app            = (fun (id,ps) -> P_app (id,ps))
  ; p_record         = (fun (ps,b) -> P_record (ps,b))
  ; p_vector         = (fun ps -> P_vector ps)
  ; p_vector_concat  = (fun ps -> P_vector_concat ps)
  ; p_tup            = (fun ps -> P_tup ps)
  ; p_list           = (fun ps -> P_list ps)
  ; p_cons           = (fun (ph,pt) -> P_cons (ph,pt))
  ; p_string_append  = (fun (ps) -> P_string_append (ps))
  ; p_aux            = (fun (pat,annot) -> P_aux (pat,annot))
  ; fP_aux           = (fun (fpat,annot) -> FP_aux (fpat,annot))
  ; fP_Fpat          = (fun (id,pat) -> FP_Fpat (id,pat))
  }

type ('a,'exp,'exp_aux,'lexp,'lexp_aux,'fexp,'fexp_aux,
      'opt_default_aux,'opt_default,'pexp,'pexp_aux,'letbind_aux,'letbind,
      'pat,'pat_aux,'fpat,'fpat_aux) exp_alg =
  { e_block                  : 'exp list -> 'exp_aux
  ; e_nondet                 : 'exp list -> 'exp_aux
  ; e_id                     : id -> 'exp_aux
  ; e_ref                    : id -> 'exp_aux
  ; e_lit                    : lit -> 'exp_aux
  ; e_cast                   : Ast.typ * 'exp -> 'exp_aux
  ; e_app                    : id * 'exp list -> 'exp_aux
  ; e_app_infix              : 'exp * id * 'exp -> 'exp_aux
  ; e_tuple                  : 'exp list -> 'exp_aux
  ; e_if                     : 'exp * 'exp * 'exp -> 'exp_aux
  ; e_for                    : id * 'exp * 'exp * 'exp * Ast.order * 'exp -> 'exp_aux
  ; e_loop                   : loop * 'exp * 'exp -> 'exp_aux
  ; e_vector                 : 'exp list -> 'exp_aux
  ; e_vector_access          : 'exp * 'exp -> 'exp_aux
  ; e_vector_subrange        : 'exp * 'exp * 'exp -> 'exp_aux
  ; e_vector_update          : 'exp * 'exp * 'exp -> 'exp_aux
  ; e_vector_update_subrange : 'exp * 'exp * 'exp * 'exp -> 'exp_aux
  ; e_vector_append          : 'exp * 'exp -> 'exp_aux
  ; e_list                   : 'exp list -> 'exp_aux
  ; e_cons                   : 'exp * 'exp -> 'exp_aux
  ; e_record                 : 'fexp list -> 'exp_aux
  ; e_record_update          : 'exp * 'fexp list -> 'exp_aux
  ; e_field                  : 'exp * id -> 'exp_aux
  ; e_case                   : 'exp * 'pexp list -> 'exp_aux
  ; e_try                    : 'exp * 'pexp list -> 'exp_aux
  ; e_let                    : 'letbind * 'exp -> 'exp_aux
  ; e_assign                 : 'lexp * 'exp -> 'exp_aux
  ; e_sizeof                 : nexp -> 'exp_aux
  ; e_constraint             : n_constraint -> 'exp_aux
  ; e_exit                   : 'exp -> 'exp_aux
  ; e_throw                  : 'exp -> 'exp_aux
  ; e_return                 : 'exp -> 'exp_aux
  ; e_assert                 : 'exp * 'exp -> 'exp_aux
  ; e_var           : 'lexp * 'exp * 'exp -> 'exp_aux
  ; e_internal_plet          : 'pat * 'exp * 'exp -> 'exp_aux
  ; e_internal_return        : 'exp -> 'exp_aux
  ; e_internal_value         : Value.value -> 'exp_aux
  ; e_aux                    : 'exp_aux * 'a annot -> 'exp
  ; lEXP_id                  : id -> 'lexp_aux
  ; lEXP_deref               : 'exp -> 'lexp_aux
  ; lEXP_memory              : id * 'exp list -> 'lexp_aux
  ; lEXP_cast                : Ast.typ * id -> 'lexp_aux
  ; lEXP_tup                 : 'lexp list -> 'lexp_aux
  ; lEXP_vector              : 'lexp * 'exp -> 'lexp_aux
  ; lEXP_vector_range        : 'lexp * 'exp * 'exp -> 'lexp_aux
  ; lEXP_vector_concat       : 'lexp list -> 'lexp_aux
  ; lEXP_field               : 'lexp * id -> 'lexp_aux
  ; lEXP_aux                 : 'lexp_aux * 'a annot -> 'lexp
  ; fE_Fexp                  : id * 'exp -> 'fexp_aux
  ; fE_aux                   : 'fexp_aux * 'a annot -> 'fexp
  ; def_val_empty            : 'opt_default_aux
  ; def_val_dec              : 'exp -> 'opt_default_aux
  ; def_val_aux              : 'opt_default_aux * 'a annot -> 'opt_default
  ; pat_exp                  : 'pat * 'exp -> 'pexp_aux
  ; pat_when                 : 'pat * 'exp * 'exp -> 'pexp_aux
  ; pat_aux                  : 'pexp_aux * 'a annot -> 'pexp
  ; lB_val                   : 'pat * 'exp -> 'letbind_aux
  ; lB_aux                   : 'letbind_aux * 'a annot -> 'letbind
  ; pat_alg                  : ('a,'pat,'pat_aux,'fpat,'fpat_aux) pat_alg
  }

let rec fold_exp_aux alg = function
  | E_block es -> alg.e_block (List.map (fold_exp alg) es)
  | E_nondet es -> alg.e_nondet (List.map (fold_exp alg) es)
  | E_id id -> alg.e_id id
  | E_ref id -> alg.e_ref id
  | E_lit lit -> alg.e_lit lit
  | E_cast (typ,e) -> alg.e_cast (typ, fold_exp alg e)
  | E_app (id,es) -> alg.e_app (id, List.map (fold_exp alg) es)
  | E_app_infix (e1,id,e2) -> alg.e_app_infix (fold_exp alg e1, id, fold_exp alg e2)
  | E_tuple es -> alg.e_tuple (List.map (fold_exp alg) es)
  | E_if (e1,e2,e3) -> alg.e_if (fold_exp alg e1, fold_exp alg e2, fold_exp alg e3)
  | E_for (id,e1,e2,e3,order,e4) ->
     alg.e_for (id,fold_exp alg e1, fold_exp alg e2, fold_exp alg e3, order, fold_exp alg e4)
  | E_loop (loop_type, e1, e2) ->
     alg.e_loop (loop_type, fold_exp alg e1, fold_exp alg e2)
  | E_vector es -> alg.e_vector (List.map (fold_exp alg) es)
  | E_vector_access (e1,e2) -> alg.e_vector_access (fold_exp alg e1, fold_exp alg e2)
  | E_vector_subrange (e1,e2,e3) ->
     alg.e_vector_subrange (fold_exp alg e1, fold_exp alg e2, fold_exp alg e3)
  | E_vector_update (e1,e2,e3) ->
     alg.e_vector_update (fold_exp alg e1, fold_exp alg e2, fold_exp alg e3)
  | E_vector_update_subrange (e1,e2,e3,e4) ->
     alg.e_vector_update_subrange (fold_exp alg e1,fold_exp alg e2, fold_exp alg e3, fold_exp alg e4)
  | E_vector_append (e1,e2) -> alg.e_vector_append (fold_exp alg e1, fold_exp alg e2)
  | E_list es -> alg.e_list (List.map (fold_exp alg) es)
  | E_cons (e1,e2) -> alg.e_cons (fold_exp alg e1, fold_exp alg e2)
  | E_record fexps -> alg.e_record (List.map (fold_fexp alg) fexps)
  | E_record_update (e,fexps) -> alg.e_record_update (fold_exp alg e, List.map (fold_fexp alg) fexps)
  | E_field (e,id) -> alg.e_field (fold_exp alg e, id)
  | E_case (e,pexps) -> alg.e_case (fold_exp alg e, List.map (fold_pexp alg) pexps)
  | E_try (e,pexps) -> alg.e_try (fold_exp alg e, List.map (fold_pexp alg) pexps)
  | E_let (letbind,e) -> alg.e_let (fold_letbind alg letbind, fold_exp alg e)
  | E_assign (lexp,e) -> alg.e_assign (fold_lexp alg lexp, fold_exp alg e)
  | E_sizeof nexp -> alg.e_sizeof nexp
  | E_constraint nc -> alg.e_constraint nc
  | E_exit e -> alg.e_exit (fold_exp alg e)
  | E_throw e -> alg.e_throw (fold_exp alg e)
  | E_return e -> alg.e_return (fold_exp alg e)
  | E_assert(e1,e2) -> alg.e_assert (fold_exp alg e1, fold_exp alg e2)
  | E_var (lexp,e1,e2) ->
     alg.e_var (fold_lexp alg lexp, fold_exp alg e1, fold_exp alg e2)
  | E_internal_plet (pat,e1,e2) ->
     alg.e_internal_plet (fold_pat alg.pat_alg pat, fold_exp alg e1, fold_exp alg e2)
  | E_internal_return e -> alg.e_internal_return (fold_exp alg e)
  | E_internal_value v -> alg.e_internal_value v
and fold_exp alg (E_aux (exp_aux,annot)) = alg.e_aux (fold_exp_aux alg exp_aux, annot)
and fold_lexp_aux alg = function
  | LEXP_id id -> alg.lEXP_id id
  | LEXP_deref exp -> alg.lEXP_deref (fold_exp alg exp)
  | LEXP_memory (id,es) -> alg.lEXP_memory (id, List.map (fold_exp alg) es)
  | LEXP_tup les -> alg.lEXP_tup (List.map (fold_lexp alg) les)
  | LEXP_cast (typ,id) -> alg.lEXP_cast (typ,id)
  | LEXP_vector (lexp,e) -> alg.lEXP_vector (fold_lexp alg lexp, fold_exp alg e)
  | LEXP_vector_range (lexp,e1,e2) ->
     alg.lEXP_vector_range (fold_lexp alg lexp, fold_exp alg e1, fold_exp alg e2)
  | LEXP_vector_concat les -> alg.lEXP_vector_concat (List.map (fold_lexp alg) les)
  | LEXP_field (lexp,id) -> alg.lEXP_field (fold_lexp alg lexp, id)
and fold_lexp alg (LEXP_aux (lexp_aux,annot)) =
  alg.lEXP_aux (fold_lexp_aux alg lexp_aux, annot)
and fold_fexp_aux alg (FE_Fexp (id,e)) = alg.fE_Fexp (id, fold_exp alg e)
and fold_fexp alg (FE_aux (fexp_aux,annot)) = alg.fE_aux (fold_fexp_aux alg fexp_aux,annot)
and fold_opt_default_aux alg = function
  | Def_val_empty -> alg.def_val_empty
  | Def_val_dec e -> alg.def_val_dec (fold_exp alg e)
and fold_opt_default alg (Def_val_aux (opt_default_aux,annot)) =
  alg.def_val_aux (fold_opt_default_aux alg opt_default_aux, annot)
and fold_pexp_aux alg = function
  | Pat_exp (pat,e) -> alg.pat_exp (fold_pat alg.pat_alg pat, fold_exp alg e)
  | Pat_when (pat,e,e') -> alg.pat_when (fold_pat alg.pat_alg pat, fold_exp alg e, fold_exp alg e')
and fold_pexp alg (Pat_aux (pexp_aux,annot)) = alg.pat_aux (fold_pexp_aux alg pexp_aux, annot)
and fold_letbind_aux alg = function
  | LB_val (pat,e) -> alg.lB_val (fold_pat alg.pat_alg pat, fold_exp alg e)
and fold_letbind alg (LB_aux (letbind_aux,annot)) = alg.lB_aux (fold_letbind_aux alg letbind_aux, annot)

let fold_funcl alg (FCL_aux (FCL_Funcl (id, pexp), annot)) =
  FCL_aux (FCL_Funcl (id, fold_pexp alg pexp), annot)

let fold_function alg (FD_aux (FD_function (rec_opt, tannot_opt, effect_opt, funcls), annot)) =
  FD_aux (FD_function (rec_opt, tannot_opt, effect_opt, List.map (fold_funcl alg) funcls), annot)

let id_exp_alg =
  { e_block = (fun es -> E_block es)
  ; e_nondet = (fun es -> E_nondet es)
  ; e_id = (fun id -> E_id id)
  ; e_ref = (fun id -> E_ref id)
  ; e_lit = (fun lit -> (E_lit lit))
  ; e_cast = (fun (typ,e) -> E_cast (typ,e))
  ; e_app = (fun (id,es) -> E_app (id,es))
  ; e_app_infix = (fun (e1,id,e2) -> E_app_infix (e1,id,e2))
  ; e_tuple = (fun es -> E_tuple es)
  ; e_if = (fun (e1,e2,e3) -> E_if (e1,e2,e3))
  ; e_for = (fun (id,e1,e2,e3,order,e4) -> E_for (id,e1,e2,e3,order,e4))
  ; e_loop = (fun (lt, e1, e2) -> E_loop (lt, e1, e2))
  ; e_vector = (fun es -> E_vector es)
  ; e_vector_access = (fun (e1,e2) -> E_vector_access (e1,e2))
  ; e_vector_subrange =  (fun (e1,e2,e3) -> E_vector_subrange (e1,e2,e3))
  ; e_vector_update = (fun (e1,e2,e3) -> E_vector_update (e1,e2,e3))
  ; e_vector_update_subrange =  (fun (e1,e2,e3,e4) -> E_vector_update_subrange (e1,e2,e3,e4))
  ; e_vector_append = (fun (e1,e2) -> E_vector_append (e1,e2))
  ; e_list = (fun es -> E_list es)
  ; e_cons = (fun (e1,e2) -> E_cons (e1,e2))
  ; e_record = (fun fexps -> E_record fexps)
  ; e_record_update = (fun (e1,fexp) -> E_record_update (e1,fexp))
  ; e_field = (fun (e1,id) -> (E_field (e1,id)))
  ; e_case = (fun (e1,pexps) -> E_case (e1,pexps))
  ; e_try = (fun (e1,pexps) -> E_try (e1,pexps))
  ; e_let = (fun (lb,e2) -> E_let (lb,e2))
  ; e_assign = (fun (lexp,e2) -> E_assign (lexp,e2))
  ; e_sizeof = (fun nexp -> E_sizeof nexp)
  ; e_constraint = (fun nc -> E_constraint nc)
  ; e_exit = (fun e1 -> E_exit (e1))
  ; e_throw = (fun e1 -> E_throw (e1))
  ; e_return = (fun e1 -> E_return e1)
  ; e_assert = (fun (e1,e2) -> E_assert(e1,e2)) 
  ; e_var = (fun (lexp, e2, e3) -> E_var (lexp,e2,e3))
  ; e_internal_plet = (fun (pat, e1, e2) -> E_internal_plet (pat,e1,e2))
  ; e_internal_return = (fun e -> E_internal_return e)
  ; e_internal_value = (fun v -> E_internal_value v)
  ; e_aux = (fun (e,annot) -> E_aux (e,annot))
  ; lEXP_id = (fun id -> LEXP_id id)
  ; lEXP_deref = (fun e -> LEXP_deref e)
  ; lEXP_memory = (fun (id,es) -> LEXP_memory (id,es))
  ; lEXP_cast = (fun (typ,id) -> LEXP_cast (typ,id))
  ; lEXP_tup = (fun tups -> LEXP_tup tups)
  ; lEXP_vector = (fun (lexp,e2) -> LEXP_vector (lexp,e2))
  ; lEXP_vector_range = (fun (lexp,e2,e3) -> LEXP_vector_range (lexp,e2,e3))
  ; lEXP_vector_concat = (fun lexps -> LEXP_vector_concat lexps)
  ; lEXP_field = (fun (lexp,id) -> LEXP_field (lexp,id))
  ; lEXP_aux = (fun (lexp,annot) -> LEXP_aux (lexp,annot))
  ; fE_Fexp = (fun (id,e) -> FE_Fexp (id,e))
  ; fE_aux = (fun (fexp,annot) -> FE_aux (fexp,annot))
  ; def_val_empty = Def_val_empty
  ; def_val_dec = (fun e -> Def_val_dec e)
  ; def_val_aux = (fun (defval,aux) -> Def_val_aux (defval,aux))
  ; pat_exp = (fun (pat,e) -> (Pat_exp (pat,e)))
  ; pat_when = (fun (pat,e,e') -> (Pat_when (pat,e,e')))
  ; pat_aux = (fun (pexp,a) -> (Pat_aux (pexp,a)))
  ; lB_val = (fun (pat,e) -> LB_val (pat,e))
  ; lB_aux = (fun (lb,annot) -> LB_aux (lb,annot))
  ; pat_alg = id_pat_alg
  }

(* Folding algorithms for not only rewriting patterns/expressions, but also
   computing some additional value. Usage: Pass default value (bot) and a
   binary join operator as arguments, and specify the non-default cases of
   rewriting/computation by overwriting fields of the record.
   See rewrite_sizeof for examples. *)
let compute_pat_alg bot join =
  let join_list vs = List.fold_left join bot vs in
  let split_join f ps = let (vs,ps) = List.split ps in (join_list vs, f ps) in
  { p_lit            = (fun lit -> (bot, P_lit lit))
  ; p_wild           = (bot, P_wild)
  (* todo: I have no idea how to combine v1 and v2 in the following *)
  ; p_or             = (fun ((v1, pat1), (v2, pat2)) -> (v1, P_or(pat1, pat2)))
  ; p_not            = (fun (v, pat) -> (v, P_not(pat)))
  ; p_as             = (fun ((v,pat),id) -> (v, P_as (pat,id)))
  ; p_typ            = (fun (typ,(v,pat)) -> (v, P_typ (typ,pat)))
  ; p_id             = (fun id -> (bot, P_id id))
  ; p_var            = (fun ((v,pat),kid) -> (v, P_var (pat,kid)))
  ; p_app            = (fun (id,ps) -> split_join (fun ps -> P_app (id,ps)) ps)
  ; p_record         = (fun (ps,b) -> split_join (fun ps -> P_record (ps,b)) ps)
  ; p_vector         = split_join (fun ps -> P_vector ps)
  ; p_vector_concat  = split_join (fun ps -> P_vector_concat ps)
  ; p_tup            = split_join (fun ps -> P_tup ps)
  ; p_list           = split_join (fun ps -> P_list ps)
  ; p_cons           = (fun ((vh,ph),(vt,pt)) -> (join vh vt, P_cons (ph,pt)))
  ; p_string_append  = split_join (fun ps -> P_string_append ps)
  ; p_aux            = (fun ((v,pat),annot) -> (v, P_aux (pat,annot)))
  ; fP_aux           = (fun ((v,fpat),annot) -> (v, FP_aux (fpat,annot)))
  ; fP_Fpat          = (fun (id,(v,pat)) -> (v, FP_Fpat (id,pat)))
  }

let compute_exp_alg bot join =
  let join_list vs = List.fold_left join bot vs in
  let split_join f es = let (vs,es) = List.split es in (join_list vs, f es) in
  { e_block = split_join (fun es -> E_block es)
  ; e_nondet = split_join (fun es -> E_nondet es)
  ; e_id = (fun id -> (bot, E_id id))
  ; e_ref = (fun id -> (bot, E_ref id))
  ; e_lit = (fun lit -> (bot, E_lit lit))
  ; e_cast = (fun (typ,(v,e)) -> (v, E_cast (typ,e)))
  ; e_app = (fun (id,es) -> split_join (fun es -> E_app (id,es)) es)
  ; e_app_infix = (fun ((v1,e1),id,(v2,e2)) -> (join v1 v2, E_app_infix (e1,id,e2)))
  ; e_tuple = split_join (fun es -> E_tuple es)
  ; e_if = (fun ((v1,e1),(v2,e2),(v3,e3)) -> (join_list [v1;v2;v3], E_if (e1,e2,e3)))
  ; e_for = (fun (id,(v1,e1),(v2,e2),(v3,e3),order,(v4,e4)) ->
    (join_list [v1;v2;v3;v4], E_for (id,e1,e2,e3,order,e4)))
  ; e_loop = (fun (lt, (v1, e1), (v2, e2)) ->
    (join_list [v1;v2], E_loop (lt, e1, e2)))
  ; e_vector = split_join (fun es -> E_vector es)
  ; e_vector_access = (fun ((v1,e1),(v2,e2)) -> (join v1 v2, E_vector_access (e1,e2)))
  ; e_vector_subrange =  (fun ((v1,e1),(v2,e2),(v3,e3)) -> (join_list [v1;v2;v3], E_vector_subrange (e1,e2,e3)))
  ; e_vector_update = (fun ((v1,e1),(v2,e2),(v3,e3)) -> (join_list [v1;v2;v3], E_vector_update (e1,e2,e3)))
  ; e_vector_update_subrange =  (fun ((v1,e1),(v2,e2),(v3,e3),(v4,e4)) -> (join_list [v1;v2;v3;v4], E_vector_update_subrange (e1,e2,e3,e4)))
  ; e_vector_append = (fun ((v1,e1),(v2,e2)) -> (join v1 v2, E_vector_append (e1,e2)))
  ; e_list = split_join (fun es -> E_list es)
  ; e_cons = (fun ((v1,e1),(v2,e2)) -> (join v1 v2, E_cons (e1,e2)))
  ; e_record = (fun fexps ->
    let vs, fexps = List.split fexps in
    (join_list vs, E_record fexps))
  ; e_record_update = (fun ((v1,e1),fexps) ->
    let (vps,fexps) = List.split fexps in
    (join_list (v1::vps), E_record_update (e1,fexps)))
  ; e_field = (fun ((v1,e1),id) -> (v1, E_field (e1,id)))
  ; e_case = (fun ((v1,e1),pexps) ->
    let (vps,pexps) = List.split pexps in
    (join_list (v1::vps), E_case (e1,pexps)))
  ; e_try = (fun ((v1,e1),pexps) ->
    let (vps,pexps) = List.split pexps in
    (join_list (v1::vps), E_try (e1,pexps)))
  ; e_let = (fun ((vl,lb),(v2,e2)) -> (join vl v2, E_let (lb,e2)))
  ; e_assign = (fun ((vl,lexp),(v2,e2)) -> (join vl v2, E_assign (lexp,e2)))
  ; e_sizeof = (fun nexp -> (bot, E_sizeof nexp))
  ; e_constraint = (fun nc -> (bot, E_constraint nc))
  ; e_exit = (fun (v1,e1) -> (v1, E_exit (e1)))
  ; e_throw = (fun (v1,e1) -> (v1, E_throw (e1)))
  ; e_return = (fun (v1,e1) -> (v1, E_return e1))
  ; e_assert = (fun ((v1,e1),(v2,e2)) -> (join v1 v2, E_assert(e1,e2)) )
  ; e_var = (fun ((vl, lexp), (v2,e2), (v3,e3)) ->
    (join_list [vl;v2;v3], E_var (lexp,e2,e3)))
  ; e_internal_plet = (fun ((vp,pat), (v1,e1), (v2,e2)) ->
    (join_list [vp;v1;v2], E_internal_plet (pat,e1,e2)))
  ; e_internal_return = (fun (v,e) -> (v, E_internal_return e))
  ; e_internal_value = (fun v -> (bot, E_internal_value v))
  ; e_aux = (fun ((v,e),annot) -> (v, E_aux (e,annot)))
  ; lEXP_id = (fun id -> (bot, LEXP_id id))
  ; lEXP_deref = (fun (v, e) -> (v, LEXP_deref e))
  ; lEXP_memory = (fun (id,es) -> split_join (fun es -> LEXP_memory (id,es)) es)
  ; lEXP_cast = (fun (typ,id) -> (bot, LEXP_cast (typ,id)))
  ; lEXP_tup = (fun ls ->
    let (vs,ls) = List.split ls in
    (join_list vs, LEXP_tup ls))
  ; lEXP_vector = (fun ((vl,lexp),(v2,e2)) -> (join vl v2, LEXP_vector (lexp,e2)))
  ; lEXP_vector_range = (fun ((vl,lexp),(v2,e2),(v3,e3)) ->
    (join_list [vl;v2;v3], LEXP_vector_range (lexp,e2,e3)))
  ; lEXP_vector_concat = (fun ls ->
    let (vs,ls) = List.split ls in
    (join_list vs, LEXP_vector_concat ls))
  ; lEXP_field = (fun ((vl,lexp),id) -> (vl, LEXP_field (lexp,id)))
  ; lEXP_aux = (fun ((vl,lexp),annot) -> (vl, LEXP_aux (lexp,annot)))
  ; fE_Fexp = (fun (id,(v,e)) -> (v, FE_Fexp (id,e)))
  ; fE_aux = (fun ((vf,fexp),annot) -> (vf, FE_aux (fexp,annot)))
  ; def_val_empty = (bot, Def_val_empty)
  ; def_val_dec = (fun (v,e) -> (v, Def_val_dec e))
  ; def_val_aux = (fun ((v,defval),aux) -> (v, Def_val_aux (defval,aux)))
  ; pat_exp = (fun ((vp,pat),(v,e)) -> (join vp v, Pat_exp (pat,e)))
  ; pat_when = (fun ((vp,pat),(v,e),(v',e')) -> (join_list [vp;v;v'], Pat_when (pat,e,e')))
  ; pat_aux = (fun ((v,pexp),a) -> (v, Pat_aux (pexp,a)))
  ; lB_val = (fun ((vp,pat),(v,e)) -> (join vp v, LB_val (pat,e)))
  ; lB_aux = (fun ((vl,lb),annot) -> (vl,LB_aux (lb,annot)))
  ; pat_alg = compute_pat_alg bot join
  }

let pure_pat_alg bot join =
  let join_list vs = List.fold_left join bot vs in
  { p_lit            = (fun lit -> bot)
  ; p_wild           = bot
  ; p_or             = (fun (pat1, pat2) -> bot) (* todo: this is wrong *)
  ; p_not            = (fun pat -> bot)          (* todo: this is wrong *)
  ; p_as             = (fun (v,id) -> v)
  ; p_typ            = (fun (typ,v) -> v)
  ; p_id             = (fun id -> bot)
  ; p_var            = (fun (v,kid) -> v)
  ; p_app            = (fun (id,ps) -> join_list ps)
  ; p_record         = (fun (ps,b) -> join_list ps)
  ; p_vector         = join_list
  ; p_vector_concat  = join_list
  ; p_tup            = join_list
  ; p_list           = join_list
  ; p_string_append  = join_list
  ; p_cons           = (fun (vh,vt) -> join vh vt)
  ; p_aux            = (fun (v,annot) -> v)
  ; fP_aux           = (fun (v,annot) -> v)
  ; fP_Fpat          = (fun (id,v) -> v)
  }

let pure_exp_alg bot join =
  let join_list vs = List.fold_left join bot vs in
  { e_block = join_list
  ; e_nondet = join_list
  ; e_id = (fun id -> bot)
  ; e_ref = (fun id -> bot)
  ; e_lit = (fun lit -> bot)
  ; e_cast = (fun (typ,v) -> v)
  ; e_app = (fun (id,es) -> join_list es)
  ; e_app_infix = (fun (v1,id,v2) -> join v1 v2)
  ; e_tuple = join_list
  ; e_if = (fun (v1,v2,v3) -> join_list [v1;v2;v3])
  ; e_for = (fun (id,v1,v2,v3,order,v4) -> join_list [v1;v2;v3;v4])
  ; e_loop = (fun (lt, v1, v2) -> join v1 v2)
  ; e_vector = join_list
  ; e_vector_access = (fun (v1,v2) -> join v1 v2)
  ; e_vector_subrange =  (fun (v1,v2,v3) -> join_list [v1;v2;v3])
  ; e_vector_update = (fun (v1,v2,v3) -> join_list [v1;v2;v3])
  ; e_vector_update_subrange =  (fun (v1,v2,v3,v4) -> join_list [v1;v2;v3;v4])
  ; e_vector_append = (fun (v1,v2) -> join v1 v2)
  ; e_list = join_list
  ; e_cons = (fun (v1,v2) -> join v1 v2)
  ; e_record = (fun vs -> join_list vs)
  ; e_record_update = (fun (v1,vf) -> join_list (v1::vf))
  ; e_field = (fun (v1,id) -> v1)
  ; e_case = (fun (v1,vps) -> join_list (v1::vps))
  ; e_try = (fun (v1,vps) -> join_list (v1::vps))
  ; e_let = (fun (vl,v2) -> join vl v2)
  ; e_assign = (fun (vl,v2) -> join vl v2)
  ; e_sizeof = (fun nexp -> bot)
  ; e_constraint = (fun nc -> bot)
  ; e_exit = (fun v1 -> v1)
  ; e_throw = (fun v1 -> v1)
  ; e_return = (fun v1 -> v1)
  ; e_assert = (fun (v1,v2) -> join v1 v2)
  ; e_var = (fun (vl, v2, v3) -> join_list [vl;v2;v3])
  ; e_internal_plet = (fun (vp, v1, v2) -> join_list [vp;v1;v2])
  ; e_internal_return = (fun v -> v)
  ; e_internal_value = (fun v -> bot)
  ; e_aux = (fun (v,annot) -> v)
  ; lEXP_id = (fun id -> bot)
  ; lEXP_deref = (fun v -> v)
  ; lEXP_memory = (fun (id,es) -> join_list es)
  ; lEXP_cast = (fun (typ,id) -> bot)
  ; lEXP_tup = join_list
  ; lEXP_vector = (fun (vl,v2) -> join vl v2)
  ; lEXP_vector_range = (fun (vl,v2,v3) -> join_list [vl;v2;v3])
  ; lEXP_vector_concat = join_list
  ; lEXP_field = (fun (vl,id) -> vl)
  ; lEXP_aux = (fun (vl,annot) -> vl)
  ; fE_Fexp = (fun (id,v) -> v)
  ; fE_aux = (fun (vf,annot) -> vf)
  ; def_val_empty = bot
  ; def_val_dec = (fun v -> v)
  ; def_val_aux = (fun (v,aux) -> v)
  ; pat_exp = (fun (vp,v) -> join vp v)
  ; pat_when = (fun (vp,v,v') -> join_list [vp;v;v'])
  ; pat_aux = (fun (v,a) -> v)
  ; lB_val = (fun (vp,v) -> join vp v)
  ; lB_aux = (fun (vl,annot) -> vl)
  ; pat_alg = pure_pat_alg bot join
  }
