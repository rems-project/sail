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
open Ast
open Ast_defs
open Ast_util
open Type_check

type 'a rewriters = {
  rewrite_exp : 'a rewriters -> 'a exp -> 'a exp;
  rewrite_lexp : 'a rewriters -> 'a lexp -> 'a lexp;
  rewrite_pat : 'a rewriters -> 'a pat -> 'a pat;
  rewrite_let : 'a rewriters -> 'a letbind -> 'a letbind;
  rewrite_fun : 'a rewriters -> 'a fundef -> 'a fundef;
  rewrite_def : 'a rewriters -> 'a def -> 'a def;
  rewrite_ast : 'a rewriters -> 'a ast -> 'a ast;
}

let lookup_generated_kid env kid =
  let match_kid_nc kid = function
    | NC_aux (NC_equal (Nexp_aux (Nexp_var kid1, _), Nexp_aux (Nexp_var kid2, _)), _)
      when Kid.compare kid kid2 = 0 && not (is_kid_generated kid1) ->
        kid1
    | _ -> kid
  in
  List.fold_left match_kid_nc kid (Env.get_constraints env)

let generated_kids typ = KidSet.filter is_kid_generated (tyvars_of_typ typ)

let rec is_src_typ typ =
  match typ with
  | Typ_aux (Typ_tuple typs, l) -> List.for_all is_src_typ typs
  | _ -> (
      match destruct_exist typ with
      | Some (kopts, nc, typ') ->
          let declared_kids = KidSet.of_list (List.map kopt_kid kopts) in
          let unused_kids = KidSet.diff declared_kids (tyvars_of_typ typ') in
          KidSet.is_empty unused_kids && KidSet.is_empty (generated_kids typ)
      | None -> KidSet.is_empty (generated_kids typ)
    )

let resolve_generated_kids env typ =
  let subst_kid kid typ = subst_kid typ_subst kid (lookup_generated_kid env kid) typ in
  KidSet.fold subst_kid (generated_kids typ) typ

let rec remove_p_typ = function P_aux (P_typ (typ, pat), _) -> remove_p_typ pat | pat -> pat

let add_p_typ env typ (P_aux (paux, annot) as pat) =
  let typ' = resolve_generated_kids env typ in
  if is_src_typ typ' then P_aux (P_typ (typ', remove_p_typ pat), annot) else pat

let rec remove_e_typ = function E_aux (E_typ (_, exp), _) -> remove_e_typ exp | exp -> exp

let add_e_typ env typ (E_aux (eaux, annot) as exp) =
  let typ' = resolve_generated_kids env typ in
  if is_src_typ typ' then E_aux (E_typ (typ', remove_e_typ exp), annot) else exp

let add_typs_let env ltyp rtyp exp =
  let aux pat lhs rhs =
    let pat' = add_p_typ env ltyp pat in
    (pat', lhs, rhs)
  in
  match exp with
  | E_aux (E_let (LB_aux (LB_val (pat, lhs), lba), rhs), a) ->
      let pat', lhs', rhs' = aux pat lhs rhs in
      E_aux (E_let (LB_aux (LB_val (pat', lhs'), lba), rhs'), a)
  | E_aux (E_internal_plet (pat, lhs, rhs), a) ->
      let pat', lhs', rhs' = aux pat lhs rhs in
      E_aux (E_internal_plet (pat', lhs', rhs'), a)
  | _ -> exp

let rewrite_pexp rewriters =
  let rewrite = rewriters.rewrite_exp rewriters in
  function
  | Pat_aux (Pat_exp (p, e), pannot) -> Pat_aux (Pat_exp (rewriters.rewrite_pat rewriters p, rewrite e), pannot)
  | Pat_aux (Pat_when (p, e, e'), pannot) ->
      Pat_aux (Pat_when (rewriters.rewrite_pat rewriters p, rewrite e, rewrite e'), pannot)

let rewrite_pat rewriters (P_aux (pat, (l, annot))) =
  let rewrap p = P_aux (p, (l, annot)) in
  let rewrite = rewriters.rewrite_pat rewriters in
  match pat with
  | P_lit _ | P_wild | P_id _ | P_var _ | P_vector_subrange _ -> rewrap pat
  | P_or (pat1, pat2) -> rewrap (P_or (rewrite pat1, rewrite pat2))
  | P_not pat -> rewrap (P_not (rewrite pat))
  | P_as (pat, id) -> rewrap (P_as (rewrite pat, id))
  | P_typ (typ, pat) -> rewrap (P_typ (typ, rewrite pat))
  | P_app (id, pats) -> rewrap (P_app (id, List.map rewrite pats))
  | P_vector pats -> rewrap (P_vector (List.map rewrite pats))
  | P_vector_concat pats -> rewrap (P_vector_concat (List.map rewrite pats))
  | P_tuple pats -> rewrap (P_tuple (List.map rewrite pats))
  | P_list pats -> rewrap (P_list (List.map rewrite pats))
  | P_cons (pat1, pat2) -> rewrap (P_cons (rewrite pat1, rewrite pat2))
  | P_string_append pats -> rewrap (P_string_append (List.map rewrite pats))
  | P_struct (fpats, fwild) -> rewrap (P_struct (List.map (fun (field, pat) -> (field, rewrite pat)) fpats, fwild))

let rewrite_exp rewriters (E_aux (exp, (l, annot))) =
  let rewrap e = E_aux (e, (l, annot)) in
  let rewrite = rewriters.rewrite_exp rewriters in
  match exp with
  | E_block exps -> rewrap (E_block (List.map rewrite exps))
  | E_id _ | E_lit _ -> rewrap exp
  | E_typ (typ, exp) -> rewrap (E_typ (typ, rewrite exp))
  | E_app (id, exps) -> rewrap (E_app (id, List.map rewrite exps))
  | E_app_infix (el, id, er) -> rewrap (E_app_infix (rewrite el, id, rewrite er))
  | E_tuple exps -> rewrap (E_tuple (List.map rewrite exps))
  | E_if (c, t, e) -> rewrap (E_if (rewrite c, rewrite t, rewrite e))
  | E_for (id, e1, e2, e3, o, body) -> rewrap (E_for (id, rewrite e1, rewrite e2, rewrite e3, o, rewrite body))
  | E_loop (loop, m, e1, e2) ->
      let m =
        match m with
        | Measure_aux (Measure_none, _) -> m
        | Measure_aux (Measure_some exp, l) -> Measure_aux (Measure_some (rewrite exp), l)
      in
      rewrap (E_loop (loop, m, rewrite e1, rewrite e2))
  | E_vector exps -> rewrap (E_vector (List.map rewrite exps))
  | E_vector_access (vec, index) -> rewrap (E_vector_access (rewrite vec, rewrite index))
  | E_vector_subrange (vec, i1, i2) -> rewrap (E_vector_subrange (rewrite vec, rewrite i1, rewrite i2))
  | E_vector_update (vec, index, new_v) -> rewrap (E_vector_update (rewrite vec, rewrite index, rewrite new_v))
  | E_vector_update_subrange (vec, i1, i2, new_v) ->
      rewrap (E_vector_update_subrange (rewrite vec, rewrite i1, rewrite i2, rewrite new_v))
  | E_vector_append (v1, v2) -> rewrap (E_vector_append (rewrite v1, rewrite v2))
  | E_list exps -> rewrap (E_list (List.map rewrite exps))
  | E_cons (h, t) -> rewrap (E_cons (rewrite h, rewrite t))
  | E_struct fexps ->
      rewrap
        (E_struct (List.map (fun (FE_aux (FE_fexp (id, e), fannot)) -> FE_aux (FE_fexp (id, rewrite e), fannot)) fexps))
  | E_struct_update (re, fexps) ->
      rewrap
        (E_struct_update
           ( rewrite re,
             List.map (fun (FE_aux (FE_fexp (id, e), fannot)) -> FE_aux (FE_fexp (id, rewrite e), fannot)) fexps
           )
        )
  | E_field (exp, id) -> rewrap (E_field (rewrite exp, id))
  | E_match (exp, pexps) -> rewrap (E_match (rewrite exp, List.map (rewrite_pexp rewriters) pexps))
  | E_try (exp, pexps) -> rewrap (E_try (rewrite exp, List.map (rewrite_pexp rewriters) pexps))
  | E_let (letbind, body) -> rewrap (E_let (rewriters.rewrite_let rewriters letbind, rewrite body))
  | E_assign (lexp, exp) -> rewrap (E_assign (rewriters.rewrite_lexp rewriters lexp, rewrite exp))
  | E_sizeof n -> rewrap (E_sizeof n)
  | E_exit e -> rewrap (E_exit (rewrite e))
  | E_throw e -> rewrap (E_throw (rewrite e))
  | E_return e -> rewrap (E_return (rewrite e))
  | E_assert (e1, e2) -> rewrap (E_assert (rewrite e1, rewrite e2))
  | E_var (lexp, e1, e2) ->
      rewrap
        (E_var
           ( rewriters.rewrite_lexp rewriters lexp,
             rewriters.rewrite_exp rewriters e1,
             rewriters.rewrite_exp rewriters e2
           )
        )
  | E_internal_assume (nc, e) -> rewrap (E_internal_assume (nc, rewrite e))
  | E_internal_return e -> rewrap (E_internal_return (rewrite e))
  | E_internal_plet (pat, e1, e2) ->
      rewrap (E_internal_plet (rewriters.rewrite_pat rewriters pat, rewrite e1, rewrite e2))
  | E_ref _ | E_internal_value _ | E_constraint _ -> rewrap exp

let rewrite_let rewriters (LB_aux (letbind, (l, annot))) =
  match letbind with
  | LB_val (pat, exp) ->
      LB_aux (LB_val (rewriters.rewrite_pat rewriters pat, rewriters.rewrite_exp rewriters exp), (l, annot))

let rewrite_lexp rewriters (LE_aux (lexp, (l, annot))) =
  let rewrap le = LE_aux (le, (l, annot)) in
  match lexp with
  | LE_id _ | LE_typ _ -> rewrap lexp
  | LE_deref exp -> rewrap (LE_deref (rewriters.rewrite_exp rewriters exp))
  | LE_tuple tupls -> rewrap (LE_tuple (List.map (rewriters.rewrite_lexp rewriters) tupls))
  | LE_app (id, exps) -> rewrap (LE_app (id, List.map (rewriters.rewrite_exp rewriters) exps))
  | LE_vector (lexp, exp) ->
      rewrap (LE_vector (rewriters.rewrite_lexp rewriters lexp, rewriters.rewrite_exp rewriters exp))
  | LE_vector_range (lexp, exp1, exp2) ->
      rewrap
        (LE_vector_range
           ( rewriters.rewrite_lexp rewriters lexp,
             rewriters.rewrite_exp rewriters exp1,
             rewriters.rewrite_exp rewriters exp2
           )
        )
  | LE_vector_concat lexps -> rewrap (LE_vector_concat (List.map (rewriters.rewrite_lexp rewriters) lexps))
  | LE_field (lexp, id) -> rewrap (LE_field (rewriters.rewrite_lexp rewriters lexp, id))

let rewrite_funcl rewriters (FCL_aux (FCL_funcl (id, pexp), (l, annot))) =
  FCL_aux (FCL_funcl (id, rewrite_pexp rewriters pexp), (l, annot))

let rewrite_fun rewriters (FD_aux (FD_function (recopt, tannotopt, funcls), (l, fdannot))) =
  let recopt =
    match recopt with
    | Rec_aux (Rec_nonrec, l) -> Rec_aux (Rec_nonrec, l)
    | Rec_aux (Rec_rec, l) -> Rec_aux (Rec_rec, l)
    | Rec_aux (Rec_measure (pat, exp), l) ->
        Rec_aux (Rec_measure (rewriters.rewrite_pat rewriters pat, rewriters.rewrite_exp rewriters exp), l)
  in
  FD_aux (FD_function (recopt, tannotopt, List.map (rewrite_funcl rewriters) funcls), (l, fdannot))

let rewrite_mpexp rewriters (MPat_aux (aux, (l, annot))) =
  let aux =
    match aux with
    | MPat_pat mpat -> MPat_pat mpat
    | MPat_when (mpat, exp) -> MPat_when (mpat, rewriters.rewrite_exp rewriters exp)
  in
  MPat_aux (aux, (l, annot))

let rewrite_mapcl rewriters (MCL_aux (aux, def_annot)) =
  let aux =
    match aux with
    | MCL_bidir (mpexp1, mpexp2) -> MCL_bidir (rewrite_mpexp rewriters mpexp1, mpexp2)
    | MCL_forwards (mpexp, exp) -> MCL_forwards (rewrite_mpexp rewriters mpexp, rewriters.rewrite_exp rewriters exp)
    | MCL_backwards (mpexp, exp) -> MCL_backwards (rewrite_mpexp rewriters mpexp, rewriters.rewrite_exp rewriters exp)
  in
  MCL_aux (aux, def_annot)

let rewrite_mapdef rewriters (MD_aux (MD_mapping (id, tannot_opt, mapcls), annot)) =
  MD_aux (MD_mapping (id, tannot_opt, List.map (rewrite_mapcl rewriters) mapcls), annot)

let rewrite_scattered rewriters (SD_aux (sd, (l, annot))) =
  let sd =
    match sd with
    | SD_funcl funcl -> SD_funcl (rewrite_funcl rewriters funcl)
    | SD_mapcl (id, mapcl) -> SD_mapcl (id, rewrite_mapcl rewriters mapcl)
    | SD_variant _ | SD_unioncl _ | SD_mapping _ | SD_function _ | SD_end _ | SD_enum _ | SD_enumcl _
    | SD_internal_unioncl_record _ ->
        sd
  in
  SD_aux (sd, (l, annot))

let rec rewrite_def rewriters (DEF_aux (aux, def_annot)) =
  let aux =
    match aux with
    | DEF_register (DEC_aux (DEC_reg (typ, id, Some exp), annot)) ->
        DEF_register (DEC_aux (DEC_reg (typ, id, Some (rewriters.rewrite_exp rewriters exp)), annot))
    | DEF_type _ | DEF_mapdef _ | DEF_val _ | DEF_default _ | DEF_register _ | DEF_overload _ | DEF_fixity _
    | DEF_instantiation _ ->
        aux
    | DEF_fundef fdef -> DEF_fundef (rewriters.rewrite_fun rewriters fdef)
    | DEF_impl funcl -> DEF_impl (rewrite_funcl rewriters funcl)
    | DEF_outcome (outcome_spec, defs) -> DEF_outcome (outcome_spec, List.map (rewrite_def rewriters) defs)
    | DEF_internal_mutrec fdefs -> DEF_internal_mutrec (List.map (rewriters.rewrite_fun rewriters) fdefs)
    | DEF_let letbind -> DEF_let (rewriters.rewrite_let rewriters letbind)
    | DEF_pragma (pragma, arg, l) -> DEF_pragma (pragma, arg, l)
    | DEF_scattered sd -> DEF_scattered (rewrite_scattered rewriters sd)
    | DEF_measure (id, pat, exp) ->
        DEF_measure (id, rewriters.rewrite_pat rewriters pat, rewriters.rewrite_exp rewriters exp)
    | DEF_loop_measures (id, _) ->
        raise (Reporting.err_unreachable (id_loc id) __POS__ "DEF_loop_measures survived to rewriter")
  in
  DEF_aux (aux, def_annot)

let rewrite_ast_defs rewriters defs =
  let rec rewrite ds = match ds with [] -> [] | d :: ds -> rewriters.rewrite_def rewriters d :: rewrite ds in
  rewrite defs

let rewrite_ast_base rewriters ast =
  let rec rewrite ds = match ds with [] -> [] | d :: ds -> rewriters.rewrite_def rewriters d :: rewrite ds in
  { ast with defs = rewrite ast.defs }

let rewrite_ast_base_progress prefix rewriters ast =
  let total = List.length ast.defs in
  let rec rewrite n = function
    | [] -> []
    | d :: ds ->
        Util.progress (prefix ^ " ") (string_of_int n ^ "/" ^ string_of_int total) n total;
        let d = rewriters.rewrite_def rewriters d in
        d :: rewrite (n + 1) ds
  in
  { ast with defs = rewrite 1 ast.defs }

let rewriters_base =
  { rewrite_exp; rewrite_pat; rewrite_let; rewrite_lexp; rewrite_fun; rewrite_def; rewrite_ast = rewrite_ast_base }

let rewrite_ast ast = rewrite_ast_base rewriters_base ast

type ('a, 'pat, 'pat_aux) pat_alg = {
  p_lit : lit -> 'pat_aux;
  p_wild : 'pat_aux;
  p_or : 'pat * 'pat -> 'pat_aux;
  p_not : 'pat -> 'pat_aux;
  p_as : 'pat * id -> 'pat_aux;
  p_typ : Ast.typ * 'pat -> 'pat_aux;
  p_id : id -> 'pat_aux;
  p_var : 'pat * typ_pat -> 'pat_aux;
  p_app : id * 'pat list -> 'pat_aux;
  p_vector : 'pat list -> 'pat_aux;
  p_vector_concat : 'pat list -> 'pat_aux;
  p_vector_subrange : id * Big_int.num * Big_int.num -> 'pat_aux;
  p_tuple : 'pat list -> 'pat_aux;
  p_list : 'pat list -> 'pat_aux;
  p_cons : 'pat * 'pat -> 'pat_aux;
  p_string_append : 'pat list -> 'pat_aux;
  p_struct : (id * 'pat) list * field_pat_wildcard -> 'pat_aux;
  p_aux : 'pat_aux * 'a annot -> 'pat;
}

let rec fold_pat_aux (alg : ('a, 'pat, 'pat_aux) pat_alg) : 'a pat_aux -> 'pat_aux = function
  | P_lit lit -> alg.p_lit lit
  | P_wild -> alg.p_wild
  | P_or (p1, p2) -> alg.p_or (fold_pat alg p1, fold_pat alg p2)
  | P_not p -> alg.p_not (fold_pat alg p)
  | P_id id -> alg.p_id id
  | P_var (p, tpat) -> alg.p_var (fold_pat alg p, tpat)
  | P_as (p, id) -> alg.p_as (fold_pat alg p, id)
  | P_typ (typ, p) -> alg.p_typ (typ, fold_pat alg p)
  | P_app (id, ps) -> alg.p_app (id, List.map (fold_pat alg) ps)
  | P_vector ps -> alg.p_vector (List.map (fold_pat alg) ps)
  | P_vector_concat ps -> alg.p_vector_concat (List.map (fold_pat alg) ps)
  | P_vector_subrange (id, n, m) -> alg.p_vector_subrange (id, n, m)
  | P_tuple ps -> alg.p_tuple (List.map (fold_pat alg) ps)
  | P_list ps -> alg.p_list (List.map (fold_pat alg) ps)
  | P_cons (ph, pt) -> alg.p_cons (fold_pat alg ph, fold_pat alg pt)
  | P_string_append ps -> alg.p_string_append (List.map (fold_pat alg) ps)
  | P_struct (fpats, fwild) -> alg.p_struct (List.map (fun (field, pat) -> (field, fold_pat alg pat)) fpats, fwild)

and fold_pat (alg : ('a, 'pat, 'pat_aux) pat_alg) : 'a pat -> 'pat = function
  | P_aux (pat, annot) -> alg.p_aux (fold_pat_aux alg pat, annot)

let rec fold_mpat_aux (alg : ('a, 'mpat, 'mpat_aux) pat_alg) : 'a mpat_aux -> 'mpat_aux = function
  | MP_lit lit -> alg.p_lit lit
  | MP_id id -> alg.p_id id
  | MP_as (p, id) -> alg.p_as (fold_mpat alg p, id)
  | MP_typ (p, typ) -> alg.p_typ (typ, fold_mpat alg p)
  | MP_app (id, ps) -> alg.p_app (id, List.map (fold_mpat alg) ps)
  | MP_vector ps -> alg.p_vector (List.map (fold_mpat alg) ps)
  | MP_vector_concat ps -> alg.p_vector_concat (List.map (fold_mpat alg) ps)
  | MP_vector_subrange (id, n, m) -> alg.p_vector_subrange (id, n, m)
  | MP_tuple ps -> alg.p_tuple (List.map (fold_mpat alg) ps)
  | MP_list ps -> alg.p_list (List.map (fold_mpat alg) ps)
  | MP_cons (ph, pt) -> alg.p_cons (fold_mpat alg ph, fold_mpat alg pt)
  | MP_string_append ps -> alg.p_string_append (List.map (fold_mpat alg) ps)
  | MP_struct fmpats -> alg.p_struct (List.map (fun (field, mpat) -> (field, fold_mpat alg mpat)) fmpats, FP_no_wild)

and fold_mpat (alg : ('a, 'mpat, 'mpat_aux) pat_alg) : 'a mpat -> 'mpat = function
  | MP_aux (mpat, annot) -> alg.p_aux (fold_mpat_aux alg mpat, annot)

(* identity fold from term alg to term alg *)
let id_pat_alg : ('a, 'a pat, 'a pat_aux) pat_alg =
  {
    p_lit = (fun lit -> P_lit lit);
    p_wild = P_wild;
    p_or = (fun (pat1, pat2) -> P_or (pat1, pat2));
    p_not = (fun pat -> P_not pat);
    p_as = (fun (pat, id) -> P_as (pat, id));
    p_typ = (fun (typ, pat) -> P_typ (typ, pat));
    p_id = (fun id -> P_id id);
    p_var = (fun (pat, tpat) -> P_var (pat, tpat));
    p_app = (fun (id, ps) -> P_app (id, ps));
    p_vector = (fun ps -> P_vector ps);
    p_vector_concat = (fun ps -> P_vector_concat ps);
    p_vector_subrange = (fun (id, n, m) -> P_vector_subrange (id, n, m));
    p_tuple = (fun ps -> P_tuple ps);
    p_list = (fun ps -> P_list ps);
    p_cons = (fun (ph, pt) -> P_cons (ph, pt));
    p_string_append = (fun ps -> P_string_append ps);
    p_struct = (fun (fpats, fwild) -> P_struct (fpats, fwild));
    p_aux = (fun (pat, annot) -> P_aux (pat, annot));
  }

let id_mpat_alg : ('a, 'a mpat option, 'a mpat_aux option) pat_alg =
  {
    p_lit = (fun lit -> Some (MP_lit lit));
    p_wild = None;
    p_or = (fun _ -> None);
    p_not = (fun _ -> None);
    p_as = (fun (pat, id) -> Option.map (fun pat -> MP_as (pat, id)) pat);
    p_typ = (fun (typ, pat) -> Option.map (fun pat -> MP_typ (pat, typ)) pat);
    p_id = (fun id -> Some (MP_id id));
    p_var = (fun _ -> None);
    p_app = (fun (id, ps) -> Option.map (fun ps -> MP_app (id, ps)) (Util.option_all ps));
    p_vector = (fun ps -> Option.map (fun ps -> MP_vector ps) (Util.option_all ps));
    p_vector_concat = (fun ps -> Option.map (fun ps -> MP_vector_concat ps) (Util.option_all ps));
    p_vector_subrange = (fun (id, n, m) -> Some (MP_vector_subrange (id, n, m)));
    p_tuple = (fun ps -> Option.map (fun ps -> MP_tuple ps) (Util.option_all ps));
    p_list = (fun ps -> Option.map (fun ps -> MP_list ps) (Util.option_all ps));
    p_cons = (fun (ph, pt) -> Option.bind ph (fun ph -> Option.map (fun pt -> MP_cons (ph, pt)) pt));
    p_string_append = (fun ps -> Option.map (fun ps -> MP_string_append ps) (Util.option_all ps));
    p_struct = (fun _ -> None);
    p_aux = (fun (pat, annot) -> Option.map (fun pat -> MP_aux (pat, annot)) pat);
  }

type ( 'a,
       'exp,
       'exp_aux,
       'lexp,
       'lexp_aux,
       'fexp,
       'fexp_aux,
       'opt_default_aux,
       'opt_default,
       'pexp,
       'pexp_aux,
       'letbind_aux,
       'letbind,
       'pat,
       'pat_aux
     )
     exp_alg = {
  e_block : 'exp list -> 'exp_aux;
  e_id : id -> 'exp_aux;
  e_ref : id -> 'exp_aux;
  e_lit : lit -> 'exp_aux;
  e_typ : Ast.typ * 'exp -> 'exp_aux;
  e_app : id * 'exp list -> 'exp_aux;
  e_app_infix : 'exp * id * 'exp -> 'exp_aux;
  e_tuple : 'exp list -> 'exp_aux;
  e_if : 'exp * 'exp * 'exp -> 'exp_aux;
  e_for : id * 'exp * 'exp * 'exp * Ast.order * 'exp -> 'exp_aux;
  e_loop : loop * ('exp option * Parse_ast.l) * 'exp * 'exp -> 'exp_aux;
  e_vector : 'exp list -> 'exp_aux;
  e_vector_access : 'exp * 'exp -> 'exp_aux;
  e_vector_subrange : 'exp * 'exp * 'exp -> 'exp_aux;
  e_vector_update : 'exp * 'exp * 'exp -> 'exp_aux;
  e_vector_update_subrange : 'exp * 'exp * 'exp * 'exp -> 'exp_aux;
  e_vector_append : 'exp * 'exp -> 'exp_aux;
  e_list : 'exp list -> 'exp_aux;
  e_cons : 'exp * 'exp -> 'exp_aux;
  e_struct : 'fexp list -> 'exp_aux;
  e_struct_update : 'exp * 'fexp list -> 'exp_aux;
  e_field : 'exp * id -> 'exp_aux;
  e_case : 'exp * 'pexp list -> 'exp_aux;
  e_try : 'exp * 'pexp list -> 'exp_aux;
  e_let : 'letbind * 'exp -> 'exp_aux;
  e_assign : 'lexp * 'exp -> 'exp_aux;
  e_sizeof : nexp -> 'exp_aux;
  e_constraint : n_constraint -> 'exp_aux;
  e_exit : 'exp -> 'exp_aux;
  e_throw : 'exp -> 'exp_aux;
  e_return : 'exp -> 'exp_aux;
  e_assert : 'exp * 'exp -> 'exp_aux;
  e_var : 'lexp * 'exp * 'exp -> 'exp_aux;
  e_internal_plet : 'pat * 'exp * 'exp -> 'exp_aux;
  e_internal_return : 'exp -> 'exp_aux;
  e_internal_value : Value.value -> 'exp_aux;
  e_internal_assume : n_constraint * 'exp -> 'exp_aux;
  e_aux : 'exp_aux * 'a annot -> 'exp;
  le_id : id -> 'lexp_aux;
  le_deref : 'exp -> 'lexp_aux;
  le_app : id * 'exp list -> 'lexp_aux;
  le_typ : Ast.typ * id -> 'lexp_aux;
  le_tuple : 'lexp list -> 'lexp_aux;
  le_vector : 'lexp * 'exp -> 'lexp_aux;
  le_vector_range : 'lexp * 'exp * 'exp -> 'lexp_aux;
  le_vector_concat : 'lexp list -> 'lexp_aux;
  le_field : 'lexp * id -> 'lexp_aux;
  le_aux : 'lexp_aux * 'a annot -> 'lexp;
  fe_fexp : id * 'exp -> 'fexp_aux;
  fe_aux : 'fexp_aux * 'a annot -> 'fexp;
  def_val_empty : 'opt_default_aux;
  def_val_dec : 'exp -> 'opt_default_aux;
  def_val_aux : 'opt_default_aux * 'a annot -> 'opt_default;
  pat_exp : 'pat * 'exp -> 'pexp_aux;
  pat_when : 'pat * 'exp * 'exp -> 'pexp_aux;
  pat_aux : 'pexp_aux * 'a annot -> 'pexp;
  lb_val : 'pat * 'exp -> 'letbind_aux;
  lb_aux : 'letbind_aux * 'a annot -> 'letbind;
  pat_alg : ('a, 'pat, 'pat_aux) pat_alg;
}

let rec fold_exp_aux alg = function
  | E_block es -> alg.e_block (List.map (fold_exp alg) es)
  | E_id id -> alg.e_id id
  | E_ref id -> alg.e_ref id
  | E_lit lit -> alg.e_lit lit
  | E_typ (typ, e) -> alg.e_typ (typ, fold_exp alg e)
  | E_app (id, es) -> alg.e_app (id, List.map (fold_exp alg) es)
  | E_app_infix (e1, id, e2) -> alg.e_app_infix (fold_exp alg e1, id, fold_exp alg e2)
  | E_tuple es -> alg.e_tuple (List.map (fold_exp alg) es)
  | E_if (e1, e2, e3) -> alg.e_if (fold_exp alg e1, fold_exp alg e2, fold_exp alg e3)
  | E_for (id, e1, e2, e3, order, e4) ->
      alg.e_for (id, fold_exp alg e1, fold_exp alg e2, fold_exp alg e3, order, fold_exp alg e4)
  | E_loop (loop_type, m, e1, e2) ->
      let m =
        match m with
        | Measure_aux (Measure_none, l) -> (None, l)
        | Measure_aux (Measure_some exp, l) -> (Some (fold_exp alg exp), l)
      in
      alg.e_loop (loop_type, m, fold_exp alg e1, fold_exp alg e2)
  | E_vector es -> alg.e_vector (List.map (fold_exp alg) es)
  | E_vector_access (e1, e2) -> alg.e_vector_access (fold_exp alg e1, fold_exp alg e2)
  | E_vector_subrange (e1, e2, e3) -> alg.e_vector_subrange (fold_exp alg e1, fold_exp alg e2, fold_exp alg e3)
  | E_vector_update (e1, e2, e3) -> alg.e_vector_update (fold_exp alg e1, fold_exp alg e2, fold_exp alg e3)
  | E_vector_update_subrange (e1, e2, e3, e4) ->
      alg.e_vector_update_subrange (fold_exp alg e1, fold_exp alg e2, fold_exp alg e3, fold_exp alg e4)
  | E_vector_append (e1, e2) -> alg.e_vector_append (fold_exp alg e1, fold_exp alg e2)
  | E_list es -> alg.e_list (List.map (fold_exp alg) es)
  | E_cons (e1, e2) -> alg.e_cons (fold_exp alg e1, fold_exp alg e2)
  | E_struct fexps -> alg.e_struct (List.map (fold_fexp alg) fexps)
  | E_struct_update (e, fexps) -> alg.e_struct_update (fold_exp alg e, List.map (fold_fexp alg) fexps)
  | E_field (e, id) -> alg.e_field (fold_exp alg e, id)
  | E_match (e, pexps) -> alg.e_case (fold_exp alg e, List.map (fold_pexp alg) pexps)
  | E_try (e, pexps) -> alg.e_try (fold_exp alg e, List.map (fold_pexp alg) pexps)
  | E_let (letbind, e) -> alg.e_let (fold_letbind alg letbind, fold_exp alg e)
  | E_assign (lexp, e) -> alg.e_assign (fold_lexp alg lexp, fold_exp alg e)
  | E_sizeof nexp -> alg.e_sizeof nexp
  | E_constraint nc -> alg.e_constraint nc
  | E_exit e -> alg.e_exit (fold_exp alg e)
  | E_throw e -> alg.e_throw (fold_exp alg e)
  | E_return e -> alg.e_return (fold_exp alg e)
  | E_assert (e1, e2) -> alg.e_assert (fold_exp alg e1, fold_exp alg e2)
  | E_var (lexp, e1, e2) -> alg.e_var (fold_lexp alg lexp, fold_exp alg e1, fold_exp alg e2)
  | E_internal_plet (pat, e1, e2) -> alg.e_internal_plet (fold_pat alg.pat_alg pat, fold_exp alg e1, fold_exp alg e2)
  | E_internal_return e -> alg.e_internal_return (fold_exp alg e)
  | E_internal_value v -> alg.e_internal_value v
  | E_internal_assume (nc, e) -> alg.e_internal_assume (nc, fold_exp alg e)

and fold_exp alg (E_aux (exp_aux, annot)) = alg.e_aux (fold_exp_aux alg exp_aux, annot)

and fold_lexp_aux alg = function
  | LE_id id -> alg.le_id id
  | LE_deref exp -> alg.le_deref (fold_exp alg exp)
  | LE_app (id, es) -> alg.le_app (id, List.map (fold_exp alg) es)
  | LE_tuple les -> alg.le_tuple (List.map (fold_lexp alg) les)
  | LE_typ (typ, id) -> alg.le_typ (typ, id)
  | LE_vector (lexp, e) -> alg.le_vector (fold_lexp alg lexp, fold_exp alg e)
  | LE_vector_range (lexp, e1, e2) -> alg.le_vector_range (fold_lexp alg lexp, fold_exp alg e1, fold_exp alg e2)
  | LE_vector_concat les -> alg.le_vector_concat (List.map (fold_lexp alg) les)
  | LE_field (lexp, id) -> alg.le_field (fold_lexp alg lexp, id)

and fold_lexp alg (LE_aux (lexp_aux, annot)) = alg.le_aux (fold_lexp_aux alg lexp_aux, annot)

and fold_fexp_aux alg (FE_fexp (id, e)) = alg.fe_fexp (id, fold_exp alg e)

and fold_fexp alg (FE_aux (fexp_aux, annot)) = alg.fe_aux (fold_fexp_aux alg fexp_aux, annot)

and fold_pexp_aux alg = function
  | Pat_exp (pat, e) -> alg.pat_exp (fold_pat alg.pat_alg pat, fold_exp alg e)
  | Pat_when (pat, e, e') -> alg.pat_when (fold_pat alg.pat_alg pat, fold_exp alg e, fold_exp alg e')

and fold_pexp alg (Pat_aux (pexp_aux, annot)) = alg.pat_aux (fold_pexp_aux alg pexp_aux, annot)

and fold_letbind_aux alg = function LB_val (pat, e) -> alg.lb_val (fold_pat alg.pat_alg pat, fold_exp alg e)

and fold_letbind alg (LB_aux (letbind_aux, annot)) = alg.lb_aux (fold_letbind_aux alg letbind_aux, annot)

let fold_funcl alg (FCL_aux (FCL_funcl (id, pexp), annot)) = FCL_aux (FCL_funcl (id, fold_pexp alg pexp), annot)

let fold_function alg (FD_aux (FD_function (rec_opt, tannot_opt, funcls), annot)) =
  FD_aux (FD_function (rec_opt, tannot_opt, List.map (fold_funcl alg) funcls), annot)

let id_exp_alg =
  {
    e_block = (fun es -> E_block es);
    e_id = (fun id -> E_id id);
    e_ref = (fun id -> E_ref id);
    e_lit = (fun lit -> E_lit lit);
    e_typ = (fun (typ, e) -> E_typ (typ, e));
    e_app = (fun (id, es) -> E_app (id, es));
    e_app_infix = (fun (e1, id, e2) -> E_app_infix (e1, id, e2));
    e_tuple = (fun es -> E_tuple es);
    e_if = (fun (e1, e2, e3) -> E_if (e1, e2, e3));
    e_for = (fun (id, e1, e2, e3, order, e4) -> E_for (id, e1, e2, e3, order, e4));
    e_loop =
      (fun (lt, (m, l), e1, e2) ->
        let m = match m with None -> Measure_none | Some e -> Measure_some e in
        E_loop (lt, Measure_aux (m, l), e1, e2)
      );
    e_vector = (fun es -> E_vector es);
    e_vector_access = (fun (e1, e2) -> E_vector_access (e1, e2));
    e_vector_subrange = (fun (e1, e2, e3) -> E_vector_subrange (e1, e2, e3));
    e_vector_update = (fun (e1, e2, e3) -> E_vector_update (e1, e2, e3));
    e_vector_update_subrange = (fun (e1, e2, e3, e4) -> E_vector_update_subrange (e1, e2, e3, e4));
    e_vector_append = (fun (e1, e2) -> E_vector_append (e1, e2));
    e_list = (fun es -> E_list es);
    e_cons = (fun (e1, e2) -> E_cons (e1, e2));
    e_struct = (fun fexps -> E_struct fexps);
    e_struct_update = (fun (e1, fexp) -> E_struct_update (e1, fexp));
    e_field = (fun (e1, id) -> E_field (e1, id));
    e_case = (fun (e1, pexps) -> E_match (e1, pexps));
    e_try = (fun (e1, pexps) -> E_try (e1, pexps));
    e_let = (fun (lb, e2) -> E_let (lb, e2));
    e_assign = (fun (lexp, e2) -> E_assign (lexp, e2));
    e_sizeof = (fun nexp -> E_sizeof nexp);
    e_constraint = (fun nc -> E_constraint nc);
    e_exit = (fun e1 -> E_exit e1);
    e_throw = (fun e1 -> E_throw e1);
    e_return = (fun e1 -> E_return e1);
    e_assert = (fun (e1, e2) -> E_assert (e1, e2));
    e_var = (fun (lexp, e2, e3) -> E_var (lexp, e2, e3));
    e_internal_plet = (fun (pat, e1, e2) -> E_internal_plet (pat, e1, e2));
    e_internal_return = (fun e -> E_internal_return e);
    e_internal_value = (fun v -> E_internal_value v);
    e_internal_assume = (fun (nc, e) -> E_internal_assume (nc, e));
    e_aux = (fun (e, annot) -> E_aux (e, annot));
    le_id = (fun id -> LE_id id);
    le_deref = (fun e -> LE_deref e);
    le_app = (fun (id, es) -> LE_app (id, es));
    le_typ = (fun (typ, id) -> LE_typ (typ, id));
    le_tuple = (fun tups -> LE_tuple tups);
    le_vector = (fun (lexp, e2) -> LE_vector (lexp, e2));
    le_vector_range = (fun (lexp, e2, e3) -> LE_vector_range (lexp, e2, e3));
    le_vector_concat = (fun lexps -> LE_vector_concat lexps);
    le_field = (fun (lexp, id) -> LE_field (lexp, id));
    le_aux = (fun (lexp, annot) -> LE_aux (lexp, annot));
    fe_fexp = (fun (id, e) -> FE_fexp (id, e));
    fe_aux = (fun (fexp, annot) -> FE_aux (fexp, annot));
    def_val_empty = Def_val_empty;
    def_val_dec = (fun e -> Def_val_dec e);
    def_val_aux = (fun (defval, aux) -> Def_val_aux (defval, aux));
    pat_exp = (fun (pat, e) -> Pat_exp (pat, e));
    pat_when = (fun (pat, e, e') -> Pat_when (pat, e, e'));
    pat_aux = (fun (pexp, a) -> Pat_aux (pexp, a));
    lb_val = (fun (pat, e) -> LB_val (pat, e));
    lb_aux = (fun (lb, annot) -> LB_aux (lb, annot));
    pat_alg = id_pat_alg;
  }

(* Folding algorithms for not only rewriting patterns/expressions, but also
   computing some additional value. Usage: Pass default value (bot) and a
   binary join operator as arguments, and specify the non-default cases of
   rewriting/computation by overwriting fields of the record.
   See rewrite_sizeof for examples. *)
let compute_pat_alg bot join =
  let join_list vs = List.fold_left join bot vs in
  let split_join f ps =
    let vs, ps = List.split ps in
    (join_list vs, f ps)
  in
  {
    p_lit = (fun lit -> (bot, P_lit lit));
    p_wild = (bot, P_wild) (* todo: I have no idea how to combine v1 and v2 in the following *);
    p_or = (fun ((v1, pat1), (v2, pat2)) -> (v1, P_or (pat1, pat2)));
    p_not = (fun (v, pat) -> (v, P_not pat));
    p_as = (fun ((v, pat), id) -> (v, P_as (pat, id)));
    p_typ = (fun (typ, (v, pat)) -> (v, P_typ (typ, pat)));
    p_id = (fun id -> (bot, P_id id));
    p_var = (fun ((v, pat), kid) -> (v, P_var (pat, kid)));
    p_app = (fun (id, ps) -> split_join (fun ps -> P_app (id, ps)) ps);
    p_vector = split_join (fun ps -> P_vector ps);
    p_vector_concat = split_join (fun ps -> P_vector_concat ps);
    p_vector_subrange = (fun (id, n, m) -> (bot, P_vector_subrange (id, n, m)));
    p_tuple = split_join (fun ps -> P_tuple ps);
    p_list = split_join (fun ps -> P_list ps);
    p_cons = (fun ((vh, ph), (vt, pt)) -> (join vh vt, P_cons (ph, pt)));
    p_string_append = split_join (fun ps -> P_string_append ps);
    p_struct =
      (fun (fpats, fwild) ->
        let fields, ps = List.split fpats in
        let vs, ps = List.split ps in
        (join_list vs, P_struct (List.map2 (fun field p -> (field, p)) fields ps, fwild))
      );
    p_aux = (fun ((v, pat), annot) -> (v, P_aux (pat, annot)));
  }

let compute_exp_alg bot join =
  let join_list vs = List.fold_left join bot vs in
  let split_join f es =
    let vs, es = List.split es in
    (join_list vs, f es)
  in
  {
    e_block = split_join (fun es -> E_block es);
    e_id = (fun id -> (bot, E_id id));
    e_ref = (fun id -> (bot, E_ref id));
    e_lit = (fun lit -> (bot, E_lit lit));
    e_typ = (fun (typ, (v, e)) -> (v, E_typ (typ, e)));
    e_app = (fun (id, es) -> split_join (fun es -> E_app (id, es)) es);
    e_app_infix = (fun ((v1, e1), id, (v2, e2)) -> (join v1 v2, E_app_infix (e1, id, e2)));
    e_tuple = split_join (fun es -> E_tuple es);
    e_if = (fun ((v1, e1), (v2, e2), (v3, e3)) -> (join_list [v1; v2; v3], E_if (e1, e2, e3)));
    e_for =
      (fun (id, (v1, e1), (v2, e2), (v3, e3), order, (v4, e4)) ->
        (join_list [v1; v2; v3; v4], E_for (id, e1, e2, e3, order, e4))
      );
    e_loop =
      (fun (lt, (m, l), (v1, e1), (v2, e2)) ->
        let vs, m = match m with None -> ([], Measure_none) | Some (v, e) -> ([v], Measure_some e) in
        (join_list (vs @ [v1; v2]), E_loop (lt, Measure_aux (m, l), e1, e2))
      );
    e_vector = split_join (fun es -> E_vector es);
    e_vector_access = (fun ((v1, e1), (v2, e2)) -> (join v1 v2, E_vector_access (e1, e2)));
    e_vector_subrange = (fun ((v1, e1), (v2, e2), (v3, e3)) -> (join_list [v1; v2; v3], E_vector_subrange (e1, e2, e3)));
    e_vector_update = (fun ((v1, e1), (v2, e2), (v3, e3)) -> (join_list [v1; v2; v3], E_vector_update (e1, e2, e3)));
    e_vector_update_subrange =
      (fun ((v1, e1), (v2, e2), (v3, e3), (v4, e4)) ->
        (join_list [v1; v2; v3; v4], E_vector_update_subrange (e1, e2, e3, e4))
      );
    e_vector_append = (fun ((v1, e1), (v2, e2)) -> (join v1 v2, E_vector_append (e1, e2)));
    e_list = split_join (fun es -> E_list es);
    e_cons = (fun ((v1, e1), (v2, e2)) -> (join v1 v2, E_cons (e1, e2)));
    e_struct =
      (fun fexps ->
        let vs, fexps = List.split fexps in
        (join_list vs, E_struct fexps)
      );
    e_struct_update =
      (fun ((v1, e1), fexps) ->
        let vps, fexps = List.split fexps in
        (join_list (v1 :: vps), E_struct_update (e1, fexps))
      );
    e_field = (fun ((v1, e1), id) -> (v1, E_field (e1, id)));
    e_case =
      (fun ((v1, e1), pexps) ->
        let vps, pexps = List.split pexps in
        (join_list (v1 :: vps), E_match (e1, pexps))
      );
    e_try =
      (fun ((v1, e1), pexps) ->
        let vps, pexps = List.split pexps in
        (join_list (v1 :: vps), E_try (e1, pexps))
      );
    e_let = (fun ((vl, lb), (v2, e2)) -> (join vl v2, E_let (lb, e2)));
    e_assign = (fun ((vl, lexp), (v2, e2)) -> (join vl v2, E_assign (lexp, e2)));
    e_sizeof = (fun nexp -> (bot, E_sizeof nexp));
    e_constraint = (fun nc -> (bot, E_constraint nc));
    e_exit = (fun (v1, e1) -> (v1, E_exit e1));
    e_throw = (fun (v1, e1) -> (v1, E_throw e1));
    e_return = (fun (v1, e1) -> (v1, E_return e1));
    e_assert = (fun ((v1, e1), (v2, e2)) -> (join v1 v2, E_assert (e1, e2)));
    e_var = (fun ((vl, lexp), (v2, e2), (v3, e3)) -> (join_list [vl; v2; v3], E_var (lexp, e2, e3)));
    e_internal_plet = (fun ((vp, pat), (v1, e1), (v2, e2)) -> (join_list [vp; v1; v2], E_internal_plet (pat, e1, e2)));
    e_internal_return = (fun (v, e) -> (v, E_internal_return e));
    e_internal_value = (fun v -> (bot, E_internal_value v));
    e_internal_assume = (fun (nc, (v, e)) -> (v, E_internal_assume (nc, e)));
    e_aux = (fun ((v, e), annot) -> (v, E_aux (e, annot)));
    le_id = (fun id -> (bot, LE_id id));
    le_deref = (fun (v, e) -> (v, LE_deref e));
    le_app = (fun (id, es) -> split_join (fun es -> LE_app (id, es)) es);
    le_typ = (fun (typ, id) -> (bot, LE_typ (typ, id)));
    le_tuple =
      (fun ls ->
        let vs, ls = List.split ls in
        (join_list vs, LE_tuple ls)
      );
    le_vector = (fun ((vl, lexp), (v2, e2)) -> (join vl v2, LE_vector (lexp, e2)));
    le_vector_range = (fun ((vl, lexp), (v2, e2), (v3, e3)) -> (join_list [vl; v2; v3], LE_vector_range (lexp, e2, e3)));
    le_vector_concat =
      (fun ls ->
        let vs, ls = List.split ls in
        (join_list vs, LE_vector_concat ls)
      );
    le_field = (fun ((vl, lexp), id) -> (vl, LE_field (lexp, id)));
    le_aux = (fun ((vl, lexp), annot) -> (vl, LE_aux (lexp, annot)));
    fe_fexp = (fun (id, (v, e)) -> (v, FE_fexp (id, e)));
    fe_aux = (fun ((vf, fexp), annot) -> (vf, FE_aux (fexp, annot)));
    def_val_empty = (bot, Def_val_empty);
    def_val_dec = (fun (v, e) -> (v, Def_val_dec e));
    def_val_aux = (fun ((v, defval), aux) -> (v, Def_val_aux (defval, aux)));
    pat_exp = (fun ((vp, pat), (v, e)) -> (join vp v, Pat_exp (pat, e)));
    pat_when = (fun ((vp, pat), (v, e), (v', e')) -> (join_list [vp; v; v'], Pat_when (pat, e, e')));
    pat_aux = (fun ((v, pexp), a) -> (v, Pat_aux (pexp, a)));
    lb_val = (fun ((vp, pat), (v, e)) -> (join vp v, LB_val (pat, e)));
    lb_aux = (fun ((vl, lb), annot) -> (vl, LB_aux (lb, annot)));
    pat_alg = compute_pat_alg bot join;
  }

let pure_pat_alg bot join =
  let join_list vs = List.fold_left join bot vs in
  {
    p_lit = (fun _ -> bot);
    p_wild = bot;
    p_or = (fun (pat1, pat2) -> bot) (* todo: this is wrong *);
    p_not = (fun _ -> bot) (* todo: this is wrong *);
    p_as = (fun (v, _) -> v);
    p_typ = (fun (_, v) -> v);
    p_id = (fun id -> bot);
    p_var = (fun (v, kid) -> v);
    p_app = (fun (id, ps) -> join_list ps);
    p_vector = join_list;
    p_vector_concat = join_list;
    p_vector_subrange = (fun _ -> bot);
    p_tuple = join_list;
    p_list = join_list;
    p_string_append = join_list;
    p_struct = (fun (xs, _) -> join_list (List.map snd xs));
    p_cons = (fun (vh, vt) -> join vh vt);
    p_aux = (fun (v, annot) -> v);
  }

let pure_exp_alg bot join =
  let join_list vs = List.fold_left join bot vs in
  {
    e_block = join_list;
    e_id = (fun id -> bot);
    e_ref = (fun id -> bot);
    e_lit = (fun lit -> bot);
    e_typ = (fun (typ, v) -> v);
    e_app = (fun (id, es) -> join_list es);
    e_app_infix = (fun (v1, id, v2) -> join v1 v2);
    e_tuple = join_list;
    e_if = (fun (v1, v2, v3) -> join_list [v1; v2; v3]);
    e_for = (fun (id, v1, v2, v3, order, v4) -> join_list [v1; v2; v3; v4]);
    e_loop =
      (fun (lt, (m, _), v1, v2) ->
        let v = join v1 v2 in
        match m with None -> v | Some v' -> join v v'
      );
    e_vector = join_list;
    e_vector_access = (fun (v1, v2) -> join v1 v2);
    e_vector_subrange = (fun (v1, v2, v3) -> join_list [v1; v2; v3]);
    e_vector_update = (fun (v1, v2, v3) -> join_list [v1; v2; v3]);
    e_vector_update_subrange = (fun (v1, v2, v3, v4) -> join_list [v1; v2; v3; v4]);
    e_vector_append = (fun (v1, v2) -> join v1 v2);
    e_list = join_list;
    e_cons = (fun (v1, v2) -> join v1 v2);
    e_struct = (fun vs -> join_list vs);
    e_struct_update = (fun (v1, vf) -> join_list (v1 :: vf));
    e_field = (fun (v1, id) -> v1);
    e_case = (fun (v1, vps) -> join_list (v1 :: vps));
    e_try = (fun (v1, vps) -> join_list (v1 :: vps));
    e_let = (fun (vl, v2) -> join vl v2);
    e_assign = (fun (vl, v2) -> join vl v2);
    e_sizeof = (fun nexp -> bot);
    e_constraint = (fun nc -> bot);
    e_exit = (fun v1 -> v1);
    e_throw = (fun v1 -> v1);
    e_return = (fun v1 -> v1);
    e_assert = (fun (v1, v2) -> join v1 v2);
    e_var = (fun (vl, v2, v3) -> join_list [vl; v2; v3]);
    e_internal_plet = (fun (vp, v1, v2) -> join_list [vp; v1; v2]);
    e_internal_return = (fun v -> v);
    e_internal_value = (fun v -> bot);
    e_internal_assume = (fun (_nc, v) -> v);
    e_aux = (fun (v, annot) -> v);
    le_id = (fun id -> bot);
    le_deref = (fun v -> v);
    le_app = (fun (id, es) -> join_list es);
    le_typ = (fun (typ, id) -> bot);
    le_tuple = join_list;
    le_vector = (fun (vl, v2) -> join vl v2);
    le_vector_range = (fun (vl, v2, v3) -> join_list [vl; v2; v3]);
    le_vector_concat = join_list;
    le_field = (fun (vl, id) -> vl);
    le_aux = (fun (vl, annot) -> vl);
    fe_fexp = (fun (id, v) -> v);
    fe_aux = (fun (vf, annot) -> vf);
    def_val_empty = bot;
    def_val_dec = (fun v -> v);
    def_val_aux = (fun (v, aux) -> v);
    pat_exp = (fun (vp, v) -> join vp v);
    pat_when = (fun (vp, v, v') -> join_list [vp; v; v']);
    pat_aux = (fun (v, a) -> v);
    lb_val = (fun (vp, v) -> join vp v);
    lb_aux = (fun (vl, annot) -> vl);
    pat_alg = pure_pat_alg bot join;
  }

let default_fold_fexp f x (FE_aux (FE_fexp (id, e), annot)) =
  let x, e = f x e in
  (x, FE_aux (FE_fexp (id, e), annot))

let default_fold_pexp f x (Pat_aux (pe, ann)) =
  let x, pe =
    match pe with
    | Pat_exp (p, e) ->
        let x, e = f x e in
        (x, Pat_exp (p, e))
    | Pat_when (p, e1, e2) ->
        let x, e1 = f x e1 in
        let x, e2 = f x e2 in
        (x, Pat_when (p, e1, e2))
  in
  (x, Pat_aux (pe, ann))

let default_fold_letbind f x (LB_aux (LB_val (p, e), ann)) =
  let x, e = f x e in
  (x, LB_aux (LB_val (p, e), ann))

let rec default_fold_lexp f x (LE_aux (le, ann) as lexp) =
  let re le = LE_aux (le, ann) in
  match le with
  | LE_id _ | LE_typ _ -> (x, lexp)
  | LE_deref e ->
      let x, e = f x e in
      (x, re (LE_deref e))
  | LE_app (id, es) ->
      let x, es =
        List.fold_left
          (fun (x, es) e ->
            let x, e' = f x e in
            (x, e' :: es)
          )
          (x, []) es
      in
      (x, re (LE_app (id, List.rev es)))
  | LE_tuple les ->
      let x, les =
        List.fold_left
          (fun (x, les) le ->
            let x, le' = default_fold_lexp f x le in
            (x, le' :: les)
          )
          (x, []) les
      in
      (x, re (LE_tuple (List.rev les)))
  | LE_vector_concat les ->
      let x, les =
        List.fold_left
          (fun (x, les) le ->
            let x, le' = default_fold_lexp f x le in
            (x, le' :: les)
          )
          (x, []) les
      in
      (x, re (LE_vector_concat (List.rev les)))
  | LE_vector (le, e) ->
      let x, le = default_fold_lexp f x le in
      let x, e = f x e in
      (x, re (LE_vector (le, e)))
  | LE_vector_range (le, e1, e2) ->
      let x, le = default_fold_lexp f x le in
      let x, e1 = f x e1 in
      let x, e2 = f x e2 in
      (x, re (LE_vector_range (le, e1, e2)))
  | LE_field (le, id) ->
      let x, le = default_fold_lexp f x le in
      (x, re (LE_field (le, id)))

let default_fold_exp f x (E_aux (e, ann) as exp) =
  let re e = E_aux (e, ann) in
  match e with
  | E_block es ->
      let x, es =
        List.fold_left
          (fun (x, es) e ->
            let x, e' = f x e in
            (x, e' :: es)
          )
          (x, []) es
      in
      (x, re (E_block (List.rev es)))
  | E_id _ | E_ref _ | E_lit _ -> (x, exp)
  | E_typ (typ, e) ->
      let x, e = f x e in
      (x, re (E_typ (typ, e)))
  | E_app (id, es) ->
      let x, es =
        List.fold_left
          (fun (x, es) e ->
            let x, e' = f x e in
            (x, e' :: es)
          )
          (x, []) es
      in
      (x, re (E_app (id, List.rev es)))
  | E_app_infix (e1, id, e2) ->
      let x, e1 = f x e1 in
      let x, e2 = f x e2 in
      (x, re (E_app_infix (e1, id, e2)))
  | E_tuple es ->
      let x, es =
        List.fold_left
          (fun (x, es) e ->
            let x, e' = f x e in
            (x, e' :: es)
          )
          (x, []) es
      in
      (x, re (E_tuple (List.rev es)))
  | E_if (e1, e2, e3) ->
      let x, e1 = f x e1 in
      let x, e2 = f x e2 in
      let x, e3 = f x e3 in
      (x, re (E_if (e1, e2, e3)))
  | E_for (id, e1, e2, e3, order, e4) ->
      let x, e1 = f x e1 in
      let x, e2 = f x e2 in
      let x, e3 = f x e3 in
      let x, e4 = f x e4 in
      (x, re (E_for (id, e1, e2, e3, order, e4)))
  | E_loop (loop_type, m, e1, e2) ->
      let x, m =
        match m with
        | Measure_aux (Measure_none, _) -> (x, m)
        | Measure_aux (Measure_some exp, l) ->
            let x, exp = f x exp in
            (x, Measure_aux (Measure_some exp, l))
      in
      let x, e1 = f x e1 in
      let x, e2 = f x e2 in
      (x, re (E_loop (loop_type, m, e1, e2)))
  | E_vector es ->
      let x, es =
        List.fold_left
          (fun (x, es) e ->
            let x, e' = f x e in
            (x, e' :: es)
          )
          (x, []) es
      in
      (x, re (E_vector (List.rev es)))
  | E_vector_access (e1, e2) ->
      let x, e1 = f x e1 in
      let x, e2 = f x e2 in
      (x, re (E_vector_access (e1, e2)))
  | E_vector_subrange (e1, e2, e3) ->
      let x, e1 = f x e1 in
      let x, e2 = f x e2 in
      let x, e3 = f x e3 in
      (x, re (E_vector_subrange (e1, e2, e3)))
  | E_vector_update (e1, e2, e3) ->
      let x, e1 = f x e1 in
      let x, e2 = f x e2 in
      let x, e3 = f x e3 in
      (x, re (E_vector_update (e1, e2, e3)))
  | E_vector_update_subrange (e1, e2, e3, e4) ->
      let x, e1 = f x e1 in
      let x, e2 = f x e2 in
      let x, e3 = f x e3 in
      let x, e4 = f x e4 in
      (x, re (E_vector_update_subrange (e1, e2, e3, e4)))
  | E_vector_append (e1, e2) ->
      let x, e1 = f x e1 in
      let x, e2 = f x e2 in
      (x, re (E_vector_append (e1, e2)))
  | E_list es ->
      let x, es =
        List.fold_left
          (fun (x, es) e ->
            let x, e' = f x e in
            (x, e' :: es)
          )
          (x, []) es
      in
      (x, re (E_list (List.rev es)))
  | E_cons (e1, e2) ->
      let x, e1 = f x e1 in
      let x, e2 = f x e2 in
      (x, re (E_cons (e1, e2)))
  | E_struct fexps ->
      let x, fexps =
        List.fold_left
          (fun (x, fes) fe ->
            let x, fe' = default_fold_fexp f x fe in
            (x, fe' :: fes)
          )
          (x, []) fexps
      in
      (x, re (E_struct (List.rev fexps)))
  | E_struct_update (e, fexps) ->
      let x, e = f x e in
      let x, fexps =
        List.fold_left
          (fun (x, fes) fe ->
            let x, fe' = default_fold_fexp f x fe in
            (x, fe' :: fes)
          )
          (x, []) fexps
      in
      (x, re (E_struct_update (e, List.rev fexps)))
  | E_field (e, id) ->
      let x, e = f x e in
      (x, re (E_field (e, id)))
  | E_match (e, pexps) ->
      let x, e = f x e in
      let x, pexps =
        List.fold_left
          (fun (x, pes) pe ->
            let x, pe' = default_fold_pexp f x pe in
            (x, pe' :: pes)
          )
          (x, []) pexps
      in
      (x, re (E_match (e, List.rev pexps)))
  | E_try (e, pexps) ->
      let x, e = f x e in
      let x, pexps =
        List.fold_left
          (fun (x, pes) pe ->
            let x, pe' = default_fold_pexp f x pe in
            (x, pe' :: pes)
          )
          (x, []) pexps
      in
      (x, re (E_try (e, List.rev pexps)))
  | E_let (letbind, e) ->
      let x, letbind = default_fold_letbind f x letbind in
      let x, e = f x e in
      (x, re (E_let (letbind, e)))
  | E_assign (lexp, e) ->
      let x, lexp = default_fold_lexp f x lexp in
      let x, e = f x e in
      (x, re (E_assign (lexp, e)))
  | E_sizeof _ | E_constraint _ -> (x, exp)
  | E_exit e ->
      let x, e = f x e in
      (x, re (E_exit e))
  | E_throw e ->
      let x, e = f x e in
      (x, re (E_throw e))
  | E_return e ->
      let x, e = f x e in
      (x, re (E_return e))
  | E_assert (e1, e2) ->
      let x, e1 = f x e1 in
      let x, e2 = f x e2 in
      (x, re (E_assert (e1, e2)))
  | E_var (lexp, e1, e2) ->
      let x, lexp = default_fold_lexp f x lexp in
      let x, e1 = f x e1 in
      let x, e2 = f x e2 in
      (x, re (E_var (lexp, e1, e2)))
  | E_internal_plet (pat, e1, e2) ->
      let x, e1 = f x e1 in
      let x, e2 = f x e2 in
      (x, re (E_internal_plet (pat, e1, e2)))
  | E_internal_return e ->
      let x, e = f x e in
      (x, re (E_internal_return e))
  | E_internal_value _ -> (x, exp)
  | E_internal_assume (nc, e) ->
      let x, e = f x e in
      (x, re (E_internal_assume (nc, e)))

let rec foldin_exp f x e = f (default_fold_exp (foldin_exp f)) x e
let foldin_pexp f x e = default_fold_pexp (foldin_exp f) x e
