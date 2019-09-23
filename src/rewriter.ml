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

type 'a rewriters = {
    rewrite_exp     : 'a rewriters -> 'a exp -> 'a exp;
    rewrite_lexp    : 'a rewriters -> 'a lexp -> 'a lexp;
    rewrite_pat     : 'a rewriters -> 'a pat -> 'a pat;
    rewrite_let     : 'a rewriters -> 'a letbind -> 'a letbind;
    rewrite_fun     : 'a rewriters -> 'a fundef -> 'a fundef;
    rewrite_mapping : 'a rewriters -> 'a mapdef -> 'a mapdef;
    rewrite_def     : 'a rewriters -> 'a def -> 'a def;
    rewrite_defs    : 'a rewriters -> 'a defs -> 'a defs;
  }

let effect_of_lexp (LEXP_aux (_,(_,a))) = effect_of_annot a
let effect_of_fexp (FE_aux (FE_Fexp (_, exp), _)) = effect_of exp
let effect_of_fexps fexps =
  List.fold_left union_effects no_effect (List.map effect_of_fexp fexps)
let effect_of_guard (G_aux (aux, _)) =
  match aux with
  | G_if exp -> effect_of exp
  | G_pattern (pat, exp) -> union_effects (effect_of_pat pat) (effect_of exp)
let effect_of_pexp (Pat_aux (Pat_case (p, gs, e), l)) =
  List.fold_left union_effects no_effect (effect_of_pat p :: effect_of e :: List.map effect_of_guard gs)
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
    | E_loop (_,_,e1,e2) -> union_eff_exps [e1;e2]
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
    | E_internal_cascade (e,fs,pexps) ->
       union_effects (List.fold_left union_effects no_effect (List.map (fun (id, Fallthrough pexps) ->
                                                                  List.fold_left union_effects no_effect (List.map effect_of_pexp pexps)) fs))
                     (List.fold_left union_effects (effect_of e) (List.map effect_of_pexp pexps))
    | E_internal_value v -> no_effect
  in
  E_aux (e, (l, mk_tannot env typ effsum))
| None ->
  E_aux (e, (l, empty_tannot (env_of_annot annot)))

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
  LEXP_aux (lexp, (l, empty_tannot (env_of_annot annot)))

let fix_eff_lb (LB_aux (lb,((l,_) as annot))) = match destruct_tannot (snd annot) with
| Some (env, typ, eff) ->
  let effsum = match lb with
    | LB_val (_,e) -> effect_of e in
  LB_aux (lb, (l, mk_tannot env typ effsum))
| None ->
  LB_aux (lb, (l, empty_tannot (env_of_annot annot)))

let rewrite_guard rewriters = function
  | G_aux (G_if exp, l) ->
     G_aux (G_if (rewriters.rewrite_exp rewriters exp), l)
  | G_aux (G_pattern (pat, exp), l) ->
     G_aux (G_pattern (rewriters.rewrite_pat rewriters pat, rewriters.rewrite_exp rewriters exp), l)

let rewrite_pexp rewriters =
  let rewrite = rewriters.rewrite_exp rewriters in
  function
  | Pat_aux (Pat_case(p, gs, e), pannot) ->
     Pat_aux (Pat_case(rewriters.rewrite_pat rewriters p, List.map (rewrite_guard rewriters) gs, rewrite e), pannot)

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
  | P_vector pats -> rewrap (P_vector(List.map rewrite pats))
  | P_vector_concat pats -> rewrap (P_vector_concat (List.map rewrite pats))
  | P_tup pats -> rewrap (P_tup (List.map rewrite pats))
  | P_list pats -> rewrap (P_list (List.map rewrite pats))
  | P_cons (pat1, pat2) -> rewrap (P_cons (rewrite pat1, rewrite pat2))
  | P_string_append pats -> rewrap (P_string_append (List.map rewrite pats))
  | P_view (pat, id, exps) -> rewrap (P_view (rewrite pat, id, List.map (rewriters.rewrite_exp rewriters) exps))

let rewrite_exp rewriters (E_aux (exp,(l,annot)) as orig_exp) =
  let rewrap e = E_aux (e,(l,annot)) in
  let rewrite = rewriters.rewrite_exp rewriters in
  match exp with
  | E_block exps -> rewrap (E_block (List.map rewrite exps))
  | E_id _ | E_lit _  -> rewrap exp
  | E_cast (typ, exp) -> rewrap (E_cast (typ, rewrite exp))
  | E_app (id,exps) -> rewrap (E_app (id,List.map rewrite exps))
  | E_app_infix(el,id,er) -> rewrap (E_app_infix(rewrite el,id,rewrite er))
  | E_tuple exps -> rewrap (E_tuple (List.map rewrite exps))
  | E_if (c,t,e) -> rewrap (E_if (rewrite c,rewrite t, rewrite e))
  | E_for (id, e1, e2, e3, o, body) ->
    rewrap (E_for (id, rewrite e1, rewrite e2, rewrite e3, o, rewrite body))
  | E_loop (loop, m, e1, e2) ->
     let m = match m with
       | Measure_aux (Measure_none,_) -> m
       | Measure_aux (Measure_some exp,l) -> Measure_aux (Measure_some (rewrite exp),l)
     in
    rewrap (E_loop (loop, m, rewrite e1, rewrite e2))
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
              (List.map (fun (FE_aux(FE_Fexp(id,e),l)) ->
                   FE_aux(FE_Fexp(id,rewrite e),l)) fexps))
  | E_record_update (re, fexps) ->
    rewrap (E_record_update ((rewrite re),
                             (List.map (fun (FE_aux(FE_Fexp(id,e),l)) ->
                                  FE_aux(FE_Fexp(id,rewrite e),l)) fexps)))
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

let rewrite_mapping rewriters (MD_aux (MD_mapping (id, args, tannot_opt, mapcls), (l, annot)))  = 
  let rewrite_mapcl (MCL_aux (aux, (l, annot))) =
    match aux with
    | MCL_forwards pexp -> MCL_aux (MCL_forwards (rewrite_pexp rewriters pexp), (l, annot))
    | MCL_backwards pexp -> MCL_aux (MCL_backwards (rewrite_pexp rewriters pexp), (l, annot))
    | MCL_bidir _ ->
       Reporting.unreachable l __POS__ "Bi-directional mapping clause should have been removed by type checker"
  in
  MD_aux (MD_mapping (id, List.map (rewrite_pat rewriters) args, tannot_opt, List.map rewrite_mapcl mapcls), (l, annot))

let rewrite_def rewriters d = match d with
  | DEF_reg_dec (DEC_aux (DEC_config (id, typ, exp), annot)) ->
     DEF_reg_dec (DEC_aux (DEC_config (id, typ, rewriters.rewrite_exp rewriters exp), annot))
  | DEF_type _ | DEF_spec _ | DEF_default _ | DEF_reg_dec _ | DEF_overload _ | DEF_fixity _ -> d
  | DEF_mapdef mdef -> DEF_mapdef (rewriters.rewrite_mapping rewriters mdef)
  | DEF_fundef fdef -> DEF_fundef (rewriters.rewrite_fun rewriters fdef)
  | DEF_internal_mutrec fdefs -> DEF_internal_mutrec (List.map (rewriters.rewrite_fun rewriters) fdefs)
  | DEF_val letbind -> DEF_val (rewriters.rewrite_let rewriters letbind)
  | DEF_pragma (pragma, arg, l) -> DEF_pragma (pragma, arg, l)
  | DEF_scattered _ -> raise (Reporting.err_unreachable Parse_ast.Unknown __POS__ "DEF_scattered survived to rewriter")
  | DEF_measure (id,pat,exp) -> DEF_measure (id,rewriters.rewrite_pat rewriters pat, rewriters.rewrite_exp rewriters exp)
  | DEF_loop_measures (id,_) -> raise (Reporting.err_unreachable (id_loc id) __POS__ "DEF_loop_measures survived to rewriter")

let rewrite_defs_base rewriters (Defs defs) =
  let rec rewrite ds = match ds with
    | [] -> []
    | d::ds -> (rewriters.rewrite_def rewriters d)::(rewrite ds) in
  Defs (rewrite defs)

let rewrite_defs_base_progress prefix rewriters (Defs defs) =
  let total = List.length defs in
  let rec rewrite n = function
    | [] -> []
    | d :: ds ->
       Util.progress (prefix ^ " ") (string_of_int n ^ "/" ^ string_of_int total) n total;
       let d = rewriters.rewrite_def rewriters d in
       d :: rewrite (n + 1) ds
  in
  Defs (rewrite 1 defs)

let rec takedrop n xs =
  match n, xs with
  | 0, _ -> [], xs
  | n, [] -> [], []
  | n, x :: xs ->
     let ys, xs = takedrop (n - 1) xs in
     x :: ys, xs

let rewrite_defs_base_parallel j rewriters (Defs defs) =
  let module IntMap = Map.Make(struct type t = int let compare = compare end) in
  let total = List.length defs in
  let defs = ref defs in

  (* We have a list of child processes in pids, and a mapping from pid
     to result location in results. *)
  let pids = ref [] in
  let results = ref IntMap.empty in
  for i = 1 to j do
    let work = if i = 1 then total / j + total mod j else total / j in
    let work, rest = takedrop work !defs in
    (* Create a temporary file where the child process will return it's result *)
    let result = Filename.temp_file "sail" ".rewrite" in
    let pid = Unix.fork () in
    begin
      if pid = 0 then
        let Defs work = rewrite_defs_base rewriters (Defs work) in
        let out_chan = open_out result in
        Marshal.to_channel out_chan work [Marshal.Closures];
        close_out out_chan;
        exit 0
      else
        (pids := pid :: !pids; results := IntMap.add pid result !results)
    end;
    defs := rest
  done;
  (* Make sure we haven't left any definitions behind! *)
  assert(List.length !defs = 0);

  let rewritten = ref [] in

  (* Now we wait for all our child processes *)
  while List.compare_length_with !pids 0 > 0 do
    let child = List.hd !pids in
    pids := List.tl !pids;
    let _, status = Unix.waitpid [] child in
    match status with
    | WEXITED 0 ->
       let result = IntMap.find child !results in
       let in_chan = open_in result in
       rewritten := Marshal.from_channel in_chan :: !rewritten;
       close_in in_chan;
       Sys.remove result
    | _ ->
       prerr_endline "Child process exited abnormally in parallel rewrite";
       exit 1
  done;
  Defs (List.concat !rewritten)

let rewriters_base =
  {rewrite_exp = rewrite_exp;
   rewrite_pat = rewrite_pat;
   rewrite_let = rewrite_let;
   rewrite_lexp = rewrite_lexp;
   rewrite_fun = rewrite_fun;
   rewrite_mapping = rewrite_mapping;
   rewrite_def = rewrite_def;
   rewrite_defs = rewrite_defs_base}

let rewrite_defs (Defs defs) = rewrite_defs_base rewriters_base (Defs defs)

type ('a,
      'exp, 'exp_aux,
      'lexp, 'lexp_aux,
      'fexp, 'fexp_aux,
      'guard, 'guard_aux,
      'pexp, 'pexp_aux,
      'letbind_aux, 'letbind,
      'pat, 'pat_aux) algebra =
 { e_block                  : 'exp list -> 'exp_aux
 ; e_id                     : id -> 'exp_aux
 ; e_ref                    : id -> 'exp_aux
 ; e_lit                    : lit -> 'exp_aux
 ; e_cast                   : Ast.typ * 'exp -> 'exp_aux
 ; e_app                    : id * 'exp list -> 'exp_aux
 ; e_app_infix              : 'exp * id * 'exp -> 'exp_aux
 ; e_tuple                  : 'exp list -> 'exp_aux
 ; e_if                     : 'exp * 'exp * 'exp -> 'exp_aux
 ; e_for                    : id * 'exp * 'exp * 'exp * Ast.order * 'exp -> 'exp_aux
 ; e_loop                   : loop * ('exp option * Parse_ast.l) * 'exp * 'exp -> 'exp_aux
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
 ; e_var                    : 'lexp * 'exp * 'exp -> 'exp_aux
 ; e_internal_plet          : 'pat * 'exp * 'exp -> 'exp_aux
 ; e_internal_return        : 'exp -> 'exp_aux
 ; e_internal_cascade       : 'exp * (id * 'pexp list) list * 'pexp list -> 'exp_aux
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
 ; fE_aux                   : 'fexp_aux * l -> 'fexp
 ; g_aux                    : 'guard_aux * l -> 'guard
 ; g_if                     : 'exp -> 'guard_aux
 ; g_pattern                : 'pat * 'exp -> 'guard_aux
 ; pat_case                 : 'pat * 'guard list * 'exp -> 'pexp_aux
 ; pat_aux                  : 'pexp_aux * l -> 'pexp
 ; lB_val                   : 'pat * 'exp -> 'letbind_aux
 ; lB_aux                   : 'letbind_aux * 'a annot -> 'letbind
 ; p_lit                    : lit -> 'pat_aux
 ; p_wild                   : 'pat_aux
 ; p_or                     : 'pat * 'pat -> 'pat_aux
 ; p_not                    : 'pat -> 'pat_aux
 ; p_as                     : 'pat * id -> 'pat_aux
 ; p_typ                    : Ast.typ * 'pat -> 'pat_aux
 ; p_id                     : id -> 'pat_aux
 ; p_var                    : 'pat * typ_pat -> 'pat_aux
 ; p_app                    : id * 'pat list -> 'pat_aux
 ; p_vector                 : 'pat list -> 'pat_aux
 ; p_vector_concat          : 'pat list -> 'pat_aux
 ; p_tup                    : 'pat list -> 'pat_aux
 ; p_list                   : 'pat list -> 'pat_aux
 ; p_cons                   : 'pat * 'pat -> 'pat_aux
 ; p_string_append          : 'pat list -> 'pat_aux
 ; p_view                   : 'pat * id * 'exp list -> 'pat_aux
 ; p_aux                    : 'pat_aux * 'a annot -> 'pat
 }

let rec fold_pat_aux (alg : ('a,'exp,'exp_aux,'lexp,'lexp_aux,'fexp,'fexp_aux,
                             'guard,'guard_aux,'pexp,'pexp_aux,'letbind_aux,'letbind,
                             'pat,'pat_aux) algebra) : 'a pat_aux -> 'pat_aux =
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
  | P_vector ps         -> alg.p_vector (List.map (fold_pat alg) ps)
  | P_vector_concat ps  -> alg.p_vector_concat (List.map (fold_pat alg) ps)
  | P_tup ps            -> alg.p_tup (List.map (fold_pat alg) ps)
  | P_list ps           -> alg.p_list (List.map (fold_pat alg) ps)
  | P_cons (ph,pt)      -> alg.p_cons (fold_pat alg ph, fold_pat alg pt)
  | P_string_append ps  -> alg.p_string_append (List.map (fold_pat alg) ps)
  | P_view (p,id,exps)  -> alg.p_view (fold_pat alg p, id, List.map (fold_exp alg) exps)

and fold_pat (alg : ('a,'exp,'exp_aux,'lexp,'lexp_aux,'fexp,'fexp_aux,
                     'guard,'guard_aux,'pexp,'pexp_aux,'letbind_aux,'letbind,
                     'pat,'pat_aux) algebra) : 'a pat -> 'pat =
  function
  | P_aux (pat,annot)   -> alg.p_aux (fold_pat_aux alg pat,annot)

and fold_exp_aux (alg : ('a,'exp,'exp_aux,'lexp,'lexp_aux,'fexp,'fexp_aux,
                         'guard,'guard_aux,'pexp,'pexp_aux,'letbind_aux,'letbind,
                         'pat,'pat_aux) algebra) : 'a exp_aux -> 'exp_aux =
  function
  | E_block es -> alg.e_block (List.map (fold_exp alg) es)
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
  | E_loop (loop_type, m, e1, e2) ->
     let m = match m with
       | Measure_aux (Measure_none,l) -> None,l
       | Measure_aux (Measure_some exp,l) -> Some (fold_exp alg exp),l
     in
     alg.e_loop (loop_type, m, fold_exp alg e1, fold_exp alg e2)
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
     alg.e_internal_plet (fold_pat alg pat, fold_exp alg e1, fold_exp alg e2)
  | E_internal_return e -> alg.e_internal_return (fold_exp alg e)
  | E_internal_cascade (e,fs,pexps) -> alg.e_internal_cascade (fold_exp alg e, List.map (fun (id, Fallthrough f) -> id, List.map (fold_pexp alg) f) fs, List.map (fold_pexp alg) pexps)
  | E_internal_value v -> alg.e_internal_value v

and fold_exp (alg : ('a,'exp,'exp_aux,'lexp,'lexp_aux,'fexp,'fexp_aux,
                     'guard,'guard_aux,'pexp,'pexp_aux,'letbind_aux,'letbind,
                     'pat,'pat_aux) algebra) (E_aux (exp_aux,annot) : 'a exp) : 'exp =
  alg.e_aux (fold_exp_aux alg exp_aux, annot)

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
and fold_fexp alg (FE_aux (fexp_aux, l)) = alg.fE_aux (fold_fexp_aux alg fexp_aux, l)

and fold_guard_aux alg = function
  | G_if exp -> alg.g_if (fold_exp alg exp)
  | G_pattern (pat, exp) -> alg.g_pattern (fold_pat alg pat, fold_exp alg exp)
and fold_guard alg (G_aux (guard_aux, l)) = alg.g_aux (fold_guard_aux alg guard_aux, l)

and fold_pexp_aux alg (Pat_case (pat,guards,e)) = alg.pat_case (fold_pat alg pat, List.map (fold_guard alg) guards, fold_exp alg e)
and fold_pexp alg (Pat_aux (pexp_aux,l)) = alg.pat_aux (fold_pexp_aux alg pexp_aux, l)

and fold_letbind_aux alg (LB_val (pat,e)) = alg.lB_val (fold_pat alg pat, fold_exp alg e)
and fold_letbind alg (LB_aux (letbind_aux,annot)) = alg.lB_aux (fold_letbind_aux alg letbind_aux, annot)

let fold_funcl alg (FCL_aux (FCL_Funcl (id, pexp), annot)) =
  FCL_aux (FCL_Funcl (id, fold_pexp alg pexp), annot)

let fold_function alg (FD_aux (FD_function (rec_opt, tannot_opt, effect_opt, funcls), annot)) =
  FD_aux (FD_function (rec_opt, tannot_opt, effect_opt, List.map (fold_funcl alg) funcls), annot)

let id_algebra =
  { e_block = (fun es -> E_block es)
  ; e_id = (fun id -> E_id id)
  ; e_ref = (fun id -> E_ref id)
  ; e_lit = (fun lit -> (E_lit lit))
  ; e_cast = (fun (typ,e) -> E_cast (typ,e))
  ; e_app = (fun (id,es) -> E_app (id,es))
  ; e_app_infix = (fun (e1,id,e2) -> E_app_infix (e1,id,e2))
  ; e_tuple = (fun es -> E_tuple es)
  ; e_if = (fun (e1,e2,e3) -> E_if (e1,e2,e3))
  ; e_for = (fun (id,e1,e2,e3,order,e4) -> E_for (id,e1,e2,e3,order,e4))
  ; e_loop = (fun (lt, (m,l), e1, e2) ->
    let m = match m with None -> Measure_none | Some e -> Measure_some e in
    E_loop (lt, Measure_aux (m,l), e1, e2))
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
  ; e_internal_cascade = (fun (e, fs, pexps) -> E_internal_cascade (e, List.map (fun (id, pexps) -> id, Fallthrough pexps) fs, pexps))
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
  ; fE_aux = (fun (fexp,l) -> FE_aux (fexp,l))
  ; g_if = (fun exp -> G_if exp)
  ; g_pattern = (fun (pat, exp) -> G_pattern (pat, exp))
  ; g_aux = (fun (guard,l) -> G_aux (guard, l))
  ; pat_case = (fun (pat,guards,e) -> (Pat_case (pat,guards,e)))
  ; pat_aux = (fun (pexp,a) -> (Pat_aux (pexp,a)))
  ; lB_val = (fun (pat,e) -> LB_val (pat,e))
  ; lB_aux = (fun (lb,annot) -> LB_aux (lb,annot))
  ; p_lit = (fun lit -> P_lit lit)
  ; p_wild = P_wild
  ; p_or = (fun (pat1, pat2) -> P_or(pat1, pat2))
  ; p_not = (fun pat -> P_not(pat))
  ; p_as = (fun (pat,id) -> P_as (pat,id))
  ; p_typ = (fun (typ,pat) -> P_typ (typ,pat))
  ; p_id = (fun id -> P_id id)
  ; p_var = (fun (pat,tpat) -> P_var (pat,tpat))
  ; p_app = (fun (id,ps) -> P_app (id,ps))
  ; p_vector = (fun ps -> P_vector ps)
  ; p_vector_concat  = (fun ps -> P_vector_concat ps)
  ; p_tup = (fun ps -> P_tup ps)
  ; p_list = (fun ps -> P_list ps)
  ; p_cons = (fun (ph,pt) -> P_cons (ph,pt))
  ; p_string_append  = (fun (ps) -> P_string_append (ps))
  ; p_view = (fun (pat,id,exps) -> P_view (pat,id,exps))
  ; p_aux = (fun (pat,annot) -> P_aux (pat,annot))
  }

(* Folding algorithms for not only rewriting patterns/expressions, but also
   computing some additional value. Usage: Pass default value (bot) and a
   binary join operator as arguments, and specify the non-default cases of
   rewriting/computation by overwriting fields of the record. *)
let compute_algebra bot join =
  let join_list vs = List.fold_left join bot vs in
  let split_join f es = let (vs,es) = List.split es in (join_list vs, f es) in
  { e_block = split_join (fun es -> E_block es)
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
  ; e_loop = (fun (lt, (m,l), (v1, e1), (v2, e2)) ->
    let vs,m = match m with
    | None -> [], Measure_none
    | Some (v,e) -> [v], Measure_some e
    in
    (join_list (vs@[v1;v2]), E_loop (lt, Measure_aux (m,l), e1, e2)))
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
  ; e_internal_cascade = (fun ((v,e),fs,pexps) ->
    let acc = ref v in
    let fs = List.map (fun (id, pexps) -> id, Fallthrough (List.map (fun (v, pexp) -> acc := join !acc v; pexp) pexps)) fs in
    let pexps = List.map (fun (v, pexp) -> acc := join !acc v; pexp) pexps in
    !acc, E_internal_cascade (e,fs,pexps)
  )
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
  ; fE_aux = (fun ((vf,fexp),l) -> (vf, FE_aux (fexp,l)))
  ; g_if = (fun (ve, e) -> (ve, G_if e))
  ; g_pattern = (fun ((vp, pat), (ve, e)) -> (join vp ve, G_pattern (pat, e)))
  ; g_aux = (fun ((v,guard),l) -> (v, G_aux (guard, l)))
  ; pat_case = (fun ((vp, pat), guards, (ve, e)) -> (join_list (vp :: ve :: List.map fst guards), Pat_case (pat, List.map snd guards, e)))
  ; pat_aux = (fun ((v,pexp),a) -> (v, Pat_aux (pexp,a)))
  ; lB_val = (fun ((vp,pat),(v,e)) -> (join vp v, LB_val (pat,e)))
  ; lB_aux = (fun ((vl,lb),annot) -> (vl,LB_aux (lb,annot)))
  ; p_lit = (fun lit -> (bot, P_lit lit))
  ; p_wild = (bot, P_wild)
  ; p_or = (fun ((v1, pat1), (v2, pat2)) -> (join v1 v2, P_or(pat1, pat2)))
  ; p_not = (fun (v, pat) -> (v, P_not(pat)))
  ; p_as = (fun ((v,pat),id) -> (v, P_as (pat,id)))
  ; p_typ = (fun (typ,(v,pat)) -> (v, P_typ (typ,pat)))
  ; p_id = (fun id -> (bot, P_id id))
  ; p_var = (fun ((v,pat),kid) -> (v, P_var (pat,kid)))
  ; p_app = (fun (id,ps) -> split_join (fun ps -> P_app (id,ps)) ps)
  ; p_vector = split_join (fun ps -> P_vector ps)
  ; p_vector_concat  = split_join (fun ps -> P_vector_concat ps)
  ; p_tup = split_join (fun ps -> P_tup ps)
  ; p_list = split_join (fun ps -> P_list ps)
  ; p_cons = (fun ((vh,ph),(vt,pt)) -> (join vh vt, P_cons (ph,pt)))
  ; p_view = (fun ((v, pat), id, exps) -> (join_list (v :: List.map fst exps), P_view (pat, id, List.map snd exps)))
  ; p_string_append  = split_join (fun ps -> P_string_append ps)
  ; p_aux = (fun ((v,pat),annot) -> (v, P_aux (pat,annot)))
  }

let pure_algebra bot join =
  let join_list vs = List.fold_left join bot vs in
  { e_block = join_list
  ; e_id = (fun id -> bot)
  ; e_ref = (fun id -> bot)
  ; e_lit = (fun lit -> bot)
  ; e_cast = (fun (typ,v) -> v)
  ; e_app = (fun (id,es) -> join_list es)
  ; e_app_infix = (fun (v1,id,v2) -> join v1 v2)
  ; e_tuple = join_list
  ; e_if = (fun (v1,v2,v3) -> join_list [v1;v2;v3])
  ; e_for = (fun (id,v1,v2,v3,order,v4) -> join_list [v1;v2;v3;v4])
  ; e_loop = (fun (lt, (m,_), v1, v2) ->
    let v = join v1 v2 in match m with None -> v | Some v' -> join v v')
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
  ; e_internal_cascade = (fun (v,fs,vs) -> join_list (v :: List.concat (List.map snd fs) @ vs))
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
  ; fE_aux = (fun (vf,l) -> vf)
  ; g_if = (fun v -> v)
  ; g_pattern = (fun (vp, v) -> join vp v)
  ; g_aux = (fun (v, l) -> v)
  ; pat_case = (fun (vp,vs,v) -> join_list (vp :: v :: vs))
  ; pat_aux = (fun (v,l) -> v)
  ; lB_val = (fun (vp,v) -> join vp v)
  ; lB_aux = (fun (vl,annot) -> vl)
  ; p_lit = (fun lit -> bot)
  ; p_wild = bot
  ; p_or = (fun (v1, v2) -> join v1 v2)
  ; p_not = (fun v -> v)
  ; p_as = (fun (v,id) -> v)
  ; p_typ = (fun (typ,v) -> v)
  ; p_id = (fun id -> bot)
  ; p_var = (fun (v,kid) -> v)
  ; p_app = (fun (id,ps) -> join_list ps)
  ; p_vector = join_list
  ; p_vector_concat = join_list
  ; p_tup = join_list
  ; p_list = join_list
  ; p_string_append = join_list
  ; p_view = (fun (v, _, vs) -> join_list (v :: vs))
  ; p_cons = (fun (vh,vt) -> join vh vt)
  ; p_aux = (fun (v,annot) -> v)
  }

let default_fold_fexp f x (FE_aux (FE_Fexp (id,e),l)) =
  let x,e = f x e in
  x, FE_aux (FE_Fexp (id,e),l)

let default_fold_pexp f x (Pat_aux (pe,ann)) =
  let x,pe = match pe with
  | Pat_case (p,gs,e) ->
     let x,e = f x e in
     x,Pat_case (p,gs,e)
  in x, Pat_aux (pe,ann)

let default_fold_letbind f x (LB_aux (LB_val (p,e),ann)) =
  let x,e = f x e in
  x, LB_aux (LB_val (p,e),ann)

let rec default_fold_lexp f x (LEXP_aux (le,ann) as lexp) =
  let re le = LEXP_aux (le,ann) in
  match le with
  | LEXP_id _
  | LEXP_cast _
    -> x, lexp
  | LEXP_deref e ->
     let x, e = f x e in
     x, re (LEXP_deref e)
  | LEXP_memory (id,es) ->
     let x,es = List.fold_left (fun (x,es) e ->
                    let x,e' = f x e in x,e'::es) (x,[]) es in
     x, re (LEXP_memory (id, List.rev es))
  | LEXP_tup les ->
     let x,les = List.fold_left (fun (x,les) le ->
                    let x,le' = default_fold_lexp f x le in x,le'::les) (x,[]) les in
     x, re (LEXP_tup (List.rev les))
  | LEXP_vector_concat les ->
     let x,les = List.fold_left (fun (x,les) le ->
                    let x,le' = default_fold_lexp f x le in x,le'::les) (x,[]) les in
     x, re (LEXP_vector_concat (List.rev les))
  | LEXP_vector (le,e) ->
     let x, le = default_fold_lexp f x le in
     let x, e = f x e in
     x, re (LEXP_vector (le,e))
  | LEXP_vector_range (le,e1,e2) ->
     let x, le = default_fold_lexp f x le in
     let x, e1 = f x e1 in
     let x, e2 = f x e2 in
     x, re (LEXP_vector_range (le,e1,e2))
  | LEXP_field (le,id) ->
     let x, le = default_fold_lexp f x le in
     x, re (LEXP_field (le,id))

let default_fold_exp f x (E_aux (e,ann) as exp) =
  let re e = E_aux (e,ann) in
  match e with
  | E_block es ->
     let x,es = List.fold_left (fun (x,es) e ->
                    let x,e' = f x e in x,e'::es) (x,[]) es in
     x, re (E_block (List.rev es))
  | E_id _
  | E_ref _
  | E_lit _ -> x, exp
  | E_cast (typ,e) ->
     let x,e = f x e in
     x, re (E_cast (typ,e))
  | E_app (id,es) ->
     let x,es = List.fold_left (fun (x,es) e ->
                    let x,e' = f x e in x,e'::es) (x,[]) es in
     x, re (E_app (id, List.rev es))
  | E_app_infix (e1,id,e2) ->
     let x,e1 = f x e1 in
     let x,e2 = f x e2 in
     x, re (E_app_infix (e1,id,e2))
  | E_tuple es ->
     let x,es = List.fold_left (fun (x,es) e ->
                    let x,e' = f x e in x,e'::es) (x,[]) es in
     x, re (E_tuple (List.rev es))
  | E_if (e1,e2,e3) ->
     let x,e1 = f x e1 in
     let x,e2 = f x e2 in
     let x,e3 = f x e3 in
     x, re (E_if (e1,e2,e3))
  | E_for (id,e1,e2,e3,order,e4) ->
     let x,e1 = f x e1 in
     let x,e2 = f x e2 in
     let x,e3 = f x e3 in
     let x,e4 = f x e4 in
     x, re (E_for (id,e1,e2,e3,order,e4))
  | E_loop (loop_type, m, e1, e2) ->
     let x,m = match m with
       | Measure_aux (Measure_none,_) -> x,m
       | Measure_aux (Measure_some exp,l) ->
          let x, exp = f x exp in
          x, Measure_aux (Measure_some exp,l)
     in
     let x,e1 = f x e1 in
     let x,e2 = f x e2 in
     x, re (E_loop (loop_type, m, e1, e2))
  | E_vector es ->
     let x,es = List.fold_left (fun (x,es) e ->
                    let x,e' = f x e in x,e'::es) (x,[]) es in
     x, re (E_vector (List.rev es))
  | E_vector_access (e1,e2) ->
     let x,e1 = f x e1 in
     let x,e2 = f x e2 in
     x, re (E_vector_access (e1,e2))
  | E_vector_subrange (e1,e2,e3) ->
     let x,e1 = f x e1 in
     let x,e2 = f x e2 in
     let x,e3 = f x e3 in
     x, re (E_vector_subrange (e1,e2,e3))
  | E_vector_update (e1,e2,e3) ->
     let x,e1 = f x e1 in
     let x,e2 = f x e2 in
     let x,e3 = f x e3 in
     x, re (E_vector_update (e1,e2,e3))
  | E_vector_update_subrange (e1,e2,e3,e4) ->
     let x,e1 = f x e1 in
     let x,e2 = f x e2 in
     let x,e3 = f x e3 in
     let x,e4 = f x e4 in
     x, re (E_vector_update_subrange (e1,e2,e3,e4))
  | E_vector_append (e1,e2) ->
     let x,e1 = f x e1 in
     let x,e2 = f x e2 in
     x, re (E_vector_append (e1,e2))
  | E_list es ->
     let x,es = List.fold_left (fun (x,es) e ->
                    let x,e' = f x e in x,e'::es) (x,[]) es in
     x, re (E_list (List.rev es))
  | E_cons (e1,e2) ->
     let x,e1 = f x e1 in
     let x,e2 = f x e2 in
     x, re (E_cons (e1,e2))
  | E_record fexps ->
     let x,fexps = List.fold_left (fun (x,fes) fe ->
                       let x,fe' = default_fold_fexp f x fe in x,fe'::fes) (x,[]) fexps in
     x, re (E_record (List.rev fexps))
  | E_record_update (e,fexps) ->
     let x,e = f x e in
     let x,fexps = List.fold_left (fun (x,fes) fe ->
                       let x,fe' = default_fold_fexp f x fe in x,fe'::fes) (x,[]) fexps in
     x, re (E_record_update (e, List.rev fexps))
  | E_field (e,id) ->
     let x,e = f x e in x, re (E_field (e,id))
  | E_case (e,pexps) ->
     let x,e = f x e in
     let x,pexps = List.fold_left (fun (x,pes) pe ->
                       let x,pe' = default_fold_pexp f x pe in x,pe'::pes) (x,[]) pexps in
     x, re (E_case (e, List.rev pexps))
  | E_try (e,pexps) ->
     let x,e = f x e in
     let x,pexps = List.fold_left (fun (x,pes) pe ->
                       let x,pe' = default_fold_pexp f x pe in x,pe'::pes) (x,[]) pexps in
     x, re (E_try (e, List.rev pexps))
  | E_let (letbind,e) ->
     let x,letbind = default_fold_letbind f x letbind in
     let x,e = f x e in
     x, re (E_let (letbind,e))
  | E_assign (lexp,e) ->
     let x,lexp = default_fold_lexp f x lexp in
     let x,e = f x e in
     x, re (E_assign (lexp,e))
  | E_sizeof _
  | E_constraint _
    -> x,exp
  | E_exit e ->
     let x,e = f x e in x, re (E_exit e)
  | E_throw e ->
     let x,e = f x e in x, re (E_throw e)
  | E_return e ->
     let x,e = f x e in x, re (E_return e)
  | E_assert(e1,e2) ->
     let x,e1 = f x e1 in
     let x,e2 = f x e2 in
     x, re (E_assert (e1,e2))
  | E_var (lexp,e1,e2) ->
     let x,lexp = default_fold_lexp f x lexp in
     let x,e1 = f x e1 in
     let x,e2 = f x e2 in
     x, re (E_var (lexp,e1,e2))
  | E_internal_plet (pat,e1,e2) ->
     let x,e1 = f x e1 in
     let x,e2 = f x e2 in
     x, re (E_internal_plet (pat,e1,e2))
  | E_internal_return e ->
     let x,e = f x e in x, re (E_internal_return e)
  | E_internal_value _ -> x,exp

let rec foldin_exp f x e = f (default_fold_exp (foldin_exp f)) x e
let rec foldin_pexp f x e = default_fold_pexp (foldin_exp f) x e
