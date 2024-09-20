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
(*  SPDX-License-Identifier: BSD-2-Clause                                   *)
(****************************************************************************)

open Ast
open Ast_defs
open Ast_util
open Util

(* Functions for finding the set of variables assigned to.  Used in constant propagation
   and monomorphisation. *)

let assigned_vars exp =
  Rewriter.fold_exp
    {
      (Rewriter.pure_exp_alg IdSet.empty IdSet.union) with
      Rewriter.le_id = (fun id -> IdSet.singleton id);
      Rewriter.le_typ = (fun (ty, id) -> IdSet.singleton id);
    }
    exp

let assigned_vars_in_fexps fes =
  List.fold_left (fun vs (FE_aux (FE_fexp (_, e), _)) -> IdSet.union vs (assigned_vars e)) IdSet.empty fes

let assigned_vars_in_pexp (Pat_aux (p, _)) =
  match p with
  | Pat_exp (_, e) -> assigned_vars e
  | Pat_when (p, e1, e2) -> IdSet.union (assigned_vars e1) (assigned_vars e2)

let rec assigned_vars_in_lexp (LE_aux (le, _)) =
  match le with
  | LE_id id | LE_typ (_, id) -> IdSet.singleton id
  | LE_tuple lexps | LE_vector_concat lexps ->
      List.fold_left (fun vs le -> IdSet.union vs (assigned_vars_in_lexp le)) IdSet.empty lexps
  | LE_app (_, es) -> List.fold_left (fun vs e -> IdSet.union vs (assigned_vars e)) IdSet.empty es
  | LE_vector (le, e) -> IdSet.union (assigned_vars_in_lexp le) (assigned_vars e)
  | LE_vector_range (le, e1, e2) ->
      IdSet.union (assigned_vars_in_lexp le) (IdSet.union (assigned_vars e1) (assigned_vars e2))
  | LE_field (le, _) -> assigned_vars_in_lexp le
  | LE_deref e -> assigned_vars e

let bound_vars exp =
  let open Rewriter in
  let pat_alg =
    { (pure_pat_alg IdSet.empty IdSet.union) with p_id = IdSet.singleton; p_as = (fun (ids, id) -> IdSet.add id ids) }
  in
  fold_exp { (pure_exp_alg IdSet.empty IdSet.union) with pat_alg } exp

let pat_id_is_variable env id =
  match Type_check.Env.lookup_id id env with
  (* Unbound is returned for both variables and constructors which take
     arguments, but the latter only don't appear in a P_id *)
  | Unbound _
  (* Shadowing of immutable locals is allowed; mutable locals and registers
     are rejected by the type checker, so don't matter *)
  | Local _ | Register _ ->
      true
  | Enum _ -> false

let bindings_from_pat p =
  let rec aux_pat (P_aux (p, (l, annot))) =
    let env = Type_check.env_of_annot (l, annot) in
    match p with
    | P_lit _ | P_wild -> []
    | P_or (p1, p2) -> aux_pat p1 @ aux_pat p2
    | P_not p -> aux_pat p
    | P_as (p, id) -> id :: aux_pat p
    | P_typ (_, p) -> aux_pat p
    | P_vector_subrange (id, _, _) -> [id]
    | P_id id -> if pat_id_is_variable env id then [id] else []
    | P_var (p, kid) -> aux_pat p
    | P_vector ps | P_vector_concat ps | P_string_append ps | P_app (_, ps) | P_tuple ps | P_list ps ->
        List.concat (List.map aux_pat ps)
    | P_cons (p1, p2) -> aux_pat p1 @ aux_pat p2
    | P_struct (fps, _) -> List.map snd fps |> List.map aux_pat |> List.concat
  in
  aux_pat p

(* TODO: replace the below with solutions that don't depend so much on the
   structure of the environment. *)

let rec flatten_constraints = function
  | [] -> []
  | NC_aux (NC_and (nc1, nc2), _) :: t -> flatten_constraints (nc1 :: nc2 :: t)
  | h :: t -> h :: flatten_constraints t

(* NB: this only looks for direct equalities with the given kid.  It would be
   better in principle to find the entire set of equal kids, but it isn't
   necessary to deal with the fresh kids produced by the type checker while
   checking P_var patterns, so we don't do it for now. *)
let equal_kids_ncs kid ncs =
  let rec add_equal_kids_nc s = function
    | NC_aux
        (NC_equal (A_aux (A_nexp (Nexp_aux (Nexp_var var1, _)), _), A_aux (A_nexp (Nexp_aux (Nexp_var var2, _)), _)), _)
      ->
        if Kid.compare kid var1 == 0 then KidSet.add var2 s
        else if Kid.compare kid var2 == 0 then KidSet.add var1 s
        else s
    | NC_aux (NC_and (nc1, nc2), _) -> add_equal_kids_nc (add_equal_kids_nc s nc1) nc2
    | _ -> s
  in
  List.fold_left add_equal_kids_nc (KidSet.singleton kid) ncs

let equal_kids env kid =
  let ncs = flatten_constraints (Type_check.Env.get_constraints env) in
  equal_kids_ncs kid ncs

(* TODO: kid shadowing *)
let nexp_subst_fns substs =
  let s_t t = subst_kids_typ substs t in
  (* let s_typschm (TypSchm_aux (TypSchm_ts (q,t),l)) = TypSchm_aux (TypSchm_ts (q,s_t t),l) in
     hopefully don't need this anyway *)
  (*
  let s_typschm tsh = tsh in*)
  let s_tannot tannot =
    match Type_check.destruct_tannot tannot with
    | None -> tannot
    | Some (_env, t) -> Type_check.replace_typ (s_t t) tannot
    (* TODO: what about env? *)
  in
  let rec s_pat (P_aux (p, (l, annot))) =
    let re p = P_aux (p, (l, s_tannot annot)) in
    match p with
    | P_lit _ | P_wild | P_id _ | P_vector_subrange _ -> re p
    | P_or (p1, p2) -> re (P_or (s_pat p1, s_pat p2))
    | P_not p -> re (P_not (s_pat p))
    | P_var (p', tpat) -> re (P_var (s_pat p', tpat))
    | P_as (p', id) -> re (P_as (s_pat p', id))
    | P_typ (ty, p') -> re (P_typ (s_t ty, s_pat p'))
    | P_app (id, ps) -> re (P_app (id, List.map s_pat ps))
    | P_vector ps -> re (P_vector (List.map s_pat ps))
    | P_vector_concat ps -> re (P_vector_concat (List.map s_pat ps))
    | P_string_append ps -> re (P_string_append (List.map s_pat ps))
    | P_tuple ps -> re (P_tuple (List.map s_pat ps))
    | P_list ps -> re (P_list (List.map s_pat ps))
    | P_cons (p1, p2) -> re (P_cons (s_pat p1, s_pat p2))
    | P_struct (fps, fwild) -> re (P_struct (List.map (fun (field, p) -> (field, s_pat p)) fps, fwild))
  in
  let rec s_exp (E_aux (e, (l, annot))) =
    let re e = E_aux (e, (l, s_tannot annot)) in
    match e with
    | E_block es -> re (E_block (List.map s_exp es))
    | E_id _ | E_ref _ | E_lit _ | E_internal_value _ -> re e
    | E_sizeof ne -> begin
        let ne' = subst_kids_nexp substs ne in
        match ne' with Nexp_aux (Nexp_constant i, l) -> re (E_lit (L_aux (L_num i, l))) | _ -> re (E_sizeof ne')
      end
    | E_constraint nc -> re (E_constraint (subst_kids_nc substs nc))
    | E_typ (t, e') -> re (E_typ (s_t t, s_exp e'))
    | E_app (id, es) -> re (E_app (id, List.map s_exp es))
    | E_app_infix (e1, id, e2) -> re (E_app_infix (s_exp e1, id, s_exp e2))
    | E_tuple es -> re (E_tuple (List.map s_exp es))
    | E_if (e1, e2, e3) -> re (E_if (s_exp e1, s_exp e2, s_exp e3))
    | E_for (id, e1, e2, e3, ord, e4) -> re (E_for (id, s_exp e1, s_exp e2, s_exp e3, ord, s_exp e4))
    | E_loop (loop, m, e1, e2) -> re (E_loop (loop, s_measure m, s_exp e1, s_exp e2))
    | E_vector es -> re (E_vector (List.map s_exp es))
    | E_vector_access (e1, e2) -> re (E_vector_access (s_exp e1, s_exp e2))
    | E_vector_subrange (e1, e2, e3) -> re (E_vector_subrange (s_exp e1, s_exp e2, s_exp e3))
    | E_vector_update (e1, e2, e3) -> re (E_vector_update (s_exp e1, s_exp e2, s_exp e3))
    | E_vector_update_subrange (e1, e2, e3, e4) -> re (E_vector_update_subrange (s_exp e1, s_exp e2, s_exp e3, s_exp e4))
    | E_vector_append (e1, e2) -> re (E_vector_append (s_exp e1, s_exp e2))
    | E_list es -> re (E_list (List.map s_exp es))
    | E_cons (e1, e2) -> re (E_cons (s_exp e1, s_exp e2))
    | E_struct fes -> re (E_struct (List.map s_fexp fes))
    | E_struct_update (e, fes) -> re (E_struct_update (s_exp e, List.map s_fexp fes))
    | E_field (e, id) -> re (E_field (s_exp e, id))
    | E_match (e, cases) -> re (E_match (s_exp e, List.map s_pexp cases))
    | E_let (lb, e) -> re (E_let (s_letbind lb, s_exp e))
    | E_assign (le, e) -> re (E_assign (s_lexp le, s_exp e))
    | E_exit e -> re (E_exit (s_exp e))
    | E_return e -> re (E_return (s_exp e))
    | E_assert (e1, e2) -> re (E_assert (s_exp e1, s_exp e2))
    | E_var (le, e1, e2) -> re (E_var (s_lexp le, s_exp e1, s_exp e2))
    | E_internal_plet (p, e1, e2) -> re (E_internal_plet (s_pat p, s_exp e1, s_exp e2))
    | E_internal_return e -> re (E_internal_return (s_exp e))
    | E_throw e -> re (E_throw (s_exp e))
    | E_try (e, cases) -> re (E_try (s_exp e, List.map s_pexp cases))
    | E_internal_assume (nc, e) -> re (E_internal_assume (subst_kids_nc substs nc, s_exp e))
  and s_measure (Measure_aux (m, l)) =
    let m = match m with Measure_none -> m | Measure_some exp -> Measure_some (s_exp exp) in
    Measure_aux (m, l)
  and s_fexp (FE_aux (FE_fexp (id, e), (l, annot))) = FE_aux (FE_fexp (id, s_exp e), (l, s_tannot annot))
  and s_pexp = function
    | Pat_aux (Pat_exp (p, e), (l, annot)) -> Pat_aux (Pat_exp (s_pat p, s_exp e), (l, s_tannot annot))
    | Pat_aux (Pat_when (p, e1, e2), (l, annot)) -> Pat_aux (Pat_when (s_pat p, s_exp e1, s_exp e2), (l, s_tannot annot))
  and s_letbind (LB_aux (lb, (l, annot))) =
    match lb with LB_val (p, e) -> LB_aux (LB_val (s_pat p, s_exp e), (l, s_tannot annot))
  and s_lexp (LE_aux (e, (l, annot))) =
    let re e = LE_aux (e, (l, s_tannot annot)) in
    match e with
    | LE_id _ -> re e
    | LE_typ (typ, id) -> re (LE_typ (s_t typ, id))
    | LE_app (id, es) -> re (LE_app (id, List.map s_exp es))
    | LE_tuple les -> re (LE_tuple (List.map s_lexp les))
    | LE_vector (le, e) -> re (LE_vector (s_lexp le, s_exp e))
    | LE_vector_range (le, e1, e2) -> re (LE_vector_range (s_lexp le, s_exp e1, s_exp e2))
    | LE_vector_concat les -> re (LE_vector_concat (List.map s_lexp les))
    | LE_field (le, id) -> re (LE_field (s_lexp le, id))
    | LE_deref e -> re (LE_deref (s_exp e))
  in
  (s_pat, s_exp)
let nexp_subst_pat substs = fst (nexp_subst_fns substs)
let nexp_subst_exp substs = snd (nexp_subst_fns substs)
