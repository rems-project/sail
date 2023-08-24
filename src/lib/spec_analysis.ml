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

open Ast
open Ast_defs
open Ast_util
open Util

module Nameset = Set.Make (String)

let mt = Nameset.empty

(************************************************************************************************)
(*FV finding analysis: identifies the free variables of a function, expression, etc *)

let conditional_add typ_or_exp bound used id =
  let known_list =
    if typ_or_exp (*true for typ*) then ["bit"; "vector"; "unit"; "string"; "int"; "bool"]
    else ["=="; "!="; "|"; "~"; "&"; "add_int"]
  in
  let i = string_of_id (if typ_or_exp then prepend_id "typ:" id else id) in
  if Nameset.mem i bound || List.mem i known_list then used else Nameset.add i used

let conditional_add_typ = conditional_add true
let conditional_add_exp = conditional_add false

let nameset_bigunion = List.fold_left Nameset.union mt

let rec free_type_names_t consider_var (Typ_aux (t, l)) =
  match t with
  | Typ_var name -> if consider_var then Nameset.add (string_of_kid name) mt else mt
  | Typ_id name -> Nameset.add (string_of_id name) mt
  | Typ_fn (arg_typs, ret_typ) ->
      List.fold_left Nameset.union
        (free_type_names_t consider_var ret_typ)
        (List.map (free_type_names_t consider_var) arg_typs)
  | Typ_bidir (t1, t2) -> Nameset.union (free_type_names_t consider_var t1) (free_type_names_t consider_var t2)
  | Typ_tuple ts -> free_type_names_ts consider_var ts
  | Typ_app (name, targs) -> Nameset.add (string_of_id name) (free_type_names_t_args consider_var targs)
  | Typ_exist (kopts, _, t') ->
      List.fold_left
        (fun s kopt -> Nameset.remove (string_of_kid (kopt_kid kopt)) s)
        (free_type_names_t consider_var t') kopts
  | Typ_internal_unknown -> Reporting.unreachable l __POS__ "escaped Typ_internal_unknown"

and free_type_names_ts consider_var ts = nameset_bigunion (List.map (free_type_names_t consider_var) ts)

and free_type_names_t_arg consider_var = function A_aux (A_typ t, _) -> free_type_names_t consider_var t | _ -> mt

and free_type_names_t_args consider_var targs = nameset_bigunion (List.map (free_type_names_t_arg consider_var) targs)

let rec fv_of_typ consider_var bound used (Typ_aux (t, l)) : Nameset.t =
  match t with
  | Typ_var (Kid_aux (Var v, l)) ->
      if consider_var then conditional_add_typ bound used (Ast.Id_aux (Ast.Id v, l)) else used
  | Typ_id id -> conditional_add_typ bound used id
  | Typ_fn (arg, ret) ->
      fv_of_typ consider_var bound
        (List.fold_left Nameset.union Nameset.empty (List.map (fv_of_typ consider_var bound used) arg))
        ret
  | Typ_bidir (t1, t2) -> fv_of_typ consider_var bound (fv_of_typ consider_var bound used t1) t2 (* TODO FIXME? *)
  | Typ_tuple ts -> List.fold_right (fun t n -> fv_of_typ consider_var bound n t) ts used
  | Typ_app (id, targs) ->
      List.fold_right (fun ta n -> fv_of_targ consider_var bound n ta) targs (conditional_add_typ bound used id)
  | Typ_exist (kopts, _, t') ->
      fv_of_typ consider_var
        (List.fold_left (fun b (KOpt_aux (KOpt_kind (_, Kid_aux (Var v, _)), _)) -> Nameset.add v b) bound kopts)
        used t'
  | Typ_internal_unknown -> Reporting.unreachable l __POS__ "escaped Typ_internal_unknown"

and fv_of_tannot consider_var bound used tannot =
  match Type_check.destruct_tannot tannot with None -> mt | Some (_, t) -> fv_of_typ consider_var bound used t

and fv_of_targ consider_var bound used (Ast.A_aux (targ, _)) : Nameset.t =
  match targ with
  | A_typ t -> fv_of_typ consider_var bound used t
  | A_nexp n -> fv_of_nexp consider_var bound used n
  | _ -> used

and fv_of_nexp consider_var bound used (Ast.Nexp_aux (n, _)) =
  match n with
  | Nexp_id id -> conditional_add_typ bound used id
  | Nexp_var (Ast.Kid_aux (Ast.Var i, _)) ->
      if consider_var then conditional_add_typ bound used (Ast.Id_aux (Ast.Id i, Parse_ast.Unknown)) else used
  | Nexp_times (n1, n2) | Ast.Nexp_sum (n1, n2) | Ast.Nexp_minus (n1, n2) ->
      fv_of_nexp consider_var bound (fv_of_nexp consider_var bound used n1) n2
  | Nexp_exp n | Ast.Nexp_neg n -> fv_of_nexp consider_var bound used n
  | _ -> used

and fv_of_nconstraint consider_var bound used (Ast.NC_aux (nc, _)) =
  match nc with
  | NC_equal (n1, n2)
  | NC_bounded_ge (n1, n2)
  | NC_bounded_gt (n1, n2)
  | NC_bounded_le (n1, n2)
  | NC_bounded_lt (n1, n2)
  | NC_not_equal (n1, n2) ->
      fv_of_nexp consider_var bound (fv_of_nexp consider_var bound used n1) n2
  | NC_set (Ast.Kid_aux (Ast.Var i, _), _) | NC_var (Ast.Kid_aux (Ast.Var i, _)) ->
      if consider_var then conditional_add_typ bound used (Ast.Id_aux (Ast.Id i, Parse_ast.Unknown)) else used
  | NC_or (nc1, nc2) | NC_and (nc1, nc2) ->
      fv_of_nconstraint consider_var bound (fv_of_nconstraint consider_var bound used nc1) nc2
  | NC_app (id, targs) ->
      List.fold_right (fun ta n -> fv_of_targ consider_var bound n ta) targs (conditional_add_typ bound used id)
  | NC_true | NC_false -> used

let typq_bindings (TypQ_aux (tq, _)) =
  match tq with
  | TypQ_tq quants ->
      List.fold_right
        (fun (QI_aux (qi, _)) bounds ->
          match qi with
          | QI_id (KOpt_aux (k, _)) -> (
              match k with KOpt_kind (_, Kid_aux (Var s, _)) -> Nameset.add s bounds
            )
          | _ -> bounds
        )
        quants mt
  | TypQ_no_forall -> mt

let fv_of_typschm consider_var bound used (Ast.TypSchm_aux (Ast.TypSchm_ts (typq, typ), _)) =
  let ts_bound = if consider_var then typq_bindings typq else mt in
  (ts_bound, fv_of_typ consider_var (Nameset.union bound ts_bound) used typ)

let rec fv_of_typ_pat consider_var bound used (TP_aux (tp, _)) =
  match tp with
  | TP_wild -> (bound, used)
  | TP_var (Kid_aux (Var v, l)) -> (Nameset.add (string_of_id (Ast.Id_aux (Ast.Id v, l))) bound, used)
  | TP_app (id, tps) ->
      let u = conditional_add_typ bound used id in
      List.fold_right (fun ta (b, u) -> fv_of_typ_pat consider_var b u ta) tps (bound, u)

let rec pat_bindings consider_var bound used (P_aux (p, (_, tannot))) =
  let list_fv bound used ps = List.fold_right (fun p (b, n) -> pat_bindings consider_var b n p) ps (bound, used) in
  match p with
  | P_lit _ | P_wild -> (bound, used)
  | P_or (p1, p2) ->
      (* The typechecker currently drops bindings in disjunctions entirely *)
      let _b1, u1 = pat_bindings consider_var bound used p1 in
      let _b2, u2 = pat_bindings consider_var bound used p2 in
      (bound, Nameset.union u1 u2)
  | P_not p ->
      let _b, u = pat_bindings consider_var bound used p in
      (bound, u)
  | P_as (p, id) ->
      let b, ns = pat_bindings consider_var bound used p in
      (Nameset.add (string_of_id id) b, ns)
  | P_typ (t, p) ->
      let used = fv_of_tannot consider_var bound used tannot in
      let ns = fv_of_typ consider_var bound used t in
      pat_bindings consider_var bound ns p
  | P_id id | P_vector_subrange (id, _, _) ->
      let used = fv_of_tannot consider_var bound used tannot in
      (Nameset.add (string_of_id id) bound, used)
  | P_var (p, typ_p) ->
      let b, u = pat_bindings consider_var bound used p in
      fv_of_typ_pat consider_var b u typ_p
  | P_app (id, pats) ->
      let used = fv_of_tannot consider_var bound used tannot in
      list_fv bound (Nameset.add (string_of_id id) used) pats
  | P_vector pats | Ast.P_vector_concat pats | Ast.P_tuple pats | Ast.P_list pats | P_string_append pats ->
      list_fv bound used pats
  | P_struct (fpats, _) ->
      let pats = List.map snd fpats in
      list_fv bound used pats
  | P_cons (p1, p2) ->
      let b1, u1 = pat_bindings consider_var bound used p1 in
      pat_bindings consider_var b1 u1 p2

let rec fv_of_exp consider_var bound used set (E_aux (e, (_, tannot))) : Nameset.t * Nameset.t * Nameset.t =
  let list_fv b n s es = List.fold_right (fun e (b, n, s) -> fv_of_exp consider_var b n s e) es (b, n, s) in
  match e with
  | E_lit _ | E_internal_value _ -> (bound, used, set)
  | E_block es | Ast.E_tuple es | Ast.E_vector es | Ast.E_list es -> list_fv bound used set es
  | E_id id | E_ref id ->
      let used = conditional_add_exp bound used id in
      let used = fv_of_tannot consider_var bound used tannot in
      (bound, used, set)
  | E_typ (t, e) ->
      let u = fv_of_typ consider_var (if consider_var then bound else mt) used t in
      fv_of_exp consider_var bound u set e
  | E_app (id, es) ->
      let us = conditional_add_exp bound used id in
      let us = conditional_add_exp bound us (prepend_id "val:" id) in
      list_fv bound us set es
  | E_app_infix (l, id, r) ->
      let us = conditional_add_exp bound used id in
      let us = conditional_add_exp bound us (prepend_id "val:" id) in
      list_fv bound us set [l; r]
  | E_if (c, t, e) -> list_fv bound used set [c; t; e]
  | E_for (id, from, to_, by, _, body) ->
      let _, used, set = list_fv bound used set [from; to_; by] in
      fv_of_exp consider_var (Nameset.add (string_of_id id) bound) used set body
  | E_loop (_, measure, cond, body) ->
      let m = match measure with Measure_aux (Measure_some exp, _) -> [exp] | _ -> [] in
      list_fv bound used set (m @ [cond; body])
  | E_vector_access (v, i) -> list_fv bound used set [v; i]
  | E_vector_subrange (v, i1, i2) -> list_fv bound used set [v; i1; i2]
  | E_vector_update (v, i, e) -> list_fv bound used set [v; i; e]
  | E_vector_update_subrange (v, i1, i2, e) -> list_fv bound used set [v; i1; i2; e]
  | E_vector_append (e1, e2) | E_cons (e1, e2) -> list_fv bound used set [e1; e2]
  | E_struct fexps ->
      let used = fv_of_tannot consider_var bound used tannot in
      List.fold_right
        (fun (FE_aux (FE_fexp (_, e), _)) (b, u, s) -> fv_of_exp consider_var b u s e)
        fexps (bound, used, set)
  | E_struct_update (e, fexps) ->
      let b, u, s = fv_of_exp consider_var bound used set e in
      List.fold_right (fun (FE_aux (FE_fexp (_, e), _)) (b, u, s) -> fv_of_exp consider_var b u s e) fexps (b, u, s)
  | E_field (e, _) -> fv_of_exp consider_var bound used set e
  | E_match (e, pes) | E_try (e, pes) ->
      let b, u, s = fv_of_exp consider_var bound used set e in
      fv_of_pes consider_var b u s pes
  | E_let (lebind, e) ->
      let b, u, s = fv_of_let consider_var bound used set lebind in
      fv_of_exp consider_var b u s e
  | E_var (lexp, exp1, exp2) ->
      let b, u, s = fv_of_lexp consider_var bound used set lexp in
      let _, used, set = fv_of_exp consider_var bound used set exp1 in
      fv_of_exp consider_var b used set exp2
  | E_assign (lexp, e) ->
      let b, u, s = fv_of_lexp consider_var bound used set lexp in
      let _, used, set = fv_of_exp consider_var bound u s e in
      (b, used, set)
  | E_exit e -> fv_of_exp consider_var bound used set e
  | E_assert (c, m) -> list_fv bound used set [c; m]
  | E_sizeof ne -> (bound, fv_of_nexp consider_var bound used ne, set)
  | E_return e | E_throw e | E_internal_return e -> fv_of_exp consider_var bound used set e
  | E_internal_plet (pat, exp1, exp2) ->
      let bp, up = pat_bindings consider_var bound used pat in
      let _, u1, s1 = fv_of_exp consider_var bound used set exp1 in
      fv_of_exp consider_var bp (Nameset.union up u1) s1 exp2
  | E_constraint nc -> (bound, fv_of_nconstraint consider_var bound used nc, set)
  | E_internal_assume (nc, e) -> fv_of_exp consider_var bound (fv_of_nconstraint consider_var bound used nc) set e

and fv_of_pes consider_var bound used set pes =
  match pes with
  | [] -> (bound, used, set)
  | Pat_aux (Pat_exp (p, e), _) :: pes ->
      let bound_p, us_p = pat_bindings consider_var bound used p in
      let bound_e, us_e, set_e = fv_of_exp consider_var bound_p us_p set e in
      fv_of_pes consider_var bound us_e set_e pes
  | Pat_aux (Pat_when (p, g, e), _) :: pes ->
      let bound_p, us_p = pat_bindings consider_var bound used p in
      let bound_g, us_g, set_g = fv_of_exp consider_var bound_p us_p set g in
      let bound_e, us_e, set_e = fv_of_exp consider_var bound_g us_g set_g e in
      fv_of_pes consider_var bound us_e set_e pes

and fv_of_let consider_var bound used set (LB_aux (lebind, _)) =
  match lebind with
  | LB_val (pat, exp) ->
      let bound_p, us_p = pat_bindings consider_var bound used pat in
      let _, us_e, set_e = fv_of_exp consider_var bound used set exp in
      (bound_p, Nameset.union us_p us_e, set_e)

and fv_of_lexp consider_var bound used set (LE_aux (lexp, (_, tannot))) =
  match lexp with
  | LE_id id ->
      let used = fv_of_tannot consider_var bound used tannot in
      let i = string_of_id id in
      if Nameset.mem i bound then (bound, used, Nameset.add i set) else (Nameset.add i bound, Nameset.add i used, set)
  | LE_deref exp -> fv_of_exp consider_var bound used set exp
  | LE_typ (typ, id) ->
      let used = fv_of_tannot consider_var bound used tannot in
      let i = string_of_id id in
      let used_t = fv_of_typ consider_var bound used typ in
      if Nameset.mem i bound then (bound, used_t, Nameset.add i set)
      else (Nameset.add i bound, Nameset.add i used_t, set)
  | LE_tuple tups -> List.fold_right (fun l (b, u, s) -> fv_of_lexp consider_var b u s l) tups (bound, used, set)
  | LE_app (id, args) ->
      let bound, used, set =
        List.fold_right (fun e (b, u, s) -> fv_of_exp consider_var b u s e) args (bound, used, set)
      in
      (bound, Nameset.add (string_of_id id) used, set)
  | LE_vector_concat args -> List.fold_right (fun e (b, u, s) -> fv_of_lexp consider_var b u s e) args (bound, used, set)
  | LE_field (lexp, _) -> fv_of_lexp consider_var bound used set lexp
  | LE_vector (lexp, exp) ->
      let bound_l, used, set = fv_of_lexp consider_var bound used set lexp in
      let _, used, set = fv_of_exp consider_var bound used set exp in
      (bound_l, used, set)
  | LE_vector_range (lexp, e1, e2) ->
      let bound_l, used, set = fv_of_lexp consider_var bound used set lexp in
      let _, used, set = fv_of_exp consider_var bound used set e1 in
      let _, used, set = fv_of_exp consider_var bound used set e2 in
      (bound_l, used, set)

let init_env s = Nameset.singleton s

let typ_variants consider_var bound tunions =
  List.fold_right
    (fun (Tu_aux (Tu_ty_id (t, id), _)) (b, n) -> (Nameset.add (string_of_id id) b, fv_of_typ consider_var b n t))
    tunions (bound, mt)

let fv_of_abbrev consider_var bound used typq typ_arg =
  let ts_bound = if consider_var then typq_bindings typq else mt in
  (ts_bound, fv_of_targ consider_var (Nameset.union bound ts_bound) used typ_arg)

let fv_of_type_def consider_var (TD_aux (t, _)) =
  match t with
  | TD_abbrev (id, typq, typ_arg) ->
      (init_env ("typ:" ^ string_of_id id), snd (fv_of_abbrev consider_var mt mt typq typ_arg))
  | TD_record (id, typq, tids, _) ->
      let binds = init_env ("typ:" ^ string_of_id id) in
      let bounds = if consider_var then typq_bindings typq else mt in
      (binds, List.fold_right (fun (t, _) n -> fv_of_typ consider_var bounds n t) tids mt)
  | TD_variant (id, typq, tunions, _) ->
      let bindings = Nameset.add ("typ:" ^ string_of_id id) (if consider_var then typq_bindings typq else mt) in
      typ_variants consider_var bindings tunions
  | TD_enum (id, ids, _) -> (Nameset.of_list (("typ:" ^ string_of_id id) :: List.map string_of_id ids), mt)
  | TD_bitfield (id, typ, _) -> (init_env ("typ:" ^ string_of_id id), Nameset.empty (* fv_of_typ consider_var mt typ *))

let fv_of_fun consider_var (FD_aux (FD_function (rec_opt, tannot_opt, funcls), _) as fd) =
  let fun_name =
    match funcls with
    | [] -> failwith "fv_of_fun fell off the end looking for the function name"
    | FCL_aux (FCL_funcl (id, _), _) :: _ -> string_of_id id
  in
  let base_bounds =
    match rec_opt with
    (* Current Sail does not require syntax for declaring functions as recursive,
          and type checker does not check whether functions are recursive, so
          just always add a self-dependency of functions on themselves, as well as
          adding dependencies from any specified termination measure further below
       | Rec_aux(Ast.Rec_rec,_) -> init_env fun_name
       | _ -> mt*)
    | _ -> init_env fun_name
  in
  let base_bounds, ns_r =
    match tannot_opt with
    | Typ_annot_opt_aux (Typ_annot_opt_some (typq, typ), _) ->
        let bindings = if consider_var then typq_bindings typq else mt in
        let bound = Nameset.union bindings base_bounds in
        (bound, fv_of_typ consider_var bound mt typ)
    | Typ_annot_opt_aux (Typ_annot_opt_none, _) -> (base_bounds, mt)
  in
  let ns_measure =
    match rec_opt with
    | Rec_aux (Rec_measure (pat, exp), _) ->
        let pat_bs, pat_ns = pat_bindings consider_var base_bounds mt pat in
        let _, exp_ns, _ = fv_of_exp consider_var pat_bs pat_ns Nameset.empty exp in
        exp_ns
    | _ -> mt
  in
  let ns =
    List.fold_right
      (fun (FCL_aux (FCL_funcl (_, pexp), _)) ns ->
        match pexp with
        | Pat_aux (Pat_exp (pat, exp), _) ->
            let pat_bs, pat_ns = pat_bindings consider_var base_bounds ns pat in
            let _, exp_ns, _ = fv_of_exp consider_var pat_bs pat_ns Nameset.empty exp in
            exp_ns
        | Pat_aux (Pat_when (pat, guard, exp), _) ->
            let pat_bs, pat_ns = pat_bindings consider_var base_bounds ns pat in
            let guard_bs, guard_ns, _ = fv_of_exp consider_var pat_bs pat_ns Nameset.empty guard in
            let _, exp_ns, _ = fv_of_exp consider_var guard_bs guard_ns Nameset.empty exp in
            exp_ns
      )
      funcls mt
  in
  let ns_vs = init_env ("val:" ^ string_of_id (id_of_fundef fd)) in
  (* let _ = Printf.eprintf "Function %s uses %s\n" fun_name (set_to_string (Nameset.union ns ns_r)) in *)
  (init_env fun_name, Nameset.union ns_vs (Nameset.union ns (Nameset.union ns_r ns_measure)))

let fv_of_vspec consider_var (VS_aux (vspec, _)) =
  match vspec with
  | VS_val_spec (ts, id, _) -> (init_env ("val:" ^ string_of_id id), snd (fv_of_typschm consider_var mt mt ts))

let rec find_scattered_of name = function
  | [] -> []
  | DEF_scattered (SD_aux (sda, _) as sd) :: defs ->
      ( match sda with
      | SD_function (_, _, id) | SD_funcl (FCL_aux (FCL_funcl (id, _), _)) | SD_unioncl (id, _) ->
          if name = string_of_id id then [sd] else []
      | _ -> []
      )
      @ find_scattered_of name defs
  | _ :: defs -> find_scattered_of name defs

let rec fv_of_scattered consider_var consider_scatter_as_one all_defs (SD_aux (sd, (l, _))) =
  match sd with
  | SD_function (_, tannot_opt, id) ->
      let b, ns =
        match tannot_opt with
        | Typ_annot_opt_aux (Typ_annot_opt_some (typq, typ), _) ->
            let bindings = if consider_var then typq_bindings typq else mt in
            (bindings, fv_of_typ consider_var bindings mt typ)
        | Typ_annot_opt_aux (Typ_annot_opt_none, _) -> (mt, mt)
      in
      (init_env (string_of_id id), ns)
  | SD_funcl (FCL_aux (FCL_funcl (id, pexp), _)) -> begin
      match pexp with
      | Pat_aux (Pat_exp (pat, exp), _) ->
          let pat_bs, pat_ns = pat_bindings consider_var mt mt pat in
          let _, exp_ns, _ = fv_of_exp consider_var pat_bs pat_ns Nameset.empty exp in
          let scattered_binds =
            match pat with P_aux (P_app (pid, _), _) -> init_env (string_of_id id ^ "/" ^ string_of_id pid) | _ -> mt
          in
          (scattered_binds, exp_ns)
      | Pat_aux (Pat_when (pat, guard, exp), _) ->
          let pat_bs, pat_ns = pat_bindings consider_var mt mt pat in
          let guard_bs, guard_ns, _ = fv_of_exp consider_var pat_bs pat_ns Nameset.empty guard in
          let _, exp_ns, _ = fv_of_exp consider_var guard_bs guard_ns Nameset.empty exp in
          let scattered_binds =
            match pat with P_aux (P_app (pid, _), _) -> init_env (string_of_id id ^ "/" ^ string_of_id pid) | _ -> mt
          in
          (scattered_binds, exp_ns)
    end
  | SD_variant (id, _) ->
      let name = string_of_id id in
      let uses =
        if consider_scatter_as_one then (
          let variant_defs = find_scattered_of name all_defs in
          let pieces_uses =
            List.fold_right
              (fun (binds, uses) all_uses -> Nameset.union uses all_uses)
              (List.map (fv_of_scattered consider_var false []) variant_defs)
              mt
          in
          Nameset.remove name pieces_uses
        )
        else mt
      in
      (init_env name, uses)
  | SD_unioncl (id, type_union) ->
      let typ_name = string_of_id id in
      let b = init_env typ_name in
      let b, r = typ_variants consider_var b [type_union] in
      (Nameset.remove typ_name b, Nameset.add typ_name r)
  | SD_end id ->
      let name = string_of_id id in
      let uses =
        if consider_scatter_as_one (*Note: if this is a function ending, the dec is included *) then (
          let scattered_defs = find_scattered_of name all_defs in
          List.fold_right
            (fun (binds, uses) all_uses -> Nameset.union (Nameset.union binds uses) all_uses)
            (List.map (fv_of_scattered consider_var false []) scattered_defs)
            (init_env name)
        )
        else init_env name
      in
      (init_env (name ^ "/end"), uses)
  | _ -> raise (Reporting.err_unreachable l __POS__ "Tried to find free variables for scattered mapping clause")

let fv_of_rd consider_var (DEC_aux (d, annot)) =
  (* When we get the free variables of a register, we have to ensure
     that we expand all synonyms so we can pick up dependencies with
     undefined_type function, even when type is indirected through a
     synonym. *)
  let open Type_check in
  let env = env_of_annot annot in
  match d with
  | DEC_reg (t, id, _) ->
      let t' = Env.expand_synonyms env t in
      (init_env (string_of_id id), Nameset.union (fv_of_typ consider_var mt mt t) (fv_of_typ consider_var mt mt t'))

let fv_of_def consider_var consider_scatter_as_one all_defs (DEF_aux (aux, _) as def) =
  match aux with
  | DEF_type tdef -> fv_of_type_def consider_var tdef
  | DEF_fundef fdef -> fv_of_fun consider_var fdef
  | DEF_mapdef mdef -> (mt, mt (* fv_of_map consider_var mdef *))
  | DEF_let lebind -> (fun (b, u, _) -> (b, u)) (fv_of_let consider_var mt mt mt lebind)
  | DEF_val vspec -> fv_of_vspec consider_var vspec
  | DEF_fixity _ -> (mt, mt)
  | DEF_overload (id, ids) ->
      (init_env (string_of_id id), List.fold_left (fun ns id -> Nameset.add ("val:" ^ string_of_id id) ns) mt ids)
  | DEF_default def -> (mt, mt)
  | DEF_internal_mutrec fdefs ->
      let fvs = List.map (fv_of_fun consider_var) fdefs in
      ( List.fold_left Nameset.union Nameset.empty (List.map fst fvs),
        List.fold_left Nameset.union Nameset.empty (List.map snd fvs)
      )
  | DEF_scattered sdef -> fv_of_scattered consider_var consider_scatter_as_one all_defs sdef
  | DEF_register rdec -> fv_of_rd consider_var rdec
  | DEF_pragma _ -> (mt, mt)
  (* removed beforehand for Coq, but may still be present otherwise *)
  | DEF_measure (id, pat, exp) ->
      let i = string_of_id id in
      let used = Nameset.of_list [i; "val:" ^ i] in
      (fun (_, u, _) -> (Nameset.singleton ("measure:" ^ i), u))
        (fv_of_pes consider_var mt used mt [Pat_aux (Pat_exp (pat, exp), (Unknown, Type_check.empty_tannot))])
  | DEF_loop_measures _ | DEF_impl _ | DEF_outcome _ | DEF_instantiation _ ->
      Reporting.unreachable (def_loc def) __POS__ "Found definition that should have been rewritten previously"

(*
 *  Sorting definitions, take 3
 *)

module Namemap = Map.Make (String)
module NameGraph = Graph.Make (String)

let add_def_to_map id d defset =
  Namemap.add id (match Namemap.find id defset with t -> t @ [d] | exception Not_found -> [d]) defset

let add_def_to_graph (prelude_rev, original_order_rev, defset, graph) d =
  let bound, used = fv_of_def false true [] d in
  let used =
    match d with
    | DEF_aux (DEF_register (DEC_aux (DEC_reg (typ, _, _), annot)), _) ->
        (* For a register, we need to ensure that any undefined_type
           functions for types used by the register are placed before
           the register declaration. *)
        let env = Type_check.env_of_annot annot in
        let typ' = Type_check.Env.expand_synonyms env typ in
        let undefineds = Nameset.map (fun name -> "undefined_" ^ name) (free_type_names_t false typ') in
        Nameset.union undefineds used
    | _ -> used
  in
  try
    (* A definition may bind multiple identifiers, e.g. "let (x, y) = ...".
       We add all identifiers to the dependency graph as a cycle.  The actual
       definition is attached to only one of the identifiers, so it will not
       be duplicated in the final output. *)
    let id = Nameset.choose bound in
    let other_ids = Nameset.elements (Nameset.remove id bound) in
    let graph' =
      NameGraph.add_edges id (other_ids @ Nameset.elements used) graph
      |> List.fold_right (fun id' g -> NameGraph.add_edge id' id g) other_ids
    in
    (prelude_rev, id :: original_order_rev, add_def_to_map id d defset, graph')
  with Not_found ->
    (* Some definitions do not bind any identifiers at all.  This *should*
       only happen for default bitvector order declarations, operator fixity
       declarations, and comments.  The sorting does not (currently) attempt
       to preserve the positions of these AST nodes; they are collected
       separately and placed at the beginning of the output.  Comments are
       currently ignored by the Lem and OCaml backends, anyway.  For
       default order and fixity declarations, this means that specifications
       currently have to assume those declarations are moved to the
       beginning when using a backend that requires topological sorting. *)
    (d :: prelude_rev, original_order_rev, defset, graph)

let def_of_component graph defset comp =
  let get_def id = if Namemap.mem id defset then Namemap.find id defset else [] in
  match List.concat (List.map get_def comp) with
  | [] -> []
  | [def] -> [def]
  | (DEF_aux ((DEF_fundef _ | DEF_internal_mutrec _), _) as def) :: _ as defs ->
      let get_fundefs = function
        | DEF_aux (DEF_fundef fundef, _) -> [fundef]
        | DEF_aux (DEF_internal_mutrec fundefs, _) -> fundefs
        | _ ->
            raise
              (Reporting.err_unreachable (def_loc def) __POS__
                 "Trying to merge non-function definition with mutually recursive functions"
              )
      in
      let fundefs = List.concat (List.map get_fundefs defs) in
      (* print_dot graph (List.map (fun fd -> string_of_id (id_of_fundef fd)) fundefs); *)
      [mk_def (DEF_internal_mutrec fundefs)]
  (* We could merge other stuff, in particular overloads, but don't need to just now *)
  | defs -> defs

let top_sort_defs ast =
  let prelude_rev, original_order_rev, defset, graph =
    List.fold_left add_def_to_graph ([], [], Namemap.empty, Namemap.empty) ast.defs
  in
  let prelude, original_order = (List.rev prelude_rev, List.rev original_order_rev) in
  let components = NameGraph.scc ~original_order graph in
  { ast with defs = prelude @ List.concat (List.map (def_of_component graph defset) components) }

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
    | NC_aux (NC_equal (Nexp_aux (Nexp_var var1, _), Nexp_aux (Nexp_var var2, _)), _) ->
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
    | None -> Type_check.empty_tannot
    | Some (env, t) -> Type_check.mk_tannot env (s_t t)
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
