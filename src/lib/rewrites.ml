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
open Spec_analysis
open Rewriter

let fresh_name_counter = ref 0

let fresh_name () =
  let current = !fresh_name_counter in
  let () = fresh_name_counter := current + 1 in
  current

let reset_fresh_name_counter () = fresh_name_counter := 0

let fresh_id pre l =
  let current = fresh_name () in
  Id_aux (Id (pre ^ string_of_int current), gen_loc l)

let fresh_id_pat pre (l, annot) =
  let id = fresh_id pre l in
  P_aux (P_id id, (gen_loc l, annot))

let get_loc_exp (E_aux (_, (l, _))) = l

let gen_vs ~pure (id, spec) = Initial_check.extern_of_string ~pure (mk_id id) spec

let simple_annot l typ = (gen_loc l, mk_tannot initial_env typ)

let annot_exp e_aux l env typ = E_aux (e_aux, (l, mk_tannot env typ))
let annot_pat p_aux l env typ = P_aux (p_aux, (l, mk_tannot env typ))
let annot_letbind (p_aux, exp) l env typ = LB_aux (LB_val (annot_pat p_aux l env typ, exp), (l, mk_tannot env typ))

let simple_num l n =
  E_aux (E_lit (L_aux (L_num n, gen_loc l)), simple_annot (gen_loc l) (atom_typ (Nexp_aux (Nexp_constant n, gen_loc l))))

let effectful eaux = Ast_util.effectful (effect_of eaux)
let effectful_pexp pexp =
  let pat, guard, exp, _ = destruct_pexp pexp in
  let guard_eff = match guard with Some g -> effect_of g | None -> no_effect in
  Ast_util.effectful (union_effects guard_eff (effect_of exp))

let rec small (E_aux (exp, _)) =
  match exp with
  | E_id _ | E_lit _ -> true
  | E_typ (_, e) -> small e
  | E_list es -> List.for_all small es
  | E_cons (e1, e2) -> small e1 && small e2
  | E_sizeof _ -> true
  | _ -> false

let id_is_local_var id env = match Env.lookup_id id env with Local _ -> true | _ -> false

let id_is_unbound id env = match Env.lookup_id id env with Unbound _ -> true | _ -> false

let rec lexp_is_local (LE_aux (lexp, _)) env =
  match lexp with
  | LE_app _ | LE_deref _ -> false
  | LE_id id | LE_typ (_, id) -> id_is_local_var id env
  | LE_tuple lexps | LE_vector_concat lexps -> List.for_all (fun lexp -> lexp_is_local lexp env) lexps
  | LE_vector (lexp, _) | LE_vector_range (lexp, _, _) | LE_field (lexp, _) -> lexp_is_local lexp env

let rec lexp_is_local_intro (LE_aux (lexp, _)) env =
  match lexp with
  | LE_app _ | LE_deref _ -> false
  | LE_id id | LE_typ (_, id) -> id_is_unbound id env
  | LE_tuple lexps | LE_vector_concat lexps -> List.for_all (fun lexp -> lexp_is_local_intro lexp env) lexps
  | LE_vector (lexp, _) | LE_vector_range (lexp, _, _) | LE_field (lexp, _) -> lexp_is_local_intro lexp env

let lexp_is_effectful (LE_aux (_, (_, tannot))) = Ast_util.effectful (effect_of_annot tannot)

let find_used_vars exp =
  (* Overapproximates the set of used identifiers, but for the use cases below
     this is acceptable. *)
  let e_id id = (IdSet.singleton id, E_id id) in
  fst (fold_exp { (compute_exp_alg IdSet.empty IdSet.union) with e_id } exp)

let find_introduced_vars exp =
  let le_aux ((ids, lexp), annot) =
    let ids =
      match lexp with
      | (LE_id id | LE_typ (_, id)) when id_is_unbound id (env_of_annot annot) -> IdSet.add id ids
      | _ -> ids
    in
    (ids, LE_aux (lexp, annot))
  in
  fst (fold_exp { (compute_exp_alg IdSet.empty IdSet.union) with le_aux } exp)

let find_updated_vars exp =
  let intros = find_introduced_vars exp in
  let le_aux ((ids, lexp), annot) =
    let ids =
      match lexp with
      | (LE_id id | LE_typ (_, id)) when id_is_local_var id (env_of_annot annot) && not (IdSet.mem id intros) ->
          IdSet.add id ids
      | _ -> ids
    in
    (ids, LE_aux (lexp, annot))
  in
  fst (fold_exp { (compute_exp_alg IdSet.empty IdSet.union) with le_aux } exp)

let lookup_equal_kids env =
  let get_eq_kids kid eqs = try KBindings.find kid eqs with Not_found -> KidSet.singleton kid in
  let add_eq_kids kid1 kid2 eqs =
    let kids = KidSet.union (get_eq_kids kid2 eqs) (get_eq_kids kid1 eqs) in
    eqs |> KBindings.add kid1 kids |> KBindings.add kid2 kids
  in
  let add_nc eqs = function
    | NC_aux (NC_equal (Nexp_aux (Nexp_var kid1, _), Nexp_aux (Nexp_var kid2, _)), _) -> add_eq_kids kid1 kid2 eqs
    | _ -> eqs
  in
  List.fold_left add_nc KBindings.empty (Env.get_constraints env)

let lookup_constant_kid env kid =
  let kids =
    match KBindings.find kid (lookup_equal_kids env) with kids -> kids | exception Not_found -> KidSet.singleton kid
  in
  let check_nc const nc =
    match (const, nc) with
    | None, NC_aux (NC_equal (Nexp_aux (Nexp_var kid, _), Nexp_aux (Nexp_constant i, _)), _) when KidSet.mem kid kids ->
        Some i
    | _, _ -> const
  in
  List.fold_left check_nc None (Env.get_constraints env)

let rec rewrite_nexp_ids env (Nexp_aux (nexp, l) as nexp_aux) =
  match nexp with
  | Nexp_id id -> Env.expand_nexp_synonyms env nexp_aux
  | Nexp_var kid -> begin match lookup_constant_kid env kid with Some i -> nconstant i | None -> nexp_aux end
  | Nexp_times (nexp1, nexp2) -> Nexp_aux (Nexp_times (rewrite_nexp_ids env nexp1, rewrite_nexp_ids env nexp2), l)
  | Nexp_sum (nexp1, nexp2) -> Nexp_aux (Nexp_sum (rewrite_nexp_ids env nexp1, rewrite_nexp_ids env nexp2), l)
  | Nexp_minus (nexp1, nexp2) -> Nexp_aux (Nexp_minus (rewrite_nexp_ids env nexp1, rewrite_nexp_ids env nexp2), l)
  | Nexp_exp nexp -> Nexp_aux (Nexp_exp (rewrite_nexp_ids env nexp), l)
  | Nexp_neg nexp -> Nexp_aux (Nexp_neg (rewrite_nexp_ids env nexp), l)
  | _ -> nexp_aux

let rewrite_ast_nexp_ids, _rewrite_typ_nexp_ids =
  let rec rewrite_typ env (Typ_aux (typ, l) as typ_aux) =
    match typ with
    | Typ_fn (arg_ts, ret_t) -> Typ_aux (Typ_fn (List.map (rewrite_typ env) arg_ts, rewrite_typ env ret_t), l)
    | Typ_tuple ts -> Typ_aux (Typ_tuple (List.map (rewrite_typ env) ts), l)
    | Typ_exist (kids, c, typ) -> Typ_aux (Typ_exist (kids, c, rewrite_typ env typ), l)
    | Typ_app (id, targs) -> Typ_aux (Typ_app (id, List.map (rewrite_typ_arg env) targs), l)
    | _ -> typ_aux
  and rewrite_typ_arg env (A_aux (targ, l)) =
    match targ with
    | A_nexp nexp -> A_aux (A_nexp (rewrite_nexp_ids env nexp), l)
    | A_typ typ -> A_aux (A_typ (rewrite_typ env typ), l)
    | A_bool nc -> A_aux (A_bool nc, l)
  in

  let rewrite_annot (l, tannot) =
    match destruct_tannot tannot with
    | Some (env, typ) -> (l, replace_typ (rewrite_typ env typ) tannot)
    | None -> (l, empty_tannot)
  in

  let rewrite_typschm env (TypSchm_aux (TypSchm_ts (tq, typ), l)) =
    TypSchm_aux (TypSchm_ts (tq, rewrite_typ env typ), l)
  in

  let rewrite_def env rewriters = function
    | DEF_aux (DEF_val (VS_aux (VS_val_spec (typschm, id, exts), a)), def_annot) ->
        let typschm = rewrite_typschm env typschm in
        let a = rewrite_annot a in
        DEF_aux (DEF_val (VS_aux (VS_val_spec (typschm, id, exts), a)), def_annot)
    | DEF_aux (DEF_type (TD_aux (TD_abbrev (id, typq, typ_arg), a)), def_annot) ->
        DEF_aux (DEF_type (TD_aux (TD_abbrev (id, typq, rewrite_typ_arg env typ_arg), a)), def_annot)
    | DEF_aux (DEF_type (TD_aux (TD_record (id, typq, fields, b), a)), def_annot) ->
        let fields' = List.map (fun (t, id) -> (rewrite_typ env t, id)) fields in
        DEF_aux (DEF_type (TD_aux (TD_record (id, typq, fields', b), a)), def_annot)
    | DEF_aux (DEF_type (TD_aux (TD_variant (id, typq, constrs, b), a)), def_annot) ->
        let constrs' =
          List.map (fun (Tu_aux (Tu_ty_id (t, id), l)) -> Tu_aux (Tu_ty_id (rewrite_typ env t, id), l)) constrs
        in
        DEF_aux (DEF_type (TD_aux (TD_variant (id, typq, constrs', b), a)), def_annot)
    | d -> Rewriter.rewrite_def rewriters d
  in

  ( (fun env defs ->
      rewrite_ast_base
        { rewriters_base with rewrite_exp = (fun _ -> map_exp_annot rewrite_annot); rewrite_def = rewrite_def env }
        defs
    ),
    rewrite_typ
  )

let rewrite_ast_remove_vector_subrange_pats env ast =
  let rewrite_pattern pat =
    let appends = ref Bindings.empty in
    let rec insert_into_append (n1, m1, id1, typ1) = function
      | (n2, m2, id2, typ2) :: xs ->
          if Big_int.greater m1 n2 then (n1, m1, id1, typ1) :: (n2, m2, id2, typ2) :: xs
          else (n2, m2, id2, typ2) :: insert_into_append (n1, m1, id1, typ1) xs
      | [] -> [(n1, m1, id1, typ1)]
    in
    let pat_alg =
      {
        id_pat_alg with
        p_aux =
          (fun (aux, annot) ->
            let typ = typ_of_annot annot in
            match aux with
            | P_vector_subrange (id, n, m) ->
                let range_id =
                  Printf.ksprintf mk_id "%s_%s_%s#" (string_of_id id) (Big_int.to_string n) (Big_int.to_string m)
                in
                appends :=
                  Bindings.update id
                    (fun a -> Some (insert_into_append (n, m, range_id, typ) (Option.value a ~default:[])))
                    !appends;
                P_aux (P_typ (typ, P_aux (P_id range_id, annot)), annot)
            | _ -> P_aux (aux, annot)
          );
      }
    in
    let pat = fold_pat pat_alg pat in
    (pat, !appends)
  in
  let rewrite_pexp pat body =
    let pat, appends = rewrite_pattern pat in
    let body =
      Bindings.fold
        (fun id append body ->
          match append with
          | (_, _, id1, _) :: tl_append ->
              let env =
                List.fold_left (fun env (_, _, id, typ) -> Env.add_local id (Immutable, typ) env) (env_of body) append
              in
              let append_exp =
                List.fold_left
                  (fun e1 (_, _, id2, _) -> mk_exp (E_vector_append (e1, mk_exp (E_id id2))))
                  (mk_exp (E_id id1)) tl_append
              in
              let bind = mk_exp (E_let (mk_letbind (mk_pat (P_id id)) append_exp, mk_lit_exp L_unit)) in
              let bind = check_exp env bind unit_typ in
              begin
                match bind with
                | E_aux (E_let (letbind, _), annot) -> E_aux (E_let (letbind, body), annot)
                | _ -> assert false
              end
          | [] -> body
        )
        appends body
    in
    (pat, body)
  in
  let exp_alg =
    {
      id_exp_alg with
      pat_exp =
        (fun (pat, body) ->
          let pat, body = rewrite_pexp pat body in
          Pat_exp (pat, body)
        );
      pat_when =
        (fun (pat, guard, body) ->
          let pat, body = rewrite_pexp pat body in
          Pat_when (pat, guard, body)
        );
    }
  in
  let rewrite_exp _ = fold_exp exp_alg in
  let rewrite_funcl (FCL_aux (FCL_funcl (id, pexp), annot)) = FCL_aux (FCL_funcl (id, fold_pexp exp_alg pexp), annot) in
  let rewrite_fun _ (FD_aux (FD_function (r_o, t_o, funcls), a)) =
    FD_aux (FD_function (r_o, t_o, List.map rewrite_funcl funcls), a)
  in
  rewrite_ast_base { rewriters_base with rewrite_exp; rewrite_fun } ast

let remove_vector_concat_pat pat =
  let fresh_id_v = fresh_id "v__" in

  (* expects that P_typ elements have been removed from AST,
     that the length of all vectors involved is known,
     that we don't have indexed vectors *)

  (* introduce names for all patterns of form P_vector_concat *)
  let name_vector_concat_roots =
    {
      p_lit = (fun lit -> P_lit lit);
      p_typ = (fun (typ, p) -> P_typ (typ, p false)) (* cannot happen *);
      p_wild =
        P_wild
        (* ToDo: I have no idea what the boolean parameter means so guessed that
         * "true" was a good value to use.
         * (Adding a comment explaining the boolean might be useful?)
         *);
      p_or = (fun (pat1, pat2) -> P_or (pat1 true, pat2 true));
      p_not = (fun pat -> P_not (pat true));
      p_as = (fun (pat, id) -> P_as (pat true, id));
      p_id = (fun id -> P_id id);
      p_var = (fun (pat, kid) -> P_var (pat true, kid));
      p_app = (fun (id, ps) -> P_app (id, List.map (fun p -> p false) ps));
      p_vector = (fun ps -> P_vector (List.map (fun p -> p false) ps));
      p_vector_concat = (fun ps -> P_vector_concat (List.map (fun p -> p false) ps));
      p_vector_subrange = (fun (id, n, m) -> P_vector_subrange (id, n, m));
      p_tuple = (fun ps -> P_tuple (List.map (fun p -> p false) ps));
      p_list = (fun ps -> P_list (List.map (fun p -> p false) ps));
      p_cons = (fun (p, ps) -> P_cons (p false, ps false));
      p_string_append = (fun ps -> P_string_append (List.map (fun p -> p false) ps));
      p_struct = (fun (fpats, fwild) -> P_struct (List.map (fun (field, p) -> (field, p false)) fpats, fwild));
      p_aux =
        (fun (pat, ((l, _) as annot)) contained_in_p_as ->
          match pat with
          | P_vector_concat pats ->
              if contained_in_p_as then P_aux (pat, annot) else P_aux (P_as (P_aux (pat, annot), fresh_id_v l), annot)
          | _ -> P_aux (pat, annot)
        );
    }
  in

  let pat = (fold_pat name_vector_concat_roots pat) false in

  (* introduce names for all unnamed child nodes of P_vector_concat *)
  let name_vector_concat_elements =
    let p_vector_concat pats =
      let rec aux (P_aux (p, ((l, _) as a)) as pat) =
        match p with
        | P_vector _ -> P_aux (P_as (pat, fresh_id_v l), a)
        | P_lit _ -> P_aux (P_as (pat, fresh_id_v l), a)
        | P_id id -> P_aux (P_id id, a)
        | P_as (p, id) -> P_aux (P_as (p, id), a)
        | P_typ (typ, pat) -> P_aux (P_typ (typ, aux pat), a)
        | P_wild -> P_aux (P_wild, a)
        | P_app (id, pats) when Env.is_mapping id (env_of_annot a) -> P_aux (P_app (id, List.map aux pats), a)
        | _ ->
            Reporting.unreachable l __POS__
              ("name_vector_concat_elements: Non-vector " ^ string_of_pat pat ^ " in vector-concat pattern")
      in
      P_vector_concat (List.map aux pats)
    in
    { id_pat_alg with p_vector_concat }
  in

  let pat = fold_pat name_vector_concat_elements pat in

  let rec tag_last = function
    | x :: xs ->
        let is_last = xs = [] in
        (x, is_last) :: tag_last xs
    | _ -> []
  in

  (* remove names from vectors in vector_concat patterns and collect them as declarations for the
     function body or expression *)
  let unname_vector_concat_elements =
    (* build a let-expression of the form "let child = root[i..j] in body" *)
    let letbind_vec typ_opt (rootid, rannot) (child, cannot) (i, j) =
      let l, _ = cannot in
      let env = env_of_annot rannot in
      let rootname = string_of_id rootid in
      let childname = string_of_id child in

      let root = E_aux (E_id rootid, rannot) in
      let index_i = simple_num l i in
      let index_j = simple_num l j in

      let subv = E_aux (E_vector_subrange (root, index_i, index_j), cannot) in

      let id_pat =
        match typ_opt with
        | Some typ -> add_p_typ env typ (P_aux (P_id child, cannot))
        | None -> P_aux (P_id child, cannot)
      in
      let letbind = LB_aux (LB_val (id_pat, subv), cannot) in
      ( letbind,
        (fun body ->
          if IdSet.mem child (find_used_vars body) then annot_exp (E_let (letbind, body)) l env (typ_of body) else body
        ),
        (rootname, childname)
      )
    in

    let p_aux = function
      | (P_as (P_aux (P_vector_concat pats, rannot'), rootid), decls), rannot ->
          let rtyp = Env.base_typ_of (env_of_annot rannot') (typ_of_annot rannot') in
          let ord = Env.get_default_order (env_of_annot rannot) in
          let start, last_idx =
            match (vector_start_index (env_of_annot rannot) rtyp, vector_typ_args_of rtyp) with
            | Nexp_aux (Nexp_constant start, _), (Nexp_aux (Nexp_constant length, _), _) ->
                ( start,
                  if is_order_inc ord then Big_int.sub (Big_int.add start length) (Big_int.of_int 1)
                  else Big_int.add (Big_int.sub start length) (Big_int.of_int 1)
                )
            | _ ->
                Reporting.unreachable (fst rannot') __POS__
                  "unname_vector_concat_elements: vector of unspecified length in vector-concat pattern"
          in
          let rec aux typ_opt (pos, pat_acc, decl_acc) (P_aux (p, cannot), is_last) =
            let ctyp = Env.base_typ_of (env_of_annot cannot) (typ_of_annot cannot) in
            let length, _ = vector_typ_args_of ctyp in
            let pos', index_j =
              match Type_check.solve_unique (env_of_annot cannot) length with
              | Some i ->
                  if is_order_inc ord then (Big_int.add pos i, Big_int.sub (Big_int.add pos i) (Big_int.of_int 1))
                  else (Big_int.sub pos i, Big_int.add (Big_int.sub pos i) (Big_int.of_int 1))
              | None ->
                  if is_last then (pos, last_idx)
                  else
                    Reporting.unreachable (fst cannot) __POS__
                      "unname_vector_concat_elements: vector of unspecified length in vector-concat pattern"
            in
            match p with
            (* if we see a named vector pattern, remove the name and remember to
               declare it later *)
            | P_as (P_aux (p, cannot), cname) ->
                let lb, decl, info = letbind_vec typ_opt (rootid, rannot) (cname, cannot) (pos, index_j) in
                (pos', pat_acc @ [P_aux (p, cannot)], decl_acc @ [((lb, decl), info)])
            (* if we see a P_id variable, remember to declare it later *)
            | P_id cname ->
                let lb, decl, info = letbind_vec typ_opt (rootid, rannot) (cname, cannot) (pos, index_j) in
                (pos', pat_acc @ [P_aux (P_id cname, cannot)], decl_acc @ [((lb, decl), info)])
            | P_typ (typ, pat) -> aux (Some typ) (pos, pat_acc, decl_acc) (pat, is_last)
            (* | P_app (cname, pats) if Env.is_mapping cname (en) ->
             *    let (lb,decl,info) = letbind_vec typ_opt (rootid,rannot) (cname,cannot) (pos,index_j) in
             *    (pos', pat_acc @ [P_aux (P_app (cname,pats),cannot)], decl_acc @ [((lb,decl),info)]) *)
            (* normal vector patterns are fine *)
            | _ -> (pos', pat_acc @ [P_aux (p, cannot)], decl_acc)
          in
          let pats_tagged = tag_last pats in
          let _, pats', decls' = List.fold_left (aux None) (start, [], []) pats_tagged in

          (* abuse P_vector_concat as a P_vector_const pattern: it has the of
             patterns as an argument but they're meant to be consed together *)
          (P_aux (P_as (P_aux (P_vector_concat pats', rannot'), rootid), rannot), decls @ decls')
      | (p, decls), annot -> (P_aux (p, annot), decls)
    in

    {
      p_lit = (fun lit -> (P_lit lit, []));
      p_wild = (P_wild, []);
      p_or = (fun ((pat1, ds1), (pat2, ds2)) -> (P_or (pat1, pat2), ds1 @ ds2));
      p_not = (fun (pat, ds) -> (P_not pat, ds));
      p_as = (fun ((pat, decls), id) -> (P_as (pat, id), decls));
      p_typ = (fun (typ, (pat, decls)) -> (P_typ (typ, pat), decls));
      p_id = (fun id -> (P_id id, []));
      p_var = (fun ((pat, decls), kid) -> (P_var (pat, kid), decls));
      p_app =
        (fun (id, ps) ->
          let ps, decls = List.split ps in
          (P_app (id, ps), List.flatten decls)
        );
      p_vector =
        (fun ps ->
          let ps, decls = List.split ps in
          (P_vector ps, List.flatten decls)
        );
      p_vector_concat =
        (fun ps ->
          let ps, decls = List.split ps in
          (P_vector_concat ps, List.flatten decls)
        );
      p_vector_subrange = (fun (id, n, m) -> (P_vector_subrange (id, n, m), []));
      p_tuple =
        (fun ps ->
          let ps, decls = List.split ps in
          (P_tuple ps, List.flatten decls)
        );
      p_list =
        (fun ps ->
          let ps, decls = List.split ps in
          (P_list ps, List.flatten decls)
        );
      p_string_append =
        (fun ps ->
          let ps, decls = List.split ps in
          (P_string_append ps, List.flatten decls)
        );
      p_struct =
        (fun (fpats, fwild) ->
          let fields, ps = List.split fpats in
          let ps, decls = List.split ps in
          (P_struct (List.map2 (fun field p -> (field, p)) fields ps, fwild), List.flatten decls)
        );
      p_cons = (fun ((p, decls), (p', decls')) -> (P_cons (p, p'), decls @ decls'));
      p_aux = (fun ((pat, decls), annot) -> p_aux ((pat, decls), annot));
    }
  in

  let pat, decls = fold_pat unname_vector_concat_elements pat in

  (* We need to put the decls in the right order so letbinds are generated correctly for nested patterns *)
  let module G = Graph.Make (String) in
  let root_graph = List.fold_left (fun g (_, (root_id, child_id)) -> G.add_edge root_id child_id g) G.empty decls in
  let root_order = G.topsort root_graph in
  let find_root root_id =
    try List.find (fun (_, (root_id', _)) -> root_id = root_id') decls
    with Not_found -> (
      (* If it's not a root then it's a leaf node in the graph, so search for child_id *)
      try List.find (fun (_, (_, child_id)) -> root_id = child_id) decls
      with Not_found -> assert false (* Should never happen *)
    )
  in
  let decls = List.map find_root root_order in

  let letbinds, decls =
    let decls = List.map fst decls in
    List.split decls
  in

  let decls = List.fold_left (fun f g x -> f (g x)) (fun b -> b) decls in

  (* Finally we patch up the top location for the expressions wrapped
     by decls, otherwise this can cause the coverage instrumentation
     to get super confused by the generated locations *)
  let decls (E_aux (_, (l, _)) as exp) =
    let (E_aux (aux, (_, annot))) = decls exp in
    E_aux (aux, (gen_loc l, annot))
  in

  (* at this point shouldn't have P_as patterns in P_vector_concat patterns any more,
     all P_as and P_id vectors should have their declarations in decls.
     Now flatten all vector_concat patterns *)
  let flatten =
    let p_vector_concat ps =
      let aux p acc = match p with P_aux (P_vector_concat pats, _) -> pats @ acc | pat -> pat :: acc in
      P_vector_concat (List.fold_right aux ps [])
    in
    { id_pat_alg with p_vector_concat }
  in

  let pat = fold_pat flatten pat in

  (* at this point pat should be a flat pattern: no vector_concat patterns
     with vector_concats patterns as direct child-nodes anymore *)
  let range a b =
    let rec aux a b = if Big_int.greater a b then [] else a :: aux (Big_int.add a (Big_int.of_int 1)) b in
    if Big_int.greater a b then List.rev (aux b a) else aux a b
  in

  let remove_vector_concats =
    let p_vector_concat ps =
      let aux acc (P_aux (p, annot), is_last) =
        let env = env_of_annot annot in
        let typ = Env.base_typ_of env (typ_of_annot annot) in
        let l, _ = annot in
        let wild _ = P_aux (P_wild, (gen_loc l, mk_tannot env bit_typ)) in
        if is_vector_typ typ || is_bitvector_typ typ then (
          match (p, vector_typ_args_of typ) with
          | P_vector ps, _ -> acc @ ps
          | _, (nexp, _) -> begin
              match Type_check.solve_unique env nexp with
              | Some length -> acc @ List.map wild (range Big_int.zero (Big_int.sub length (Big_int.of_int 1)))
              | None -> acc @ [wild Big_int.zero]
            end
        )
        else
          raise
            (Reporting.err_unreachable l __POS__
               ("remove_vector_concats: Non-vector in vector-concat pattern " ^ string_of_typ (typ_of_annot annot))
            )
      in

      let ps_tagged = tag_last ps in
      let ps' = List.fold_left aux [] ps_tagged in

      P_vector ps'
    in

    { id_pat_alg with p_vector_concat }
  in

  let pat = fold_pat remove_vector_concats pat in

  (pat, letbinds, decls)

(* assumes there are no more E_internal expressions *)
let rewrite_exp_remove_vector_concat_pat rewriters (E_aux (exp, (l, annot)) as full_exp) =
  let rewrap e = E_aux (e, (l, annot)) in
  let rewrite_rec = rewriters.rewrite_exp rewriters in
  let rewrite_base = rewrite_exp rewriters in
  match exp with
  | E_match (e, ps) ->
      let aux = function
        | Pat_aux (Pat_exp (pat, body), annot') ->
            let pat, _, decls = remove_vector_concat_pat pat in
            Pat_aux (Pat_exp (pat, decls (rewrite_rec body)), annot')
        | Pat_aux (Pat_when (pat, guard, body), annot') ->
            let pat, _, decls = remove_vector_concat_pat pat in
            Pat_aux (Pat_when (pat, decls (rewrite_rec guard), decls (rewrite_rec body)), annot')
      in
      rewrap (E_match (rewrite_rec e, List.map aux ps))
  | E_let (LB_aux (LB_val (pat, v), annot'), body) ->
      let pat, _, decls = remove_vector_concat_pat pat in
      rewrap (E_let (LB_aux (LB_val (pat, rewrite_rec v), annot'), decls (rewrite_rec body)))
  | exp -> rewrite_base full_exp

let rewrite_fun_remove_vector_concat_pat rewriters (FD_aux (FD_function (recopt, tannotopt, funcls), (l, fdannot))) =
  let rewrite_funcl (FCL_aux (FCL_funcl (id, pexp), (l, annot))) =
    let pat, guard, exp, pannot = destruct_pexp pexp in
    let pat', _, decls = remove_vector_concat_pat pat in
    let guard' = match guard with Some exp -> Some (decls (rewriters.rewrite_exp rewriters exp)) | None -> None in
    let exp' = decls (rewriters.rewrite_exp rewriters exp) in
    let pexp' = construct_pexp (pat', guard', exp', pannot) in
    FCL_aux (FCL_funcl (id, pexp'), (l, annot))
  in
  FD_aux (FD_function (recopt, tannotopt, List.map rewrite_funcl funcls), (l, fdannot))

let rewrite_ast_remove_vector_concat env ast =
  let rewriters =
    {
      rewrite_exp = rewrite_exp_remove_vector_concat_pat;
      rewrite_pat;
      rewrite_let;
      rewrite_lexp;
      rewrite_fun = rewrite_fun_remove_vector_concat_pat;
      rewrite_def;
      rewrite_ast = rewrite_ast_base;
    }
  in
  let rewrite_def d =
    let d = rewriters.rewrite_def rewriters d in
    match d with
    | DEF_aux (DEF_let (LB_aux (LB_val (pat, exp), a)), def_annot) ->
        let pat, letbinds, _ = remove_vector_concat_pat pat in
        let defvals = List.map (fun lb -> DEF_aux (DEF_let lb, mk_def_annot (gen_loc def_annot.loc))) letbinds in
        [DEF_aux (DEF_let (LB_aux (LB_val (pat, exp), a)), def_annot)] @ defvals
    | d -> [d]
  in
  { ast with defs = List.flatten (List.map rewrite_def ast.defs) }

(* A few helper functions for rewriting guarded pattern clauses.
   Used both by the rewriting of P_when and separately by the rewriting of
   bitvectors in parameter patterns of function clauses *)

let remove_wildcards pre (P_aux (_, (l, _)) as pat) =
  fold_pat
    {
      id_pat_alg with
      p_aux = (function P_wild, (l, annot) -> P_aux (P_id (fresh_id pre l), (l, annot)) | p, annot -> P_aux (p, annot));
    }
    pat

let rec is_irrefutable_pattern (P_aux (p, ann)) =
  match p with
  | P_lit (L_aux (L_unit, _)) | P_wild -> true
  | P_or (pat1, pat2) -> is_irrefutable_pattern pat1 && is_irrefutable_pattern pat2
  | P_not pat -> is_irrefutable_pattern pat
  | P_lit _ -> false
  | P_as (p1, _) | P_typ (_, p1) -> is_irrefutable_pattern p1
  | P_vector_subrange _ -> true
  | P_id id -> begin
      match Env.lookup_id id (env_of_annot ann) with
      | Local _ | Unbound _ -> true
      | Register _ -> false (* should be impossible, anyway *)
      | Enum enum -> (
          match enum with
          | Typ_aux (Typ_id enum_id, _) -> List.length (Env.get_enum enum_id (env_of_annot ann)) <= 1
          | _ -> false (* should be impossible, anyway *)
        )
    end
  | P_var (p1, _) -> is_irrefutable_pattern p1
  | P_app (f, args) ->
      Env.is_singleton_union_constructor f (env_of_annot ann) && List.for_all is_irrefutable_pattern args
  | P_vector ps | P_vector_concat ps | P_tuple ps | P_list ps -> List.for_all is_irrefutable_pattern ps
  | P_struct (fpats, _) ->
      let ps = List.map snd fpats in
      List.for_all is_irrefutable_pattern ps
  | P_cons (p1, p2) -> is_irrefutable_pattern p1 && is_irrefutable_pattern p2
  | P_string_append ps -> List.for_all is_irrefutable_pattern ps

(* Check if one pattern subsumes the other, and if so, calculate a
   substitution of variables that are used in the same position.
   TODO: Check somewhere that there are no variable clashes (the same variable
   name used in different positions of the patterns)
*)
let rec subsumes_pat (P_aux (p1, annot1) as pat1) (P_aux (p2, annot2) as pat2) =
  let rewrap p = P_aux (p, annot1) in
  let subsumes_list pats1 pats2 =
    if List.length pats1 = List.length pats2 then (
      let subs = List.map2 subsumes_pat pats1 pats2 in
      List.fold_right
        (fun p acc -> match (p, acc) with Some subst, Some substs -> Some (subst @ substs) | _ -> None)
        subs (Some [])
    )
    else None
  in
  match (p1, p2) with
  | P_lit (L_aux (lit1, _)), P_lit (L_aux (lit2, _)) -> if lit1 = lit2 then Some [] else None
  | P_or (pat1, pat2), _ -> (* todo: possibly not the right answer *) None
  | _, P_or (pat1, pat2) -> (* todo: possibly not the right answer *) None
  | P_not pat, _ -> (* todo: possibly not the right answer *) None
  | _, P_not pat -> (* todo: possibly not the right answer *) None
  | P_as (pat1, id1), _ ->
      (* Abuse subsumes_list to check that both the nested pattern and the
       * variable binding can subsume the other pattern *)
      subsumes_list [P_aux (P_id id1, annot1); pat1] [pat2; pat2]
  | _, P_as (pat2, id2) ->
      (* Ditto for the other direction *)
      subsumes_list [pat1; pat1] [P_aux (P_id id2, annot2); pat2]
  | P_typ (_, pat1), _ -> subsumes_pat pat1 pat2
  | _, P_typ (_, pat2) -> subsumes_pat pat1 pat2
  | P_id (Id_aux (id1, _) as aid1), P_id (Id_aux (id2, _) as aid2) ->
      if id1 = id2 then Some []
      else if is_unbound (Env.lookup_id aid1 (env_of_annot annot1)) then
        if is_unbound (Env.lookup_id aid2 (env_of_annot annot2)) then Some [(id2, id1)] else Some []
      else None
  | P_id id1, _ -> if is_unbound (Env.lookup_id id1 (env_of_annot annot1)) then Some [] else None
  | P_var (pat1, _), P_var (pat2, _) -> subsumes_pat pat1 pat2
  | P_wild, _ -> Some []
  | P_app (Id_aux (id1, _), args1), P_app (Id_aux (id2, _), args2) ->
      if id1 = id2 then subsumes_list args1 args2 else None
  | P_vector pats1, P_vector pats2
  | P_vector_concat pats1, P_vector_concat pats2
  | P_tuple pats1, P_tuple pats2
  | P_list pats1, P_list pats2 ->
      subsumes_list pats1 pats2
  | P_list (pat1 :: pats1), P_cons _ -> subsumes_pat (rewrap (P_cons (pat1, rewrap (P_list pats1)))) pat2
  | P_cons _, P_list (pat2 :: pats2) -> subsumes_pat pat1 (rewrap (P_cons (pat2, rewrap (P_list pats2))))
  | P_cons (pat1, pats1), P_cons (pat2, pats2) -> (
      match (subsumes_pat pat1 pat2, subsumes_pat pats1 pats2) with
      | Some substs1, Some substs2 -> Some (substs1 @ substs2)
      | _ -> None
    )
  | P_struct (fields1, wild1), P_struct (fields2, wild2) ->
      List.fold_left
        (fun acc (f1, p1) ->
          match List.find_opt (fun (f2, _) -> Id.compare f1 f2 == 0) fields2 with
          | Some (_, p2) -> (
              match (subsumes_pat p1 p2, acc) with Some subst, Some substs -> Some (subst @ substs) | _ -> None
            )
          | None -> (
              match wild2 with
              | FP_wild _ -> if is_irrefutable_pattern p1 then acc else None
              | FP_no_wild -> Reporting.unreachable (fst annot2) __POS__ "Field mismatch in guarded patterns rewrite"
            )
        )
        (Some []) fields1
  | _, P_wild -> if is_irrefutable_pattern pat1 then Some [] else None
  | _ -> None

let vector_string_to_bits_pat (L_aux (lit, _) as l_aux) (l, tannot) =
  let bit_annot = match destruct_tannot tannot with Some (env, _) -> mk_tannot env bit_typ | None -> empty_tannot in
  begin
    match lit with
    | L_hex _ | L_bin _ ->
        P_aux
          (P_vector (List.map (fun p -> P_aux (P_lit p, (l, bit_annot))) (vector_string_to_bit_list l_aux)), (l, tannot))
    | lit -> P_aux (P_lit l_aux, (l, tannot))
  end

let vector_string_to_bits_exp (L_aux (lit, _) as l_aux) (l, tannot) =
  let bit_annot = match destruct_tannot tannot with Some (env, _) -> mk_tannot env bit_typ | None -> empty_tannot in
  begin
    match lit with
    | L_hex _ | L_bin _ ->
        E_aux
          (E_vector (List.map (fun p -> E_aux (E_lit p, (l, bit_annot))) (vector_string_to_bit_list l_aux)), (l, tannot))
    | lit -> E_aux (E_lit l_aux, (l, tannot))
  end

(* A simple check for pattern disjointness; used for optimisation in the
   guarded pattern rewrite step *)
let rec disjoint_pat env (P_aux (p1, annot1) as pat1) (P_aux (p2, annot2) as pat2) =
  match (p1, p2) with
  | P_as (pat1, _), _ -> disjoint_pat env pat1 pat2
  | _, P_as (pat2, _) -> disjoint_pat env pat1 pat2
  | P_typ (_, pat1), _ -> disjoint_pat env pat1 pat2
  | _, P_typ (_, pat2) -> disjoint_pat env pat1 pat2
  | P_var (pat1, _), _ -> disjoint_pat env pat1 pat2
  | _, P_var (pat2, _) -> disjoint_pat env pat1 pat2
  | P_id id, _ when id_is_unbound id env -> false
  | _, P_id id when id_is_unbound id env -> false
  | P_id id1, P_id id2 -> Id.compare id1 id2 <> 0
  | P_lit (L_aux ((L_bin _ | L_hex _), _) as lit), _ ->
      disjoint_pat env (vector_string_to_bits_pat lit (Unknown, empty_tannot)) pat2
  | _, P_lit (L_aux ((L_bin _ | L_hex _), _) as lit) ->
      disjoint_pat env pat1 (vector_string_to_bits_pat lit (Unknown, empty_tannot))
  | P_lit (L_aux (L_num n1, _)), P_lit (L_aux (L_num n2, _)) -> not (Big_int.equal n1 n2)
  | P_lit (L_aux (l1, _)), P_lit (L_aux (l2, _)) -> l1 <> l2
  | P_app (id1, args1), P_app (id2, args2) -> Id.compare id1 id2 <> 0 || List.exists2 (disjoint_pat env) args1 args2
  | P_vector pats1, P_vector pats2 | P_tuple pats1, P_tuple pats2 | P_list pats1, P_list pats2 ->
      List.length pats1 <> List.length pats2 || List.exists2 (disjoint_pat env) pats1 pats2
  | _ -> false

let equiv_pats pat1 pat2 =
  match (subsumes_pat pat1 pat2, subsumes_pat pat2 pat1) with Some _, Some _ -> true | _, _ -> false

let subst_id_pat pat (id1, id2) =
  let p_id (Id_aux (id, l)) = if id = id1 then P_id (Id_aux (id2, l)) else P_id (Id_aux (id, l)) in
  fold_pat { id_pat_alg with p_id } pat

let subst_id_exp exp (id1, id2) =
  Ast_util.subst
    (Id_aux (id1, Parse_ast.Unknown))
    (E_aux (E_id (Id_aux (id2, Parse_ast.Unknown)), (Parse_ast.Unknown, empty_tannot)))
    exp

let rec pat_to_exp (P_aux (pat, (l, annot)) as p_aux) =
  let rewrap e = E_aux (e, (l, annot)) in
  let env = env_of_pat p_aux in
  let typ = typ_of_pat p_aux in
  match pat with
  | P_lit lit -> rewrap (E_lit lit)
  | P_wild -> Reporting.unreachable l __POS__ "pat_to_exp given wildcard pattern"
  | P_or (pat1, pat2) -> (* todo: insert boolean or *) pat_to_exp pat1
  | P_not pat -> (* todo: insert boolean not *) pat_to_exp pat
  | P_as (pat, id) -> rewrap (E_id id)
  | P_var (pat, _) -> pat_to_exp pat
  | P_typ (_, pat) -> pat_to_exp pat
  | P_id id -> rewrap (E_id id)
  | P_vector_subrange (id, n, m) ->
      let subrange = mk_exp (E_vector_subrange (mk_exp (E_id id), mk_lit_exp (L_num n), mk_lit_exp (L_num m))) in
      check_exp env subrange typ
  | P_app (id, pats) -> rewrap (E_app (id, List.map pat_to_exp pats))
  | P_vector pats -> rewrap (E_vector (List.map pat_to_exp pats))
  | P_vector_concat pats -> begin
      let empty_vec = E_aux (E_vector [], (l, empty_uannot)) in
      let concat_vectors vec1 vec2 = E_aux (E_vector_append (vec1, vec2), (l, empty_uannot)) in
      check_exp env (List.fold_right concat_vectors (List.map (fun p -> strip_exp (pat_to_exp p)) pats) empty_vec) typ
    end
  | P_tuple pats -> rewrap (E_tuple (List.map pat_to_exp pats))
  | P_list pats -> rewrap (E_list (List.map pat_to_exp pats))
  | P_cons (p, ps) -> rewrap (E_cons (pat_to_exp p, pat_to_exp ps))
  | P_string_append pats -> begin
      let empty_string = annot_exp (E_lit (L_aux (L_string "", l))) l env string_typ in
      let string_append str1 str2 = annot_exp (E_app (mk_id "string_append", [str1; str2])) l env string_typ in
      List.fold_right string_append (List.map pat_to_exp pats) empty_string
    end
  | P_struct (fpats, FP_no_wild) ->
      rewrap
        (E_struct
           (List.map (fun (field, pat) -> FE_aux (FE_fexp (field, pat_to_exp pat), (gen_loc l, empty_tannot))) fpats)
        )
  | P_struct (_, FP_wild l) -> Reporting.unreachable l __POS__ "pat_to_exp given field wildcard"

let case_exp e t cs =
  let l = get_loc_exp e in
  let env = env_of e in
  match cs with
  | [(P_aux (P_wild, _), body, _)] -> body
  | [((P_aux (P_id id, pannot) as pat), body, _)] -> annot_exp (E_let (LB_aux (LB_val (pat, e), pannot), body)) l env t
  | _ ->
      let pexp (pat, body, annot) = Pat_aux (Pat_exp (pat, body), annot) in
      let ps = List.map pexp cs in
      annot_exp (E_match (e, ps)) l env t

module PC_config = struct
  type t = tannot
  let typ_of_t = typ_of_tannot
  let add_attribute l attr arg = map_uannot (add_attribute l attr arg)
end

module PC = Pattern_completeness.Make (PC_config)

let pats_complete l env ps typ =
  let ctx =
    {
      Pattern_completeness.variants = Env.get_variants env;
      Pattern_completeness.structs = Env.get_records env;
      Pattern_completeness.enums = Env.get_enums env;
      Pattern_completeness.constraints = Env.get_constraints env;
    }
  in
  PC.is_complete l ctx ps typ

(* Rewrite guarded patterns into a combination of if-expressions and
    unguarded pattern matches

    Strategy:
    - Split clauses into groups where the first pattern subsumes all the
      following ones
    - Translate the groups in reverse order, using the next group as a
      fall-through target, if there is one
    - Within a group,
      - translate the sequence of clauses to an if-then-else cascade using the
        guards as long as the patterns are equivalent modulo substitution, or
      - recursively translate the remaining clauses to a pattern match if
        there is a difference in the patterns.

   TODO: Compare this more closely with the algorithm in the CPP'18 paper of
   Spector-Zabusky et al, who seem to use the opposite grouping and merging
   strategy to ours: group *mutually exclusive* clauses, and try to merge them
   into a pattern match first instead of an if-then-else cascade.
*)
let rewrite_toplevel_guarded_clauses mk_fallthrough l env pat_typ typ
    (cs : (tannot pat * tannot exp option * tannot exp * tannot clause_annot) list) =
  let annot_from_clause (def_annot, tannot) = (def_annot.loc, tannot) in
  let fix_fallthrough (pat, guard, exp, (l, tannot)) = (pat, guard, exp, (mk_def_annot l, tannot)) in

  let rec group fallthrough clauses =
    let add_clause (pat, cls, annot) c = (pat, cls @ [c], annot) in
    let rec group_aux current acc = function
      | ((pat, guard, body, annot) as c) :: cs -> (
          let current_pat, _, _ = current in
          match subsumes_pat current_pat pat with
          | Some substs ->
              let pat' = List.fold_left subst_id_pat pat substs in
              let guard' =
                match guard with Some exp -> Some (List.fold_left subst_id_exp exp substs) | None -> None
              in
              let body' = List.fold_left subst_id_exp body substs in
              let c' = (pat', guard', body', annot) in
              group_aux (add_clause current c') acc cs
          | None ->
              let pat = match cs with _ :: _ -> remove_wildcards "g__" pat | _ -> pat in
              group_aux (pat, [c], annot_from_clause annot) (acc @ [current]) cs
        )
      | [] -> acc @ [current]
    in
    let groups =
      match clauses with
      | [((pat, guard, body, annot) as c)] -> [(pat, [c], annot_from_clause annot)]
      | ((pat, guard, body, annot) as c) :: cs ->
          group_aux (remove_wildcards "g__" pat, [c], annot_from_clause annot) [] cs
      | _ -> raise (Reporting.err_unreachable l __POS__ "group given empty list in rewrite_guarded_clauses")
    in
    let add_group cs groups = if_pexp (groups @ fallthrough) cs :: groups in
    List.fold_right add_group groups []
  and if_pexp fallthrough (pat, cs, annot) =
    match cs with
    | c :: _ ->
        let body = if_exp fallthrough pat cs in
        (pat, body, annot)
    | [] -> raise (Reporting.err_unreachable l __POS__ "if_pexp given empty list in rewrite_guarded_clauses")
  and if_exp fallthrough current_pat = function
    | (pat, guard, body, annot) :: ((pat', guard', body', annot') as c') :: cs -> (
        match guard with
        | Some exp ->
            let else_exp =
              if equiv_pats current_pat pat' then if_exp fallthrough current_pat (c' :: cs)
              else case_exp (pat_to_exp current_pat) (typ_of body') (group fallthrough (c' :: cs))
            in
            annot_exp (E_if (exp, body, else_exp)) (fst annot).loc (env_of exp) (typ_of body)
        | None -> body
      )
    | [(pat, guard, body, annot)] -> (
        (* For singleton clauses with a guard, use fallthrough clauses if the
           guard is not satisfied, but only those fallthrough clauses that are
           not disjoint with the current pattern *)
        let overlapping_clause (pat, _, _) = not (disjoint_pat env current_pat pat) in
        let fallthrough = List.filter overlapping_clause fallthrough in
        match (guard, fallthrough) with
        | Some exp, _ :: _ ->
            let else_exp = case_exp (pat_to_exp current_pat) (typ_of body) fallthrough in
            annot_exp (E_if (exp, body, else_exp)) (fst annot).loc (env_of exp) (typ_of body)
        | _, _ -> body
      )
    | [] -> raise (Reporting.err_unreachable l __POS__ "if_exp given empty list in rewrite_guarded_clauses")
  in

  let is_complete =
    pats_complete l env
      (List.map (fun (pat, guard, body, cl_annot) -> construct_pexp (pat, guard, body, annot_from_clause cl_annot)) cs)
      pat_typ
  in
  let fallthrough =
    if not is_complete then [fix_fallthrough (destruct_pexp (mk_fallthrough l env pat_typ typ))] else []
  in
  group [] (cs @ fallthrough)

let rewrite_guarded_clauses mk_fallthrough l env pat_typ typ
    (cs : (tannot pat * tannot exp option * tannot exp * tannot annot) list) =
  let map_clause_annot f cs = List.map (fun (pat, guard, body, annot) -> (pat, guard, body, f annot)) cs in
  let cs = map_clause_annot (fun (l, tannot) -> (mk_def_annot l, tannot)) cs in
  rewrite_toplevel_guarded_clauses mk_fallthrough l env pat_typ typ cs

let mk_pattern_match_failure_pexp l env pat_typ typ =
  let p = P_aux (P_wild, (gen_loc l, mk_tannot env pat_typ)) in
  let msg = "Pattern match failure at " ^ Reporting.short_loc_to_string l in
  let a = mk_exp ~loc:(gen_loc l) (E_assert (mk_lit_exp L_false, mk_lit_exp (L_string msg))) in
  let b = mk_exp ~loc:(gen_loc l) (E_exit (mk_lit_exp L_unit)) in
  let (E_aux (_, (_, ann)) as e) = check_exp env (mk_exp ~loc:(gen_loc l) (E_block [a; b])) typ in
  construct_pexp (p, None, e, (gen_loc l, ann))

let mk_rethrow_pexp l env pat_typ typ =
  let p, env' = bind_pat_no_guard env (mk_pat (P_id (mk_id "e"))) pat_typ in
  let (E_aux (_, a) as e) = check_exp env' (mk_exp ~loc:(gen_loc l) (E_throw (mk_exp (E_id (mk_id "e"))))) typ in
  construct_pexp (p, None, e, a)

let bitwise_and_exp exp1 exp2 =
  let (E_aux (_, (l, _))) = exp1 in
  let andid = Id_aux (Id "and_bool", gen_loc l) in
  annot_exp (E_app (andid, [exp1; exp2])) l (env_of exp1) bool_typ

let compose_guard_opt g1 g2 =
  match (g1, g2) with
  | Some g1, Some g2 -> Some (bitwise_and_exp g1 g2)
  | Some g1, None -> Some g1
  | None, Some g2 -> Some g2
  | None, None -> None

let rec contains_bitvector_pat (P_aux (pat, annot)) =
  match pat with
  | P_lit _ | P_wild | P_id _ -> false
  | P_vector_subrange _ -> true
  | P_as (pat, _) | P_typ (_, pat) | P_var (pat, _) -> contains_bitvector_pat pat
  | P_or (pat1, pat2) -> contains_bitvector_pat pat1 || contains_bitvector_pat pat2
  | P_not pat -> contains_bitvector_pat pat
  | P_vector _ | P_vector_concat _ ->
      let typ = Env.base_typ_of (env_of_annot annot) (typ_of_annot annot) in
      is_bitvector_typ typ
  | P_app (_, pats) | P_tuple pats | P_list pats -> List.exists contains_bitvector_pat pats
  | P_cons (p, ps) -> contains_bitvector_pat p || contains_bitvector_pat ps
  | P_string_append ps -> List.exists contains_bitvector_pat ps
  | P_struct (fpats, _) -> List.exists contains_bitvector_pat (List.map snd fpats)

let contains_bitvector_pexp = function
  | Pat_aux (Pat_exp (pat, _), _) | Pat_aux (Pat_when (pat, _, _), _) -> contains_bitvector_pat pat

(* Rewrite bitvector patterns to guarded patterns *)

let remove_bitvector_pat (P_aux (_, (l, _)) as pat) =
  let env =
    try env_of_pat pat with _ -> raise (Reporting.err_unreachable l __POS__ "Pattern without annotation found")
  in

  (* first introduce names for bitvector patterns *)
  let name_bitvector_roots =
    {
      p_lit = (fun lit -> P_lit lit);
      p_typ = (fun (typ, p) -> P_typ (typ, p false));
      p_wild =
        P_wild
        (* todo: I have no idea what the boolean parameter means - so I randomly
         * passed "true".  A comment to explain the bool might be a good idea?
         *);
      p_or = (fun (pat1, pat2) -> P_or (pat1 true, pat2 true));
      p_not = (fun pat -> P_not (pat true));
      p_as = (fun (pat, id) -> P_as (pat true, id));
      p_id = (fun id -> P_id id);
      p_var = (fun (pat, kid) -> P_var (pat true, kid));
      p_app = (fun (id, ps) -> P_app (id, List.map (fun p -> p false) ps));
      p_vector = (fun ps -> P_vector (List.map (fun p -> p false) ps));
      p_vector_concat = (fun ps -> P_vector_concat (List.map (fun p -> p false) ps));
      p_vector_subrange = (fun (id, n, m) -> P_vector_subrange (id, n, m));
      p_string_append = (fun ps -> P_string_append (List.map (fun p -> p false) ps));
      p_tuple = (fun ps -> P_tuple (List.map (fun p -> p false) ps));
      p_list = (fun ps -> P_list (List.map (fun p -> p false) ps));
      p_cons = (fun (p, ps) -> P_cons (p false, ps false));
      p_struct = (fun (fpats, fwild) -> P_struct (List.map (fun (field, p) -> (field, p false)) fpats, fwild));
      p_aux =
        (fun (pat, annot) contained_in_p_as ->
          let env = env_of_annot annot in
          let t = Env.base_typ_of env (typ_of_annot annot) in
          let l, _ = annot in
          match (pat, is_bitvector_typ t, contained_in_p_as) with
          | P_vector _, true, false -> P_aux (P_as (P_aux (pat, annot), fresh_id "b__" l), annot)
          | _ -> P_aux (pat, annot)
        );
    }
  in
  let pat, env = bind_pat_no_guard env (strip_pat ((fold_pat name_bitvector_roots pat) false)) (typ_of_pat pat) in

  (* Then collect guard expressions testing whether the literal bits of a
     bitvector pattern match those of a given bitvector, and collect let
     bindings for the bits bound by P_id or P_as patterns *)

  (* Helper functions for generating guard expressions *)
  let mk_exp e_aux = E_aux (e_aux, (l, empty_uannot)) in
  let mk_num_exp i = mk_lit_exp (L_num i) in
  let check_eq_exp l r =
    let exp = mk_exp (E_app_infix (l, Id_aux (Operator "==", Parse_ast.Unknown), r)) in
    check_exp env exp bool_typ
  in

  let access_bit_exp rootid l typ idx =
    let access_aux = E_vector_access (mk_exp (E_id rootid), mk_num_exp idx) in
    check_exp env (mk_exp access_aux) bit_typ
  in

  let test_subvec_exp rootid l typ i j lits =
    let start = vector_start_index env typ in
    let length, _ = vector_typ_args_of typ in
    let subvec_exp =
      match (start, length) with
      | Nexp_aux (Nexp_constant s, _), Nexp_aux (Nexp_constant l, _)
        when Big_int.equal s i && Big_int.equal l (Big_int.of_int (List.length lits)) ->
          mk_exp (E_id rootid)
      | _ -> mk_exp (E_vector_subrange (mk_exp (E_id rootid), mk_num_exp i, mk_num_exp j))
    in
    check_eq_exp subvec_exp (mk_exp (E_vector (List.map strip_exp lits)))
  in

  let letbind_bit_exp rootid l typ idx id =
    let elem = access_bit_exp rootid l typ idx in
    let e = annot_pat (P_id id) l env bit_typ in
    let letbind = LB_aux (LB_val (e, elem), (l, mk_tannot env bit_typ)) in
    let letexp body =
      let (E_aux (_, (_, bannot))) = body in
      if IdSet.mem id (find_used_vars body) then annot_exp (E_let (letbind, body)) l env (typ_of body) else body
    in
    (letexp, letbind)
  in

  let compose_guards guards = List.fold_right compose_guard_opt guards None in

  let flatten_guards_decls gd =
    let guards, decls, letbinds = Util.split3 gd in
    (compose_guards guards, List.fold_right ( @@ ) decls, List.flatten letbinds)
  in

  (* Collect guards and let bindings *)
  let guard_bitvector_pat =
    let collect_guards_decls ps rootid t =
      let start = vector_start_index env t in
      let ord = Env.get_default_order env in
      let _, _ = vector_typ_args_of t in
      let start_idx =
        match start with
        | Nexp_aux (Nexp_constant s, _) -> s
        | _ ->
            raise
              (Reporting.err_unreachable l __POS__ "guard_bitvector_pat called on pattern with non-constant start index")
      in
      let add_bit_pat (idx, current, guards, dls) pat =
        let idx' =
          if is_order_inc ord then Big_int.add idx (Big_int.of_int 1) else Big_int.sub idx (Big_int.of_int 1)
        in
        let ids =
          fst
            (fold_pat
               {
                 (compute_pat_alg IdSet.empty IdSet.union) with
                 p_id = (fun id -> (IdSet.singleton id, P_id id));
                 p_as = (fun ((ids, pat), id) -> (IdSet.add id ids, P_as (pat, id)));
               }
               pat
            )
        in
        let lits =
          fst
            (fold_pat
               {
                 (compute_pat_alg [] ( @ )) with
                 p_aux =
                   (fun ((lits, paux), (l, annot)) ->
                     let lits = match paux with P_lit lit -> E_aux (E_lit lit, (l, annot)) :: lits | _ -> lits in
                     (lits, P_aux (paux, (l, annot)))
                   );
               }
               pat
            )
        in
        let add_letbind id dls = dls @ [letbind_bit_exp rootid l t idx id] in
        let dls' = IdSet.fold add_letbind ids dls in
        let current', guards' =
          match current with
          | Some (l, i, j, lits') ->
              if lits = [] then (None, guards @ [Some (test_subvec_exp rootid l t i j lits')])
              else (Some (l, i, idx, lits' @ lits), guards)
          | None -> begin
              match lits with E_aux (_, (l, _)) :: _ -> (Some (l, idx, idx, lits), guards) | [] -> (None, guards)
            end
        in
        (idx', current', guards', dls')
      in
      let _, final, guards, dls = List.fold_left add_bit_pat (start_idx, None, [], []) ps in
      let guards =
        match final with
        | Some (l, i, j, lits) -> guards @ [Some (test_subvec_exp rootid l t i j lits)]
        | None -> guards
      in
      let decls, letbinds = List.split dls in
      (compose_guards guards, List.fold_right ( @@ ) decls, letbinds)
    in

    {
      p_lit = (fun lit -> (P_lit lit, (None, (fun b -> b), [])));
      p_wild = (P_wild, (None, (fun b -> b), []));
      p_or = (fun ((pat1, gdl1), (pat2, gdl2)) -> (P_or (pat1, pat2), flatten_guards_decls [gdl1; gdl2]));
      p_not = (fun (pat, gdl) -> (P_not pat, gdl));
      p_as = (fun ((pat, gdls), id) -> (P_as (pat, id), gdls));
      p_typ = (fun (typ, (pat, gdls)) -> (P_typ (typ, pat), gdls));
      p_id = (fun id -> (P_id id, (None, (fun b -> b), [])));
      p_var = (fun ((pat, gdls), kid) -> (P_var (pat, kid), gdls));
      p_app =
        (fun (id, ps) ->
          let ps, gdls = List.split ps in
          (P_app (id, ps), flatten_guards_decls gdls)
        );
      p_vector =
        (fun ps ->
          let ps, gdls = List.split ps in
          (P_vector ps, flatten_guards_decls gdls)
        );
      p_vector_concat =
        (fun ps ->
          let ps, gdls = List.split ps in
          (P_vector_concat ps, flatten_guards_decls gdls)
        );
      p_vector_subrange = (fun (id, n, m) -> (P_vector_subrange (id, n, m), (None, (fun b -> b), [])));
      p_string_append =
        (fun ps ->
          let ps, gdls = List.split ps in
          (P_string_append ps, flatten_guards_decls gdls)
        );
      p_struct =
        (fun (fpats, fwild) ->
          let fields, ps = List.split fpats in
          let ps, gdls = List.split ps in
          (P_struct (List.map2 (fun field p -> (field, p)) fields ps, fwild), flatten_guards_decls gdls)
        );
      p_tuple =
        (fun ps ->
          let ps, gdls = List.split ps in
          (P_tuple ps, flatten_guards_decls gdls)
        );
      p_list =
        (fun ps ->
          let ps, gdls = List.split ps in
          (P_list ps, flatten_guards_decls gdls)
        );
      p_cons = (fun ((p, gdls), (p', gdls')) -> (P_cons (p, p'), flatten_guards_decls [gdls; gdls']));
      p_aux =
        (fun ((pat, gdls), annot) ->
          let env = env_of_annot annot in
          let t = Env.base_typ_of env (typ_of_annot annot) in
          match (pat, is_bitvector_typ t) with
          | P_as (P_aux (P_vector ps, _), id), true -> (P_aux (P_id id, annot), collect_guards_decls ps id t)
          | _, _ -> (P_aux (pat, annot), gdls)
        );
    }
  in
  fold_pat guard_bitvector_pat pat

let rewrite_exp_remove_bitvector_pat rewriters (E_aux (exp, (l, annot)) as full_exp) =
  let rewrap e = E_aux (e, (l, annot)) in
  let rewrite_rec = rewriters.rewrite_exp rewriters in
  let rewrite_base = rewrite_exp rewriters in
  match exp with
  | E_match (e, ps) when List.exists contains_bitvector_pexp ps ->
      let rewrite_pexp = function
        | Pat_aux (Pat_exp (pat, body), annot') -> (
            let pat', (guard', decls, _) = remove_bitvector_pat pat in
            let body' = decls (rewrite_rec body) in
            match guard' with
            | Some guard' -> Pat_aux (Pat_when (pat', guard', body'), annot')
            | None -> Pat_aux (Pat_exp (pat', body'), annot')
          )
        | Pat_aux (Pat_when (pat, guard, body), annot') -> (
            let pat', (guard', decls, _) = remove_bitvector_pat pat in
            let guard'' = rewrite_rec guard in
            let body' = decls (rewrite_rec body) in
            match guard' with
            | Some guard' -> Pat_aux (Pat_when (pat', bitwise_and_exp (decls guard'') guard', body'), annot')
            | None -> Pat_aux (Pat_when (pat', decls guard'', body'), annot')
          )
      in
      rewrap (E_match (e, List.map rewrite_pexp ps))
  | E_let (LB_aux (LB_val (pat, v), annot'), body) ->
      let pat, (_, decls, _) = remove_bitvector_pat pat in
      rewrap (E_let (LB_aux (LB_val (pat, rewrite_rec v), annot'), decls (rewrite_rec body)))
  | _ -> rewrite_base full_exp

let rewrite_fun_remove_bitvector_pat rewriters (FD_aux (FD_function (recopt, tannotopt, funcls), (l, fdannot))) =
  let _ = reset_fresh_name_counter () in
  let funcls =
    match funcls with
    | FCL_aux (FCL_funcl (id, _), _) :: _ ->
        let clause (FCL_aux (FCL_funcl (_, pexp), fcl_annot)) =
          let pat, fguard, exp, pannot = destruct_pexp pexp in
          let pat, (guard, decls, _) = remove_bitvector_pat pat in
          let guard =
            let guard = Option.map (rewriters.rewrite_exp rewriters) guard in
            let fguard = Option.map (rewriters.rewrite_exp rewriters) fguard in
            match (guard, fguard) with None, e | e, None -> e | Some g, Some wh -> Some (bitwise_and_exp g (decls wh))
          in
          let exp = decls (rewriters.rewrite_exp rewriters exp) in
          (* AA: Why can't this use pannot ? *)
          FCL_aux (FCL_funcl (id, construct_pexp (pat, guard, exp, ((fst fcl_annot).loc, snd fcl_annot))), fcl_annot)
        in
        List.map clause funcls
    | _ -> funcls
  in
  FD_aux (FD_function (recopt, tannotopt, funcls), (l, fdannot))

let rewrite_ast_remove_bitvector_pats env ast =
  let rewriters =
    {
      rewrite_exp = rewrite_exp_remove_bitvector_pat;
      rewrite_pat;
      rewrite_let;
      rewrite_lexp;
      rewrite_fun = rewrite_fun_remove_bitvector_pat;
      rewrite_def;
      rewrite_ast = rewrite_ast_base;
    }
  in
  let rewrite_def d =
    let d = rewriters.rewrite_def rewriters d in
    match d with
    | DEF_aux (DEF_let (LB_aux (LB_val (pat, exp), a)), def_annot) ->
        let pat', (_, _, letbinds) = remove_bitvector_pat pat in
        let defvals = List.map (fun lb -> DEF_aux (DEF_let lb, mk_def_annot (gen_loc def_annot.loc))) letbinds in
        [DEF_aux (DEF_let (LB_aux (LB_val (pat', exp), a)), def_annot)] @ defvals
    | d -> [d]
  in
  (* FIXME See above in rewrite_sizeof *)
  (* fst (check initial_env ( *)
  { ast with defs = List.flatten (List.map rewrite_def ast.defs) }
(* )) *)

(* Rewrite literal number patterns to guarded patterns
   Those numeral patterns are not handled very well by Lem (or Isabelle)
*)
let rewrite_ast_remove_numeral_pats env =
  let p_lit outer_env = function
    | L_aux (L_num n, l) ->
        let id = fresh_id "l__" Parse_ast.Unknown in
        let typ = atom_typ (nconstant n) in
        let guard = mk_exp (E_app_infix (mk_exp (E_id id), mk_id "==", mk_lit_exp (L_num n))) in
        (* Check expression in reasonable approx of environment to resolve overriding *)
        let env = Env.add_local id (Immutable, typ) outer_env in
        let checked_guard = check_exp env guard bool_typ in
        (Some checked_guard, P_id id)
    | lit -> (None, P_lit lit)
  in
  let guard_pat outer_env = fold_pat { (compute_pat_alg None compose_guard_opt) with p_lit = p_lit outer_env } in
  let pat_aux (pexp_aux, a) =
    let pat, guard, exp, a = destruct_pexp (Pat_aux (pexp_aux, a)) in
    let guard', pat = guard_pat (env_of_pat pat) pat in
    match compose_guard_opt guard guard' with
    | Some g -> Pat_aux (Pat_when (pat, g, exp), a)
    | None -> Pat_aux (Pat_exp (pat, exp), a)
  in
  let exp_alg = { id_exp_alg with pat_aux } in
  let rewrite_exp _ = fold_exp exp_alg in
  let rewrite_funcl (FCL_aux (FCL_funcl (id, pexp), annot)) = FCL_aux (FCL_funcl (id, fold_pexp exp_alg pexp), annot) in
  let rewrite_fun _ (FD_aux (FD_function (r_o, t_o, funcls), a)) =
    FD_aux (FD_function (r_o, t_o, List.map rewrite_funcl funcls), a)
  in
  rewrite_ast_base { rewriters_base with rewrite_exp; rewrite_fun }

let rewrite_ast_vector_string_pats_to_bit_list env =
  let rewrite_p_aux (pat, (annot : tannot annot)) =
    match pat with P_lit lit -> vector_string_to_bits_pat lit annot | pat -> P_aux (pat, annot)
  in
  let rewrite_e_aux (exp, (annot : tannot annot)) =
    match exp with E_lit lit -> vector_string_to_bits_exp lit annot | exp -> E_aux (exp, annot)
  in
  let pat_alg = { id_pat_alg with p_aux = rewrite_p_aux } in
  let rewrite_pat rw pat = fold_pat pat_alg pat in
  let rewrite_exp rw exp = fold_exp { id_exp_alg with e_aux = rewrite_e_aux; pat_alg } exp in
  rewrite_ast_base { rewriters_base with rewrite_pat; rewrite_exp }

let rewrite_bit_lists_to_lits env =
  (* TODO Make all rewriting passes support bitvector literals instead of
     converting back and forth *)
  let open Sail2_values in
  let bit_of_lit = function L_aux (L_zero, _) -> Some B0 | L_aux (L_one, _) -> Some B1 | _ -> None in
  let bit_of_exp = function E_aux (E_lit lit, _) -> bit_of_lit lit | _ -> None in
  let string_of_chars cs = String.concat "" (List.map (String.make 1) cs) in
  let lit_of_bits bits =
    match hexstring_of_bits bits with
    | Some h -> L_hex (string_of_chars h)
    | None -> L_bin (string_of_chars (List.map bitU_char bits))
  in
  let e_aux (e, (l, annot)) =
    let rewrap e = E_aux (e, (l, annot)) in
    try
      let env = env_of_annot (l, annot) in
      let typ = typ_of_annot (l, annot) in
      match e with
      | E_vector es when is_bitvector_typ typ -> (
          match just_list (List.map bit_of_exp es) with
          | Some bits -> check_exp env (mk_exp (E_typ (typ, mk_lit_exp (lit_of_bits bits)))) typ
          | None -> rewrap e
        )
      | E_typ (typ', E_aux (E_typ (_, e'), _)) -> rewrap (E_typ (typ', e'))
      | _ -> rewrap e
    with _ -> rewrap e
  in
  let rewrite_exp rw = fold_exp { id_exp_alg with e_aux } in
  rewrite_ast_base { rewriters_base with rewrite_exp }

(* Remove pattern guards by rewriting them to if-expressions within the
   pattern expression. *)
let rewrite_exp_guarded_pats rewriters (E_aux (exp, (l, annot)) as full_exp) =
  let rewrap e = E_aux (e, (l, annot)) in
  let rewrite_rec = rewriters.rewrite_exp rewriters in
  let rewrite_base = rewrite_exp rewriters in
  let is_guarded_pexp = function Pat_aux (Pat_when (_, _, _), _) -> true | _ -> false in
  (* Also rewrite potentially incomplete pattern matches, adding a fallthrough clause *)
  match exp with
  | E_match (e, ps) when List.exists is_guarded_pexp ps || not (pats_complete l (env_of full_exp) ps (typ_of full_exp))
    ->
      let add_mapping_match (E_aux (e, (l, a)) as exp) =
        if Option.is_some (get_attribute "mapping_match" (untyped_annot annot)) then
          E_aux (e, (l, map_uannot (add_attribute Parse_ast.Unknown "mapping_match" "") a))
        else exp
      in
      let clause = function
        | Pat_aux (Pat_exp (pat, body), annot) -> (pat, None, rewrite_rec body, annot)
        | Pat_aux (Pat_when (pat, guard, body), annot) -> (pat, Some (rewrite_rec guard), rewrite_rec body, annot)
      in
      let clauses =
        rewrite_guarded_clauses mk_pattern_match_failure_pexp l (env_of full_exp) (typ_of e) (typ_of full_exp)
          (List.map clause ps)
      in
      let e = rewrite_rec e in
      if effectful e then (
        let (E_aux (_, (el, eannot))) = e in
        let pat_e' = fresh_id_pat "p__" (el, mk_tannot (env_of e) (typ_of e)) in
        let exp_e' = pat_to_exp pat_e' in
        let letbind_e = LB_aux (LB_val (pat_e', e), (el, eannot)) in
        let exp' = add_mapping_match (case_exp exp_e' (typ_of full_exp) clauses) in
        rewrap (E_let (letbind_e, exp'))
      )
      else add_mapping_match (case_exp e (typ_of full_exp) clauses)
  | E_try (e, ps) when List.exists is_guarded_pexp ps || not (pats_complete l (env_of full_exp) ps (typ_of full_exp)) ->
      let e = rewrite_rec e in
      let clause = function
        | Pat_aux (Pat_exp (pat, body), annot) -> (pat, None, rewrite_rec body, annot)
        | Pat_aux (Pat_when (pat, guard, body), annot) -> (pat, Some (rewrite_rec guard), rewrite_rec body, annot)
      in
      let clauses =
        rewrite_guarded_clauses mk_rethrow_pexp l (env_of full_exp) exc_typ (typ_of full_exp) (List.map clause ps)
      in
      let pexp (pat, body, annot) = Pat_aux (Pat_exp (pat, body), annot) in
      let ps = List.map pexp clauses in
      annot_exp (E_try (e, ps)) l (env_of full_exp) (typ_of full_exp)
  | _ -> rewrite_base full_exp

let rewrite_fun_guarded_pats rewriters (FD_aux (FD_function (r, t, funcls), (l, fdannot))) =
  let funcls =
    match funcls with
    | FCL_aux (FCL_funcl (id, pexp), fcl_annot) :: _ ->
        let clause (FCL_aux (FCL_funcl (_, pexp), annot)) =
          let pexp' = rewrite_pexp rewriters pexp in
          let pat, guard, exp, _ = destruct_pexp pexp' in
          (pat, guard, exp, annot)
        in
        let pexp_pat_typ, pexp_ret_typ =
          let pat, _, exp, _ = destruct_pexp pexp in
          (typ_of_pat pat, typ_of exp)
        in
        let pat_typ, ret_typ =
          match Env.get_val_spec_orig id (env_of_tannot (snd fcl_annot)) with
          | tq, Typ_aux (Typ_fn ([arg_typ], ret_typ), _) -> (arg_typ, ret_typ)
          | tq, Typ_aux (Typ_fn (arg_typs, ret_typ), _) -> (tuple_typ arg_typs, ret_typ)
          | _ -> (pexp_pat_typ, pexp_ret_typ)
          | exception _ -> (pexp_pat_typ, pexp_ret_typ)
        in
        let cs =
          rewrite_toplevel_guarded_clauses mk_pattern_match_failure_pexp l
            (env_of_tannot (snd fcl_annot))
            pat_typ ret_typ (List.map clause funcls)
        in
        List.map
          (fun (pat, exp, annot) ->
            FCL_aux
              ( FCL_funcl (id, construct_pexp (pat, None, exp, (Parse_ast.Unknown, empty_tannot))),
                (mk_def_annot (fst annot), snd annot)
              )
          )
          cs
    | _ -> funcls (* TODO is the empty list possible here? *)
  in
  FD_aux (FD_function (r, t, funcls), (l, fdannot))

let rewrite_ast_guarded_pats env =
  rewrite_ast_base
    { rewriters_base with rewrite_exp = rewrite_exp_guarded_pats; rewrite_fun = rewrite_fun_guarded_pats }

let rec rewrite_lexp_to_rhs (LE_aux (lexp, ((l, _) as annot)) as le) =
  match lexp with
  | LE_id _ | LE_typ (_, _) | LE_tuple _ | LE_deref _ -> (le, fun exp -> exp)
  | LE_vector (lexp, e) ->
      let lhs, rhs = rewrite_lexp_to_rhs lexp in
      (lhs, fun exp -> rhs (E_aux (E_vector_update (lexp_to_exp lexp, e, exp), annot)))
  | LE_vector_range (lexp, e1, e2) ->
      let lhs, rhs = rewrite_lexp_to_rhs lexp in
      (lhs, fun exp -> rhs (E_aux (E_vector_update_subrange (lexp_to_exp lexp, e1, e2, exp), annot)))
  | LE_field (lexp, id) -> begin
      let lhs, rhs = rewrite_lexp_to_rhs lexp in
      let (LE_aux (_, lannot)) = lexp in
      let env = env_of_annot lannot in
      match Env.expand_synonyms env (typ_of_annot lannot) with
      | (Typ_aux (Typ_id rectyp_id, _) | Typ_aux (Typ_app (rectyp_id, _), _)) when Env.is_record rectyp_id env ->
          let field_update exp = FE_aux (FE_fexp (id, exp), annot) in
          (lhs, fun exp -> rhs (E_aux (E_struct_update (lexp_to_exp lexp, [field_update exp]), lannot)))
      | _ -> raise (Reporting.err_unreachable l __POS__ ("Unsupported lexp: " ^ string_of_lexp le))
    end
  | _ -> raise (Reporting.err_unreachable l __POS__ ("Unsupported lexp: " ^ string_of_lexp le))

let updates_vars exp =
  let e_assign ((_, lexp), (u, exp)) = (u || lexp_is_local lexp (env_of exp), E_assign (lexp, exp)) in
  fst (fold_exp { (compute_exp_alg false ( || )) with e_assign } exp)

(*Expects to be called after rewrite_ast; thus the following should not appear:
  internal_exp of any form
  lit vectors in patterns or expressions
*)
let rewrite_exp_lift_assign_intro rewriters (E_aux (exp, ((l, _) as annot)) as full_exp) =
  let rewrite_rec = rewriters.rewrite_exp rewriters in
  let rewrite_base = rewrite_exp rewriters in
  match exp with
  | E_block exps ->
      let rec walker exps =
        match exps with
        | [] -> []
        | E_aux (E_assign (le, e), (l, tannot)) :: exps
          when (not (is_empty_tannot tannot)) && lexp_is_local_intro le (env_of_annot (l, tannot)) ->
            let env = env_of_annot (l, tannot) in
            let le', re' = rewrite_lexp_to_rhs le in
            let e' = re' (rewrite_base e) in
            let exps' = walker exps in
            let block = E_aux (E_block exps', (gen_loc l, mk_tannot env unit_typ)) in
            [E_aux (E_var (le', e', block), annot)]
        | e :: exps -> rewrite_rec e :: walker exps
      in
      E_aux (E_block (walker exps), annot)
  | E_assign (le, e) when lexp_is_local_intro le (env_of full_exp) && not (lexp_is_effectful le) ->
      let le', re' = rewrite_lexp_to_rhs le in
      let e' = re' (rewrite_base e) in
      let block = annot_exp (E_block []) (gen_loc l) (env_of full_exp) unit_typ in
      E_aux (E_var (le', e', block), annot)
  | _ -> rewrite_base full_exp

let rewrite_ast_exp_lift_assign env defs =
  rewrite_ast_base
    {
      rewrite_exp = rewrite_exp_lift_assign_intro;
      rewrite_pat;
      rewrite_let;
      rewrite_lexp;
      (*_lift_assign_intro*) rewrite_fun;
      rewrite_def;
      rewrite_ast = rewrite_ast_base;
    }
    defs

(* Remove redundant return statements, and translate remaining ones into an
   (effectful) call to builtin function "early_return" (in the Lem shallow
   embedding).

   TODO: Maybe separate generic removal of redundant returns, and Lem-specific
   rewriting of early returns
*)
let rewrite_ast_early_return effect_info env ast =
  let is_unit (E_aux (exp, _)) = match exp with E_lit (L_aux (L_unit, _)) -> true | _ -> false in

  let rec is_return (E_aux (exp, _)) = match exp with E_return _ -> true | E_typ (_, e) -> is_return e | _ -> false in

  let rec get_return (E_aux (e, annot) as exp) =
    match e with E_return e -> e | E_typ (typ, e) -> E_aux (E_typ (typ, get_return e), annot) | _ -> exp
  in

  let contains_return exp =
    fst (fold_exp { (compute_exp_alg false ( || )) with e_return = (fun (_, r) -> (true, E_return r)) } exp)
  in

  let e_if (e1, e2, e3) =
    if is_return e2 && is_return e3 then (
      let (E_aux (_, annot)) = get_return e2 in
      E_return (E_aux (E_if (e1, get_return e2, get_return e3), annot))
    )
    else E_if (e1, e2, e3)
  in

  let rec e_block es =
    (* If one of the branches of an if-expression in a block is an early
       return, fold the rest of the block after the if-expression into the
       other branch *)
    let fold_if_return exp block =
      match exp with
      | E_aux (E_if (c, t, (E_aux (_, annot) as e)), _) when is_return t ->
          let annot =
            match block with
            | [] -> annot
            | _ ->
                let (E_aux (_, annot)) = Util.last block in
                annot
          in
          let block = if is_unit e then block else e :: block in
          let e' = E_aux (e_block block, annot) in
          [E_aux (e_if (c, t, e'), annot)]
      | E_aux (E_if (c, (E_aux (_, annot) as t), e), _) when is_return e ->
          let annot =
            match block with
            | [] -> annot
            | _ ->
                let (E_aux (_, annot)) = Util.last block in
                annot
          in
          let block = if is_unit t then block else t :: block in
          let t' = E_aux (e_block block, annot) in
          [E_aux (e_if (c, t', e), annot)]
      | _ -> exp :: block
    in
    let es = List.fold_right fold_if_return es [] in
    match es with
    | [E_aux (e, _)] -> e
    | _ :: _ when is_return (Util.last es) ->
        let (E_aux (_, annot) as e) = get_return (Util.last es) in
        E_return (E_aux (E_block (Util.butlast es @ [get_return e]), annot))
    | _ -> E_block es
  in

  let e_case (e, pes) =
    let is_return_pexp (Pat_aux (pexp, _)) = match pexp with Pat_exp (_, e) | Pat_when (_, _, e) -> is_return e in
    let get_return_pexp (Pat_aux (pexp, a)) =
      match pexp with
      | Pat_exp (p, e) -> Pat_aux (Pat_exp (p, get_return e), a)
      | Pat_when (p, g, e) -> Pat_aux (Pat_when (p, g, get_return e), a)
    in
    let annot =
      match List.map get_return_pexp pes with
      | Pat_aux (Pat_exp (_, E_aux (_, annot)), _) :: _ -> annot
      | Pat_aux (Pat_when (_, _, E_aux (_, annot)), _) :: _ -> annot
      | [] -> (Parse_ast.Unknown, empty_tannot)
    in
    if List.for_all is_return_pexp pes then E_return (E_aux (E_match (e, List.map get_return_pexp pes), annot))
    else E_match (e, pes)
  in

  let e_let (lb, exp) =
    let (E_aux (_, annot) as ret_exp) = get_return exp in
    if is_return exp then E_return (E_aux (E_let (lb, ret_exp), annot)) else E_let (lb, exp)
  in

  let e_var (lexp, exp1, exp2) =
    let (E_aux (_, annot) as ret_exp2) = get_return exp2 in
    if is_return exp2 then E_return (E_aux (E_var (lexp, exp1, ret_exp2), annot)) else E_var (lexp, exp1, exp2)
  in

  let e_app (id, es) = try E_return (get_return (List.find is_return es)) with Not_found -> E_app (id, es) in

  let e_aux (exp, (l, annot)) =
    let full_exp = E_aux (exp, (l, annot)) in
    match full_exp with
    | E_aux (E_return exp, (l, tannot)) when not (is_empty_tannot tannot) ->
        let typ = typ_of_annot (l, tannot) in
        let env = env_of_annot (l, tannot) in
        let tannot' = mk_tannot env typ in
        let exp' = match Env.get_ret_typ env with Some typ -> add_e_typ env typ exp | None -> exp in
        E_aux (E_app (mk_id "early_return", [exp']), (l, tannot'))
    | _ -> full_exp
  in

  (* Make sure that all final leaves of an expression (e.g. all branches of
     the last if-expression) are wrapped in a return statement.  This allows
     the above rewriting to uniformly pull these returns back out, even if
     originally only one of the branches of the last if-expression was a
     return, and the other an "exit()", for example. *)
  let rec add_final_return nested (E_aux (e, annot) as exp) =
    let rewrap e = E_aux (e, annot) in
    match e with
    | E_return _ -> exp
    | E_typ (typ, e') -> begin
        let (E_aux (e_aux', annot') as e') = add_final_return nested e' in
        match e_aux' with E_return e' -> rewrap (E_return (rewrap (E_typ (typ, e')))) | _ -> rewrap (E_typ (typ, e'))
      end
    | E_block (_ :: _ as es) -> rewrap (E_block (Util.butlast es @ [add_final_return true (Util.last es)]))
    | E_if (c, t, e) -> rewrap (E_if (c, add_final_return true t, add_final_return true e))
    | E_match (e, pes) ->
        let add_final_return_pexp = function
          | Pat_aux (Pat_exp (p, e), a) -> Pat_aux (Pat_exp (p, add_final_return true e), a)
          | Pat_aux (Pat_when (p, g, e), a) -> Pat_aux (Pat_when (p, g, add_final_return true e), a)
        in
        rewrap (E_match (e, List.map add_final_return_pexp pes))
    | E_let (lb, exp) -> rewrap (E_let (lb, add_final_return true exp))
    | E_var (lexp, e1, e2) -> rewrap (E_var (lexp, e1, add_final_return true e2))
    | _ -> if nested && not (contains_return exp) then rewrap (E_return exp) else exp
  in

  let rewrite_funcl_early_return _ (FCL_aux (FCL_funcl (id, pexp), a)) =
    let pat, guard, exp, pannot = destruct_pexp pexp in
    let exp =
      if contains_return exp then (
        (* Try to pull out early returns as far as possible *)
        let exp' =
          fold_exp { id_exp_alg with e_block; e_if; e_case; e_let; e_var; e_app } (add_final_return false exp)
        in
        (* Remove early return if we can pull it out completely, and rewrite
           remaining early returns to "early_return" calls *)
        fold_exp { id_exp_alg with e_aux } (if is_return exp' then get_return exp' else exp)
      )
      else exp
    in
    let a = match destruct_tannot (snd a) with Some (env, typ) -> (fst a, mk_tannot env typ) | _ -> a in
    FCL_aux (FCL_funcl (id, construct_pexp (pat, guard, exp, pannot)), a)
  in

  let rewrite_fun_early_return rewriters (FD_aux (FD_function (rec_opt, tannot_opt, funcls), a)) =
    FD_aux (FD_function (rec_opt, tannot_opt, List.map (rewrite_funcl_early_return rewriters) funcls), a)
  in

  let early_ret_spec =
    fst
      (Type_error.check_defs initial_env
         [gen_vs ~pure:false ("early_return", "forall ('a : Type) ('b : Type). 'a -> 'b")]
      )
  in
  let effect_info = Effects.add_monadic_built_in (mk_id "early_return") effect_info in

  let new_ast =
    rewrite_ast_base
      { rewriters_base with rewrite_fun = rewrite_fun_early_return }
      { ast with defs = early_ret_spec @ ast.defs }
  in
  (new_ast, effect_info, env)

let swaptyp typ (l, tannot) =
  match destruct_tannot tannot with
  | Some (env, typ') -> (l, mk_tannot env typ)
  | _ -> raise (Reporting.err_unreachable l __POS__ "swaptyp called with empty type annotation")

let is_funcl_rec (FCL_aux (FCL_funcl (id, pexp), _)) =
  fold_pexp
    {
      (pure_exp_alg false ( || )) with
      e_app = (fun (id', args) -> Id.compare id id' == 0 || List.exists (fun x -> x) args);
      e_app_infix = (fun (arg1, id', arg2) -> arg1 || arg2 || Id.compare id id' == 0);
    }
    pexp

(* Sail code isn't required to declare recursive functions as
   recursive, so if a backend needs them then this rewrite updates
   them.  (Also see minimise_recursive_functions.) *)
let rewrite_add_unspecified_rec env ast =
  let rewrite_function (FD_aux (FD_function (recopt, topt, funcls), ann) as fd) =
    match recopt with
    | Rec_aux (Rec_nonrec, l) when List.exists is_funcl_rec funcls ->
        FD_aux (FD_function (Rec_aux (Rec_rec, Generated l), topt, funcls), ann)
    | _ -> fd
  in
  let rewrite_def = function
    | DEF_aux (DEF_fundef fd, def_annot) -> DEF_aux (DEF_fundef (rewrite_function fd), def_annot)
    | d -> d
  in
  { ast with defs = List.map rewrite_def ast.defs }

let pat_var (P_aux (paux, a)) =
  let env = env_of_annot a in
  let is_var id =
    (not (Env.is_union_constructor id env)) && match Env.lookup_id id env with Enum _ -> false | _ -> true
  in
  match paux with (P_as (_, id) | P_id id) when is_var id -> Some id | _ -> None

(** Split out function clauses for individual union constructor patterns
   (e.g. AST nodes) into auxiliary functions. Used for the execute function.

   For example:

   function execute(Instr(x, y)) = ...

   would become

   function execute_Instr(x, y) = ...

   function execute(Instr(x, y)) = execute_C(x, y)

   This is actually a slightly complex rewrite than it first appears, because
   we have to deal with cases where the AST type has constraints in various
   places, e.g.

   union ast('x: Int), 0 <= 'x < 32 = {
     Instr : {'r, 'r in {32, 64}. (int('x), bits('r))}
   }
 *)
let rewrite_split_fun_ctor_pats fun_name effect_info env ast =
  let rewrite_fundef typquant (FD_aux (FD_function (r_o, t_o, clauses), ((l, _) as fdannot))) def_annot =
    (* let rec_clauses, clauses = List.partition is_funcl_rec clauses in *)
    let clauses, aux_funs =
      List.fold_left
        (fun (clauses, aux_funs) (FCL_aux (FCL_funcl (id, pexp), fannot) as clause) ->
          let pat, guard, exp, annot = destruct_pexp pexp in
          match pat with
          | P_aux (P_app (ctor_id, args), pannot) | P_aux (P_tuple [P_aux (P_app (ctor_id, args), pannot)], _) ->
              let ctor_typq, ctor_typ = Env.get_union_id ctor_id env in
              let args = match args with [P_aux (P_tuple args, _)] -> args | _ -> args in
              let argstup_typ = tuple_typ (List.map typ_of_pat args) in
              let pannot' = swaptyp argstup_typ pannot in
              let pat' = match args with [arg] -> arg | _ -> P_aux (P_tuple args, pannot') in
              let pexp' = construct_pexp (pat', guard, exp, annot) in
              let aux_fun_id = prepend_id (fun_name ^ "_") ctor_id in
              let aux_funcl = FCL_aux (FCL_funcl (aux_fun_id, pexp'), (mk_def_annot (fst pannot'), snd pannot')) in
              begin
                try
                  let aux_clauses = Bindings.find aux_fun_id aux_funs in
                  (clauses, Bindings.add aux_fun_id (aux_clauses @ [(aux_funcl, ctor_typq, ctor_typ)]) aux_funs)
                with Not_found ->
                  let argpats, argexps =
                    List.split
                      (List.mapi
                         (fun idx (P_aux (_, a) as pat) ->
                           let id =
                             match pat_var pat with Some id -> id | None -> mk_id ("arg" ^ string_of_int idx)
                           in
                           (P_aux (P_id id, a), E_aux (E_id id, a))
                         )
                         args
                      )
                  in
                  let pexp =
                    construct_pexp
                      (P_aux (P_app (ctor_id, argpats), pannot), None, E_aux (E_app (aux_fun_id, argexps), annot), annot)
                  in
                  ( clauses @ [FCL_aux (FCL_funcl (id, pexp), fannot)],
                    Bindings.add aux_fun_id [(aux_funcl, ctor_typq, ctor_typ)] aux_funs
                  )
              end
          | _ -> (clauses @ [clause], aux_funs)
        )
        ([], Bindings.empty) clauses
    in
    let add_aux_def id aux_funs (valdefs, fundefs) =
      let funcls = List.map (fun (fcl, _, _) -> fcl) aux_funs in
      let env, quants, args_typ, ret_typ =
        match aux_funs with
        | (FCL_aux (FCL_funcl (_, pexp), _), ctor_typq, ctor_typ) :: _ ->
            let pat, _, exp, _ = destruct_pexp pexp in
            let ctor_quants args_typ =
              List.filter
                (fun qi -> KOptSet.subset (kopts_of_quant_item qi) (kopts_of_typ args_typ))
                (quant_items ctor_typq)
            in
            begin
              match ctor_typ with
              | Typ_aux (Typ_fn ([Typ_aux (Typ_exist (kopts, nc, args_typ), _)], _), _) ->
                  (env_of exp, ctor_quants args_typ @ List.map mk_qi_kopt kopts @ [mk_qi_nc nc], args_typ, typ_of exp)
              | Typ_aux (Typ_fn ([args_typ], _), _) -> (env_of exp, ctor_quants args_typ, args_typ, typ_of exp)
              | _ ->
                  raise
                    (Reporting.err_unreachable l __POS__
                       ("Union constructor has non-function type: " ^ string_of_typ ctor_typ)
                    )
            end
        | _ -> raise (Reporting.err_unreachable l __POS__ "rewrite_split_fun_constr_pats: empty auxiliary function")
      in
      let fun_typ =
        (* Because we got the argument type from a pattern we need to
           do this. *)
        match args_typ with
        | Typ_aux (Typ_tuple args_typs, _) -> function_typ args_typs ret_typ
        | _ -> function_typ [args_typ] ret_typ
      in
      let val_spec =
        VS_aux (VS_val_spec (mk_typschm (mk_typquant quants) fun_typ, id, None), (Parse_ast.Unknown, empty_tannot))
      in
      let fundef = FD_aux (FD_function (r_o, t_o, funcls), fdannot) in
      let def_annot = mk_def_annot (gen_loc def_annot.loc) in
      (DEF_aux (DEF_val val_spec, def_annot) :: valdefs, DEF_aux (DEF_fundef fundef, def_annot) :: fundefs)
    in
    let valdefs, fundefs =
      Bindings.fold add_aux_def aux_funs
        ([], [DEF_aux (DEF_fundef (FD_aux (FD_function (r_o, t_o, clauses), fdannot)), def_annot)])
    in
    (valdefs @ fundefs, List.map fst (Bindings.bindings aux_funs))
  in
  let typquant =
    List.fold_left
      (fun tq def ->
        match def with
        | DEF_aux (DEF_val (VS_aux (VS_val_spec (TypSchm_aux (TypSchm_ts (tq, _), _), id, _), _)), _)
          when string_of_id id = fun_name ->
            tq
        | _ -> tq
      )
      (mk_typquant []) ast.defs
  in
  let defs, new_effect_info =
    List.fold_right
      (fun def (defs, effect_info) ->
        match def with
        | DEF_aux (DEF_fundef fundef, def_annot) when string_of_id (id_of_fundef fundef) = fun_name ->
            let new_defs, new_ids = rewrite_fundef typquant fundef def_annot in
            (new_defs @ defs, List.fold_left (Effects.copy_function_effect (id_of_fundef fundef)) effect_info new_ids)
        | _ -> (def :: defs, effect_info)
      )
      ast.defs ([], effect_info)
  in

  (* If we have a call to execute(Clause(...)) we can directly
     transform that to execute_Clause(...). This removes recursion
     from when one execute clause is implemented in terms of another,
     like RISC-V compressed instructions. *)
  let optimize_split_call (f, args) =
    match args with
    | [E_aux (E_app (ctor_id, ctor_args), annot)]
      when string_of_id f = fun_name && Env.is_union_constructor ctor_id (env_of_annot annot) -> begin
        match ctor_args with
        | [E_aux (E_tuple ctor_args, _)] -> E_app (prepend_id (fun_name ^ "_") ctor_id, ctor_args)
        | [ctor_arg] -> E_app (prepend_id (fun_name ^ "_") ctor_id, [ctor_arg])
        | _ -> Reporting.unreachable (fst annot) __POS__ "Constructor with more than 1 argument found in split rewrite"
      end
    | _ -> E_app (f, args)
  in
  let optimize_exp = fold_exp { id_exp_alg with e_app = optimize_split_call } in

  let defs =
    List.map
      (fun def ->
        match def with
        | DEF_aux (DEF_fundef (FD_aux (FD_function (r_o, t_o, clauses), fdannot)), def_annot) ->
            DEF_aux
              ( DEF_fundef
                  (FD_aux
                     ( FD_function
                         ( r_o,
                           t_o,
                           List.map
                             (fun (FCL_aux (FCL_funcl (id, Pat_aux (pexp, pann)), fannot)) ->
                               match pexp with
                               | Pat_exp (pat, exp) ->
                                   FCL_aux (FCL_funcl (id, Pat_aux (Pat_exp (pat, optimize_exp exp), pann)), fannot)
                               | Pat_when (pat, guard, exp) ->
                                   FCL_aux
                                     ( FCL_funcl
                                         (id, Pat_aux (Pat_when (pat, optimize_exp guard, optimize_exp exp), pann)),
                                       fannot
                                     )
                             )
                             clauses
                         ),
                       fdannot
                     )
                  ),
                def_annot
              )
        | _ -> def
      )
      defs
  in
  ({ ast with defs }, new_effect_info, env)

let rewrite_type_union_typs rw_typ (Tu_aux (Tu_ty_id (typ, id), annot)) = Tu_aux (Tu_ty_id (rw_typ typ, id), annot)

let rewrite_type_def_typs rw_typ rw_typquant (TD_aux (td, annot)) =
  match td with
  | TD_abbrev (id, typq, A_aux (A_typ typ, l)) ->
      TD_aux (TD_abbrev (id, rw_typquant typq, A_aux (A_typ (rw_typ typ), l)), annot)
  | TD_abbrev (id, typq, typ_arg) -> TD_aux (TD_abbrev (id, rw_typquant typq, typ_arg), annot)
  | TD_record (id, typq, typ_ids, flag) ->
      TD_aux (TD_record (id, rw_typquant typq, List.map (fun (typ, id) -> (rw_typ typ, id)) typ_ids, flag), annot)
  | TD_variant (id, typq, tus, flag) ->
      TD_aux (TD_variant (id, rw_typquant typq, List.map (rewrite_type_union_typs rw_typ) tus, flag), annot)
  | TD_enum (id, ids, flag) -> TD_aux (TD_enum (id, ids, flag), annot)
  | TD_bitfield _ -> assert false (* Processed before re-writing *)

(* FIXME: rewrite in opt_exp? *)
let rewrite_dec_spec_typs rw_typ (DEC_aux (ds, annot)) =
  match ds with DEC_reg (typ, id, opt_exp) -> DEC_aux (DEC_reg (rw_typ typ, id, opt_exp), annot)

let rewrite_undefined mwords env =
  let rewrite_e_aux (E_aux (e_aux, _) as exp) =
    match e_aux with
    | E_lit (L_aux (L_undef, l)) ->
        check_exp (env_of exp)
          (undefined_of_typ mwords l (fun _ -> empty_uannot) (Env.expand_synonyms (env_of exp) (typ_of exp)))
          (typ_of exp)
    | _ -> exp
  in
  let rewrite_exp_undefined = { id_exp_alg with e_aux = (fun (exp, annot) -> rewrite_e_aux (E_aux (exp, annot))) } in
  rewrite_ast_base { rewriters_base with rewrite_exp = (fun _ -> fold_exp rewrite_exp_undefined) }

let rewrite_undefined_if_gen always_bitvector env defs =
  if !Initial_check.opt_undefined_gen then rewrite_undefined (always_bitvector || !Monomorphise.opt_mwords) env defs
  else defs

let rec simple_typ (Typ_aux (typ_aux, l)) = Typ_aux (simple_typ_aux l typ_aux, l)

and simple_typ_aux l = function
  | Typ_id id -> Typ_id id
  | Typ_app (id, [_; A_aux (A_typ typ, l)]) when Id.compare id (mk_id "vector") = 0 ->
      Typ_app (mk_id "list", [A_aux (A_typ (simple_typ typ), l)])
  | Typ_app (id, [_]) when Id.compare id (mk_id "bitvector") = 0 ->
      Typ_app (mk_id "list", [A_aux (A_typ bit_typ, gen_loc l)])
  | Typ_app (id, [_]) when Id.compare id (mk_id "atom") = 0 -> Typ_id (mk_id "int")
  | Typ_app (id, [_; _]) when Id.compare id (mk_id "range") = 0 -> Typ_id (mk_id "int")
  | Typ_app (id, [_]) when Id.compare id (mk_id "atom_bool") = 0 -> Typ_id (mk_id "bool")
  | Typ_app (id, args) -> Typ_app (id, List.concat (List.map simple_typ_arg args))
  | Typ_fn (arg_typs, ret_typ) -> Typ_fn (List.map simple_typ arg_typs, simple_typ ret_typ)
  | Typ_tuple typs -> Typ_tuple (List.map simple_typ typs)
  | Typ_exist (_, _, Typ_aux (typ, l)) -> simple_typ_aux l typ
  | typ_aux -> typ_aux

and simple_typ_arg (A_aux (typ_arg_aux, l)) =
  match typ_arg_aux with A_typ typ -> [A_aux (A_typ (simple_typ typ), l)] | _ -> []

(* This pass aims to remove all the Num quantifiers from the specification. *)
let rewrite_simple_types env ast =
  let is_simple = function QI_aux (QI_id kopt, annot) when is_typ_kopt kopt -> true | _ -> false in
  let simple_typquant (TypQ_aux (tq_aux, annot)) =
    match tq_aux with
    | TypQ_no_forall -> TypQ_aux (TypQ_no_forall, annot)
    | TypQ_tq quants -> TypQ_aux (TypQ_tq (List.filter (fun q -> is_simple q) quants), annot)
  in
  let simple_typschm (TypSchm_aux (TypSchm_ts (typq, typ), annot)) =
    TypSchm_aux (TypSchm_ts (simple_typquant typq, simple_typ typ), annot)
  in
  let simple_vs (VS_aux (vs_aux, annot)) =
    match vs_aux with VS_val_spec (typschm, id, ext) -> VS_aux (VS_val_spec (simple_typschm typschm, id, ext), annot)
  in
  let simple_lit (L_aux (lit_aux, l) as lit) =
    match lit_aux with
    | L_bin _ | L_hex _ ->
        E_list (List.map (fun b -> E_aux (E_lit b, simple_annot l bit_typ)) (vector_string_to_bit_list lit))
    | _ -> E_lit lit
  in
  let simple_def (DEF_aux (aux, def_annot)) =
    let aux =
      match aux with
      | DEF_val vs -> DEF_val (simple_vs vs)
      | DEF_type td -> DEF_type (rewrite_type_def_typs simple_typ simple_typquant td)
      | DEF_register ds -> DEF_register (rewrite_dec_spec_typs simple_typ ds)
      | _ -> aux
    in
    DEF_aux (aux, def_annot)
  in
  let simple_pat =
    {
      id_pat_alg with
      p_typ = (fun (typ, pat) -> P_typ (simple_typ typ, pat));
      p_var = (fun (pat, kid) -> unaux_pat pat);
      p_vector = (fun pats -> P_list pats);
    }
  in
  let simple_exp =
    {
      id_exp_alg with
      e_lit = simple_lit;
      e_vector = (fun exps -> E_list exps);
      e_typ = (fun (typ, exp) -> E_typ (simple_typ typ, exp));
      (* e_assert = (fun (E_aux (_, annot), str) -> E_assert (E_aux (E_lit (mk_lit L_true), annot), str)); *)
      le_typ = (fun (typ, lexp) -> LE_typ (simple_typ typ, lexp));
      pat_alg = simple_pat;
    }
  in
  let simple_defs =
    { rewriters_base with rewrite_exp = (fun _ -> fold_exp simple_exp); rewrite_pat = (fun _ -> fold_pat simple_pat) }
  in
  let ast = { ast with defs = List.map simple_def ast.defs } in
  rewrite_ast_base simple_defs ast

let rewrite_vector_concat_assignments env defs =
  let lit_int i = mk_exp (E_lit (mk_lit (L_num i))) in
  let sub m n =
    match (m, n) with
    | E_aux (E_lit (L_aux (L_num m, _)), _), E_aux (E_lit (L_aux (L_num n, _)), _) -> lit_int (Big_int.sub m n)
    | _, _ -> mk_exp (E_app_infix (m, mk_id "-", n))
  in
  let add m n =
    match (m, n) with
    | E_aux (E_lit (L_aux (L_num m, _)), _), E_aux (E_lit (L_aux (L_num n, _)), _) -> lit_int (Big_int.add m n)
    | _, _ -> mk_exp (E_app_infix (m, mk_id "+", n))
  in

  let assign_tuple e_aux annot =
    let env = env_of_annot annot in
    match e_aux with
    | E_assign (LE_aux (LE_vector_concat lexps, lannot), exp) ->
        let typ = Env.base_typ_of env (typ_of exp) in
        if is_vector_typ typ || is_bitvector_typ typ then (
          (* let _ = Pretty_print_common.print stderr (Pretty_print_sail.doc_exp (E_aux (e_aux, annot))) in *)
          let start = vector_start_index env typ in
          let ord = Env.get_default_order env in
          let len (LE_aux (le, lannot)) =
            let ltyp = Env.base_typ_of env (typ_of_annot lannot) in
            if is_vector_typ ltyp || is_bitvector_typ ltyp then (
              let len, _ = vector_typ_args_of ltyp in
              match Type_check.solve_unique (env_of_annot lannot) len with
              | Some len -> mk_exp (E_lit (mk_lit (L_num len)))
              | None -> mk_exp (E_sizeof (nexp_simp len))
            )
            else Reporting.unreachable (fst lannot) __POS__ "Lexp in vector concatenation assignment is not a vector"
          in
          let next i step =
            if is_order_inc ord then (sub (add i step) (lit_int (Big_int.of_int 1)), add i step)
            else (add (sub i step) (lit_int (Big_int.of_int 1)), sub i step)
          in
          let i =
            match Type_check.solve_unique (env_of exp) start with
            | Some i -> lit_int i
            | None -> mk_exp (E_sizeof (nexp_simp start))
          in
          let vec_id = mk_id "split_vec" in
          let exp' = if small exp then strip_exp exp else mk_exp (E_id vec_id) in
          let lexp_to_exp (i, exps) lexp =
            let j, i' = next i (len lexp) in
            let sub = mk_exp (E_vector_subrange (exp', i, j)) in
            (i', exps @ [sub])
          in
          let _, exps = List.fold_left lexp_to_exp (i, []) lexps in
          let assign lexp exp = mk_exp (E_assign (strip_lexp lexp, exp)) in
          let block = mk_exp (E_block (List.map2 assign lexps exps)) in
          let full_exp =
            if small exp then block else mk_exp (E_let (mk_letbind (mk_pat (P_id vec_id)) (strip_exp exp), block))
          in
          begin
            try check_exp env full_exp unit_typ
            with Type_error.Type_error (l, err) -> raise (Reporting.err_typ l (Type_error.string_of_type_error err))
          end
        )
        else E_aux (e_aux, annot)
    | _ -> E_aux (e_aux, annot)
  in
  let assign_exp = { id_exp_alg with e_aux = (fun (e_aux, annot) -> assign_tuple e_aux annot) } in
  let assign_defs = { rewriters_base with rewrite_exp = (fun _ -> fold_exp assign_exp) } in
  rewrite_ast_base assign_defs defs

let rewrite_tuple_assignments env defs =
  let assign_tuple e_aux annot =
    let env = env_of_annot annot in
    match e_aux with
    | E_assign (LE_aux (LE_tuple lexps, _), exp) ->
        let _, ids =
          List.fold_left (fun (n, ids) _ -> (n + 1, ids @ [mk_id ("tup__" ^ string_of_int n)])) (0, []) lexps
        in
        let block_assign i lexp =
          mk_exp (E_assign (strip_lexp lexp, mk_exp (E_id (mk_id ("tup__" ^ string_of_int i)))))
        in
        let block = mk_exp (E_block (List.mapi block_assign lexps)) in
        let pat = mk_pat (P_tuple (List.map (fun id -> mk_pat (P_id id)) ids)) in
        let exp' = add_e_typ env (typ_of exp) exp in
        let let_exp = mk_exp (E_let (mk_letbind pat (strip_exp exp'), block)) in
        begin
          try check_exp env let_exp unit_typ
          with Type_error.Type_error (l, err) -> raise (Reporting.err_typ l (Type_error.string_of_type_error err))
        end
    | _ -> E_aux (e_aux, annot)
  in
  let assign_exp = { id_exp_alg with e_aux = (fun (e_aux, annot) -> assign_tuple e_aux annot) } in
  let assign_defs = { rewriters_base with rewrite_exp = (fun _ -> fold_exp assign_exp) } in
  rewrite_ast_base assign_defs defs

let rewrite_simple_assignments allow_fields env defs =
  let rec is_simple (LE_aux (aux, _)) =
    match aux with
    | LE_id _ -> true
    | LE_typ _ -> true
    | LE_field (lexp, _) when allow_fields -> is_simple lexp
    | _ -> false
  in
  let assign_e_aux e_aux annot =
    let env = env_of_annot annot in
    match e_aux with
    | E_assign (lexp, _) when is_simple lexp -> E_aux (e_aux, annot)
    | E_assign (lexp, exp) ->
        let lexp, rhs = rewrite_lexp_to_rhs lexp in
        let assign = mk_exp (E_assign (strip_lexp lexp, strip_exp (rhs exp))) in
        check_exp env assign unit_typ
    | _ -> E_aux (e_aux, annot)
  in
  let assign_exp = { id_exp_alg with e_aux = (fun (e_aux, annot) -> assign_e_aux e_aux annot) } in
  let assign_defs = { rewriters_base with rewrite_exp = (fun _ -> fold_exp assign_exp) } in
  rewrite_ast_base assign_defs defs

let rewrite_ast_remove_blocks env =
  let letbind_wild v body =
    let l = get_loc_exp v in
    let env = env_of v in
    let typ = typ_of v in
    let wild = annot_pat P_wild l env typ in
    let e_aux = E_let (annot_letbind (unaux_pat wild, v) l env typ, body) in
    annot_exp e_aux l env (typ_of body) |> add_typs_let env typ (typ_of body)
  in

  let rec f l = function
    | [] -> E_aux (E_lit (L_aux (L_unit, gen_loc l)), simple_annot l unit_typ)
    | [e] -> e (* check with Kathy if that annotation is fine *)
    | e :: es -> letbind_wild e (f l es)
  in

  let e_aux = function E_block es, (l, _) -> f l es | e, annot -> E_aux (e, annot) in

  let alg = { id_exp_alg with e_aux } in

  rewrite_ast_base
    {
      rewrite_exp = (fun _ -> fold_exp alg);
      rewrite_pat;
      rewrite_let;
      rewrite_lexp;
      rewrite_fun;
      rewrite_def;
      rewrite_ast = rewrite_ast_base;
    }

let letbind (v : 'a exp) (body : 'a exp -> 'a exp) : 'a exp =
  (* body is a function : E_id variable -> actual body *)
  let (E_aux (_, (l, annot))) = v in
  match destruct_tannot annot with
  | Some (env, typ) when is_unit_typ typ ->
      let body = body (annot_exp (E_lit (mk_lit L_unit)) l env unit_typ) in
      let body_typ = try typ_of body with _ -> unit_typ in
      let wild = annot_pat P_wild l env typ in
      let lb = annot_letbind (unaux_pat wild, v) l env unit_typ in
      annot_exp (E_let (lb, body)) l env body_typ |> add_typs_let env typ body_typ
  | Some (env, typ) ->
      let id = fresh_id "w__" l in
      let pat = annot_pat (P_id id) l env typ in
      let lb = annot_letbind (unaux_pat pat, v) l env typ in
      let body = body (annot_exp (E_id id) l env typ) in
      annot_exp (E_let (lb, body)) l env (typ_of body) |> add_typs_let env typ (typ_of body)
  | None -> Reporting.unreachable l __POS__ "no type information"

let rec mapCont (f : 'b -> ('b -> 'a exp) -> 'a exp) (l : 'b list) (k : 'b list -> 'a exp) : 'a exp =
  match l with [] -> k [] | exp :: exps -> f exp (fun exp -> mapCont f exps (fun exps -> k (exp :: exps)))

let rewrite_ast_letbind_effects effect_info env =
  let monadic (E_aux (aux, (l, tannot))) = E_aux (aux, (l, add_effect_annot tannot monadic_effect)) in

  let purify (E_aux (aux, (l, tannot))) = E_aux (aux, (l, add_effect_annot tannot no_effect)) in

  let value (E_aux (exp_aux, _) as exp) = not (effectful exp || updates_vars exp) in

  let rec n_exp_name (exp : 'a exp) (k : 'a exp -> 'a exp) : 'a exp =
    n_exp exp (fun exp -> if value exp then k exp else monadic (letbind exp k))
  and n_exp_pure (exp : 'a exp) (k : 'a exp -> 'a exp) : 'a exp =
    n_exp exp (fun exp -> if value exp then k exp else monadic (letbind exp k))
  and n_exp_nameL (exps : 'a exp list) (k : 'a exp list -> 'a exp) : 'a exp = mapCont n_exp_name exps k
  and n_fexp (fexp : 'a fexp) (k : 'a fexp -> 'a exp) : 'a exp =
    let (FE_aux (FE_fexp (id, exp), annot)) = fexp in
    n_exp_name exp (fun exp -> k (FE_aux (FE_fexp (id, exp), annot)))
  and n_fexpL (fexps : 'a fexp list) (k : 'a fexp list -> 'a exp) : 'a exp = mapCont n_fexp fexps k
  and n_pexp : 'b. bool -> 'a pexp -> ('a pexp -> 'b) -> 'b =
   fun newreturn pexp k ->
    match pexp with
    | Pat_aux (Pat_exp (pat, exp), annot) -> k (Pat_aux (Pat_exp (pat, n_exp_term newreturn exp), annot))
    | Pat_aux (Pat_when (pat, guard, exp), annot) ->
        k (Pat_aux (Pat_when (pat, n_exp_term newreturn guard, n_exp_term newreturn exp), annot))
  and n_pexpL (newreturn : bool) (pexps : 'a pexp list) (k : 'a pexp list -> 'a exp) : 'a exp =
    mapCont (n_pexp newreturn) pexps k
  and n_lb (lb : 'a letbind) (k : 'a letbind -> 'a exp) : 'a exp =
    let (LB_aux (lb, annot)) = lb in
    match lb with LB_val (pat, exp1) -> n_exp exp1 (fun exp1 -> k (LB_aux (LB_val (pat, exp1), annot)))
  and n_lexp (lexp : 'a lexp) (k : 'a lexp -> 'a exp) : 'a exp =
    let (LE_aux (lexp_aux, annot)) = lexp in
    match lexp_aux with
    | LE_id _ -> k lexp
    | LE_deref exp -> n_exp_name exp (fun exp -> k (LE_aux (LE_deref exp, annot)))
    | LE_app (id, es) -> n_exp_nameL es (fun es -> k (LE_aux (LE_app (id, es), annot)))
    | LE_tuple es -> n_lexpL es (fun es -> k (LE_aux (LE_tuple es, annot)))
    | LE_typ (typ, id) -> k (LE_aux (LE_typ (typ, id), annot))
    | LE_vector (lexp, e) -> n_lexp lexp (fun lexp -> n_exp_name e (fun e -> k (LE_aux (LE_vector (lexp, e), annot))))
    | LE_vector_range (lexp, e1, e2) ->
        n_lexp lexp (fun lexp ->
            n_exp_name e1 (fun e1 -> n_exp_name e2 (fun e2 -> k (LE_aux (LE_vector_range (lexp, e1, e2), annot))))
        )
    | LE_vector_concat es -> n_lexpL es (fun es -> k (LE_aux (LE_vector_concat es, annot)))
    | LE_field (lexp, id) -> n_lexp lexp (fun lexp -> k (LE_aux (LE_field (lexp, id), annot)))
  and n_lexpL (lexps : 'a lexp list) (k : 'a lexp list -> 'a exp) : 'a exp = mapCont n_lexp lexps k
  and n_exp_term ?(cast = false) (newreturn : bool) (exp : 'a exp) : 'a exp =
    let (E_aux (_, (l, tannot))) = exp in
    let exp =
      if newreturn then (
        (* let typ = try typ_of exp with _ -> unit_typ in *)
        let exp = if cast then add_e_typ (env_of exp) (typ_of exp) exp else exp in
        annot_exp (E_internal_return exp) l (env_of exp) (typ_of exp)
      )
      else exp
    in
    (* n_exp_term forces an expression to be translated into a form
       "let .. let .. let .. in EXP" where EXP has no effect and does not update
       variables *)
    n_exp_pure exp (fun exp -> exp)
  and n_exp (E_aux (exp_aux, annot) as exp : 'a exp) (k : 'a exp -> 'a exp) : 'a exp =
    let rewrap e = E_aux (e, annot) in
    let pure_rewrap e = purify (rewrap e) in
    match exp_aux with
    | E_block es -> failwith "E_block should have been removed till now"
    | E_id id -> k exp
    | E_ref id -> k exp
    | E_lit _ -> k exp
    | E_typ (typ, exp') -> n_exp_name exp' (fun exp' -> k (pure_rewrap (E_typ (typ, exp'))))
    | E_app (op_bool, [l; r]) when string_of_id op_bool = "and_bool" || string_of_id op_bool = "or_bool" ->
        (* Leave effectful operands of Boolean "and"/"or" in place to allow
           short-circuiting. *)
        let newreturn = effectful l || effectful r in
        let l = n_exp_term ~cast:true newreturn l in
        let r = n_exp_term ~cast:true newreturn r in
        k (rewrap (E_app (op_bool, [l; r])))
    | E_app (id, exps) ->
        let fix_eff = if Effects.function_is_pure id effect_info then purify else fun exp -> exp in
        n_exp_nameL exps (fun exps -> k (fix_eff (rewrap (E_app (id, exps)))))
    | E_app_infix (exp1, id, exp2) ->
        let fix_eff = if Effects.function_is_pure id effect_info then purify else fun exp -> exp in
        n_exp_name exp1 (fun exp1 -> n_exp_name exp2 (fun exp2 -> k (fix_eff (rewrap (E_app_infix (exp1, id, exp2))))))
    | E_tuple exps -> n_exp_nameL exps (fun exps -> k (pure_rewrap (E_tuple exps)))
    | E_if (exp1, exp2, exp3) ->
        let e_if exp1 =
          let newreturn = effectful exp2 || effectful exp3 in
          let exp2 = n_exp_term newreturn exp2 in
          let exp3 = n_exp_term newreturn exp3 in
          k (rewrap (E_if (exp1, exp2, exp3)))
        in
        if value exp1 then e_if (n_exp_term false exp1) else n_exp_name exp1 e_if
    | E_for (id, start, stop, by, dir, body) ->
        n_exp_name start (fun start ->
            n_exp_name stop (fun stop ->
                n_exp_name by (fun by ->
                    let body = n_exp_term (effectful body) body in
                    k (rewrap (E_for (id, start, stop, by, dir, body)))
                )
            )
        )
    | E_loop (loop, measure, cond, body) ->
        let measure =
          match measure with
          | Measure_aux (Measure_none, _) -> measure
          | Measure_aux (Measure_some exp, l) -> Measure_aux (Measure_some (n_exp_term false exp), l)
        in
        let cond = n_exp_term ~cast:true (effectful cond) cond in
        let body = n_exp_term (effectful body) body in
        k (rewrap (E_loop (loop, measure, cond, body)))
    | E_vector exps -> n_exp_nameL exps (fun exps -> k (pure_rewrap (E_vector exps)))
    | E_vector_access (exp1, exp2) ->
        n_exp_name exp1 (fun exp1 -> n_exp_name exp2 (fun exp2 -> k (pure_rewrap (E_vector_access (exp1, exp2)))))
    | E_vector_subrange (exp1, exp2, exp3) ->
        n_exp_name exp1 (fun exp1 ->
            n_exp_name exp2 (fun exp2 ->
                n_exp_name exp3 (fun exp3 -> k (pure_rewrap (E_vector_subrange (exp1, exp2, exp3))))
            )
        )
    | E_vector_update (exp1, exp2, exp3) ->
        n_exp_name exp1 (fun exp1 ->
            n_exp_name exp2 (fun exp2 ->
                n_exp_name exp3 (fun exp3 -> k (pure_rewrap (E_vector_update (exp1, exp2, exp3))))
            )
        )
    | E_vector_update_subrange (exp1, exp2, exp3, exp4) ->
        n_exp_name exp1 (fun exp1 ->
            n_exp_name exp2 (fun exp2 ->
                n_exp_name exp3 (fun exp3 ->
                    n_exp_name exp4 (fun exp4 -> k (pure_rewrap (E_vector_update_subrange (exp1, exp2, exp3, exp4))))
                )
            )
        )
    | E_vector_append (exp1, exp2) ->
        n_exp_name exp1 (fun exp1 -> n_exp_name exp2 (fun exp2 -> k (pure_rewrap (E_vector_append (exp1, exp2)))))
    | E_list exps -> n_exp_nameL exps (fun exps -> k (pure_rewrap (E_list exps)))
    | E_cons (exp1, exp2) ->
        n_exp_name exp1 (fun exp1 -> n_exp_name exp2 (fun exp2 -> k (pure_rewrap (E_cons (exp1, exp2)))))
    | E_struct fexps -> n_fexpL fexps (fun fexps -> k (pure_rewrap (E_struct fexps)))
    | E_struct_update (exp1, fexps) ->
        n_exp_name exp1 (fun exp1 -> n_fexpL fexps (fun fexps -> k (pure_rewrap (E_struct_update (exp1, fexps)))))
    | E_field (exp1, id) -> n_exp_name exp1 (fun exp1 -> k (pure_rewrap (E_field (exp1, id))))
    | E_match (exp1, pexps) ->
        let newreturn = List.exists effectful_pexp pexps in
        n_exp_name exp1 (fun exp1 -> n_pexpL newreturn pexps (fun pexps -> k (rewrap (E_match (exp1, pexps)))))
    | E_try (exp1, pexps) ->
        let newreturn = effectful exp1 || List.exists effectful_pexp pexps in
        let exp1 = n_exp_term newreturn exp1 in
        n_pexpL newreturn pexps (fun pexps -> k (rewrap (E_try (exp1, pexps))))
    | E_let (lb, body) -> n_lb lb (fun lb -> rewrap (E_let (lb, n_exp body k)))
    | E_sizeof nexp -> k (rewrap (E_sizeof nexp))
    | E_constraint nc -> k (rewrap (E_constraint nc))
    | E_assign (lexp, exp1) -> n_lexp lexp (fun lexp -> n_exp_name exp1 (fun exp1 -> k (rewrap (E_assign (lexp, exp1)))))
    | E_exit exp' -> k (E_aux (E_exit (n_exp_term (effectful exp') exp'), annot))
    | E_assert (exp1, exp2) ->
        n_exp_name exp1 (fun exp1 -> n_exp_name exp2 (fun exp2 -> k (rewrap (E_assert (exp1, exp2)))))
    | E_var (lexp, exp1, exp2) ->
        n_lexp lexp (fun lexp -> n_exp exp1 (fun exp1 -> rewrap (E_var (lexp, exp1, n_exp exp2 k))))
    | E_internal_return exp1 ->
        let is_early_return = function E_aux (E_app (id, _), _) -> string_of_id id = "early_return" | _ -> false in
        n_exp_name exp1 (fun exp1 ->
            k (if effectful exp1 || is_early_return exp1 then exp1 else rewrap (E_internal_return exp1))
        )
    | E_internal_value v -> k (rewrap (E_internal_value v))
    | E_return exp' -> n_exp_name exp' (fun exp' -> k (pure_rewrap (E_return exp')))
    | E_throw exp' -> n_exp_name exp' (fun exp' -> k (rewrap (E_throw exp')))
    | E_internal_assume (nc, exp') -> rewrap (E_internal_assume (nc, n_exp exp' k))
    | E_internal_plet _ -> failwith "E_internal_plet should not be here yet"
  in

  let rewrite_fun _ (FD_aux (FD_function (recopt, tannotopt, funcls), fdannot)) =
    (* TODO EFFECT *)
    let effectful_vs = false in
    let effectful_funcl (FCL_aux (FCL_funcl (_, pexp), _)) = effectful_pexp pexp in
    let newreturn = effectful_vs || List.exists effectful_funcl funcls in
    let rewrite_funcl (FCL_aux (FCL_funcl (id, pexp), annot)) =
      let _ = reset_fresh_name_counter () in
      FCL_aux (FCL_funcl (id, n_pexp newreturn pexp (fun x -> x)), annot)
    in
    FD_aux (FD_function (recopt, tannotopt, List.map rewrite_funcl funcls), fdannot)
  in
  let rewrite_def rewriters (DEF_aux (aux, def_annot)) =
    let aux =
      match aux with
      | DEF_let (LB_aux (lb, annot)) ->
          let rewrap lb = DEF_let (LB_aux (lb, annot)) in
          begin
            match lb with LB_val (pat, exp) -> rewrap (LB_val (pat, n_exp_term (effectful exp) exp))
          end
      | DEF_fundef fdef -> DEF_fundef (rewrite_fun rewriters fdef)
      | DEF_internal_mutrec fdefs -> DEF_internal_mutrec (List.map (rewrite_fun rewriters) fdefs)
      | _ -> aux
    in
    DEF_aux (aux, def_annot)
  in
  fun ast ->
    ( rewrite_ast_base
        {
          rewrite_exp;
          rewrite_pat;
          rewrite_let;
          rewrite_lexp;
          rewrite_fun;
          rewrite_def;
          rewrite_ast = rewrite_ast_base;
        }
        ast,
      effect_info,
      env
    )

let rewrite_ast_internal_lets env =
  let rec pat_of_local_lexp (LE_aux (lexp, ((l, _) as annot))) =
    match lexp with
    | LE_id id -> P_aux (P_id id, annot)
    | LE_typ (typ, id) -> add_p_typ (env_of_annot annot) typ (P_aux (P_id id, annot))
    | LE_tuple lexps -> P_aux (P_tuple (List.map pat_of_local_lexp lexps), annot)
    | _ -> raise (Reporting.err_unreachable l __POS__ "unexpected local lexp")
  in

  let e_let (lb, body) =
    match lb with
    | LB_aux
        ( LB_val
            ( P_aux ((P_wild | P_typ (_, P_aux (P_wild, _))), _),
              E_aux (E_assign ((LE_aux (_, annot) as le), exp), (l, _))
            ),
          _
        )
      when lexp_is_local le (env_of_annot annot) && not (lexp_is_effectful le) ->
        (* Rewrite assignments to local variables into let bindings *)
        let lhs, rhs = rewrite_lexp_to_rhs le in
        let (LE_aux (_, lannot)) = lhs in
        let ltyp =
          typ_of_annot
            (* The type in the lannot might come from exp rather than being the
               type of the storage, so ask the type checker what it really is. *)
            ( match infer_lexp (env_of_annot lannot) (strip_lexp lhs) with
            | LE_aux (_, lexp_annot') -> lexp_annot'
            | exception _ -> lannot
            )
        in
        let rhs = add_e_typ (env_of exp) ltyp (rhs exp) in
        E_let (LB_aux (LB_val (pat_of_local_lexp lhs, rhs), annot), body)
    | LB_aux (LB_val (pat, exp'), annot') ->
        if effectful exp' then E_internal_plet (pat, exp', body) else E_let (lb, body)
  in

  let e_var (lexp, exp1, exp2) =
    let paux, annot =
      match lexp with
      | LE_aux (LE_id id, annot) -> (P_id id, annot)
      | LE_aux (LE_typ (typ, id), annot) ->
          (unaux_pat (add_p_typ (env_of_annot annot) typ (P_aux (P_id id, annot))), annot)
      | _ -> failwith "E_var with unexpected lexp"
    in
    if effectful exp1 then E_internal_plet (P_aux (paux, annot), exp1, exp2)
    else E_let (LB_aux (LB_val (P_aux (paux, annot), exp1), annot), exp2)
  in

  let alg = { id_exp_alg with e_let; e_var } in
  rewrite_ast_base
    {
      rewrite_exp = (fun _ exp -> fold_exp alg exp);
      rewrite_pat;
      rewrite_let;
      rewrite_lexp;
      rewrite_fun;
      rewrite_def;
      rewrite_ast = rewrite_ast_base;
    }

let fold_typed_guards env guards =
  match guards with
  | [] -> annot_exp (E_lit (mk_lit L_true)) Parse_ast.Unknown env bool_typ
  | g :: gs ->
      List.fold_left (fun g g' -> annot_exp (E_app (mk_id "and_bool", [g; g'])) Parse_ast.Unknown env bool_typ) g gs

let pexp_rewriters rewrite_pexp =
  let alg = { id_exp_alg with pat_aux = (fun (pexp_aux, annot) -> rewrite_pexp (Pat_aux (pexp_aux, annot))) } in
  rewrite_ast_base { rewriters_base with rewrite_exp = (fun _ -> fold_exp alg) }

let stringappend_counter = ref 0

let fresh_stringappend_id () =
  let id = mk_id ("_s" ^ string_of_int !stringappend_counter ^ "#") in
  stringappend_counter := !stringappend_counter + 1;
  id

let unk = Parse_ast.Unknown
let unkt = (Parse_ast.Unknown, empty_tannot)

let construct_bool_match env (match_on : tannot exp) (pexp : tannot pexp) : tannot exp =
  let true_exp = annot_exp (E_lit (mk_lit L_true)) unk env bool_typ in
  let false_exp = annot_exp (E_lit (mk_lit L_false)) unk env bool_typ in
  let true_pexp =
    match pexp with
    | Pat_aux (Pat_exp (pat, exp), annot) -> Pat_aux (Pat_exp (pat, true_exp), unkt)
    | Pat_aux (Pat_when (pat, guards, exp), annot) -> Pat_aux (Pat_when (pat, guards, true_exp), unkt)
  in
  let false_pexp = Pat_aux (Pat_exp (annot_pat P_wild unk env (typ_of match_on), false_exp), unkt) in
  annot_exp (E_match (match_on, [true_pexp; false_pexp])) unk env bool_typ

let rec bindings_of_pat (P_aux (p_aux, p_annot) as pat) =
  match p_aux with
  | P_lit _ | P_wild -> []
  | P_id id -> [pat]
  (* Should have been rewritten early *)
  | P_vector_subrange _ -> []
  (* we assume the type-checker has already checked the two sides have the same bindings *)
  | P_or (left, right) -> bindings_of_pat left
  | P_as (p, id) -> [annot_pat (P_id id) unk (env_of_pat p) (typ_of_pat p)]
  | P_cons (left, right) -> bindings_of_pat left @ bindings_of_pat right
  (* todo: is this right for negated patterns? *)
  | P_not p | P_typ (_, p) | P_var (p, _) -> bindings_of_pat p
  | P_app (_, ps) | P_vector ps | P_vector_concat ps | P_tuple ps | P_list ps | P_string_append ps ->
      List.map bindings_of_pat ps |> List.flatten
  | P_struct (fpats, _) -> List.map snd fpats |> List.map bindings_of_pat |> List.flatten

let rec binding_typs_of_pat (P_aux (p_aux, p_annot) as pat) =
  match p_aux with
  | P_lit _ | P_wild -> []
  (* This pattern should be rewritten early *)
  | P_vector_subrange _ -> []
  | P_id id -> [typ_of_pat pat]
  (* we assume the type-checker has already checked the two sides have the same bindings *)
  | P_or (left, right) -> binding_typs_of_pat left
  | P_as (p, id) -> [typ_of_pat p]
  | P_cons (left, right) -> binding_typs_of_pat left @ binding_typs_of_pat right
  (* todo: is this right for negated patterns? *)
  | P_not p | P_typ (_, p) | P_var (p, _) -> binding_typs_of_pat p
  | P_app (_, ps) | P_vector ps | P_vector_concat ps | P_tuple ps | P_list ps | P_string_append ps ->
      List.map binding_typs_of_pat ps |> List.flatten
  | P_struct (fpats, _) -> List.map snd fpats |> List.map binding_typs_of_pat |> List.flatten

let rewrite_ast_toplevel_string_append effect_info env ast = (ast, effect_info, env)

let rewrite_ast_pat_string_append env =
  let alg = { (pure_pat_alg false ( || )) with p_string_append = (fun _ -> true) } in
  let has_string_append_pattern = fold_pat alg in
  let rewrite_pexp pexp =
    let (P_aux (_, pat_annot) as pat), _, E_aux (_, exp_annot), annot = destruct_pexp pexp in
    if has_string_append_pattern pat then (
      let lit_unit = check_exp env (mk_lit_exp L_unit) unit_typ in
      construct_pexp (P_aux (P_wild, pat_annot), None, E_aux (E_exit lit_unit, exp_annot), annot)
    )
    else pexp
  in
  pexp_rewriters rewrite_pexp

let rewrite_lit_lem (L_aux (lit, _)) =
  match lit with L_num _ | L_string _ | L_hex _ | L_bin _ | L_real _ -> true | _ -> false

let rewrite_lit_ocaml (L_aux (lit, _)) =
  match lit with L_num _ | L_string _ | L_hex _ | L_bin _ | L_real _ | L_unit -> false | _ -> true

let rewrite_ast_pat_lits rewrite_lit env ast =
  let rewrite_pexp (Pat_aux (pexp_aux, annot)) =
    let guards = ref [] in
    let counter = ref 0 in

    let rewrite_pat = function
      (* Matching on unit is always the same as matching on wildcard *)
      | P_lit (L_aux (L_unit, _) as lit), p_annot when rewrite_lit lit -> P_aux (P_wild, p_annot)
      | P_lit lit, p_annot when rewrite_lit lit ->
          let env = env_of_annot p_annot in
          let typ = typ_of_annot p_annot in
          let id = mk_id ("p" ^ string_of_int !counter ^ "#") in
          let guard = mk_exp (E_app_infix (mk_exp (E_id id), mk_id "==", mk_exp (E_lit lit))) in
          let guard = check_exp (Env.add_local id (Immutable, typ) env) guard bool_typ in
          guards := guard :: !guards;
          incr counter;
          P_aux (P_id id, p_annot)
      | p_aux, p_annot -> P_aux (p_aux, p_annot)
    in

    match pexp_aux with
    | Pat_exp (pat, exp) -> begin
        let pat = fold_pat { id_pat_alg with p_aux = rewrite_pat } pat in
        match !guards with
        | [] -> Pat_aux (Pat_exp (pat, exp), annot)
        | g :: gs ->
            let guard_annot = (fst annot, mk_tannot (env_of exp) bool_typ) in
            Pat_aux
              ( Pat_when
                  (pat, List.fold_left (fun g g' -> E_aux (E_app (mk_id "and_bool", [g; g']), guard_annot)) g gs, exp),
                annot
              )
      end
    | Pat_when (pat, guard, exp) -> begin
        let pat = fold_pat { id_pat_alg with p_aux = rewrite_pat } pat in
        let guard_annot = (fst annot, mk_tannot (env_of exp) bool_typ) in
        Pat_aux
          ( Pat_when
              ( pat,
                List.fold_left (fun g g' -> E_aux (E_app (mk_id "and_bool", [g; g']), guard_annot)) guard !guards,
                exp
              ),
            annot
          )
      end
  in

  let rewrite_funcl (FCL_aux (FCL_funcl (id, pexp), (l, annot))) =
    FCL_aux (FCL_funcl (id, rewrite_pexp pexp), (l, annot))
  in
  let rewrite_fun (FD_aux (FD_function (recopt, tannotopt, funcls), (l, annot))) =
    FD_aux (FD_function (recopt, tannotopt, List.map rewrite_funcl funcls), (l, annot))
  in
  let rewrite_def = function
    | DEF_aux (DEF_fundef fdef, def_annot) -> DEF_aux (DEF_fundef (rewrite_fun fdef), def_annot)
    | def -> def
  in

  let alg = { id_exp_alg with pat_aux = (fun (pexp_aux, annot) -> rewrite_pexp (Pat_aux (pexp_aux, annot))) } in
  let ast = rewrite_ast_base { rewriters_base with rewrite_exp = (fun _ -> fold_exp alg) } ast in
  { ast with defs = List.map rewrite_def ast.defs }

(* Now all expressions have no blocks anymore, any term is a sequence of let-expressions,
 * internal let-expressions, or internal plet-expressions ended by a term that does not
 * access memory or registers and does not update variables *)

type 'a updated_term = Added_vars of 'a exp * 'a pat | Same_vars of 'a exp

let rec rewrite_var_updates (E_aux (expaux, ((l, _) as annot)) as exp) =
  let env = env_of exp in

  let tuple_exp = function
    | [] -> annot_exp (E_lit (mk_lit L_unit)) l env unit_typ
    | [e] -> e
    | es -> annot_exp (E_tuple es) l env (tuple_typ (List.map typ_of es))
  in

  let tuple_pat = function
    | [] -> annot_pat P_wild l env unit_typ
    | [pat] ->
        let typ = typ_of_pat pat in
        add_p_typ env typ pat
    | pats ->
        let typ = tuple_typ (List.map typ_of_pat pats) in
        add_p_typ env typ (annot_pat (P_tuple pats) l env typ)
  in

  let rec add_vars overwrite (E_aux (expaux, annot) as exp) vars =
    match expaux with
    | E_let (lb, exp) ->
        let exp = add_vars overwrite exp vars in
        E_aux (E_let (lb, exp), swaptyp (typ_of exp) annot)
    | E_var (lexp, exp1, exp2) ->
        let exp2 = add_vars overwrite exp2 vars in
        E_aux (E_var (lexp, exp1, exp2), swaptyp (typ_of exp2) annot)
    | E_internal_plet (pat, exp1, exp2) ->
        let exp2 = add_vars overwrite exp2 vars in
        E_aux (E_internal_plet (pat, exp1, exp2), swaptyp (typ_of exp2) annot)
    | E_internal_return exp2 ->
        let exp2 = add_vars overwrite exp2 vars in
        E_aux (E_internal_return exp2, swaptyp (typ_of exp2) annot)
    | E_typ (typ, exp) ->
        let (E_aux (expaux, annot) as exp) = add_vars overwrite exp vars in
        let typ' = typ_of exp in
        add_e_typ (env_of exp) typ' (E_aux (expaux, swaptyp typ' annot))
    | E_app (early_return, args) when string_of_id early_return = "early_return" ->
        (* Special case early return:  It has to be monadic for the prover
         * backends, so the addition of vars below wouldn't work without an
         * extra E_internal_return.  But threading through local vars to the
         * outer block isn't necessary anyway, because we will exit the
         * function, so just keep the early_return expression as is. *)
        exp
    | E_internal_assume (nc, exp) ->
        let exp = add_vars overwrite exp vars in
        E_aux (E_internal_assume (nc, exp), swaptyp (typ_of exp) annot)
    | _ ->
        (* after rewrite_ast_letbind_effects there cannot be terms that have
           effects/update local variables in "tail-position": check n_exp_term
           and where it is used. *)
        if overwrite then (
          let lb = LB_aux (LB_val (P_aux (P_wild, annot), exp), annot) in
          let exp' = tuple_exp vars in
          E_aux (E_let (lb, exp'), swaptyp (typ_of exp') annot) |> add_typs_let env (typ_of exp) (typ_of exp')
        )
        else tuple_exp (exp :: vars)
  in

  let mk_var_exps_pats l env ids =
    ids |> IdSet.elements
    |> List.map (fun id ->
           let (E_aux (_, a) as exp) = infer_exp env (E_aux (E_id id, (l, empty_uannot))) in
           (exp, P_aux (P_id id, a))
       )
    |> List.split
  in

  let rec rewrite used_vars (E_aux (expaux, ((el, _) as annot)) as full_exp) (P_aux (paux, (pl, pannot)) as pat) =
    let env = env_of_annot annot in
    let overwrite = match paux with P_wild | P_typ (_, P_aux (P_wild, _)) -> true | _ -> false in
    match expaux with
    | E_for (id, exp1, exp2, exp3, order, exp4) ->
        (* Translate for loops into calls to one of the foreach combinators.
           The loop body becomes a function of the loop variable and any
           mutable local variables that are updated inside the loop and
           are used after or within the loop.
           Since the foreach* combinators are higher-order functions,
           they cannot be represented faithfully in the AST. The following
           code abuses the parameters of an E_app node, embedding the loop body
           function as an expression followed by the list of variables it
           expects. In (Lem) pretty-printing, this turned into an anonymous
           function and passed to foreach*. *)
        let vars, varpats =
          find_updated_vars exp4
          |> IdSet.inter (IdSet.union used_vars (find_used_vars full_exp))
          |> mk_var_exps_pats pl env
        in
        let exp4 = rewrite_var_updates (add_vars overwrite exp4 vars) in
        (* Bind the loop variable in the body, annotated with constraints *)
        let lvar_kid = mk_kid ("loop_" ^ string_of_id id) in
        let lower_id = mk_id ("loop_" ^ string_of_id id ^ "_lower") in
        let upper_id = mk_id ("loop_" ^ string_of_id id ^ "_upper") in
        let lower_kid = mk_kid ("loop_" ^ string_of_id id ^ "_lower") in
        let upper_kid = mk_kid ("loop_" ^ string_of_id id ^ "_upper") in
        let env' =
          env
          |> Env.add_typ_var el (mk_kopt K_int lvar_kid)
          |> Env.add_typ_var el (mk_kopt K_int lower_kid)
          |> Env.add_typ_var el (mk_kopt K_int upper_kid)
        in
        let lower_id_exp = annot_exp (E_id lower_id) el env' (atom_typ (nvar lower_kid)) in
        let upper_id_exp = annot_exp (E_id upper_id) el env' (atom_typ (nvar upper_kid)) in
        let annot_bool_lit lit = annot_exp (E_lit lit) el env' bool_typ in
        let ord_exp, lower_exp, upper_exp, exp1, exp2 =
          if is_order_inc order then (annot_bool_lit (mk_lit L_true), exp1, exp2, lower_id_exp, upper_id_exp)
          else (annot_bool_lit (mk_lit L_false), exp2, exp1, upper_id_exp, lower_id_exp)
        in
        let lvar_nc = nc_and (nc_lteq (nvar lower_kid) (nvar lvar_kid)) (nc_lteq (nvar lvar_kid) (nvar upper_kid)) in
        let lvar_typ = mk_typ (Typ_exist (List.map (mk_kopt K_int) [lvar_kid], lvar_nc, atom_typ (nvar lvar_kid))) in
        let lvar_pat =
          unaux_pat
            (annot_pat
               (P_var (annot_pat (P_id id) el env' (atom_typ (nvar lvar_kid)), TP_aux (TP_var lvar_kid, gen_loc el)))
               el env' lvar_typ
            )
        in
        let lb = annot_letbind (lvar_pat, exp1) el env' lvar_typ in
        let body = annot_exp (E_let (lb, exp4)) el env' (typ_of exp4) |> add_typs_let env' lvar_typ (typ_of exp4) in
        (* If lower > upper, the loop body never gets executed, and the type
           checker might not be able to prove that the initial value exp1
           satisfies the constraints on the loop variable.

           Make this explicit by guarding the loop body with lower <= upper.
           (for type-checking; the guard is later removed again by the Lem
           pretty-printer).  This could be implemented with an assertion, but
           that would force the loop to be effectful, so we use an if-expression
           instead.  This code assumes that the loop bounds have (possibly
           existential) atom types, and the loop body has type unit. *)
        let lower_pat =
          P_var
            ( annot_pat (P_id lower_id) el env (typ_of lower_exp),
              mk_typ_pat (TP_app (mk_id "atom", [mk_typ_pat (TP_var lower_kid)]))
            )
        in
        let lb_lower = annot_letbind (lower_pat, lower_exp) el env (typ_of lower_exp) in
        let upper_pat =
          P_var
            ( annot_pat (P_id upper_id) el env (typ_of upper_exp),
              mk_typ_pat (TP_app (mk_id "atom", [mk_typ_pat (TP_var upper_kid)]))
            )
        in
        let lb_upper = annot_letbind (upper_pat, upper_exp) el env (typ_of upper_exp) in
        let guard = annot_exp (E_constraint (nc_lteq (nvar lower_kid) (nvar upper_kid))) el env' bool_typ in
        let unit_exp = annot_exp (E_lit (mk_lit L_unit)) el env' unit_typ in
        let skip_val = tuple_exp (if overwrite then vars else unit_exp :: vars) in
        let guarded_body = annot_exp (E_if (guard, body, skip_val)) el env' (typ_of exp4) in
        let v =
          annot_exp
            (E_let
               ( lb_lower,
                 annot_exp
                   (E_let
                      ( lb_upper,
                        annot_exp
                          (E_app (mk_id "foreach#", [exp1; exp2; exp3; ord_exp; tuple_exp vars; guarded_body]))
                          el env (typ_of exp4)
                      )
                   )
                   el env (typ_of exp4)
               )
            )
            el env (typ_of exp4)
        in
        Added_vars (v, tuple_pat (if overwrite then varpats else pat :: varpats))
    | E_loop (loop, Measure_aux (measure, _), cond, body) ->
        (* Find variables that might be updated in the loop body and are used
           either after or within the loop. *)
        let vars, varpats =
          find_updated_vars body
          |> IdSet.inter (IdSet.union used_vars (find_used_vars full_exp))
          |> mk_var_exps_pats pl env
        in
        let body = rewrite_var_updates (add_vars overwrite body vars) in
        let body = add_e_typ env (typ_of body) body in
        let (E_aux (_, (_, bannot))) = body in
        let fname, measure =
          match (loop, measure) with
          | While, Measure_none -> ("while#", [])
          | Until, Measure_none -> ("until#", [])
          | While, Measure_some exp -> ("while#t", [exp])
          | Until, Measure_some exp -> ("until#t", [exp])
        in
        let funcl = Id_aux (Id fname, gen_loc el) in
        let v = E_aux (E_app (funcl, [cond; tuple_exp vars; body] @ measure), (gen_loc el, bannot)) in
        Added_vars (v, tuple_pat (if overwrite then varpats else pat :: varpats))
    | E_if (c, e1, e2) ->
        let vars, varpats =
          IdSet.union (find_updated_vars e1) (find_updated_vars e2) |> IdSet.inter used_vars |> mk_var_exps_pats pl env
        in
        if vars = [] then Same_vars (E_aux (E_if (c, rewrite_var_updates e1, rewrite_var_updates e2), annot))
        else (
          let e1 = rewrite_var_updates (add_vars overwrite e1 vars) in
          let e2 = rewrite_var_updates (add_vars overwrite e2 vars) in
          (* after rewrite_ast_letbind_effects c has no variable updates *)
          let env = env_of_annot annot in
          let typ = typ_of e1 in
          let v = E_aux (E_if (c, e1, e2), (gen_loc el, mk_tannot env typ)) in
          Added_vars (v, tuple_pat (if overwrite then varpats else pat :: varpats))
        )
    | E_match (e1, ps) | E_try (e1, ps) ->
        let is_case = match expaux with E_match _ -> true | _ -> false in
        let vars, varpats =
          (* for E_match, e1 needs no rewriting after rewrite_ast_letbind_effects *)
          (if is_case then [] else [e1]) @ List.map (fun (Pat_aux ((Pat_exp (_, e) | Pat_when (_, _, e)), _)) -> e) ps
          |> List.map find_updated_vars |> List.fold_left IdSet.union IdSet.empty |> IdSet.inter used_vars
          |> mk_var_exps_pats pl env
        in
        let e1 = if is_case then e1 else rewrite_var_updates (add_vars overwrite e1 vars) in
        if vars = [] then (
          let ps =
            List.map
              (function
                | Pat_aux (Pat_exp (p, e), a) -> Pat_aux (Pat_exp (p, rewrite_var_updates e), a)
                | Pat_aux (Pat_when (p, g, e), a) -> Pat_aux (Pat_when (p, g, rewrite_var_updates e), a)
                )
              ps
          in
          let expaux = if is_case then E_match (e1, ps) else E_try (e1, ps) in
          Same_vars (E_aux (expaux, annot))
        )
        else (
          let rewrite_pexp (Pat_aux (pexp, (l, _))) =
            match pexp with
            | Pat_exp (pat, exp) ->
                let exp = rewrite_var_updates (add_vars overwrite exp vars) in
                let pannot = (l, mk_tannot (env_of exp) (typ_of exp)) in
                Pat_aux (Pat_exp (pat, exp), pannot)
            | Pat_when _ ->
                raise (Reporting.err_unreachable l __POS__ "Guarded patterns should have been rewritten already")
          in
          let ps = List.map rewrite_pexp ps in
          let expaux = if is_case then E_match (e1, ps) else E_try (e1, ps) in
          let typ =
            match ps with
            | Pat_aux ((Pat_exp (_, first) | Pat_when (_, _, first)), _) :: _ -> typ_of first
            | _ -> unit_typ
          in
          let v = annot_exp expaux pl env typ in
          Added_vars (v, tuple_pat (if overwrite then varpats else pat :: varpats))
        )
    | E_assign (lexp, vexp) ->
        let mk_id_pat id =
          let typ = lvar_typ (Env.lookup_id id env) in
          add_p_typ env typ (annot_pat (P_id id) pl env typ)
        in
        if effectful full_exp then Same_vars (E_aux (E_assign (lexp, vexp), annot))
        else (
          match lexp with
          | LE_aux (LE_id id, annot) -> Added_vars (vexp, mk_id_pat id)
          | LE_aux (LE_typ (typ, id), annot) ->
              let pat = add_p_typ env typ (annot_pat (P_id id) pl env (typ_of vexp)) in
              Added_vars (vexp, pat)
          | LE_aux (LE_vector (LE_aux (LE_id id, ((l2, _) as annot2)), i), ((l1, _) as annot)) ->
              let eid = annot_exp (E_id id) l2 env (typ_of_annot annot2) in
              let vexp = annot_exp (E_vector_update (eid, i, vexp)) l1 env (typ_of_annot annot) in
              let pat = annot_pat (P_id id) pl env (typ_of vexp) in
              Added_vars (vexp, pat)
          | LE_aux (LE_vector_range (LE_aux (LE_id id, ((l2, _) as annot2)), i, j), ((l, _) as annot)) ->
              let eid = annot_exp (E_id id) l2 env (typ_of_annot annot2) in
              let vexp = annot_exp (E_vector_update_subrange (eid, i, j, vexp)) l env (typ_of_annot annot) in
              let pat = annot_pat (P_id id) pl env (typ_of vexp) in
              Added_vars (vexp, pat)
          | _ -> Same_vars (E_aux (E_assign (lexp, vexp), annot))
        )
    | E_typ (typ, exp) -> begin
        match rewrite used_vars exp pat with
        | Added_vars (exp', pat') -> Added_vars (add_e_typ (env_of exp') (typ_of exp') exp', pat')
        | Same_vars exp' -> Same_vars (E_aux (E_typ (typ, exp'), annot))
      end
    | _ ->
        (* after rewrite_ast_letbind_effects this expression is pure and updates
           no variables: check n_exp_term and where it's used. *)
        Same_vars (E_aux (expaux, annot))
  in

  match expaux with
  | E_let (lb, body) ->
      let body = rewrite_var_updates body in
      let (LB_aux (LB_val (pat, v), lbannot)) = lb in
      let lb =
        match rewrite (find_used_vars body) v pat with
        | Added_vars (v, P_aux (pat, _)) -> annot_letbind (pat, v) (get_loc_exp v) env (typ_of v)
        | Same_vars v -> LB_aux (LB_val (pat, v), lbannot)
      in
      annot_exp (E_let (lb, body)) l env (typ_of body)
  | E_var (lexp, v, body) ->
      (* Rewrite E_var into E_let and call recursively *)
      let rec aux lexp =
        match lexp with
        | LE_aux (LE_id id, _) -> (P_id id, typ_of v)
        | LE_aux (LE_typ (typ, id), _) -> (unaux_pat (add_p_typ env typ (annot_pat (P_id id) l env (typ_of v))), typ)
        | LE_aux (LE_tuple lexps, _) ->
            let pauxs_typs = List.map aux lexps in
            let pats, typs = List.split (List.map (fun (paux, typ) -> (annot_pat paux l env typ, typ)) pauxs_typs) in
            (P_tuple pats, mk_typ (Typ_tuple typs))
        | _ ->
            raise
              (Reporting.err_unreachable l __POS__ ("E_var with a lexp that is not a variable: " ^ string_of_lexp lexp))
      in
      let paux, typ = aux lexp in
      let lb = annot_letbind (paux, v) l env typ in
      let exp = annot_exp (E_let (lb, body)) l env (typ_of body) in
      rewrite_var_updates exp
  | E_for _ | E_loop _ | E_if _ | E_match _ | E_assign _ ->
      let var_id = fresh_id "u__" l in
      let lb = LB_aux (LB_val (P_aux (P_id var_id, annot), exp), annot) in
      let exp' = E_aux (E_let (lb, E_aux (E_id var_id, annot)), annot) in
      rewrite_var_updates exp'
  | E_internal_plet (pat, v, body) -> failwith "rewrite_var_updates: E_internal_plet shouldn't be introduced yet"
  | E_typ (typ, exp) ->
      let exp' = rewrite_var_updates exp in
      E_aux (E_typ (typ, exp'), annot)
  | E_internal_assume (nc, exp) ->
      let exp' = rewrite_var_updates exp in
      E_aux (E_internal_assume (nc, exp'), annot)
  (* There are no other expressions that have effects or variable updates in
     "tail-position": check the definition nexp_term and where it is used. *)
  | _ -> exp

let replace_memwrite_e_assign exp =
  let e_aux (expaux, annot) =
    match expaux with
    | E_assign (LE_aux (LE_app (id, args), _), v) -> E_aux (E_app (id, args @ [v]), annot)
    | _ -> E_aux (expaux, annot)
  in
  fold_exp { id_exp_alg with e_aux } exp

let remove_reference_types exp =
  let rec rewrite_t (Typ_aux (t_aux, a)) = Typ_aux (rewrite_t_aux t_aux, a)
  and rewrite_t_aux t_aux =
    match t_aux with
    | Typ_app (Id_aux (Id "reg", _), [A_aux (A_typ (Typ_aux (t_aux2, _)), _)]) -> rewrite_t_aux t_aux2
    | Typ_app (name, t_args) -> Typ_app (name, List.map rewrite_t_arg t_args)
    | Typ_fn (arg_typs, ret_typ) -> Typ_fn (List.map rewrite_t arg_typs, rewrite_t ret_typ)
    | Typ_tuple ts -> Typ_tuple (List.map rewrite_t ts)
    | _ -> t_aux
  and rewrite_t_arg t_arg = match t_arg with A_aux (A_typ t, a) -> A_aux (A_typ (rewrite_t t), a) | _ -> t_arg in

  let rewrite_annot (l, tannot) =
    match destruct_tannot tannot with
    | None -> (l, empty_tannot)
    | Some (_, typ) -> (l, replace_typ (rewrite_t typ) tannot)
  in

  map_exp_annot rewrite_annot exp

let rewrite_ast_remove_superfluous_letbinds env =
  let e_aux (exp, annot) =
    match exp with
    | E_let (LB_aux (LB_val (pat, exp1), _), exp2) | E_internal_plet (pat, exp1, exp2) -> begin
        match (untyp_pat pat, uncast_exp exp1, uncast_exp exp2) with
        (* 'let x = EXP1 in x' can be replaced with 'EXP1' *)
        | (P_aux (P_id id, _), _), _, (E_aux (E_id id', _), _) when Id.compare id id' = 0 -> exp1
        (* "let _ = () in exp" can be replaced with exp *)
        | (P_aux (P_wild, _), _), (E_aux (E_lit (L_aux (L_unit, _)), _), _), _ -> exp2
        (* "let x = EXP1 in return x" can be replaced with 'return (EXP1)', at
           least when EXP1 is 'small' enough *)
        | (P_aux (P_id id, _), _), _, (E_aux (E_internal_return (E_aux (E_id id', _)), _), _)
          when Id.compare id id' = 0 && small exp1 && not (effectful exp1) ->
            let (E_aux (_, e1annot)) = exp1 in
            E_aux (E_internal_return exp1, e1annot)
        | _, (E_aux (E_throw e, a), _), _ -> E_aux (E_throw e, a)
        | (pat, _), ((E_aux (E_assert (c, msg), a) as assert_exp), _), _ -> begin
            match typ_of c with
            | Typ_aux (Typ_app (Id_aux (Id "atom_bool", _), [A_aux (A_bool nc, _)]), _)
              when prove __POS__ (env_of c) (nc_not nc) ->
                (* Drop rest of block after an 'assert(false)' *)
                let exit_exp = E_aux (E_exit (infer_exp (env_of c) (mk_lit_exp L_unit)), a) in
                E_aux (E_internal_plet (pat, assert_exp, exit_exp), annot)
            | _ -> E_aux (exp, annot)
          end
        | _ -> E_aux (exp, annot)
      end
    | _ -> E_aux (exp, annot)
  in

  let alg = { id_exp_alg with e_aux } in
  rewrite_ast_base
    {
      rewrite_exp = (fun _ -> fold_exp alg);
      rewrite_pat;
      rewrite_let;
      rewrite_lexp;
      rewrite_fun;
      rewrite_def;
      rewrite_ast = rewrite_ast_base;
    }

(* FIXME: We shouldn't allow nested not-patterns *)
let rewrite_ast_not_pats env =
  let rewrite_pexp (pexp_aux, annot) =
    let rewrite_pexp' pat exp orig_guard =
      let guards = ref [] in
      let not_counter = ref 0 in
      let rewrite_not_pat (pat_aux, annot) =
        match pat_aux with
        | P_not pat ->
            incr not_counter;
            let np_id = mk_id ("np#" ^ string_of_int !not_counter) in
            let guard =
              mk_exp
                (E_match
                   ( mk_exp (E_id np_id),
                     [
                       mk_pexp (Pat_exp (strip_pat pat, mk_lit_exp L_false));
                       mk_pexp (Pat_exp (mk_pat P_wild, mk_lit_exp L_true));
                     ]
                   )
                )
            in
            guards := (np_id, typ_of_annot annot, guard) :: !guards;
            P_aux (P_id np_id, annot)
        | _ -> P_aux (pat_aux, annot)
      in
      let pat = fold_pat { id_pat_alg with p_aux = rewrite_not_pat } pat in
      begin
        match !guards with
        | [] -> Pat_aux (pexp_aux, annot)
        | guards ->
            let guard_exp =
              match (orig_guard, guards) with
              | Some guard, _ ->
                  List.fold_left (fun exp1 (_, _, exp2) -> mk_exp (E_app_infix (exp1, mk_id "&", exp2))) guard guards
              | None, (_, _, guard) :: guards ->
                  List.fold_left (fun exp1 (_, _, exp2) -> mk_exp (E_app_infix (exp1, mk_id "&", exp2))) guard guards
              | _ ->
                  raise
                    (Reporting.err_unreachable (fst annot) __POS__
                       "Case in not-pattern re-writing should be unreachable"
                    )
            in
            (* We need to construct an environment to check the match guard in *)
            let env = env_of_pat pat in
            let env =
              List.fold_left (fun env (np_id, np_typ, _) -> Env.add_local np_id (Immutable, np_typ) env) env guards
            in
            let guard_exp = Type_check.check_exp env guard_exp bool_typ in
            Pat_aux (Pat_when (pat, guard_exp, exp), annot)
      end
    in
    match pexp_aux with
    | Pat_exp (pat, exp) -> rewrite_pexp' pat exp None
    | Pat_when (pat, guard, exp) -> rewrite_pexp' pat exp (Some (strip_exp guard))
  in
  let rw_exp = { id_exp_alg with pat_aux = rewrite_pexp } in
  rewrite_ast_base { rewriters_base with rewrite_exp = (fun _ -> fold_exp rw_exp) }

let rewrite_ast_remove_superfluous_returns env =
  let add_opt_cast typopt1 typopt2 annot exp =
    match (typopt1, typopt2) with Some typ, _ | _, Some typ -> add_e_typ (env_of exp) typ exp | None, None -> exp
  in

  let e_aux (exp, annot) =
    match exp with
    | (E_let (LB_aux (LB_val (pat, exp1), _), exp2) | E_internal_plet (pat, exp1, exp2)) when effectful exp1 -> begin
        match (untyp_pat pat, uncast_exp exp2) with
        | ( (P_aux (P_lit (L_aux (lit, _)), _), ptyp),
            (E_aux (E_internal_return (E_aux (E_lit (L_aux (lit', _)), _)), a), etyp) )
          when lit = lit' ->
            add_opt_cast ptyp etyp a exp1
        | ( (P_aux (P_wild, pannot), ptyp),
            (E_aux ((E_internal_return (E_aux (E_lit (L_aux (L_unit, _)), _)) | E_lit (L_aux (L_unit, _))), a), etyp) )
          when is_unit_typ (typ_of exp1) ->
            add_opt_cast ptyp etyp a exp1
        | (P_aux (P_id id, _), ptyp), (E_aux (E_internal_return (E_aux (E_id id', _)), a), etyp)
          when Id.compare id id' == 0 ->
            add_opt_cast ptyp etyp a exp1
        | (P_aux (P_tuple ps, _), ptyp), (E_aux (E_internal_return (E_aux (E_tuple es, _)), a), etyp)
          when List.length ps = List.length es ->
            let same_id (P_aux (p, _)) (E_aux (e, _)) =
              match (p, e) with P_id id, E_id id' -> Id.compare id id' == 0 | _, _ -> false
            in
            let ps = List.map fst (List.map untyp_pat ps) in
            let es = List.map fst (List.map uncast_exp es) in
            if List.for_all2 same_id ps es then add_opt_cast ptyp etyp a exp1 else E_aux (exp, annot)
        | _ -> E_aux (exp, annot)
      end
    | _ -> E_aux (exp, annot)
  in

  let alg = { id_exp_alg with e_aux } in
  rewrite_ast_base
    {
      rewrite_exp = (fun _ -> fold_exp alg);
      rewrite_pat;
      rewrite_let;
      rewrite_lexp;
      rewrite_fun;
      rewrite_def;
      rewrite_ast = rewrite_ast_base;
    }

let rewrite_ast_remove_e_assign env ast =
  let loop_specs =
    fst
      (Type_error.check_defs initial_env
         (List.map (gen_vs ~pure:true)
            [
              ("foreach#", "forall ('vars_in 'vars_out : Type). (int, int, int, bool, 'vars_in, 'vars_out) -> 'vars_out");
              ("while#", "forall ('vars_in 'vars_out : Type). (bool, 'vars_in, 'vars_out) -> 'vars_out");
              ("until#", "forall ('vars_in 'vars_out : Type). (bool, 'vars_in, 'vars_out) -> 'vars_out");
              ("while#t", "forall ('vars_in 'vars_out : Type). (bool, 'vars_in, 'vars_out, int) -> 'vars_out");
              ("until#t", "forall ('vars_in 'vars_out : Type). (bool, 'vars_in, 'vars_out, int) -> 'vars_out");
            ]
         )
      )
  in
  let rewrite_exp _ e = replace_memwrite_e_assign (remove_reference_types (rewrite_var_updates e)) in
  rewrite_ast_base
    { rewrite_exp; rewrite_pat; rewrite_let; rewrite_lexp; rewrite_fun; rewrite_def; rewrite_ast = rewrite_ast_base }
    { ast with defs = loop_specs @ ast.defs }

let merge_funcls env ast =
  let merge_function (FD_aux (FD_function (r, t, fcls), ann) as f) =
    match fcls with
    | [] | [_] -> f
    | FCL_aux (FCL_funcl (id, _), (def_annot, _)) :: _ ->
        let l = def_annot.loc in
        let var = mk_id "merge#var" in
        let l_g = Parse_ast.Generated l in
        let ann_g : _ * tannot = (l_g, empty_tannot) in
        let clauses = List.map (fun (FCL_aux (FCL_funcl (_, pexp), _)) -> pexp) fcls in
        FD_aux
          ( FD_function
              ( r,
                t,
                [
                  FCL_aux
                    ( FCL_funcl
                        ( id,
                          Pat_aux
                            ( Pat_exp
                                (P_aux (P_id var, ann_g), E_aux (E_match (E_aux (E_id var, ann_g), clauses), ann_g)),
                              ann_g
                            )
                        ),
                      (mk_def_annot l, empty_tannot)
                    );
                ]
              ),
            ann
          )
  in
  let merge_in_def = function
    | DEF_aux (DEF_fundef f, def_annot) -> DEF_aux (DEF_fundef (merge_function f), def_annot)
    | DEF_aux (DEF_internal_mutrec fs, def_annot) ->
        DEF_aux (DEF_internal_mutrec (List.map merge_function fs), def_annot)
    | d -> d
  in
  { ast with defs = List.map merge_in_def ast.defs }

let rec exp_of_mpat (MP_aux (mpat, (l, annot))) =
  let empty_vec = E_aux (E_vector [], (l, empty_uannot)) in
  let concat_vectors vec1 vec2 = E_aux (E_vector_append (vec1, vec2), (l, empty_uannot)) in
  let empty_string = E_aux (E_lit (L_aux (L_string "", Parse_ast.Unknown)), (l, empty_uannot)) in
  let string_append str1 str2 = E_aux (E_app (mk_id "string_append", [str1; str2]), (l, empty_uannot)) in
  match mpat with
  | MP_lit lit -> E_aux (E_lit lit, (l, annot))
  | MP_id id -> E_aux (E_id id, (l, annot))
  | MP_app (id, args) -> E_aux (E_app (id, List.map exp_of_mpat args), (l, annot))
  | MP_vector mpats -> E_aux (E_vector (List.map exp_of_mpat mpats), (l, annot))
  | MP_vector_concat mpats -> List.fold_right concat_vectors (List.map (fun m -> exp_of_mpat m) mpats) empty_vec
  | MP_vector_subrange (id, n, m) ->
      E_aux
        (E_vector_subrange (mk_exp ~loc:(id_loc id) (E_id id), mk_lit_exp (L_num n), mk_lit_exp (L_num m)), (l, annot))
  | MP_tuple mpats -> E_aux (E_tuple (List.map exp_of_mpat mpats), (l, annot))
  | MP_list mpats -> E_aux (E_list (List.map exp_of_mpat mpats), (l, annot))
  | MP_cons (mpat1, mpat2) -> E_aux (E_cons (exp_of_mpat mpat1, exp_of_mpat mpat2), (l, annot))
  | MP_string_append mpats -> List.fold_right string_append (List.map (fun m -> exp_of_mpat m) mpats) empty_string
  | MP_typ (mpat, typ) -> E_aux (E_typ (typ, exp_of_mpat mpat), (l, annot))
  | MP_as (mpat, id) ->
      E_aux
        ( E_match (E_aux (E_id id, (l, annot)), [Pat_aux (Pat_exp (pat_of_mpat mpat, exp_of_mpat mpat), (l, annot))]),
          (l, annot)
        )
  | MP_struct fmpats ->
      let combined_loc field mpat =
        match (Reporting.simp_loc (id_loc field), Reporting.simp_loc (mpat_loc mpat)) with
        | Some (s, _), Some (_, e) -> Parse_ast.Range (s, e)
        | _, _ -> Parse_ast.Unknown
      in
      E_aux
        ( E_struct
            (List.map
               (fun (field, mpat) -> FE_aux (FE_fexp (field, exp_of_mpat mpat), (combined_loc field mpat, empty_uannot)))
               fmpats
            ),
          (l, annot)
        )
(* TODO FIXME location information? *)

let rewrite_ast_realize_mappings effect_info env ast =
  let effect_info = ref effect_info in
  let realize_mpexps forwards mpexp1 mpexp2 =
    let mpexp_pat, mpexp_exp = if forwards then (mpexp1, mpexp2) else (mpexp2, mpexp1) in
    let exp =
      match mpexp_exp with
      | MPat_aux (MPat_pat mpat, _) -> exp_of_mpat mpat
      | MPat_aux (MPat_when (mpat, _), _) -> exp_of_mpat mpat
    in
    match mpexp_pat with
    | MPat_aux (MPat_pat mpat, annot) -> Pat_aux (Pat_exp (pat_of_mpat mpat, exp), annot)
    | MPat_aux (MPat_when (mpat, guard), annot) -> Pat_aux (Pat_when (pat_of_mpat mpat, guard, exp), annot)
  in
  let realize_single_mpexp mpexp exp =
    match mpexp with
    | MPat_aux (MPat_pat mpat, annot) -> Pat_aux (Pat_exp (pat_of_mpat mpat, exp), annot)
    | MPat_aux (MPat_when (mpat, guard), annot) -> Pat_aux (Pat_when (pat_of_mpat mpat, guard, exp), annot)
  in
  let realize_mapcl forwards id mapcl =
    match mapcl with
    | MCL_aux (MCL_bidir (mpexp1, mpexp2), _) -> [realize_mpexps forwards mpexp1 mpexp2]
    | MCL_aux (MCL_forwards (mpexp, exp), _) -> if forwards then [realize_single_mpexp mpexp exp] else []
    | MCL_aux (MCL_backwards (mpexp, exp), _) -> if forwards then [] else [realize_single_mpexp mpexp exp]
  in
  let realize_bool_mapcl forwards id mapcl =
    match mapcl with
    | MCL_aux (MCL_bidir (mpexp1, mpexp2), _) ->
        let mpexp = if forwards then mpexp1 else mpexp2 in
        [realize_mpexps true mpexp (mk_mpexp (MPat_pat (mk_mpat (MP_lit (mk_lit L_true)))))]
    | MCL_aux (MCL_forwards (mpexp, exp), _) ->
        if forwards then [realize_single_mpexp mpexp (mk_lit_exp L_true)] else []
    | MCL_aux (MCL_backwards (mpexp, exp), _) ->
        if forwards then [] else [realize_single_mpexp mpexp (mk_lit_exp L_true)]
  in
  let arg_id = mk_id "arg#" in
  let arg_exp = mk_exp (E_id arg_id) in
  let arg_pat = mk_pat (P_id arg_id) in
  let realize_val_spec def_annot = function
    | VS_aux
        ( VS_val_spec (TypSchm_aux (TypSchm_ts (typq, Typ_aux (Typ_bidir (typ1, typ2), l)), _), id, _),
          ((_, (tannot : tannot)) as annot)
        ) ->
        let forwards_id = mk_id (string_of_id id ^ "_forwards") in
        let forwards_matches_id = mk_id (string_of_id id ^ "_forwards_matches") in
        let backwards_id = mk_id (string_of_id id ^ "_backwards") in
        let backwards_matches_id = mk_id (string_of_id id ^ "_backwards_matches") in

        effect_info :=
          List.fold_left (Effects.copy_mapping_to_function id) !effect_info
            [forwards_id; forwards_matches_id; backwards_id; backwards_matches_id];

        let env = env_of_annot annot in
        let forwards_typ = Typ_aux (Typ_fn ([typ1], typ2), l) in
        let forwards_matches_typ = Typ_aux (Typ_fn ([typ1], bool_typ), l) in
        let backwards_typ = Typ_aux (Typ_fn ([typ2], typ1), l) in
        let backwards_matches_typ = Typ_aux (Typ_fn ([typ2], bool_typ), l) in

        let forwards_spec = VS_aux (VS_val_spec (mk_typschm typq forwards_typ, forwards_id, None), no_annot) in
        let backwards_spec = VS_aux (VS_val_spec (mk_typschm typq backwards_typ, backwards_id, None), no_annot) in
        let forwards_matches_spec =
          VS_aux (VS_val_spec (mk_typschm typq forwards_matches_typ, forwards_matches_id, None), no_annot)
        in
        let backwards_matches_spec =
          VS_aux (VS_val_spec (mk_typschm typq backwards_matches_typ, backwards_matches_id, None), no_annot)
        in

        let forwards_spec, env = Type_check.check_val_spec env def_annot forwards_spec in
        let backwards_spec, env = Type_check.check_val_spec env def_annot backwards_spec in
        let forwards_matches_spec, env = Type_check.check_val_spec env def_annot forwards_matches_spec in
        let backwards_matches_spec, env = Type_check.check_val_spec env def_annot backwards_matches_spec in

        let prefix_id = mk_id (string_of_id id ^ "_matches_prefix") in
        let string_defs =
          begin
            if subtype_check env typ1 string_typ && subtype_check env string_typ typ1 then begin
              effect_info := Effects.copy_mapping_to_function id !effect_info prefix_id;
              let forwards_prefix_typ =
                Typ_aux
                  ( Typ_fn
                      ([typ1], app_typ (mk_id "option") [A_aux (A_typ (tuple_typ [typ2; nat_typ]), Parse_ast.Unknown)]),
                    Parse_ast.Unknown
                  )
              in
              let forwards_prefix_spec =
                VS_aux (VS_val_spec (mk_typschm typq forwards_prefix_typ, prefix_id, None), no_annot)
              in
              let forwards_prefix_spec, env = Type_check.check_val_spec env def_annot forwards_prefix_spec in
              forwards_prefix_spec
            end
            else if subtype_check env typ2 string_typ && subtype_check env string_typ typ2 then begin
              effect_info := Effects.copy_mapping_to_function id !effect_info prefix_id;
              let backwards_prefix_typ =
                Typ_aux
                  ( Typ_fn
                      ([typ2], app_typ (mk_id "option") [A_aux (A_typ (tuple_typ [typ1; nat_typ]), Parse_ast.Unknown)]),
                    Parse_ast.Unknown
                  )
              in
              let backwards_prefix_spec =
                VS_aux (VS_val_spec (mk_typschm typq backwards_prefix_typ, prefix_id, None), no_annot)
              in
              let backwards_prefix_spec, env = Type_check.check_val_spec env def_annot backwards_prefix_spec in
              backwards_prefix_spec
            end
            else []
          end
        in

        forwards_spec @ backwards_spec @ forwards_matches_spec @ backwards_matches_spec @ string_defs
    | vs -> [DEF_aux (DEF_val vs, def_annot)]
  in
  let realize_mapdef def_annot (MD_aux (MD_mapping (id, _, mapcls), (l, (tannot : tannot)))) =
    let forwards_id = mk_id (string_of_id id ^ "_forwards") in
    let forwards_matches_id = mk_id (string_of_id id ^ "_forwards_matches") in
    let backwards_id = mk_id (string_of_id id ^ "_backwards") in
    let backwards_matches_id = mk_id (string_of_id id ^ "_backwards_matches") in

    effect_info :=
      List.fold_left (Effects.copy_mapping_to_function id) !effect_info
        [forwards_id; forwards_matches_id; backwards_id; backwards_matches_id];

    let non_rec = Rec_aux (Rec_nonrec, Parse_ast.Unknown) in
    (* We need to make sure we get the environment for the last mapping clause *)
    let env =
      match List.rev mapcls with
      | MCL_aux (_, (_, mapcl_tannot)) :: _ -> env_of_tannot mapcl_tannot
      | _ -> raise (Reporting.err_unreachable l __POS__ "mapping with no clauses?")
    in
    let typq, bidir_typ = Env.get_val_spec id env in
    let typ1, typ2, l =
      match bidir_typ with
      | Typ_aux (Typ_bidir (typ1, typ2), l) -> (typ1, typ2, l)
      | _ -> raise (Reporting.err_unreachable l __POS__ "non-bidir type of mapping?")
    in

    let no_tannot = Typ_annot_opt_aux (Typ_annot_opt_none, Parse_ast.Unknown) in
    let forwards_match =
      mk_exp
        (E_match
           (arg_exp, List.map (fun mapcl -> strip_mapcl mapcl |> realize_mapcl true forwards_id) mapcls |> List.flatten)
        )
    in
    let backwards_match =
      mk_exp
        (E_match
           ( arg_exp,
             List.map (fun mapcl -> strip_mapcl mapcl |> realize_mapcl false backwards_id) mapcls |> List.flatten
           )
        )
    in

    let wildcard = mk_pexp (Pat_exp (mk_pat P_wild, mk_exp (E_lit (mk_lit L_false)))) in
    let forwards_matches_match =
      mk_exp
        (E_match
           ( arg_exp,
             (List.map (fun mapcl -> strip_mapcl mapcl |> realize_bool_mapcl true forwards_matches_id) mapcls
             |> List.flatten
             )
             @ [wildcard]
           )
        )
    in
    let backwards_matches_match =
      mk_exp
        (E_match
           ( arg_exp,
             (List.map (fun mapcl -> strip_mapcl mapcl |> realize_bool_mapcl false backwards_matches_id) mapcls
             |> List.flatten
             )
             @ [wildcard]
           )
        )
    in

    let forwards_fun =
      FD_aux (FD_function (non_rec, no_tannot, [mk_funcl forwards_id arg_pat forwards_match]), (l, empty_uannot))
    in
    let backwards_fun =
      FD_aux (FD_function (non_rec, no_tannot, [mk_funcl backwards_id arg_pat backwards_match]), (l, empty_uannot))
    in
    let forwards_matches_fun =
      FD_aux
        ( FD_function (non_rec, no_tannot, [mk_funcl forwards_matches_id arg_pat forwards_matches_match]),
          (l, empty_uannot)
        )
    in
    let backwards_matches_fun =
      FD_aux
        ( FD_function (non_rec, no_tannot, [mk_funcl backwards_matches_id arg_pat backwards_matches_match]),
          (l, empty_uannot)
        )
    in

    let forwards_fun, _ = Type_check.check_fundef env def_annot forwards_fun in
    let backwards_fun, _ = Type_check.check_fundef env def_annot backwards_fun in
    let forwards_matches_fun, _ = Type_check.check_fundef env def_annot forwards_matches_fun in
    let backwards_matches_fun, _ = Type_check.check_fundef env def_annot backwards_matches_fun in

    let all_ids = ids_of_ast ast in
    let has_def id = IdSet.mem id all_ids in

    (if has_def forwards_id then [] else forwards_fun)
    @ (if has_def backwards_id then [] else backwards_fun)
    @ (if has_def forwards_matches_id then [] else forwards_matches_fun)
    @ if has_def backwards_matches_id then [] else backwards_matches_fun
  in
  let rewrite_def def =
    match def with
    | DEF_aux (DEF_val spec, def_annot) -> realize_val_spec def_annot spec
    | DEF_aux (DEF_mapdef mdef, def_annot) -> realize_mapdef def_annot mdef
    | DEF_aux (DEF_overload (id, overloads), def_annot) ->
        [
          DEF_aux
            ( DEF_overload
                ( id,
                  List.map
                    (fun overload ->
                      if Env.is_mapping overload env then (
                        let forwards_id = mk_id (string_of_id overload ^ "_forwards") in
                        let backwards_id = mk_id (string_of_id overload ^ "_backwards") in
                        [forwards_id; backwards_id]
                      )
                      else [overload]
                    )
                    overloads
                  |> List.concat
                ),
              def_annot
            );
        ]
    | d -> [d]
  in
  let ast = { ast with defs = List.map rewrite_def ast.defs |> List.flatten } in
  (ast, !effect_info, env)

(* Rewrite to make all pattern matches in Coq output exhaustive and
   remove redundant clauses.  Assumes that guards, vector patterns,
   etc have been rewritten already, and the scattered functions have
   been merged.  It also reruns effect inference if a pattern match
   failure has to be added.

   Note: if this naive implementation turns out to be too slow or buggy, we
   could look at implementing Maranget JFP 17(3), 2007.
*)

let opt_coq_warn_nonexhaustive = ref false

module MakeExhaustive = struct
  type rlit = RL_unit | RL_true | RL_false | RL_inf

  let string_of_rlit = function RL_unit -> "()" | RL_true -> "true" | RL_false -> "false" | RL_inf -> "..."

  let rlit_of_lit (L_aux (l, _)) =
    match l with
    | L_unit -> RL_unit
    | L_zero -> RL_inf
    | L_one -> RL_inf
    | L_true -> RL_true
    | L_false -> RL_false
    | L_num _ | L_hex _ | L_bin _ | L_string _ | L_real _ -> RL_inf
    | L_undef -> assert false

  let inv_rlit_of_lit (L_aux (l, _)) =
    match l with
    | L_unit -> []
    | L_zero -> [RL_inf]
    | L_one -> [RL_inf]
    | L_true -> [RL_false]
    | L_false -> [RL_true]
    | L_num _ | L_hex _ | L_bin _ | L_string _ | L_real _ -> [RL_inf]
    | L_undef -> assert false

  type residual_pattern =
    | RP_any
    | RP_lit of rlit
    | RP_enum of id
    | RP_app of id * residual_pattern list
    | RP_tuple of residual_pattern list
    | RP_nil
    | RP_cons of residual_pattern * residual_pattern
    | RP_struct of (id * residual_pattern) list

  let rec string_of_rp = function
    | RP_any -> "_"
    | RP_lit rlit -> string_of_rlit rlit
    | RP_enum id -> string_of_id id
    | RP_app (f, args) -> string_of_id f ^ "(" ^ String.concat "," (List.map string_of_rp args) ^ ")"
    | RP_tuple rps -> "(" ^ String.concat "," (List.map string_of_rp rps) ^ ")"
    | RP_nil -> "[| |]"
    | RP_cons (rp1, rp2) -> string_of_rp rp1 ^ "::" ^ string_of_rp rp2
    | RP_struct frps ->
        "struct { "
        ^ Util.string_of_list ", " (fun (field, rp) -> string_of_id field ^ " = " ^ string_of_rp rp) frps
        ^ " }"

  type ctx = {
    env : Env.t;
    enum_to_rest : residual_pattern list Bindings.t;
    constructor_to_rest : residual_pattern list Bindings.t;
  }

  let make_enum_mappings ids m =
    IdSet.fold
      (fun id m -> Bindings.add id (List.map (fun e -> RP_enum e) (IdSet.elements (IdSet.remove id ids))) m)
      ids m

  let make_cstr_mappings env ids m =
    let ids = IdSet.elements ids in
    let constructors =
      List.map
        (fun id ->
          let _, ty = Env.get_val_spec id env in
          let args = match ty with Typ_aux (Typ_fn (tys, _), _) -> List.map (fun _ -> RP_any) tys | _ -> [RP_any] in
          RP_app (id, args)
        )
        ids
    in
    let rec aux ids acc l =
      match (ids, l) with
      | [], [] -> m
      | id :: ids, rp :: t ->
          (* We don't need to keep the ordering inside acc *)
          let m = aux ids (rp :: acc) t in
          Bindings.add id (acc @ t) m
      | _ -> assert false
    in
    aux ids [] constructors

  let ctx_from_env env =
    {
      env;
      enum_to_rest = Bindings.fold (fun _ ids m -> make_enum_mappings ids m) (Env.get_enums env) Bindings.empty;
      constructor_to_rest =
        Bindings.fold
          (fun _ ids m -> make_cstr_mappings env ids m)
          (Bindings.map (fun (_, tus) -> IdSet.of_list (List.map type_union_id tus)) (Env.get_variants env))
          Bindings.empty;
    }

  let rec remove_clause_from_pattern ctx (P_aux (rm_pat, ann)) res_pat =
    (* Remove the tuple rm_pats from the tuple of res_pats *)
    let subpats rm_pats res_pats =
      (* Pointwise removal *)
      let res_pats' = List.map2 (remove_clause_from_pattern ctx) rm_pats res_pats in
      let progress = List.exists snd res_pats' in
      (* Form the list of residual tuples by combining one position from the
         pointwise removal with the original residual of the other positions. *)
      let rec aux acc fixed residual =
        match (fixed, residual) with
        | [], [] -> []
        | fh :: ft, (rh, _) :: rt ->
            (* ... so order matters here *)
            let rt' = aux (acc @ [fh]) ft rt in
            let newr = List.map (fun x -> acc @ (x :: ft)) rh in
            newr @ rt'
        | _, _ -> assert false (* impossible because we managed map2 above *)
      in
      (aux [] res_pats res_pats', progress)
    in
    let inconsistent () =
      raise
        (Reporting.err_unreachable (fst ann) __POS__
           ("Inconsistency during exhaustiveness analysis with " ^ string_of_rp res_pat)
        )
    in
    (*let _ = print_endline (!printprefix ^ "pat: " ^string_of_pat (P_aux (rm_pat,ann))) in
      let _ = print_endline (!printprefix ^ "res_pat: " ^string_of_rp res_pat) in
      let _ = printprefix := "  " ^ !printprefix in*)
    let rp' =
      match rm_pat with
      | P_wild -> ([], true)
      | P_id id when match Env.lookup_id id ctx.env with Unbound _ | Local _ -> true | _ -> false -> ([], true)
      | P_lit lit -> (
          match res_pat with
          | RP_any -> (List.map (fun l -> RP_lit l) (inv_rlit_of_lit lit), true)
          | RP_lit RL_inf -> ([res_pat], true (* TODO: check for duplicates *))
          | RP_lit lit' -> if lit' = rlit_of_lit lit then ([], true) else ([res_pat], false)
          | _ -> inconsistent ()
        )
      | P_as (p, _) | P_typ (_, p) | P_var (p, _) -> remove_clause_from_pattern ctx p res_pat
      | P_id id -> (
          match Env.lookup_id id ctx.env with
          | Enum enum -> (
              match res_pat with
              | RP_any -> (Bindings.find id ctx.enum_to_rest, true)
              | RP_enum id' -> if Id.compare id id' == 0 then ([], true) else ([res_pat], false)
              | _ -> inconsistent ()
            )
          | _ -> assert false
        )
      | P_tuple rm_pats ->
          if Util.list_empty rm_pats then ([], true)
          else (
            let previous_res_pats =
              match res_pat with
              | RP_tuple res_pats -> res_pats
              | RP_any -> List.map (fun _ -> RP_any) rm_pats
              | _ -> inconsistent ()
            in
            let res_pats', progress = subpats rm_pats previous_res_pats in
            (List.map (fun rps -> RP_tuple rps) res_pats', progress)
          )
      | P_app (id, args) -> (
          match res_pat with
          | RP_app (id', residual_args) ->
              if Id.compare id id' == 0 then (
                let res_pats', progress =
                  (* Constructors that were specified without a return type might get
                     an extra tuple in their type; expand that here if necessary.
                     TODO: this should go away if we enforce proper arities. *)
                  match (args, residual_args) with
                  | [], [RP_any] | _ :: _ :: _, [RP_any] -> subpats args (List.map (fun _ -> RP_any) args)
                  | _, _ -> subpats args residual_args
                in
                (List.map (fun rps -> RP_app (id, rps)) res_pats', progress)
              )
              else ([res_pat], false)
          | RP_any ->
              let res_args, progress = subpats args (List.map (fun _ -> RP_any) args) in
              (List.map (fun l -> RP_app (id, l)) res_args @ Bindings.find id ctx.constructor_to_rest, progress)
          | _ -> inconsistent ()
        )
      | P_struct (field_pats, _) ->
          let all_ids, res_pats =
            match res_pat with
            | RP_struct res_fields ->
                let all_ids = List.map fst res_fields in
                let res_pats = List.map snd res_fields in
                (all_ids, res_pats)
            | RP_any ->
                let record_id =
                  match Env.expand_synonyms ctx.env (typ_of_annot ann) with
                  | Typ_aux (Typ_id id, _) | Typ_aux (Typ_app (id, _), _) -> id
                  | _ -> Reporting.unreachable (fst ann) __POS__ "Record is not a record"
                in
                let _, fields = Env.get_record record_id ctx.env in
                (List.map snd fields, List.map (fun _ -> RP_any) fields)
            | _ -> inconsistent ()
          in
          let cur_pats =
            List.map
              (fun id ->
                List.find_opt (fun (x, _) -> Id.compare id x == 0) field_pats
                |> Option.map snd
                |> Option.value ~default:(P_aux (P_wild, (Unknown, empty_tannot)))
              )
              all_ids
          in
          let res_pats', progress = subpats cur_pats res_pats in
          (List.map (fun rps -> RP_struct (List.combine all_ids rps)) res_pats', progress)
      | P_list ps -> (
          match ps with
          | p1 :: ptl -> remove_clause_from_pattern ctx (P_aux (P_cons (p1, P_aux (P_list ptl, ann)), ann)) res_pat
          | [] -> (
              match res_pat with
              | RP_any -> ([RP_cons (RP_any, RP_any)], true)
              | RP_cons _ -> ([res_pat], false)
              | RP_nil -> ([], true)
              | _ -> inconsistent ()
            )
        )
      | P_cons (p1, p2) -> begin
          let rp', rps =
            match res_pat with
            | RP_cons (rp1, rp2) -> ([], Some [rp1; rp2])
            | RP_any -> ([RP_nil], Some [RP_any; RP_any])
            | RP_nil -> ([RP_nil], None)
            | _ -> inconsistent ()
          in
          match rps with
          | None -> (rp', false)
          | Some rps ->
              let res_pats, progress = subpats [p1; p2] rps in
              (rp' @ List.map (function [rp1; rp2] -> RP_cons (rp1, rp2) | _ -> assert false) res_pats, progress)
        end
      | P_or _ -> raise (Reporting.err_unreachable (fst ann) __POS__ "Or pattern not supported")
      | P_not _ -> raise (Reporting.err_unreachable (fst ann) __POS__ "Negated pattern not supported")
      | P_vector _ | P_vector_concat _ | P_vector_subrange _ | P_string_append _ ->
          raise
            (Reporting.err_unreachable (fst ann) __POS__
               "Found pattern that should have been rewritten away in earlier stage"
            )
      (*in let _ = printprefix := String.sub (!printprefix) 0 (String.length !printprefix - 2)
        in let _ = print_endline (!printprefix ^ "res_pats': " ^ String.concat "; " (List.map string_of_rp rp'))*)
    in

    rp'

  let process_pexp env =
    let ctx = ctx_from_env env in
    fun rps patexp ->
      (*let _ = print_endline ("res_pats: " ^ String.concat "; " (List.map string_of_rp rps)) in
        let _ = print_endline ("pat: " ^ string_of_pexp patexp) in*)
      match patexp with
      | Pat_aux (Pat_exp (p, _), _) ->
          let rps, progress = List.split (List.map (remove_clause_from_pattern ctx p) rps) in
          (List.concat rps, List.exists (fun b -> b) progress)
      | Pat_aux (Pat_when _, (l, _)) ->
          raise (Reporting.err_unreachable l __POS__ "Guarded pattern should have been rewritten away")

  let check_cases process is_wild loc_of cases =
    let rec aux rps acc = function
      | [] -> (acc, rps)
      | [p] when is_wild p && match rps with [] -> true | _ -> false ->
          let () = Reporting.print_err (loc_of p) "Match checking" "Redundant wildcard clause" in
          (acc, [])
      | h :: t ->
          let rps', progress = process rps h in
          if progress then aux rps' (h :: acc) t
          else begin
            Reporting.print_err (loc_of h) "Match checking" "Redundant clause";
            aux rps' acc t
          end
    in
    let cases, rps = aux [RP_any] [] cases in
    (List.rev cases, rps)

  let not_enum env id = match Env.lookup_id id env with Enum _ -> false | _ -> true

  let pexp_is_wild = function
    | Pat_aux (Pat_exp (P_aux (P_wild, _), _), _) -> true
    | Pat_aux (Pat_exp (P_aux (P_id id, ann), _), _) when not_enum (env_of_annot ann) id -> true
    | _ -> false

  let pexp_loc = function
    | Pat_aux (Pat_exp (P_aux (_, (l, _)), _), _) -> l
    | Pat_aux (Pat_when (P_aux (_, (l, _)), _, _), _) -> l

  let funcl_is_wild = function FCL_aux (FCL_funcl (_, pexp), _) -> pexp_is_wild pexp

  let funcl_loc (FCL_aux (_, (def_annot, _))) = def_annot.loc

  let rewrite_case redo_effects (e, ann) =
    match e with
    | E_match (e1, cases) | E_try (e1, cases) -> begin
        let env = env_of_annot ann in
        let cases, rps = check_cases (process_pexp env) pexp_is_wild pexp_loc cases in
        let rebuild cases =
          match e with E_match _ -> E_match (e1, cases) | E_try _ -> E_try (e1, cases) | _ -> assert false
        in
        match rps with
        | [] -> E_aux (rebuild cases, ann)
        | example :: _ ->
            let _ =
              if !opt_coq_warn_nonexhaustive then
                Reporting.print_err (fst ann) "Non-exhaustive matching" ("Example: " ^ string_of_rp example)
            in

            let l = Parse_ast.Generated Parse_ast.Unknown in
            let p = P_aux (P_wild, (l, empty_tannot)) in
            let l_ann = mk_tannot env unit_typ in
            let ann' = mk_tannot env (typ_of_annot ann) in
            (* TODO: use an expression that specifically indicates a failed pattern match *)
            let b = E_aux (E_exit (E_aux (E_lit (L_aux (L_unit, l)), (l, l_ann))), (l, ann')) in
            redo_effects := true;
            E_aux (rebuild (cases @ [Pat_aux (Pat_exp (p, b), (l, empty_tannot))]), ann)
      end
    | E_let (LB_aux (LB_val (pat, e1), lb_ann), e2) -> begin
        let env = env_of_annot ann in
        let ctx = ctx_from_env env in
        let rps, _ = remove_clause_from_pattern ctx pat RP_any in
        match rps with
        | [] -> E_aux (e, ann)
        | example :: _ ->
            let _ =
              if !opt_coq_warn_nonexhaustive then
                Reporting.print_err (fst ann) "Non-exhaustive let" ("Example: " ^ string_of_rp example)
            in
            let l = Parse_ast.Generated Parse_ast.Unknown in
            let p = P_aux (P_wild, (l, empty_tannot)) in
            let l_ann = mk_tannot env unit_typ in
            let ann' = mk_tannot env (typ_of_annot ann) in
            (* TODO: use an expression that specifically indicates a failed pattern match *)
            let b = E_aux (E_exit (E_aux (E_lit (L_aux (L_unit, l)), (l, l_ann))), (l, ann')) in
            redo_effects := true;
            E_aux (E_match (e1, [Pat_aux (Pat_exp (pat, e2), ann); Pat_aux (Pat_exp (p, b), (l, empty_tannot))]), ann)
      end
    | _ -> E_aux (e, ann)

  let rewrite_fun rewriters (FD_aux (FD_function (r, t, fcls), f_ann)) =
    let id, fcl_ann =
      match fcls with
      | FCL_aux (FCL_funcl (id, _), ann) :: _ -> (id, ann)
      | [] -> raise (Reporting.err_unreachable (fst f_ann) __POS__ "Empty function")
    in
    let env = env_of_tannot (snd fcl_ann) in
    let process_funcl rps (FCL_aux (FCL_funcl (_, pexp), _)) = process_pexp env rps pexp in
    let fcls, rps = check_cases process_funcl funcl_is_wild funcl_loc fcls in
    let fcls' =
      List.map
        (function FCL_aux (FCL_funcl (id, pexp), ann) -> FCL_aux (FCL_funcl (id, rewrite_pexp rewriters pexp), ann))
        fcls
    in
    match rps with
    | [] -> FD_aux (FD_function (r, t, fcls'), f_ann)
    | example :: _ ->
        let _ =
          if !opt_coq_warn_nonexhaustive then
            Reporting.print_err (fst f_ann) "Non-exhaustive matching" ("Example: " ^ string_of_rp example)
        in

        let l = Parse_ast.Generated Parse_ast.Unknown in
        let p = P_aux (P_wild, (l, empty_tannot)) in
        let ann' = mk_tannot env (typ_of_tannot (snd fcl_ann)) in
        (* TODO: use an expression that specifically indicates a failed pattern match *)
        let b = E_aux (E_exit (E_aux (E_lit (L_aux (L_unit, l)), (l, empty_tannot))), (l, ann')) in
        let default = FCL_aux (FCL_funcl (id, Pat_aux (Pat_exp (p, b), (l, empty_tannot))), fcl_ann) in

        FD_aux (FD_function (r, t, fcls' @ [default]), f_ann)

  let rewrite effect_info env ast =
    let redo_effects = ref false in
    let alg = { id_exp_alg with e_aux = rewrite_case redo_effects } in
    let ast' =
      rewrite_ast_base
        {
          rewrite_exp = (fun _ -> fold_exp alg);
          rewrite_pat;
          rewrite_let;
          rewrite_lexp;
          rewrite_fun;
          rewrite_def;
          rewrite_ast = rewrite_ast_base_progress "Make patterns exhaustive";
        }
        ast
    in
    let effect_info' =
      (* TODO: if we use this for anything other than Coq we'll need
         to replace "true" with Target.asserts_termination target,
         after plumbing target through to this rewrite. *)
      if !redo_effects then Effects.infer_side_effects true ast' else effect_info
    in
    (ast', effect_info', env)
end

(* Splitting a function (e.g., an execute function on an AST) can produce
   new functions that appear to be recursive but are not.  This checks to
   see if the flag can be turned off.  Doesn't handle mutual recursion
   for now. *)
let minimise_recursive_functions env ast =
  let rewrite_function (FD_aux (FD_function (recopt, topt, funcls), ann) as fd) =
    match recopt with
    | Rec_aux (Rec_nonrec, _) -> fd
    | Rec_aux ((Rec_rec | Rec_measure _), l) ->
        if List.exists is_funcl_rec funcls then fd
        else FD_aux (FD_function (Rec_aux (Rec_nonrec, Generated l), topt, funcls), ann)
  in
  let rewrite_def = function
    | DEF_aux (DEF_fundef fd, def_annot) -> DEF_aux (DEF_fundef (rewrite_function fd), def_annot)
    | d -> d
  in
  { ast with defs = List.map rewrite_def ast.defs }

(* Move recursive function termination measures into the function definitions. *)
let move_termination_measures env ast =
  let measures =
    List.fold_left
      (fun m def ->
        match def with
        | DEF_aux (DEF_measure (id, pat, exp), ann) ->
            if Bindings.mem id m then
              raise (Reporting.err_general ann.loc ("Second termination measure given for " ^ string_of_id id))
            else Bindings.add id (pat, exp) m
        | _ -> m
      )
      Bindings.empty ast.defs
  in
  let rec aux acc = function
    | [] -> List.rev acc
    | (DEF_aux (DEF_fundef (FD_aux (FD_function (r, ty, fs), (l, f_ann))), def_annot) as d) :: t -> begin
        let id = match fs with [] -> assert false (* TODO *) | FCL_aux (FCL_funcl (id, _), _) :: _ -> id in
        match Bindings.find_opt id measures with
        | None -> aux (d :: acc) t
        | Some (pat, exp) ->
            let r = Rec_aux (Rec_measure (pat, exp), Generated l) in
            aux (DEF_aux (DEF_fundef (FD_aux (FD_function (r, ty, fs), (l, f_ann))), def_annot) :: acc) t
      end
    | DEF_aux (DEF_measure _, _) :: t -> aux acc t
    | h :: t -> aux (h :: acc) t
  in
  { ast with defs = aux [] ast.defs }

(* Make recursive functions with a measure use the measure as an
   explicit recursion limit, enforced by an assertion. *)
let rewrite_explicit_measure effect_info env ast =
  let effect_info = ref effect_info in
  let scan_function measures = function
    | FD_aux (FD_function (Rec_aux (Rec_measure (mpat, mexp), rl), topt, FCL_aux (FCL_funcl (id, _), _) :: _), ann) ->
        Bindings.add id (mpat, mexp) measures
    | _ -> measures
  in
  let scan_def measures = function
    | DEF_aux (DEF_fundef fd, _) -> scan_function measures fd
    | DEF_aux (DEF_internal_mutrec fds, _) -> List.fold_left scan_function measures fds
    | _ -> measures
  in
  let measures = List.fold_left scan_def Bindings.empty ast.defs in
  (* NB: the Coq backend relies on recognising the #rec# prefix *)
  let rec_id = function Id_aux (Id id, l) | Id_aux (Operator id, l) -> Id_aux (Id ("#rec#" ^ id), Generated l) in
  let limit = mk_id "#reclimit" in
  (* Add helper function with extra argument to spec *)
  let rewrite_spec (VS_aux (VS_val_spec (typsch, id, extern), ann) as vs) =
    match Bindings.find id measures with
    | _ -> begin
        match typsch with
        | TypSchm_aux (TypSchm_ts (tq, Typ_aux (Typ_fn (args, res), typl)), tsl) ->
            [
              VS_aux
                ( VS_val_spec
                    ( TypSchm_aux (TypSchm_ts (tq, Typ_aux (Typ_fn (args @ [int_typ], res), typl)), tsl),
                      rec_id id,
                      extern
                    ),
                  ann
                );
              VS_aux
                (VS_val_spec (TypSchm_aux (TypSchm_ts (tq, Typ_aux (Typ_fn (args, res), typl)), tsl), id, extern), ann);
            ]
        | _ -> [vs]
        (* TODO warn *)
      end
    | exception Not_found -> [vs]
  in
  (* Add extra argument and assertion to each funcl, and rewrite recursive calls *)
  let rewrite_funcl recset (FCL_aux (FCL_funcl (id, pexp), fcl_ann)) =
    let loc = Parse_ast.Generated (fst fcl_ann).loc in
    let P_aux (pat, pann), guard, body, ann = destruct_pexp pexp in
    let extra_pat = P_aux (P_id limit, (loc, empty_tannot)) in
    let pat =
      match pat with P_tuple pats -> P_tuple (pats @ [extra_pat]) | p -> P_tuple [P_aux (p, pann); extra_pat]
    in
    let assert_exp =
      E_aux
        ( E_assert
            ( E_aux
                ( E_app
                    ( mk_id "gteq_int",
                      [
                        E_aux (E_id limit, (loc, empty_tannot));
                        E_aux (E_lit (L_aux (L_num Big_int.zero, loc)), (loc, empty_tannot));
                      ]
                    ),
                  (loc, empty_tannot)
                ),
              E_aux (E_lit (L_aux (L_string "recursion limit reached", loc)), (loc, empty_tannot))
            ),
          (loc, empty_tannot)
        )
    in
    let tick =
      E_aux
        ( E_app
            ( mk_id "sub_int",
              [
                E_aux (E_id limit, (loc, empty_tannot));
                E_aux (E_lit (L_aux (L_num (Big_int.of_int 1), loc)), (loc, empty_tannot));
              ]
            ),
          (loc, empty_tannot)
        )
    in
    let open Rewriter in
    let body =
      fold_exp
        {
          id_exp_alg with
          e_app = (fun (f, args) -> if IdSet.mem f recset then E_app (rec_id f, args @ [tick]) else E_app (f, args));
        }
        body
    in
    let body = E_aux (E_block [assert_exp; body], (loc, empty_tannot)) in
    let new_id = rec_id id in
    effect_info := Effects.copy_function_effect id !effect_info new_id;
    FCL_aux (FCL_funcl (new_id, construct_pexp (P_aux (pat, pann), guard, body, ann)), fcl_ann)
  in
  let rewrite_function recset (FD_aux (FD_function (r, t, fcls), ann) as fd) =
    let loc = Parse_ast.Generated (fst ann) in
    match fcls with
    | FCL_aux (FCL_funcl (id, _), fcl_ann) :: _ -> begin
        match Bindings.find id measures with
        | measure_pat, measure_exp ->
            let arg_typs =
              match Env.get_val_spec id (env_of_tannot (snd fcl_ann)) with
              | _, Typ_aux (Typ_fn (args, _), _) -> args
              | _, _ -> raise (Reporting.err_unreachable (fst ann) __POS__ "Function doesn't have function type")
            in
            let measure_pats =
              match (arg_typs, measure_pat) with
              | [_], _ -> [measure_pat]
              | _, P_aux (P_tuple ps, _) -> ps
              | _, _ -> [measure_pat]
            in
            let mk_wrap i (P_aux (p, (l, _)) as p_full) =
              let id =
                match p with
                | P_id id | P_typ (_, P_aux (P_id id, _)) -> id
                | P_lit _ | P_wild | P_typ (_, P_aux (P_wild, _)) -> mk_id ("_arg" ^ string_of_int i)
                | _ ->
                    raise
                      (Reporting.err_todo l
                         ("Measure patterns can only be identifiers or wildcards, not " ^ string_of_pat p_full)
                      )
              in
              (P_aux (P_id id, (loc, empty_tannot)), E_aux (E_id id, (loc, empty_tannot)))
            in
            let wpats, wexps = List.split (List.mapi mk_wrap measure_pats) in
            let wpat = match wpats with [wpat] -> wpat | _ -> P_aux (P_tuple wpats, (loc, empty_tannot)) in
            let measure_exp = E_aux (E_typ (int_typ, measure_exp), (loc, empty_tannot)) in
            let wbody = E_aux (E_app (rec_id id, wexps @ [measure_exp]), (loc, empty_tannot)) in
            let wrapper =
              FCL_aux
                (FCL_funcl (id, Pat_aux (Pat_exp (wpat, wbody), (loc, empty_tannot))), (mk_def_annot loc, empty_tannot))
            in
            let new_rec =
              Rec_aux
                ( Rec_measure
                    ( P_aux
                        ( P_tuple
                            (List.map (fun _ -> P_aux (P_wild, (loc, empty_tannot))) measure_pats
                            @ [P_aux (P_id limit, (loc, empty_tannot))]
                            ),
                          (loc, empty_tannot)
                        ),
                      E_aux (E_id limit, (loc, empty_tannot))
                    ),
                  loc
                )
            in
            ( FD_aux (FD_function (new_rec, t, List.map (rewrite_funcl recset) fcls), ann),
              [FD_aux (FD_function (Rec_aux (Rec_nonrec, loc), t, [wrapper]), ann)]
            )
        | exception Not_found -> (fd, [])
      end
    | _ -> (fd, [])
  in
  let rewrite_def = function
    | DEF_aux (DEF_val vs, def_annot) -> List.map (fun vs -> DEF_aux (DEF_val vs, def_annot)) (rewrite_spec vs)
    | DEF_aux (DEF_fundef fd, def_annot) ->
        let fd, extra = rewrite_function (IdSet.singleton (id_of_fundef fd)) fd in
        List.map (fun f -> DEF_aux (DEF_fundef f, def_annot)) (fd :: extra)
    | DEF_aux (DEF_internal_mutrec fds, def_annot) as d ->
        let recset = ids_of_def d in
        let fds, extras = List.split (List.map (rewrite_function recset) fds) in
        let extras = List.concat extras in
        DEF_aux (DEF_internal_mutrec fds, def_annot) :: List.map (fun f -> DEF_aux (DEF_fundef f, def_annot)) extras
    | d -> [d]
  in
  let defs = List.flatten (List.map rewrite_def ast.defs) in
  ({ ast with defs }, !effect_info, env)

(* Add a dummy assert to loops for backends that require loops to be able to
   fail.  Note that the Coq backend will spot the assert and omit it. *)
let rewrite_loops_with_escape_effect env defs =
  let dummy_ann = (Parse_ast.Unknown, empty_tannot) in
  let assert_exp =
    E_aux
      ( E_assert
          ( E_aux (E_lit (L_aux (L_true, Unknown)), dummy_ann),
            E_aux (E_lit (L_aux (L_string "loop dummy assert", Unknown)), dummy_ann)
          ),
        dummy_ann
      )
  in
  let rewrite_exp rws exp =
    let (E_aux (e, ann) as exp) = Rewriter.rewrite_exp rws exp in
    match e with
    | E_loop (l, (Measure_aux (Measure_some _, _) as m), guard, body) ->
        (* TODO EFFECT *)
        if (* has_effect (effect_of exp) BE_escape *) false then exp
        else (
          let body =
            match body with
            | E_aux (E_block es, ann) -> E_aux (E_block (assert_exp :: es), ann)
            | _ -> E_aux (E_block [assert_exp; body], dummy_ann)
          in
          E_aux (E_loop (l, m, guard, body), ann)
        )
    | _ -> exp
  in
  rewrite_ast_base { rewriters_base with rewrite_exp } defs

(* In realize_mappings we may have duplicated a user-supplied val spec, which
   causes problems for some targets. Keep the first one, except use the externs
   from the last one, as subsequent redefinitions override earlier ones.

   AA Note: this rewrite is extremely suspect. FIXME - remove it *)
let remove_duplicate_valspecs env ast =
  let last_externs =
    List.fold_left
      (fun last_externs def ->
        match def with
        | DEF_aux (DEF_val (VS_aux (VS_val_spec (_, id, externs), _)), _) -> Bindings.add id externs last_externs
        | _ -> last_externs
      )
      Bindings.empty ast.defs
  in
  let _, rev_defs =
    List.fold_left
      (fun (set, defs) def ->
        match def with
        | DEF_aux (DEF_val (VS_aux (VS_val_spec (typschm, id, _), l)), def_annot) ->
            if IdSet.mem id set then (set, defs)
            else (
              let externs = Bindings.find id last_externs in
              let vs = VS_aux (VS_val_spec (typschm, id, externs), l) in
              (IdSet.add id set, DEF_aux (DEF_val vs, def_annot) :: defs)
            )
        | _ -> (set, def :: defs)
      )
      (IdSet.empty, []) ast.defs
  in
  { ast with defs = List.rev rev_defs }

(* Move loop termination measures into loop AST nodes.  This is used before
   type checking so that we avoid the complexity of type checking separate
   measures. *)
let move_loop_measures ast =
  let loop_measures =
    List.fold_left
      (fun m d ->
        match d with
        | DEF_aux (DEF_loop_measures (id, measures), _) ->
            (* Allow multiple measure definitions, concatenating them *)
            Bindings.add id (match Bindings.find_opt id m with None -> measures | Some m -> m @ measures) m
        | _ -> m
      )
      Bindings.empty ast.defs
  in
  let do_exp exp_rec measures (E_aux (e, ann) as exp) =
    match (e, measures) with
    | E_loop (loop, _, e1, e2), Loop (loop', exp) :: t when loop = loop' ->
        let t, e1 = exp_rec t e1 in
        let t, e2 = exp_rec t e2 in
        (t, E_aux (E_loop (loop, Measure_aux (Measure_some exp, exp_loc exp), e1, e2), ann))
    | _ -> exp_rec measures exp
  in
  let do_funcl (m, acc) (FCL_aux (FCL_funcl (id, pexp), ann) as fcl) =
    match Bindings.find_opt id m with
    | Some measures ->
        let measures, pexp = foldin_pexp do_exp measures pexp in
        (Bindings.add id measures m, FCL_aux (FCL_funcl (id, pexp), ann) :: acc)
    | None -> (m, fcl :: acc)
  in
  let unused, rev_defs =
    List.fold_left
      (fun (m, acc) d ->
        match d with
        | DEF_aux (DEF_loop_measures _, _) -> (m, acc)
        | DEF_aux (DEF_fundef (FD_aux (FD_function (r, t, fcls), ann)), def_annot) ->
            let m, rfcls = List.fold_left do_funcl (m, []) fcls in
            (m, DEF_aux (DEF_fundef (FD_aux (FD_function (r, t, List.rev rfcls), ann)), def_annot) :: acc)
        | _ -> (m, d :: acc)
      )
      (loop_measures, []) ast.defs
  in
  let () =
    Bindings.iter
      (fun id -> function
        | [] -> ()
        | _ :: _ -> Reporting.print_err (id_loc id) "Warning" ("unused loop measure for function " ^ string_of_id id)
      )
      unused
  in
  { ast with defs = List.rev rev_defs }

let rewrite_toplevel_consts target type_env ast =
  let istate = Constant_fold.initial_state ast type_env in
  let subst consts exp =
    let open Rewriter in
    let used_ids = fold_exp { (pure_exp_alg IdSet.empty IdSet.union) with e_id = IdSet.singleton } exp in
    let subst_ids = IdSet.filter (fun id -> Bindings.mem id consts) used_ids in
    IdSet.fold (fun id -> subst id (Bindings.find id consts)) subst_ids exp
  in
  let rewrite_def (revdefs, consts) = function
    | DEF_aux (DEF_let (LB_aux (LB_val (pat, exp), a) as lb), def_annot) -> begin
        match unaux_pat pat with
        | P_id id | P_typ (_, P_aux (P_id id, _)) ->
            let exp' = Constant_fold.rewrite_exp_once target istate (subst consts exp) in
            if Constant_fold.is_constant exp' then (
              try
                let exp' = infer_exp (env_of exp') (strip_exp exp') in
                let pannot = (pat_loc pat, mk_tannot (env_of_pat pat) (typ_of exp')) in
                let pat' = P_aux (P_typ (typ_of exp', P_aux (P_id id, pannot)), pannot) in
                let consts' = Bindings.add id exp' consts in
                (DEF_aux (DEF_let (LB_aux (LB_val (pat', exp'), a)), def_annot) :: revdefs, consts')
              with _ -> (DEF_aux (DEF_let lb, def_annot) :: revdefs, consts)
            )
            else (DEF_aux (DEF_let lb, def_annot) :: revdefs, consts)
        | _ -> (DEF_aux (DEF_let lb, def_annot) :: revdefs, consts)
      end
    | def -> (def :: revdefs, consts)
  in
  let revdefs, _ = List.fold_left rewrite_def ([], Bindings.empty) ast.defs in
  { ast with defs = List.rev revdefs }

(* Hex literals are always a multiple of 4 bits long.  If one of a different size is needed, users may truncate
   them down.  This can be bad for isla because the original may be too long for the concrete bitvector
   representation (e.g., 132 bits when at most 129 long bitvectors are supported), so cut them down now. *)
let rewrite_truncate_hex_literals _type_env defs =
  let rewrite_aux (e, annot) =
    match e with
    | E_app
        ( Id_aux (Id "truncate", _),
          [E_aux (E_lit (L_aux (L_hex hex, l_ann)), _); E_aux (E_lit (L_aux (L_num len, _)), _)]
        ) ->
        let bin = hex_to_bin hex in
        let len = Nat_big_num.to_int len in
        let truncation = String.sub bin (String.length bin - len) len in
        E_aux (E_lit (L_aux (L_bin truncation, l_ann)), annot)
    | _ -> E_aux (e, annot)
  in
  rewrite_ast_base
    { rewriters_base with rewrite_exp = (fun _ -> fold_exp { id_exp_alg with e_aux = rewrite_aux }) }
    defs

(* Coq's Definition command doesn't allow patterns, so rewrite
   top-level let bindings with complex patterns into a sequence of
   single definitions. *)
let rewrite_toplevel_let_patterns env ast =
  let is_pat_simple = function
    | P_aux (P_typ (_, P_aux (P_id _id, _)), _) | P_aux (P_id _id, _) -> true
    | P_aux (P_var (P_aux (P_id id, _), TP_aux (TP_var kid, _)), _)
    | P_aux (P_typ (_, P_aux (P_var (P_aux (P_id id, _), TP_aux (TP_var kid, _)), _)), _) ->
        Id.compare id (id_of_kid kid) == 0
    | P_aux (P_var (P_aux (P_id id, _), TP_aux (TP_app (app_id, [TP_aux (TP_var kid, _)]), _)), _)
    | P_aux (P_typ (_, P_aux (P_var (P_aux (P_id id, _), TP_aux (TP_app (app_id, [TP_aux (TP_var kid, _)]), _)), _)), _)
      when Id.compare app_id (mk_id "atom") == 0 ->
        Id.compare id (id_of_kid kid) == 0
    | _ -> false
  in
  let rewrite_def = function
    | DEF_aux (DEF_let (LB_aux (LB_val (pat, exp), (l, annot))), def_annot) as def ->
        if is_pat_simple pat then [def]
        else (
          let ids = pat_ids pat in
          let base_id = fresh_id "let" l in
          let base_annot = mk_tannot env (typ_of exp) in
          let base_def =
            mk_def (DEF_let (LB_aux (LB_val (P_aux (P_id base_id, (l, base_annot)), exp), (l, empty_tannot))))
          in
          let id_defs =
            List.map
              (fun id ->
                let id_typ = match Env.lookup_id id env with Local (_, t) -> t | _ -> assert false in
                let id_annot = (Parse_ast.Unknown, mk_tannot env id_typ) in
                let def_body =
                  E_aux
                    ( E_let
                        ( LB_aux (LB_val (pat, E_aux (E_id base_id, (l, base_annot))), (l, empty_tannot)),
                          E_aux (E_id id, id_annot)
                        ),
                      id_annot
                    )
                in
                mk_def (DEF_let (LB_aux (LB_val (P_aux (P_id id, id_annot), def_body), (l, empty_tannot))))
              )
              (IdSet.elements ids)
          in
          base_def :: id_defs
        )
    | d -> [d]
  in
  let defs = List.map rewrite_def ast.defs |> List.concat in
  { ast with defs }

let opt_mono_rewrites = ref false
let opt_mono_complex_nexps = ref true

let mono_rewrites env defs = if !opt_mono_rewrites then Monomorphise.mono_rewrites defs else defs

let rewrite_toplevel_nexps env defs = if !opt_mono_complex_nexps then Monomorphise.rewrite_toplevel_nexps defs else defs

let rewrite_complete_record_params env defs =
  if !opt_mono_complex_nexps then Monomorphise.rewrite_complete_record_params env defs else defs

let opt_mono_split = ref ([] : ((string * int) * string) list)
let opt_dmono_analysis = ref 0
let opt_auto_mono = ref false
let opt_dall_split_errors = ref false
let opt_dmono_continue = ref false

let monomorphise target effect_info env defs =
  let open Monomorphise in
  ( monomorphise target effect_info
      {
        auto = !opt_auto_mono;
        debug_analysis = !opt_dmono_analysis;
        all_split_errors = !opt_dall_split_errors;
        continue_anyway = !opt_dmono_continue;
      }
      !opt_mono_split defs,
    effect_info,
    env
  )

let if_mono f effect_info env ast =
  match (!opt_mono_split, !opt_auto_mono) with [], false -> (ast, effect_info, env) | _, _ -> f effect_info env ast

(* Also turn mwords stages on when we're just trying out mono *)
let if_mwords f effect_info env ast =
  if !Monomorphise.opt_mwords then f effect_info env ast else if_mono f effect_info env ast

let if_flag flag f effect_info env ast = if !flag then f effect_info env ast else (ast, effect_info, env)

type rewriter =
  | Base_rewriter of (Effects.side_effect_info -> Env.t -> tannot ast -> tannot ast * Effects.side_effect_info * Env.t)
  | Bool_rewriter of (bool -> rewriter)
  | String_rewriter of (string -> rewriter)
  | Literal_rewriter of ((lit -> bool) -> rewriter)

let basic_rewriter f = Base_rewriter (fun effect_info env ast -> (f env ast, effect_info, env))
let checking_rewriter f =
  Base_rewriter
    (fun effect_info env ast ->
      let ast, env = f env ast in
      (ast, effect_info, env)
    )

type rewriter_arg =
  | If_mono_arg
  | If_mwords_arg
  | If_flag of bool ref
  | Bool_arg of bool
  | Flag_arg of bool ref
  | String_arg of string
  | Literal_arg of string

let rec describe_rewriter = function
  | String_rewriter rw -> "<string>" :: describe_rewriter (rw "")
  | Bool_rewriter rw -> "<bool>" :: describe_rewriter (rw false)
  | Literal_rewriter rw -> "(ocaml|lem|all)" :: describe_rewriter (rw (fun _ -> true))
  | Base_rewriter _ -> []

let instantiate_rewriter rewriter args =
  let selector_function = function
    | "ocaml" -> rewrite_lit_ocaml
    | "lem" -> rewrite_lit_lem
    | "all" -> fun _ -> true
    | arg ->
        raise
          (Reporting.err_general Parse_ast.Unknown
             ("No rewrite for literal target \"" ^ arg ^ "\", valid targets are ocaml/lem/all")
          )
  in
  let instantiate rewriter arg =
    match (rewriter, arg) with
    | Base_rewriter rw, If_mono_arg -> Base_rewriter (if_mono rw)
    | Base_rewriter rw, If_mwords_arg -> Base_rewriter (if_mwords rw)
    | Base_rewriter rw, If_flag flag -> Base_rewriter (if_flag flag rw)
    | Bool_rewriter rw, Flag_arg b -> rw !b
    | Bool_rewriter rw, Bool_arg b -> rw b
    | String_rewriter rw, String_arg str -> rw str
    | Literal_rewriter rw, Literal_arg selector -> rw (selector_function selector)
    | _, _ -> Reporting.unreachable Parse_ast.Unknown __POS__ "Invalid rewrite argument"
  in
  match List.fold_left instantiate rewriter args with
  | Base_rewriter rw -> rw
  | _ -> Reporting.unreachable Parse_ast.Unknown __POS__ "Rewrite not fully instantiated"

let all_rewriters =
  [
    ("recheck_defs", checking_rewriter (fun _ ast -> Type_error.check initial_env (strip_ast ast)));
    ("realize_mappings", Base_rewriter rewrite_ast_realize_mappings);
    ("remove_duplicate_valspecs", basic_rewriter remove_duplicate_valspecs);
    ("toplevel_string_append", Base_rewriter rewrite_ast_toplevel_string_append);
    ("pat_string_append", basic_rewriter rewrite_ast_pat_string_append);
    ("mapping_patterns", basic_rewriter (fun _ -> Mappings.rewrite_ast));
    ("truncate_hex_literals", basic_rewriter rewrite_truncate_hex_literals);
    ("mono_rewrites", basic_rewriter mono_rewrites);
    ("complete_record_params", basic_rewriter rewrite_complete_record_params);
    ("toplevel_nexps", basic_rewriter rewrite_toplevel_nexps);
    ("toplevel_consts", String_rewriter (fun target -> basic_rewriter (rewrite_toplevel_consts target)));
    ("monomorphise", String_rewriter (fun target -> Base_rewriter (monomorphise target)));
    ( "atoms_to_singletons",
      String_rewriter (fun target -> basic_rewriter (fun _ -> Monomorphise.rewrite_atoms_to_singletons target))
    );
    ("add_bitvector_casts", basic_rewriter Monomorphise.add_bitvector_casts);
    ("remove_impossible_int_cases", basic_rewriter Constant_propagation.remove_impossible_int_cases);
    ("const_prop_mutrec", String_rewriter (fun target -> Base_rewriter (Constant_propagation_mutrec.rewrite_ast target)));
    ("make_cases_exhaustive", Base_rewriter MakeExhaustive.rewrite);
    ("undefined", Bool_rewriter (fun b -> basic_rewriter (rewrite_undefined_if_gen b)));
    ("vector_string_pats_to_bit_list", basic_rewriter rewrite_ast_vector_string_pats_to_bit_list);
    ("remove_not_pats", basic_rewriter rewrite_ast_not_pats);
    ("pattern_literals", Literal_rewriter (fun f -> basic_rewriter (rewrite_ast_pat_lits f)));
    ("vector_concat_assignments", basic_rewriter rewrite_vector_concat_assignments);
    ("tuple_assignments", basic_rewriter rewrite_tuple_assignments);
    ("simple_assignments", basic_rewriter (rewrite_simple_assignments false));
    ("simple_struct_assignments", basic_rewriter (rewrite_simple_assignments true));
    ("remove_vector_concat", basic_rewriter rewrite_ast_remove_vector_concat);
    ("remove_vector_subrange_pats", basic_rewriter rewrite_ast_remove_vector_subrange_pats);
    ("remove_bitvector_pats", basic_rewriter rewrite_ast_remove_bitvector_pats);
    ("remove_numeral_pats", basic_rewriter rewrite_ast_remove_numeral_pats);
    ("guarded_pats", basic_rewriter rewrite_ast_guarded_pats);
    ("bit_lists_to_lits", basic_rewriter rewrite_bit_lists_to_lits);
    ("exp_lift_assign", basic_rewriter rewrite_ast_exp_lift_assign);
    ("early_return", Base_rewriter rewrite_ast_early_return);
    ("nexp_ids", basic_rewriter rewrite_ast_nexp_ids);
    ("remove_blocks", basic_rewriter rewrite_ast_remove_blocks);
    ("letbind_effects", Base_rewriter rewrite_ast_letbind_effects);
    ("remove_e_assign", basic_rewriter rewrite_ast_remove_e_assign);
    ("internal_lets", basic_rewriter rewrite_ast_internal_lets);
    ("remove_superfluous_letbinds", basic_rewriter rewrite_ast_remove_superfluous_letbinds);
    ("remove_superfluous_returns", basic_rewriter rewrite_ast_remove_superfluous_returns);
    ("merge_function_clauses", basic_rewriter merge_funcls);
    ("minimise_recursive_functions", basic_rewriter minimise_recursive_functions);
    ("move_termination_measures", basic_rewriter move_termination_measures);
    ("rewrite_explicit_measure", Base_rewriter rewrite_explicit_measure);
    ("rewrite_loops_with_escape_effect", basic_rewriter rewrite_loops_with_escape_effect);
    ("simple_types", basic_rewriter rewrite_simple_types);
    ( "instantiate_outcomes",
      String_rewriter (fun target -> basic_rewriter (fun _ -> Outcome_rewrites.instantiate target))
    );
    ("top_sort_defs", basic_rewriter (fun _ -> top_sort_defs));
    ( "constant_fold",
      String_rewriter
        (fun target -> basic_rewriter (fun _ -> Constant_fold.(rewrite_constant_function_calls no_fixed target)))
    );
    ("split", String_rewriter (fun str -> Base_rewriter (rewrite_split_fun_ctor_pats str)));
    ("properties", basic_rewriter (fun _ -> Property.rewrite));
    ( "attach_effects",
      Base_rewriter (fun effect_info env ast -> (Effects.rewrite_attach_effects effect_info ast, effect_info, env))
    );
    ( "prover_regstate",
      Bool_rewriter
        (fun mwords ->
          Base_rewriter
            (fun effect_info env ast ->
              let env, ast = State.add_regstate_defs mwords env ast in
              (ast, effect_info, env)
            )
        )
    );
    ("add_unspecified_rec", basic_rewriter rewrite_add_unspecified_rec);
    ("toplevel_let_patterns", basic_rewriter rewrite_toplevel_let_patterns);
  ]

let rewrites_interpreter =
  [
    ("instantiate_outcomes", [String_arg "interpreter"]);
    ("realize_mappings", []);
    ("toplevel_string_append", []);
    ("pat_string_append", []);
    ("mapping_patterns", []);
    ("undefined", [Bool_arg false]);
    ("tuple_assignments", []);
    ("vector_concat_assignments", []);
    ("simple_assignments", []);
  ]

type rewrite_sequence =
  (string * (Effects.side_effect_info -> Env.t -> tannot ast -> tannot ast * Effects.side_effect_info * Env.t)) list

let instantiate_rewrites rws =
  let get_rewriter name =
    match List.assoc_opt name all_rewriters with
    | Some rewrite -> rewrite
    | None -> Reporting.unreachable Parse_ast.Unknown __POS__ ("Attempted to execute unknown rewrite " ^ name)
  in
  List.map (fun (name, args) -> (name, instantiate_rewriter (get_rewriter name) args)) rws

let opt_ddump_rewrite_ast = ref None

let rewrite_step n total (ast, effect_info, env) (name, rewriter) =
  let t = Profile.start () in
  let ast, effect_info, env = rewriter effect_info env ast in
  Profile.finish ("rewrite " ^ name) t;

  begin
    match !opt_ddump_rewrite_ast with
    | Some (f, i) ->
        let filename = f ^ "_rewrite_" ^ string_of_int i ^ "_" ^ name ^ ".sail" in
        let ((ot, _, _, _) as ext_ot) = Util.open_output_with_check_unformatted None filename in
        Pretty_print_sail.pp_ast ot (strip_ast ast);
        Util.close_output_with_check ext_ot;
        opt_ddump_rewrite_ast := Some (f, i + 1)
    | _ -> ()
  end;
  Util.progress "Rewrite " name n total;

  (ast, effect_info, env)

let rewrite effect_info env rewriters ast =
  let total = List.length rewriters in
  try
    snd
      (List.fold_left
         (fun (n, astenv) rw -> (n + 1, rewrite_step n total astenv rw))
         (1, (ast, effect_info, env))
         rewriters
      )
  with Type_error.Type_error (l, err) -> raise (Reporting.err_typ l (Type_error.string_of_type_error err))

let () =
  let open Interactive in
  ActionUnit
    (fun _ ->
      let print_rewriter (name, rw) =
        print_endline (name ^ " " ^ Util.(String.concat " " (describe_rewriter rw) |> yellow |> clear))
      in
      List.sort (fun a b -> String.compare (fst a) (fst b)) all_rewriters |> List.iter print_rewriter
    )
  |> register_command ~name:"list_rewrites" ~help:"List all rewrites for use with the :rewrite command"
