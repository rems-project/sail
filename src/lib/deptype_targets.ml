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
open Ast_compare
open Ast_util
open Reporting

let unfold_exists_typ debug env ?instantiated_type (Typ_aux (t, l) as typ) =
  match t with
  | Typ_exist (kopts, _nc, typ') ->
      let new_vars = List.fold_left (fun s kopt -> KidSet.add (kopt_kid kopt) s) KidSet.empty kopts in
      let typ' =
        match instantiated_type with
        | None -> typ'
        | Some ityp -> (
            match Type_check.unify (typ_loc ityp) env new_vars typ' ityp with
            | kmap ->
                let kmap' =
                  KBindings.filter_map
                    (fun kid v ->
                      match v with A_aux (A_nexp (Nexp_aux (Nexp_constant _, _) as nexp), _) -> Some nexp | _ -> None
                    )
                    kmap
                in
                subst_kids_typ kmap' typ'
            | exception _ ->
                debug
                  ( lazy
                    ("Unification failed when trying to fill in type variables using " ^ string_of_typ typ ^ " against "
                   ^ string_of_typ ityp
                    )
                    );
                typ'
          )
      in
      (new_vars, typ')
  | _ -> (KidSet.empty, typ)

let rec tyvars_of_typ (Typ_aux (t, l)) =
  let trec = tyvars_of_typ in
  match t with
  | Typ_id _ -> KidSet.empty
  | Typ_var kid -> tyvars_of_nexp (Type_check.orig_nexp (nvar kid))
  | Typ_fn (t1, t2) -> List.fold_left KidSet.union (trec t2) (List.map trec t1)
  | Typ_tuple ts -> List.fold_left (fun s t -> KidSet.union s (trec t)) KidSet.empty ts
  | Typ_app (Id_aux (Id "register", _), [A_aux (A_typ etyp, _)]) -> trec etyp
  | Typ_app (Id_aux (Id "implicit", _), _) | Typ_app (Id_aux (Id "atom", _), _) | Typ_app (Id_aux (Id "atom_bool", _), _)
    ->
      KidSet.empty
  (* TODO: calculate which arguments are used *)
  | Typ_app (_, tas) -> List.fold_left (fun s ta -> KidSet.union s (tyvars_of_typ_arg ta)) KidSet.empty tas
  | Typ_exist (kopts, _, t) -> List.fold_left (fun vs kopt -> KidSet.remove (kopt_kid kopt) vs) (trec t) kopts
  | Typ_bidir _ -> unreachable l __POS__ "Bidirection types should have been removed before Lean backend"
  | Typ_internal_unknown -> unreachable l __POS__ "escaped Typ_internal_unknown"

and tyvars_of_typ_arg (A_aux (ta, _)) =
  match ta with
  | A_nexp nexp -> tyvars_of_nexp (Type_check.orig_nexp nexp)
  | A_typ typ -> tyvars_of_typ typ
  | A_bool nc -> KidSet.empty

let relevant_existential_vars env kopts typ =
  let relevant_kids = tyvars_of_typ typ in
  let relevant_kopts = List.filter (fun kopt -> KidSet.mem (kopt_kid kopt) relevant_kids) kopts in
  (relevant_kopts, typ)

let relevant_type_vars env typ =
  match typ with Typ_aux (Typ_exist (kopts, _nc, typ'), _) -> relevant_existential_vars env kopts typ' | _ -> ([], typ)

(* maybe TODO: this could be provided by the type checker, and shared with bind_pat *)
let typ_of_constructor env f typ l =
  let open Type_check in
  let quants, ctor_typ = Env.get_union_id f env in
  match Env.expand_synonyms (Env.add_typquant l quants env) ctor_typ with
  | Typ_aux (Typ_fn ([arg_typ], ret_typ), _) -> (
      try
        let goals = quant_kopts quants |> List.map kopt_kid |> KidSet.of_list in
        let unifiers = unify l env goals ret_typ typ in
        let arg_typ' = subst_unifiers unifiers arg_typ in
        arg_typ'
      with exc ->
        raise
          (Reporting.err_unreachable l __POS__
             ("Unification error when pattern matching against union constructor: " ^ Printexc.to_string exc)
          )
    )
  | _ ->
      raise
        (Reporting.err_unreachable l __POS__
           ("Mal-formed constructor " ^ string_of_id f ^ " with type " ^ string_of_typ ctor_typ)
        )
