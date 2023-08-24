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
open Type_error
open Rewriter

let rec in_substs id = function
  | IS_aux (IS_id (id_from, _), _) :: _ when Id.compare id id_from = 0 -> true
  | _ :: substs -> in_substs id substs
  | [] -> false

let rec instantiate_id id = function
  | IS_aux (IS_id (id_from, id_to), _) :: _ when Id.compare id id_from = 0 -> id_to
  | _ :: substs -> instantiate_id id substs
  | [] -> id

let instantiate_typ substs typ =
  List.fold_left
    (fun typ -> function kid, (_, subst_typ) -> typ_subst kid (mk_typ_arg (A_typ subst_typ)) typ)
    typ (KBindings.bindings substs)

let instantiate_def target id substs = function
  | DEF_aux (DEF_impl (FCL_aux (FCL_funcl (target_id, pexp), (fcl_def_annot, tannot))), def_annot)
    when string_of_id target_id = target ->
      let l = gen_loc (id_loc id) in
      Some
        (DEF_aux
           ( DEF_fundef
               (FD_aux
                  ( FD_function
                      ( Rec_aux (Rec_nonrec, l),
                        Typ_annot_opt_aux (Typ_annot_opt_none, l),
                        [FCL_aux (FCL_funcl (id, pexp), (fcl_def_annot, tannot))]
                      ),
                    (l, tannot)
                  )
               ),
             def_annot
           )
        )
  | def -> None

let rec instantiated_or_abstract l = function
  | [] -> None
  | None :: xs -> instantiated_or_abstract l xs
  | Some def :: xs ->
      if List.for_all Option.is_none xs then Some def
      else raise (Reporting.err_general l "Multiple instantiations found for target")

let instantiate target ast =
  let process_def outcomes = function
    | DEF_aux (DEF_outcome (OV_aux (OV_outcome (id, TypSchm_aux (TypSchm_ts (typq, typ), _), args), l), outcome_defs), _)
      ->
        (Bindings.add id (typq, typ, args, l, outcome_defs) outcomes, [])
    | DEF_aux (DEF_instantiation (IN_aux (IN_id id, annot), id_substs), def_annot) ->
        let l = gen_loc (id_loc id) in
        let env = env_of_annot annot in
        let substs = Env.get_outcome_instantiation env in
        let typq, typ, args, outcome_l, outcome_defs =
          match Bindings.find_opt id outcomes with
          | Some outcome -> outcome
          | None ->
              Reporting.unreachable (id_loc id) __POS__
                ("Outcome for instantiation " ^ string_of_id id ^ " does not exist")
        in

        let rewrite_p_aux (pat, annot) =
          match pat with
          | P_typ (typ, pat) -> P_aux (P_typ (instantiate_typ substs typ, pat), annot)
          | pat -> P_aux (pat, annot)
        in
        let rewrite_e_aux (exp, annot) =
          match exp with
          | E_app (f, args) -> E_aux (E_app (instantiate_id f id_substs, args), annot)
          | E_typ (typ, exp) -> E_aux (E_typ (instantiate_typ substs typ, exp), annot)
          | _ -> E_aux (exp, annot)
        in
        let pat_alg = { id_pat_alg with p_aux = rewrite_p_aux } in
        let rewrite_pat rw pat = fold_pat pat_alg pat in
        let rewrite_exp _ exp = fold_exp { id_exp_alg with e_aux = rewrite_e_aux; pat_alg } exp in

        let valspec is_extern =
          let extern = if is_extern then Some { pure = false; bindings = [("_", string_of_id id)] } else None in
          DEF_aux
            ( DEF_val
                (VS_aux
                   ( VS_val_spec (TypSchm_aux (TypSchm_ts (typq, instantiate_typ substs typ), l), id, extern),
                     (l, empty_uannot)
                   )
                ),
              def_annot
            )
        in
        let instantiated_def =
          rewrite_ast_defs { rewriters_base with rewrite_pat; rewrite_exp } outcome_defs
          |> List.map (instantiate_def target id id_substs)
          |> instantiated_or_abstract (id_loc id)
        in
        let outcome_defs, _ =
          ( match instantiated_def with
          | None ->
              [
                DEF_aux
                  (DEF_pragma ("abstract", string_of_id id, gen_loc (id_loc id)), mk_def_annot (gen_loc (id_loc id)));
                valspec true;
              ]
          | Some def -> [valspec false; strip_def def]
          )
          |> Type_error.check_defs env
        in
        (outcomes, outcome_defs)
    | def -> (outcomes, [def])
  in
  { ast with defs = snd (Util.fold_left_concat_map process_def Bindings.empty ast.defs) }
