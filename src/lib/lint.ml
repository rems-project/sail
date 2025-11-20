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

module Scan (F : sig
  type t
  val do_exp : t exp -> unit
  val do_funcl_pexp : (t pat -> t exp option -> t exp -> unit) option
end) : sig
  val in_def : (F.t, 'b) def -> unit
end = struct
  let in_pexp (Pat_aux (aux, _)) =
    match aux with
    | Pat_exp (_, exp) -> F.do_exp exp
    | Pat_when (_, guard, exp) ->
        F.do_exp guard;
        F.do_exp exp

  let in_funcl (FCL_aux (FCL_funcl (_, pexp), _)) =
    match F.do_funcl_pexp with
    | Some g -> (
        match pexp with
        | Pat_aux (Pat_exp (pat, exp), _) -> g pat None exp
        | Pat_aux (Pat_when (pat, guard, exp), _) -> g pat (Some guard) exp
      )
    | None -> in_pexp pexp

  let in_mpexp (MPat_aux (aux, _)) = match aux with MPat_when (_, exp) -> F.do_exp exp | MPat_pat _ -> ()

  let in_mapcl (MCL_aux (aux, _)) =
    match aux with
    | MCL_forwards pexp | MCL_backwards pexp -> in_pexp pexp
    | MCL_bidir (left, right) ->
        in_mpexp left;
        in_mpexp right

  let in_scattered_def (SD_aux (aux, _)) =
    match aux with
    | SD_function _ | SD_unioncl _ | SD_variant _ | SD_internal_unioncl_record _ | SD_enumcl _ | SD_enum _
    | SD_mapping _ | SD_end _ ->
        ()
    | SD_funcl funcl -> in_funcl funcl
    | SD_mapcl (_, mapcl) -> in_mapcl mapcl

  let in_fundef (FD_aux (FD_function (_, _, funcls), _)) = List.iter in_funcl funcls

  let rec in_def (DEF_aux (aux, _)) =
    match aux with
    | DEF_fundef fdef -> in_fundef fdef
    | DEF_mapdef (MD_aux (MD_mapping (_, _, mapcls), _)) -> List.iter in_mapcl mapcls
    | DEF_register (DEC_aux (DEC_reg (_, _, exp_opt), _)) -> Option.iter F.do_exp exp_opt
    | DEF_outcome (_, defs) -> List.iter in_def defs
    | DEF_impl funcl -> in_funcl funcl
    | DEF_let (LB_aux (LB_val (_, exp), _)) -> F.do_exp exp
    | DEF_scattered sdef -> in_scattered_def sdef
    | DEF_internal_mutrec fdefs -> List.iter in_fundef fdefs
    | DEF_loop_measures _ -> ()
    | DEF_measure (_, _, exp) -> F.do_exp exp
    | DEF_type _ | DEF_constraint _ | DEF_val _ | DEF_fixity _ | DEF_overload _ | DEF_default _ | DEF_pragma _
    | DEF_instantiation _ ->
        ()
end

let warn_unmodified_variables (type a) (ast : (a, 'b) ast) : unit =
  let warn_unmodified (lexp, bind, exp) =
    let unmodified = IdSet.diff lexp exp in
    IdSet.iter
      (fun id ->
        Reporting.warn "Unnecessary mutability" (id_loc id)
          "This variable is mutable, but it is never modified. It could be declared as immutable using 'let'."
      )
      unmodified;
    IdSet.union (IdSet.diff exp lexp) bind
  in
  let alg =
    {
      (Rewriter.pure_exp_alg IdSet.empty IdSet.union) with
      le_id = IdSet.singleton;
      le_typ = (fun (_, id) -> IdSet.singleton id);
      e_var = warn_unmodified;
    }
  in
  let module S = Scan (struct
    type t = a
    let do_exp exp = ignore (Rewriter.fold_exp alg exp)
    let do_funcl_pexp = None
  end) in
  List.iter S.in_def ast.defs

let warn_unused_variables (ast : Type_check.typed_ast) : unit =
  let ignore_variable id = (string_of_id id).[0] = '_' || is_gen_loc (id_loc id) in
  let pexp_unused pat guard_opt exp =
    let used = IdSet.union exp (Option.value ~default:IdSet.empty guard_opt) in
    let unused = IdSet.diff pat used in
    IdSet.iter
      (fun id ->
        if not (ignore_variable id) then
          Reporting.warn "Unused variable" (id_loc id) "This variable is defined but never used."
      )
      unused;
    IdSet.diff used pat
  in
  (* Gather all the variables defined by a pattern *)
  let pat_alg env =
    {
      (Rewriter.pure_pat_alg IdSet.empty IdSet.union) with
      p_id = (fun id -> if Type_check.is_enum_member id env then IdSet.empty else IdSet.singleton id);
      p_vector_subrange = (fun (id, _, _) -> IdSet.singleton id);
      p_as = (fun (_, id) -> IdSet.singleton id);
    }
  in
  let alg env =
    {
      (Rewriter.pure_exp_alg IdSet.empty IdSet.union) with
      e_id = IdSet.singleton;
      pat_exp = (fun (pat, exp) -> pexp_unused pat None exp);
      pat_when = (fun (pat, guard, exp) -> pexp_unused pat (Some guard) exp);
      pat_alg = pat_alg env;
    }
  in
  let module S = Scan (struct
    type t = Type_check.tannot
    let do_exp exp = ignore (Rewriter.fold_exp (alg (Type_check.env_of exp)) exp)
    let do_funcl_pexp =
      Some
        (fun pat guard_opt exp ->
          let env = Type_check.env_of_pat pat in
          let pat = Rewriter.fold_pat (pat_alg env) pat in
          let guard_opt = Option.map (Rewriter.fold_exp (alg env)) guard_opt in
          let exp = Rewriter.fold_exp (alg env) exp in
          ignore (pexp_unused pat guard_opt exp)
        )
  end) in
  List.iter S.in_def ast.defs
