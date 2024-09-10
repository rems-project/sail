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

let scan_exp_in_pexp f (Pat_aux (aux, _)) =
  match aux with
  | Pat_exp (_, exp) -> f exp
  | Pat_when (_, guard, exp) ->
      f guard;
      f exp

let scan_exp_in_funcl f (FCL_aux (FCL_funcl (_, pexp), _)) = scan_exp_in_pexp f pexp

let scan_exp_in_mpexp f (MPat_aux (aux, _)) = match aux with MPat_when (_, exp) -> f exp | MPat_pat _ -> ()

let scan_exp_in_mapcl f (MCL_aux (aux, _)) =
  match aux with
  | MCL_forwards pexp | MCL_backwards pexp -> scan_exp_in_pexp f pexp
  | MCL_bidir (left, right) ->
      scan_exp_in_mpexp f left;
      scan_exp_in_mpexp f right

let scan_exp_in_scattered_def f (SD_aux (aux, _)) =
  match aux with
  | SD_function _ | SD_unioncl _ | SD_variant _ | SD_internal_unioncl_record _ | SD_enumcl _ | SD_enum _ | SD_mapping _
  | SD_end _ ->
      ()
  | SD_funcl funcl -> scan_exp_in_funcl f funcl
  | SD_mapcl (_, mapcl) -> scan_exp_in_mapcl f mapcl

let scan_exp_in_fundef f (FD_aux (FD_function (_, _, funcls), _)) = List.iter (scan_exp_in_funcl f) funcls

let scan_exp_in_internal_loop_measure f (Measure_aux (aux, _)) =
  match aux with Measure_none -> () | Measure_some exp -> f exp

let rec scan_exp_in_def f (DEF_aux (aux, _)) =
  match aux with
  | DEF_fundef fdef -> scan_exp_in_fundef f fdef
  | DEF_mapdef (MD_aux (MD_mapping (_, _, mapcls), _)) -> List.iter (scan_exp_in_mapcl f) mapcls
  | DEF_register (DEC_aux (DEC_reg (_, _, exp_opt), _)) -> Option.iter f exp_opt
  | DEF_outcome (_, defs) -> List.iter (scan_exp_in_def f) defs
  | DEF_impl funcl -> scan_exp_in_funcl f funcl
  | DEF_let (LB_aux (LB_val (_, exp), _)) -> f exp
  | DEF_scattered sdef -> scan_exp_in_scattered_def f sdef
  | DEF_internal_mutrec fdefs -> List.iter (scan_exp_in_fundef f) fdefs
  | DEF_loop_measures _ -> ()
  | DEF_measure (_, _, exp) -> f exp
  | DEF_type _ | DEF_constraint _ | DEF_val _ | DEF_fixity _ | DEF_overload _ | DEF_default _ | DEF_pragma _
  | DEF_instantiation _ ->
      ()

let warn_unmodified_variables ast =
  let warn_unused (lexp, bind, exp) =
    let unused = IdSet.diff lexp exp in
    IdSet.iter
      (fun id ->
        Reporting.warn "Unnecessary mutability" (id_loc id)
          "This variable is mutable, but it is never modified. It could be declared as immutable using 'let'."
      )
      unused;
    IdSet.union (IdSet.diff exp lexp) bind
  in
  let alg =
    {
      (Rewriter.pure_exp_alg IdSet.empty IdSet.union) with
      le_id = IdSet.singleton;
      le_typ = (fun (_, id) -> IdSet.singleton id);
      e_var = warn_unused;
    }
  in
  List.iter (scan_exp_in_def (fun exp -> ignore (Rewriter.fold_exp alg exp))) ast.defs
