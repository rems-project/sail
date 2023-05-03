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
open Rewriter

let rec split_at_function' id defs acc =
  match defs with
  | [] -> None
  | ([def], env) :: defs when is_fundef id def -> Some (acc, (def, env), defs)
  | (def, env) :: defs -> split_at_function' id defs ((def, env) :: acc)

let split_at_function id defs =
  match split_at_function' id defs [] with
  | None -> None
  | Some (pre_defs, def, post_defs) -> Some (List.rev pre_defs, def, post_defs)

let rec last_env = function [] -> Type_check.initial_env | [(_, env)] -> env | _ :: xs -> last_env xs

let recheck ({ defs; _ } as ast) =
  let defs = Type_check.check_with_envs Type_check.initial_env (List.map Type_check.strip_def defs) in

  let rec find_optimizations = function
    | ([DEF_aux (DEF_pragma ("optimize", pragma, p_l), _)], env)
      :: ([(DEF_aux (DEF_val vs, vs_annot) as def1)], _)
      :: defs ->
        let id = id_of_val_spec vs in
        let args = Str.split (Str.regexp " +") (String.trim pragma) in
        begin
          match args with
          | ["unroll"; n] ->
              let n = int_of_string n in
              begin
                match split_at_function id defs with
                | Some (intervening_defs, ((DEF_aux (DEF_fundef fdef, fdef_annot) as def2), _), defs) ->
                    let rw_app subst (fn, args) =
                      if Id.compare id fn = 0 then E_app (subst, args) else E_app (fn, args)
                    in
                    let rw_exp subst = { id_exp_alg with e_app = rw_app subst } in
                    let rw_defs subst = { rewriters_base with rewrite_exp = (fun _ -> fold_exp (rw_exp subst)) } in

                    let specs = ref [def1] in
                    let bodies = ref [rewrite_def (rw_defs (append_id id "_unroll_1")) def2] in

                    for i = 1 to n do
                      let current_id = append_id id ("_unroll_" ^ string_of_int i) in
                      let next_id = if i = n then current_id else append_id id ("_unroll_" ^ string_of_int (i + 1)) in
                      (* Create a valspec for the new unrolled function *)
                      specs := !specs @ [DEF_aux (DEF_val (rename_valspec current_id vs), vs_annot)];
                      (* Then duplicate its function body and make it call the next unrolled function *)
                      bodies :=
                        !bodies
                        @ [
                            rewrite_def (rw_defs next_id)
                              (DEF_aux (DEF_fundef (rename_fundef current_id fdef), fdef_annot));
                          ]
                    done;

                    !specs @ List.concat (List.map fst intervening_defs) @ !bodies @ find_optimizations defs
                | _ ->
                    Reporting.warn "Could not find function body for unroll pragma at " p_l "";
                    def1 :: find_optimizations defs
              end
          | _ ->
              Reporting.warn "Unrecognised optimize pragma at" p_l "";
              def1 :: find_optimizations defs
        end
    | (defs, _) :: defs' -> defs @ find_optimizations defs'
    | [] -> []
  in

  ({ ast with defs = find_optimizations defs }, last_env defs)
