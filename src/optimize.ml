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

open Ast
open Ast_util
open Rewriter

let recheck (Defs defs) =
  let defs = Type_check.check_with_envs Type_check.initial_env defs in

  let rec find_optimizations = function
    | ([DEF_pragma ("optimize", pragma, p_l)], env)
      :: ([DEF_spec vs as def1], _)
      :: ([DEF_fundef fdef as def2], _)
      :: defs ->
       let id = id_of_val_spec vs in
       let args = Str.split (Str.regexp " +") (String.trim pragma) in
       begin match args with
       | ["unroll"; n]->
          let n = int_of_string n in

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
            specs := !specs @ [DEF_spec (rename_valspec current_id vs)];
            (* Then duplicate it's function body and make it call the next unrolled function *)
            bodies := !bodies @ [rewrite_def (rw_defs next_id) (DEF_fundef (rename_fundef current_id fdef))]
          done;

          !specs @ !bodies @ find_optimizations defs

       | _ ->
          Util.warn ("Unrecognised optimize pragma in this context: " ^ pragma);
          def1 :: def2 :: find_optimizations defs
       end

    | (defs, _) :: defs' ->
       defs @ find_optimizations defs'

    | [] -> []
  in

  Defs (find_optimizations defs)
