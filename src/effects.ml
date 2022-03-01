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
open Type_check

type side_effect =
  | Throw
  | Exit
  | IncompleteMatch
  | Register
  | Transitive

let string_of_side_effect = function
  | Throw -> "throw"
  | Exit -> "exit"
  | IncompleteMatch -> "incomplete match"
  | Register -> "register"
  | Transitive -> "transitive"

module Effect = struct
  type t = side_effect
  let compare e1 e2 =
    match (e1, e2) with
    | Throw, Throw -> 0
    | Exit, Exit -> 0
    | IncompleteMatch, IncompleteMatch -> 0
    | Register, Register -> 0
    | Transitive, Transitive -> 0
    | Throw, _ -> 1 | _, Throw -> -1
    | Exit, _ -> 1 | _, Exit -> -1
    | IncompleteMatch, _ -> 1 | _, IncompleteMatch -> -1
    | Transitive, _ -> 1 | _, Transitive -> -1
end

module EffectSet = Set.Make(Effect)

let throws = EffectSet.mem Throw

let pure = EffectSet.is_empty

module PC_config = struct
  type t = tannot
  let typ_of_pat = Type_check.typ_of_pat
end

module PC = Pattern_completeness.Make(PC_config)

let infer_def_direct_effects def =
  let effects = ref EffectSet.empty in

  let scan_lexp lexp_aux annot =
    let env = env_of_annot annot in
    begin match lexp_aux with
    | LEXP_cast (_, id) | LEXP_id id ->
       begin match Env.lookup_id id env with
       | Register _ ->
          effects := EffectSet.add Register !effects
       | _ -> ()
       end
    | LEXP_deref _ -> effects := EffectSet.add Register !effects
    | _ -> ()
    end;
    LEXP_aux (lexp_aux, annot)
  in

  let scan_exp e_aux annot =
    let env = env_of_annot annot in
    begin match e_aux with
    | E_id id ->
       begin match Env.lookup_id id env with
       | Register _ ->
          effects := EffectSet.add Register !effects
       | _ -> ()
       end
    | E_throw _ -> effects := EffectSet.add Throw !effects
    | E_exit _ | E_assert _ -> effects := EffectSet.add Exit !effects
    | E_app (f, _) when Id.compare f (mk_id "__deref") = 0 ->
       effects := EffectSet.add Register !effects
    | E_case (exp, cases) ->
       let ctx = {
           Pattern_completeness.variants = Env.get_variants env;
           Pattern_completeness.enums = Env.get_enums env
         } in
       if not (PC.is_complete (fst annot) ctx cases (typ_of exp)) then (
         effects := EffectSet.add IncompleteMatch !effects
       )
    | _ -> ()
    end;
    E_aux (e_aux, annot)
  in

  let rw_exp _ exp =
    fold_exp { id_exp_alg with e_aux = (fun (e_aux, annot) -> scan_exp e_aux annot);
                               lEXP_aux = (fun (l_aux, annot) -> scan_lexp l_aux annot) } exp in
  ignore (rewrite_ast_defs { rewriters_base with rewrite_exp = rw_exp } [def]);
  !effects
                      
let infer_side_effects ~known_pure:known_pure ast =
  let cg = Callgraph.graph_of_ast ast in
  Bindings.empty
