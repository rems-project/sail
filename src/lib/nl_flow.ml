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
open Ast_util

let opt_nl_flow = ref false

let rec escapes (E_aux (aux, _)) =
  match aux with
  | E_throw _ -> true
  | E_block [] -> false
  | E_block exps -> escapes (List.hd (List.rev exps))
  | _ -> false

let is_bitvector_literal (L_aux (aux, _)) = match aux with L_bin _ | L_hex _ -> true | _ -> false

let bitvector_unsigned (L_aux (aux, _)) =
  let open Sail_lib in
  match aux with
  | L_bin str -> uint (List.map bin_char (Util.string_to_list str))
  | L_hex str -> uint (bits_of_string str)
  | _ -> assert false

let rec pat_id (P_aux (aux, _)) =
  match aux with P_id id -> Some id | P_as (_, id) -> Some id | P_var (pat, _) -> pat_id pat | _ -> None

let add_assert cond (E_aux (aux, (l, uannot)) as exp) =
  let msg = mk_lit_exp (L_string "") in
  let assertion = locate (fun _ -> gen_loc l) (mk_exp (E_assert (cond, msg))) in
  match aux with
  | E_block exps -> E_aux (E_block (assertion :: exps), (l, empty_uannot))
  | _ -> E_aux (E_block (assertion :: [exp]), (l, uannot))

(* If we know that x != bitv, then after any let y = unsigned(x) we
   will also know that y != unsigned(bitv) *)
let modify_unsigned id value (E_aux (aux, annot) as exp) =
  match aux with
  | E_let ((LB_aux (LB_val (pat, E_aux (E_app (f, [E_aux (E_id id', _)]), _)), _) as lb), exp')
    when (string_of_id f = "unsigned" || string_of_id f = "UInt") && Id.compare id id' = 0 -> begin
      match pat_id pat with
      | None -> exp
      | Some uid ->
          E_aux
            ( E_let
                (lb, add_assert (mk_exp (E_app_infix (mk_exp (E_id uid), mk_id "!=", mk_lit_exp (L_num value)))) exp'),
              annot
            )
    end
  | _ -> exp

let analyze' exps =
  match exps with
  | E_aux (E_if (cond, then_exp, _), _) :: _ when escapes then_exp -> begin
      match cond with
      | E_aux (E_app_infix (E_aux (E_id id, _), op, E_aux (E_lit lit, _)), _)
      | E_aux (E_app_infix (E_aux (E_lit lit, _), op, E_aux (E_id id, _)), _)
        when string_of_id op = "==" && is_bitvector_literal lit ->
          let value = bitvector_unsigned lit in
          List.map (modify_unsigned id value) exps
      | _ -> exps
    end
  | _ -> exps

let analyze exps = if !opt_nl_flow then analyze' exps else exps
