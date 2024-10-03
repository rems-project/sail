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
open Type_check

type parameters = {
  abort_type : typ;
  barrier_type : typ;
  cache_op_type : typ;
  fault_type : typ;
  pa_type : typ;
  tlbi_type : typ;
  translation_summary_type : typ;
  arch_ak_type : typ;
  sys_reg_id_type : typ;
}

let find_monad_parameters type_env =
  (* We treat the memory read function as an indication that we want the
     concurrency interface. *)
  let memory_types =
    match Env.get_val_spec (mk_id "sail_mem_read") type_env with
    | ( _,
        Typ_aux
          ( Typ_fn
              ( [
                  Typ_aux
                    ( Typ_app
                        ( req_id,
                          [_; _; A_aux (A_typ pa_arg, _); A_aux (A_typ trans_sum_arg, _); A_aux (A_typ arch_ak_arg, _)]
                        ),
                      _
                    );
                ],
                Typ_aux (Typ_app (result_id, [_; A_aux (A_typ abort_arg, _)]), _)
              ),
            _
          ) )
      when Id.compare req_id (mk_id "Mem_read_request") == 0 && Id.compare result_id (mk_id "result") == 0 ->
        Some (abort_arg, pa_arg, trans_sum_arg, arch_ak_arg)
    | _ -> None
    | exception _ -> None
  in
  match memory_types with
  | None -> None
  | Some (abort_type, pa_type, translation_summary_type, arch_ak_type) ->
      (* and then treat the remaining types as optional *)
      let extract_arg_typ fn_name =
        match Env.get_val_spec (mk_id fn_name) type_env with
        | _, Typ_aux (Typ_fn (typ :: _, _), _) -> typ
        | _ -> unit_typ
        | exception _ -> unit_typ
      in
      let barrier_type = extract_arg_typ "sail_barrier" in
      let cache_op_type = extract_arg_typ "sail_cache_op" in
      let fault_type = extract_arg_typ "sail_take_exception" in
      let tlbi_type = extract_arg_typ "sail_tlbi" in
      let sys_reg_id_type = extract_arg_typ "sail_sys_reg_read" in
      Some
        {
          abort_type;
          barrier_type;
          cache_op_type;
          fault_type;
          pa_type;
          tlbi_type;
          translation_summary_type;
          arch_ak_type;
          sys_reg_id_type;
        }
