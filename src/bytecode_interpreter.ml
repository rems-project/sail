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
open Bytecode
open Bytecode_util

module StringMap = Map.Make(String)

type 'a frame = {
    jump_table : int StringMap.t;
    locals : 'a Bindings.t;
    pc : int;
    instrs : instr array
  }

type 'a gstate = {
    globals : 'a Bindings.t;
    cdefs : cdef list
  }

type 'a stack = {
    top : 'a frame;
    ret : ('a -> 'a frame) list
  }

let make_jump_table instrs =
  let rec aux n = function
    | I_aux (I_label label, _) :: instrs -> StringMap.add label n (aux (n + 1) instrs)
    | _ :: instrs -> aux (n + 1) instrs
    | [] -> StringMap.empty
  in
  aux 0 instrs

let new_gstate cdefs = {
    globals = Bindings.empty;
    cdefs = cdefs
  }

let new_stack instrs = {
    top = {
      jump_table = make_jump_table instrs;
      locals = Bindings.empty;
      pc = 0;
      instrs = Array.of_list instrs
    };
    ret = []
  }

let with_top stack f =
  { stack with top = f (stack.top) }

let eval_fragment gstate locals = function
  | F_id id ->
     begin match Bindings.find_opt id locals with
     | Some vl -> vl
     | None ->
        begin match Bindings.find_opt id gstate.globals with
        | Some vl -> vl
        | None -> failwith "Identifier not found"
        end
     end
  | F_lit vl -> vl
  | _ -> failwith "Cannot eval fragment"

let is_function id = function
  | CDEF_fundef (id', _, _, _) when Id.compare id id' = 0 -> true
  | _ -> false

let step (gstate, stack) =
  let I_aux (instr_aux, (_, l)) = stack.top.instrs.(stack.top.pc) in
  match instr_aux with
  | I_decl _ ->
     gstate, with_top stack (fun frame -> { frame with pc = frame.pc + 1 })

  | I_init (_, id, (fragment, _)) ->
     let vl = eval_fragment gstate stack.top.locals fragment in
     gstate,
     with_top stack (fun frame -> { frame with pc = frame.pc + 1; locals = Bindings.add id vl frame.locals })

  | I_jump ((fragment, _), label) ->
     let vl = eval_fragment gstate stack.top.locals fragment in
     gstate,
     begin match vl with
     | V_bool true ->
        with_top stack (fun frame -> { frame with pc = StringMap.find label frame.jump_table })
     | V_bool false ->
        with_top stack (fun frame -> { frame with pc = frame.pc + 1 })
     | _ ->
        failwith "Type error"
     end

  | I_funcall (clexp, _, id, cvals) ->
     let args = List.map (fun (fragment, _) -> eval_fragment gstate stack.top.locals fragment) cvals in
     let params, instrs =
       match List.find_opt (is_function id) gstate.cdefs with
       | Some (CDEF_fundef (_, _, params, instrs)) -> params, instrs
       | _ -> failwith "Function not found"
     in
     gstate,
     {
       top = {
         jump_table = make_jump_table instrs;
         locals = List.fold_left2 (fun locals param arg -> Bindings.add param arg locals) Bindings.empty params args;
         pc = 0;
         instrs = Array.of_list instrs;
       };
       ret = (fun vl -> { stack.top with pc = stack.top.pc + 1 }) :: stack.ret
     }

  | I_goto label ->
     gstate, with_top stack (fun frame -> { frame with pc = StringMap.find label frame.jump_table })

  | _ -> raise (Reporting.err_unreachable l __POS__ "Unhandled instruction")
