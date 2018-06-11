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
open Type_check
open Rewriter

module StringMap = Map.Make(String);;

(* Flag controls whether any constant folding will occur.
   false = no folding, true = perform constant folding. *)
let optimize_constant_fold = ref false

let exp_of_value =
  let open Value in
  function
  | V_int n -> mk_lit_exp (L_num n)
  | _ -> failwith "No expression for value"

(* We want to avoid evaluating things like print statements at compile
   time, so we remove them from this list of primops we can use when
   constant folding. *)
let safe_primops =
  List.fold_left
    (fun m k -> StringMap.remove k m)
    Value.primops
    [ "print_endline";
      "prerr_endline";
      "putchar";
      "print_bits";
      "print_int";
      "print_string";
      "prerr_bits";
      "prerr_int";
      "prerr_string";
      "Elf_loader.elf_entry";
      "Elf_loader.elf_tohost"
    ]

let is_literal = function
  | E_aux (E_lit _, _) -> true
  | _ -> false

(* Wrapper around interpreter that repeatedly steps until done. *)
let rec run ast frame =
  match frame with
  | Interpreter.Done (state, v) -> v
  | Interpreter.Step _ ->
     run ast (Interpreter.eval_frame ast frame)
  | Interpreter.Break frame ->
     run ast (Interpreter.eval_frame ast frame)

(** This rewriting pass looks for function applications (E_app)
   expressions where every argument is a literal. It passes these
   expressions to the OCaml interpreter in interpreter.ml, and
   reconstructs the values returned back into expressions which are
   then re-typechecked and re-inserted back into the AST.

   We don't use the effect system to decide if expressions are safe to
   evaluate, because this ignores I/O, and would force us to ignore
   functions that maybe throw exceptions internally but as called are
   totally safe. Instead any exceptions during evaluation are caught,
   and the original expression is kept. Some causes of this could be:

   - Function tries to read/write register.
   - Calls an unsafe primop.
   - Throws an exception that isn't caught.
 *)

let rewrite_constant_function_calls' ast =
  let lstate, gstate =
    Interpreter.initial_state ast safe_primops
  in
  let gstate = { gstate with Interpreter.allow_registers = false } in

  let rw_funcall e_aux annot =
    match e_aux with
    | E_app (id, args) when List.for_all is_literal args ->
       begin
         let initial_monad = Interpreter.return (E_aux (e_aux, annot)) in
         try
           begin
             let v = run ast (Interpreter.Step (lazy "", (lstate, gstate), initial_monad, [])) in
             let exp = exp_of_value v in
             try Type_check.check_exp (env_of_annot annot) exp (typ_of_annot annot) with
             | Type_error (l, err) ->
                (* A type error here would be unexpected, so don't ignore it! *)
                Util.warn ("Type error when folding constants in "
                           ^ string_of_exp (E_aux (e_aux, annot))
                           ^ "\n" ^ Type_error.string_of_type_error err);
                E_aux (e_aux, annot)
           end
         with
         (* Otherwise if anything goes wrong when trying to constant
            fold, just continue without optimising. *)
         | _ -> E_aux (e_aux, annot)
       end

    | _ -> E_aux (e_aux, annot)
  in
  let rw_exp = {
      id_exp_alg with
      e_aux = (fun (e_aux, annot) -> rw_funcall e_aux annot)
    } in
  let rw_defs = { rewriters_base with rewrite_exp = (fun _ -> fold_exp rw_exp) } in
  rewrite_defs_base rw_defs ast

let rewrite_constant_function_calls ast =
  if !optimize_constant_fold then
    rewrite_constant_function_calls' ast
  else
    ast
