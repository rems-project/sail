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

let rec fexp_of_ctor (field, value) =
  FE_aux (FE_Fexp (mk_id field, exp_of_value value), no_annot)

and exp_of_value =
  let open Value in
  function
  | V_int n -> mk_lit_exp (L_num n)
  | V_bit Sail_lib.B0 -> mk_lit_exp L_zero
  | V_bit Sail_lib.B1 -> mk_lit_exp L_one
  | V_bool true -> mk_lit_exp L_true
  | V_bool false -> mk_lit_exp L_false
  | V_string str -> mk_lit_exp (L_string str)
  | V_record ctors ->
     mk_exp (E_record (List.map fexp_of_ctor (StringMap.bindings ctors)))
  | V_vector vs ->
     mk_exp (E_vector (List.map exp_of_value vs))
  | V_tuple vs ->
     mk_exp (E_tuple (List.map exp_of_value vs))
  | V_unit -> mk_lit_exp L_unit
  | V_attempted_read str -> mk_exp (E_id (mk_id str))
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
      "print";
      "prerr";
      "print_bits";
      "print_int";
      "print_string";
      "print_real";
      "prerr_bits";
      "prerr_int";
      "prerr_string";
      "read_ram";
      "write_ram";
      "get_time_ns";
      "Elf_loader.elf_entry";
      "Elf_loader.elf_tohost"
    ]

let rec is_constant (E_aux (e_aux, _)) =
  match e_aux with
  | E_lit _ -> true
  | E_vector exps -> List.for_all is_constant exps
  | E_record fexps -> List.for_all is_constant_fexp fexps
  | E_cast (_, exp) -> is_constant exp
  | E_tuple exps -> List.for_all is_constant exps
  | _ -> false

and is_constant_fexp (FE_aux (FE_Fexp (_, exp), _)) = is_constant exp

(* Wrapper around interpreter that repeatedly steps until done. *)
let rec run frame =
  match frame with
  | Interpreter.Done (state, v) -> v
  | Interpreter.Step (lazy_str, _, _, _) ->
     run (Interpreter.eval_frame frame)
  | Interpreter.Break frame ->
     run (Interpreter.eval_frame frame)

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

let rec rewrite_constant_function_calls' ast =
  let rewrite_count = ref 0 in
  let ok () = incr rewrite_count in
  let not_ok () = decr rewrite_count in

  let lstate, gstate =
    Interpreter.initial_state ast safe_primops
  in
  let gstate = { gstate with Interpreter.allow_registers = false } in

  let evaluate e_aux annot =
    let initial_monad = Interpreter.return (E_aux (e_aux, annot)) in
    try
      begin
        let v = run (Interpreter.Step (lazy "", (lstate, gstate), initial_monad, [])) in
        let exp = exp_of_value v in
        try (ok (); Type_check.check_exp (env_of_annot annot) exp (typ_of_annot annot)) with
        | Type_error (l, err) ->
           (* A type error here would be unexpected, so don't ignore it! *)
           Util.warn ("Type error when folding constants in "
                      ^ string_of_exp (E_aux (e_aux, annot))
                      ^ "\n" ^ Type_error.string_of_type_error err);
           not_ok ();
           E_aux (e_aux, annot)
      end
    with
    (* Otherwise if anything goes wrong when trying to constant
       fold, just continue without optimising. *)
    | _ -> E_aux (e_aux, annot)
  in

  let rw_funcall e_aux annot =
    match e_aux with
    | E_app (id, args) when List.for_all is_constant args ->
       evaluate e_aux annot

    | E_field (exp, id) when is_constant exp ->
       evaluate e_aux annot

    | E_if (E_aux (E_lit (L_aux (L_true, _)), _), then_exp, _) -> ok (); then_exp
    | E_if (E_aux (E_lit (L_aux (L_false, _)), _), _, else_exp) -> ok (); else_exp

    (* We only propagate lets in the simple case where we know that
       the id will have the inferred type of the argument. For more
       complex let bindings trying to propagate them may result in
       type errors due to how type variables are bound by let bindings
       *)
    | E_let (LB_aux (LB_val (P_aux (P_id id, _), bind), _), exp) when is_constant bind ->
       ok ();
       subst id bind exp

    | _ -> E_aux (e_aux, annot)
  in
  let rw_exp = {
      id_exp_alg with
      e_aux = (fun (e_aux, annot) -> rw_funcall e_aux annot)
    } in
  let rw_defs = { rewriters_base with rewrite_exp = (fun _ -> fold_exp rw_exp) } in
  let ast = rewrite_defs_base rw_defs ast in
  (* We keep iterating until we have no more re-writes to do *)
  if !rewrite_count > 0
  then rewrite_constant_function_calls' ast
  else ast

let rewrite_constant_function_calls ast =
  if !optimize_constant_fold then
    rewrite_constant_function_calls' ast
  else
    ast
