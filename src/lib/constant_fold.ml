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
open Type_check
open Rewriter

module StringMap = Map.Make (String)

(* Flag controls whether any constant folding will occur.
   false = no folding, true = perform constant folding. *)
let optimize_constant_fold = ref false

let rec fexp_of_ctor (field, value) = FE_aux (FE_fexp (mk_id field, exp_of_value value), no_annot)

(* The interpreter will return a value for each folded expression, so
   we must convert that back to expression to re-insert it in the AST
*)
and exp_of_value =
  let open Value in
  function
  | V_int n -> mk_lit_exp (L_num n)
  | V_bit Sail_lib.B0 -> mk_lit_exp L_zero
  | V_bit Sail_lib.B1 -> mk_lit_exp L_one
  | V_bool true -> mk_lit_exp L_true
  | V_bool false -> mk_lit_exp L_false
  | V_string str -> mk_lit_exp (L_string str)
  | V_record ctors -> mk_exp (E_struct (List.map fexp_of_ctor (StringMap.bindings ctors)))
  | V_vector vs -> mk_exp (E_vector (List.map exp_of_value vs))
  | V_tuple vs -> mk_exp (E_tuple (List.map exp_of_value vs))
  | V_unit -> mk_lit_exp L_unit
  | V_attempted_read str -> mk_exp (E_id (mk_id str))
  | _ -> failwith "No expression for value"

(* A simple heuristic to avoid generating overly large literals. Note
   that we avoid traversing through every element of vectors and
   lists, so a list of large lists could still sneak through *)
let rec is_too_large =
  let open Value in
  function
  | V_int _ | V_bit _ | V_bool _ | V_string _ | V_unit | V_attempted_read _ | V_real _ | V_ref _ -> false
  | V_vector vs | V_tuple vs | V_list vs -> List.compare_length_with vs 256 > 0
  | V_record fields -> StringMap.exists (fun _ v -> is_too_large v) fields
  | V_ctor (_, vs) -> List.exists is_too_large vs

(* We want to avoid evaluating things like print statements at compile
   time, so we remove them from this list of primops we can use when
   constant folding. *)
let safe_primops =
  List.fold_left
    (fun m k -> StringMap.remove k m)
    !Value.primops
    [
      "print_endline";
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
      "Elf_loader.elf_tohost";
    ]

(** We can specify a list of identifiers that we want to remove from
   the final AST here. This is useful for removing tracing features in
   optimized builds, e.g. for booting an OS as fast as possible.

   Basically we just do this by mapping

   f(x, y, z) -> ()

   when f is in the list of identifiers to be mapped to unit. The
   advantage of doing it like this is if x, y, and z are
   computationally expensive then we remove them also. String
   concatentation is very expensive at runtime so this is something we
   really want when cutting out tracing features. Obviously it's
   important that they don't have any meaningful side effects, and
   that f does actually have type unit.
*)
let opt_fold_to_unit = ref []

let fold_to_unit id =
  let remove = !opt_fold_to_unit |> List.map mk_id |> List.fold_left (fun m id -> IdSet.add id m) IdSet.empty in
  IdSet.mem id remove

let rec is_constant (E_aux (e_aux, _) as exp) =
  match e_aux with
  | E_lit _ -> true
  | E_vector exps -> List.for_all is_constant exps
  | E_struct fexps -> List.for_all is_constant_fexp fexps
  | E_typ (_, exp) -> is_constant exp
  | E_tuple exps -> List.for_all is_constant exps
  | E_id id -> (
      match Env.lookup_id id (env_of exp) with Enum _ -> true | _ -> false
    )
  | _ -> false

and is_constant_fexp (FE_aux (FE_fexp (_, exp), _)) = is_constant exp

(* Wrapper around interpreter that repeatedly steps until done. *)
let rec run frame =
  match frame with
  | Interpreter.Done (state, v) -> v
  | Interpreter.Fail _ ->
      (* something went wrong, raise exception to abort constant folding *)
      assert false
  | Interpreter.Step (lazy_str, _, _, _) -> run (Interpreter.eval_frame frame)
  | Interpreter.Break frame -> run (Interpreter.eval_frame frame)
  | Interpreter.Effect_request (out, st, stack, Interpreter.Read_reg (reg, cont)) ->
      (* return a dummy value to read_reg requests which we handle above
         if an expression finally evals to it, but the interpreter
         will fail if it tries to actually use. See value.ml *)
      run (cont (Value.V_attempted_read reg) st)
  | Interpreter.Effect_request _ -> assert false (* effectful, raise exception to abort constant folding *)

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

let initial_state ast env = Interpreter.initial_state ~registers:false ast env safe_primops

type fixed = { registers : tannot exp Bindings.t; fields : tannot exp Bindings.t Bindings.t }

let no_fixed = { registers = Bindings.empty; fields = Bindings.empty }

let rw_exp fixed target ok not_ok istate =
  let evaluate e_aux annot =
    let initial_monad = Interpreter.return (E_aux (e_aux, annot)) in
    try
      begin
        let v = run (Interpreter.Step (lazy "", istate, initial_monad, [])) in
        if not (is_too_large v) then (
          let exp = exp_of_value v in
          try
            ok ();
            Type_check.check_exp (env_of_annot annot) exp (typ_of_annot annot)
          with Type_error.Type_error (l, err) ->
            (* A type error here would be unexpected, so don't ignore it! *)
            Reporting.warn "" l
              ("Type error when folding constants in "
              ^ string_of_exp (E_aux (e_aux, annot))
              ^ "\n" ^ Type_error.string_of_type_error err
              );
            not_ok ();
            E_aux (e_aux, annot)
        )
        else E_aux (e_aux, annot)
      end
    with
    (* Otherwise if anything goes wrong when trying to constant
       fold, just continue without optimising. *)
    | _ ->
      E_aux (e_aux, annot)
  in

  let rw_funcall e_aux annot =
    match e_aux with
    | E_app (id, args) when fold_to_unit id ->
        ok ();
        E_aux (E_lit (L_aux (L_unit, fst annot)), annot)
    | E_id id -> begin
        match Bindings.find_opt id fixed.registers with
        | Some exp ->
            ok ();
            exp
        | None -> E_aux (e_aux, annot)
      end
    | E_field (E_aux (E_id id, _), field) -> begin
        match Bindings.find_opt id fixed.fields with
        | Some fields -> begin
            match Bindings.find_opt field fields with
            | Some exp ->
                ok ();
                exp
            | None -> E_aux (e_aux, annot)
          end
        | None -> E_aux (e_aux, annot)
      end
    (* Short-circuit boolean operators with constants *)
    | E_app (id, [(E_aux (E_lit (L_aux (L_false, _)), _) as false_exp); _]) when string_of_id id = "and_bool" ->
        ok ();
        false_exp
    | E_app (id, [(E_aux (E_lit (L_aux (L_true, _)), _) as true_exp); _]) when string_of_id id = "or_bool" ->
        ok ();
        true_exp
    | E_app (id, args) when List.for_all is_constant args ->
        let env = env_of_annot annot in
        (* We want to fold all primitive operations, but avoid folding
           non-primitives that are defined in target-specific way. *)
        let is_primop =
          Env.is_extern id env "interpreter" && StringMap.mem (Env.get_extern id env "interpreter") safe_primops
        in
        if (not (Env.is_extern id env target)) || is_primop then evaluate e_aux annot else E_aux (e_aux, annot)
    | E_typ (typ, (E_aux (E_lit _, _) as lit)) ->
        ok ();
        lit
    | E_field (exp, id) when is_constant exp -> evaluate e_aux annot
    | E_if (E_aux (E_lit (L_aux (L_true, _)), _), then_exp, _) ->
        ok ();
        then_exp
    | E_if (E_aux (E_lit (L_aux (L_false, _)), _), _, else_exp) ->
        ok ();
        else_exp
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
  fold_exp { id_exp_alg with e_aux = (fun (e_aux, annot) -> rw_funcall e_aux annot) }

let rewrite_exp_once target = rw_exp no_fixed target (fun _ -> ()) (fun _ -> ())

let rec rewrite_constant_function_calls' fixed target ast =
  let rewrite_count = ref 0 in
  let ok () = incr rewrite_count in
  let not_ok () = decr rewrite_count in
  let istate = initial_state ast Type_check.initial_env in

  let rw_defs = { rewriters_base with rewrite_exp = (fun _ -> rw_exp fixed target ok not_ok istate) } in
  let ast = rewrite_ast_base rw_defs ast in
  (* We keep iterating until we have no more re-writes to do *)
  if !rewrite_count > 0 then rewrite_constant_function_calls' fixed target ast else ast

let rewrite_constant_function_calls fixed target ast =
  if !optimize_constant_fold then rewrite_constant_function_calls' fixed target ast else ast

type to_constant = Register of id * typ * tannot exp | Register_field of id * id * typ * tannot exp

let () =
  let open Interactive in
  let open Printf in
  let update_fixed fixed = function
    | Register (id, _, exp) -> { fixed with registers = Bindings.add id exp fixed.registers }
    | Register_field (id, field, _, exp) ->
        let prev_fields = match Bindings.find_opt id fixed.fields with Some f -> f | None -> Bindings.empty in
        let updated_fields = Bindings.add field exp prev_fields in
        { fixed with fields = Bindings.add id updated_fields fixed.fields }
  in

  ArgString
    ( "target",
      fun target ->
        ArgString
          ( "assignments",
            fun assignments ->
              Action
                (fun istate ->
                  let assignments = Str.split (Str.regexp " +") assignments in
                  let assignments =
                    List.map
                      (fun assignment ->
                        match String.split_on_char '=' assignment with
                        | [reg; value] -> begin
                            match String.split_on_char '.' reg with
                            | [reg; field] ->
                                let reg = mk_id reg in
                                let field = mk_id field in
                                begin
                                  match Env.lookup_id reg istate.env with
                                  | Register (Typ_aux (Typ_id rec_id, _)) ->
                                      let _, fields = Env.get_record rec_id istate.env in
                                      let typ =
                                        match List.find_opt (fun (typ, id) -> Id.compare id field = 0) fields with
                                        | Some (typ, _) -> typ
                                        | None ->
                                            failwith
                                              (sprintf "Register %s does not have a field %s" (string_of_id reg)
                                                 (string_of_id field)
                                              )
                                      in
                                      let exp = Initial_check.exp_of_string value in
                                      let exp = check_exp istate.env exp typ in
                                      Register_field (reg, field, typ, exp)
                                  | _ ->
                                      failwith
                                        (sprintf "Register %s is not defined as a record in the current environment"
                                           (string_of_id reg)
                                        )
                                end
                            | _ ->
                                let reg = mk_id reg in
                                begin
                                  match Env.lookup_id reg istate.env with
                                  | Register typ ->
                                      let exp = Initial_check.exp_of_string value in
                                      let exp = check_exp istate.env exp typ in
                                      Register (reg, typ, exp)
                                  | _ ->
                                      failwith
                                        (sprintf "Register %s is not defined in the current environment"
                                           (string_of_id reg)
                                        )
                                end
                          end
                        | _ -> failwith (sprintf "Could not parse '%s' as an assignment <register>=<value>" assignment)
                      )
                      assignments
                  in
                  let assignments = List.fold_left update_fixed no_fixed assignments in

                  { istate with ast = rewrite_constant_function_calls' assignments target istate.ast }
                )
          )
    )
  |> register_command ~name:"fix_registers"
       ~help:
         "Fix the value of specified registers, specified as a list of <register>=<value>. Can also fix a specific \
          register field as <register>.<field>=<value>. Note that this is not used to set registers normally, but \
          instead fixes their value such that the constant folding rewrite (which is subsequently invoked by this \
          command) will replace register reads with the fixed values. Requires a target (c, lem, etc.), as the set of \
          functions that can be constant folded can differ on a per-target basis."
