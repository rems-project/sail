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
(*  SPDX-License-Identifier: BSD-2-Clause                                   *)
(****************************************************************************)

open Ast
open Ast_defs
open Ast_util
open Value_type
open Value
module Document = Pretty_print_sail.Document

module Printer = Pretty_print_sail.Printer (struct
  let insert_braces = false
  let resugar = false
  let hide_attributes = true
end)

type gstate = {
  registers : value Bindings.t;
  allow_registers : bool; (* For some uses we want to forbid touching any registers. *)
  primops : (value list -> value) StringMap.t;
  letbinds : value Bindings.t;
  fundefs : Type_check.tannot fundef Bindings.t;
  typecheck_env : Type_check.Env.t;
}

type lstate = { locals : value Bindings.t }

type state = lstate * gstate

let is_value = function E_aux (E_internal_value _, _) -> true | _ -> false

let exp_of_value v = E_aux (E_internal_value v, (Parse_ast.Unknown, Type_check.empty_tannot))
let value_of_exp = function E_aux (E_internal_value v, _) -> v | _ -> failwith "value_of_exp coerction failed"

let fallthrough =
  let open Type_check in
  let open Type_error in
  try
    let env = initial_env |> Env.add_scattered_variant (mk_id "exception") (mk_typquant []) in
    check_case env exc_typ
      (mk_pexp (Pat_exp (mk_pat (P_id (mk_id "exn")), mk_exp (E_throw (mk_exp (E_id (mk_id "exn")))))))
      unit_typ
  with Type_error (l, err) -> Reporting.unreachable l __POS__ (fst (string_of_type_error err))

type return_value = Interpret.return_value

let is_interpreter_extern id env =
  let open Type_check in
  Env.is_extern id env "interpreter"

let get_interpreter_extern id env =
  let open Type_check in
  Env.get_extern id env "interpreter"

let complete_value = function
  | ((v1, n1), m1) :: partial_values ->
      let max, min =
        List.fold_left
          (fun (max, min) ((_, n), m) -> (Big_int.max max (Big_int.max n m), Big_int.min min (Big_int.min n m)))
          (n1, m1) partial_values
      in
      let len = Big_int.sub (Big_int.succ max) min in
      List.fold_left
        (fun bv ((slice, n), m) -> value_update_subrange [bv; V_int n; V_int m; slice])
        (value_zeros [V_int len])
        (((v1, n1), m1) :: partial_values)
  | [] -> Reporting.unreachable Parse_ast.Unknown __POS__ "Empty partial binding set"

let rec to_rocq_nat n =
  match Big_int.compare n Big_int.zero with
  | -1 -> raise (Reporting.err_unreachable Parse_ast.Unknown __POS__ "Invalid integer to rocq nat conversion")
  | 0 -> Datatypes.O
  | _ -> Datatypes.S (to_rocq_nat (Big_int.pred n))

module RocqSemantics = Interpret.Semantics (struct
  type tannot = Type_check.tannot

  let get_type tannot =
    let typ = Type_check.typ_of_tannot tannot in
    typ

  let get_id_type tannot id =
    let env = Type_check.env_of_tannot tannot in
    match Type_check.Env.lookup_id id env with
    | Register _ -> Interpret.Global_register
    | Local _ | Unbound _ -> Interpret.Local_variable
    | Enum _ -> Interpret.Enum_member

  let get_split tannot =
    let env = Type_check.env_of_tannot tannot in
    let typ = Type_check.typ_of_tannot tannot in
    match Type_check.destruct_vector env typ with
    | Some (Nexp_aux (Nexp_constant n, _), _) -> Interpret.Split (to_rocq_nat n)
    | _ -> (
        match Type_check.destruct_bitvector env typ with
        | Some (Nexp_aux (Nexp_constant n, _)) -> Interpret.Split (to_rocq_nat n)
        | _ -> Interpret.No_split
      )

  let id_equal x y = Id.compare x y = 0

  let num_equal x y = Big_int.compare x y = 0

  let string_equal x y = String.compare x y = 0

  let rational_equal x y = Rational.equal x y

  let id_equal_string x s = string_of_id x = s

  let string_of_id = string_of_id

  let bits_of_hex_string = Sail_lib.bits_of_string

  let bits_of_bin_string s = List.map Sail_lib.bin_char (Sail_lib.list_of_string s)

  let rational_of_string = Sail_lib.real_of_string

  let fallthrough = fallthrough

  let value_gt x y = value_gt [x; y]

  let value_lt x y = value_lt [x; y]

  let value_add_int x y = value_add_int [x; y]

  let value_sub_int x y = value_sub_int [x; y]

  let complete_value vs = complete_value vs

  let is_and_bool id = String.equal (string_of_id id) "and_bool"

  let is_or_bool id = String.equal (string_of_id id) "or_bool"
end)

module Monad = Interpret.Monad

let step env exp = RocqSemantics.step exp

let pattern_match pat value = RocqSemantics.pattern_match pat value

let complete_bindings bindings = RocqSemantics.complete_bindings bindings

let exp_of_fundef (FD_aux (FD_function (_, _, funcls), annot)) value =
  let pexp_of_funcl (FCL_aux (FCL_funcl (_, pexp), _)) = pexp in
  E_aux (E_match (exp_of_value value, List.map pexp_of_funcl funcls), annot)

let initial_lstate = { locals = Bindings.empty }

let stack_cont (_, _, cont) = cont
let stack_string (str, _, _) = str
let stack_state (_, lstate, _) = lstate

type frame =
  | Done of state * value
  | Step of
      string Lazy.t
      * state
      * Type_check.tannot exp Monad.t
      * (string Lazy.t * lstate * (Interpret.return_value -> Type_check.tannot exp Monad.t)) list
  | Break of frame
  | Effect_request of
      string Lazy.t
      * state
      * (string Lazy.t * lstate * (Interpret.return_value -> Type_check.tannot exp Monad.t)) list
      * effect_request
  | Fail of
      string Lazy.t
      * state
      * Type_check.tannot exp Monad.t
      * (string Lazy.t * lstate * (Interpret.return_value -> Type_check.tannot exp Monad.t)) list
      * string

and effect_request =
  | Read_reg of string * (value -> state -> frame)
  | Write_reg of string * value * (unit -> state -> frame)
  | Outcome of id * value list * (Interpret.return_value -> Type_check.tannot exp Monad.t)

let read_variable id lstate gstate =
  match Bindings.find_opt id lstate.locals with
  | Some v -> v
  | None -> (
      match Bindings.find_opt id gstate.letbinds with Some v -> v | None -> raise Not_found
    )

let rec eval_frame' = function
  | Done (state, v) -> Done (state, v)
  | Fail (out, state, m, stack, msg) -> Fail (out, state, m, stack, msg)
  | Break frame -> Break frame
  | Effect_request (out, state, stack, eff) -> Effect_request (out, state, stack, eff)
  | Step (out, state, m, stack) -> (
      let lstate, gstate = state in
      match (m, stack) with
      | Pure v, [] when is_value v -> Done (state, value_of_exp v)
      | Pure v, head :: stack' when is_value v ->
          Step (stack_string head, (stack_state head, gstate), stack_cont head (Return_ok (value_of_exp v)), stack')
      | Pure exp', _ ->
          let out' = lazy (Document.to_string (Printer.doc_exp (Type_check.strip_exp exp'))) in
          Step (out', state, step gstate.typecheck_env exp', stack)
      | Early_return v, [] -> Done (state, v)
      | Early_return v, head :: stack' ->
          Step (stack_string head, (stack_state head, gstate), stack_cont head (Return_ok v), stack')
      | Exception v, [] -> Fail (out, state, m, stack, "Uncaught exception: " ^ string_of_value v)
      | Exception v, head :: stack' ->
          Step (stack_string head, (stack_state head, gstate), stack_cont head (Return_exception v), stack')
      | Match_failure l, _ -> Fail (out, state, m, stack, "Pattern match failure at " ^ Reporting.short_loc_to_string l)
      | Runtime_type_error l, _ ->
          Fail (out, state, m, stack, "Runtime type error at " ^ Reporting.short_loc_to_string l)
      | Assertion_failed s, _ -> Fail (out, state, m, stack, "Assertion failed: " ^ s)
      | Call (id, args, cont), _ ->
          let env = gstate.typecheck_env in
          if Type_check.Env.is_outcome id env then Effect_request (out, state, stack, Outcome (id, args, cont))
          else if Type_check.Env.is_union_constructor id env then
            Step (lazy "", state, cont (Interpret.Return_ok (V_ctor (string_of_id id, args))), stack)
          else if is_interpreter_extern id env then (
            let extern = get_interpreter_extern id env in
            if extern = "reg_deref" then (
              let regname = coerce_ref (List.hd args) in
              Effect_request
                ( out,
                  state,
                  stack,
                  Read_reg
                    (regname, fun v state' -> eval_frame' (Step (out, state', cont (Interpret.Return_ok v), stack)))
                )
            )
            else (
              match
                StringMap.find_opt extern (if !Interactive.opt_interactive then !Value.primops else gstate.primops)
              with
              | Some op -> (
                  match
                    try Ok (op args)
                    with exn -> Error ("Exception calling primop '" ^ extern ^ "': " ^ Printexc.to_string exn)
                  with
                  | Ok v -> Step (lazy "", state, cont (Interpret.Return_ok v), stack)
                  | Error msg -> Fail (out, state, m, stack, msg)
                )
              | None -> Fail (out, state, m, stack, "No such primop: " ^ string_of_id id)
            )
          )
          else (
            let arg = if List.length args != 1 then tuple_value args else List.hd args in
            try
              let body = exp_of_fundef (Bindings.find id gstate.fundefs) arg in
              Step (lazy (string_of_exp body), (initial_lstate, gstate), Monad.pure body, (out, lstate, cont) :: stack)
            with Not_found -> Fail (out, state, m, stack, "Fundef not found: " ^ string_of_id id)
          )
      | Read_var (place, cont), _ -> (
          match place with
          | PL_id (name, var_type) -> (
              match var_type with
              | Var_register ->
                  Effect_request
                    ( out,
                      state,
                      stack,
                      Read_reg (string_of_id name, fun v state' -> eval_frame' (Step (out, state', cont v, stack)))
                    )
              | Var_local -> (
                  try eval_frame' (Step (out, state, cont (read_variable name lstate gstate), stack))
                  with Not_found -> Fail (out, state, m, stack, "Local not found: " ^ string_of_id name)
                )
            )
          | PL_register name ->
              Effect_request
                (out, state, stack, Read_reg (name, fun v state' -> eval_frame' (Step (out, state', cont v, stack))))
          | _ -> Fail (out, state, m, stack, "Unsupported read")
        )
      | Write_var (place, value, cont), _ -> (
          match place with
          | PL_id (name, var_type) -> (
              match var_type with
              | Var_register ->
                  Effect_request
                    ( out,
                      state,
                      stack,
                      Write_reg
                        (string_of_id name, value, fun () state' -> eval_frame' (Step (out, state', cont (), stack)))
                    )
              | Var_local ->
                  let state' = ({ locals = Bindings.add name value lstate.locals }, gstate) in
                  eval_frame' (Step (out, state', cont (), stack))
            )
          | PL_register name ->
              Effect_request
                ( out,
                  state,
                  stack,
                  Write_reg (name, value, fun () state' -> eval_frame' (Step (out, state', cont (), stack)))
                )
          | _ -> Fail (out, state, m, stack, "Unsupported write")
        )
      | Get_undefined (typ, cont), _ ->
          let undef_exp = Ast_util.undefined_of_typ false Parse_ast.Unknown (fun _ -> empty_uannot) typ in
          let undef_exp = Type_check.check_exp gstate.typecheck_env undef_exp typ in
          Step (lazy "", state, Monad.pure undef_exp, stack)
    )

let eval_frame frame =
  try eval_frame' frame with Type_error.Type_error (l, err) -> raise (Type_error.to_reporting_exn l err)

let default_effect_interp out state stack eff =
  let lstate, gstate = state in
  match eff with
  | Read_reg (name, cont) ->
      if gstate.allow_registers then (
        try cont (Bindings.find (mk_id name) gstate.registers) state
        with Not_found -> failwith ("Read of nonexistent register: " ^ name)
      )
      else failwith ("Register read disallowed by allow_registers setting: " ^ name)
  | Write_reg (name, v, cont) ->
      let id = mk_id name in
      if gstate.allow_registers then
        if Bindings.mem id gstate.registers then (
          let state' = (lstate, { gstate with registers = Bindings.add id v gstate.registers }) in
          cont () state'
        )
        else failwith ("Write of nonexistent register: " ^ name)
      else failwith ("Register write disallowed by allow_registers setting: " ^ name)
  | Outcome (id, vals, cont) -> (
      let arg = if List.length vals != 1 then tuple_value vals else List.hd vals in
      match Bindings.find_opt id gstate.fundefs with
      | Some fundef ->
          let body = exp_of_fundef fundef arg in
          Step (lazy "", (initial_lstate, gstate), Monad.pure body, (out, lstate, cont) :: stack)
      | None -> failwith ("Outcome implementation not found: " ^ string_of_id id)
    )

let effect_interp = ref default_effect_interp

let rec run_frame frame =
  match frame with
  | Done (state, v) -> v
  | Fail (_, _, _, _, msg) -> failwith ("run_frame got Fail: " ^ msg)
  | Step (_, _, _, _) -> run_frame (eval_frame frame)
  | Break frame -> run_frame (eval_frame frame)
  | Effect_request (out, state, stack, eff) -> run_frame (!effect_interp out state stack eff)

let eval_exp state exp = run_frame (Step (lazy "", state, Monad.pure exp, []))

let initial_gstate primops defs env =
  {
    registers = Bindings.empty;
    allow_registers = true;
    primops;
    letbinds = Bindings.empty;
    fundefs = Bindings.empty;
    typecheck_env = env;
  }

let rec initialize_registers allow_registers undef_registers gstate =
  let process_def = function
    | DEF_aux (DEF_register (DEC_aux (DEC_reg (typ, id, opt_exp), annot)), _) when allow_registers -> begin
        match opt_exp with
        | None when undef_registers ->
            let env = Type_check.env_of_annot annot in
            let typ = Type_check.Env.expand_synonyms env typ in
            let exp = mk_exp (E_typ (typ, mk_exp (E_lit (mk_lit L_undef)))) in
            let exp = Type_check.check_exp env exp typ in
            { gstate with registers = Bindings.add id (eval_exp (initial_lstate, gstate) exp) gstate.registers }
        | None -> gstate
        | Some exp ->
            let evaluated = eval_exp (initial_lstate, gstate) exp in
            { gstate with registers = Bindings.add id evaluated gstate.registers }
      end
    | DEF_aux (DEF_let (LB_aux (LB_val (pat, exp), annot)), def_annot) -> (
        try
          let evaluated = eval_exp (initial_lstate, gstate) exp in
          let _, bindings = pattern_match pat evaluated in
          {
            gstate with
            letbinds =
              List.fold_left (fun lbs (id, v) -> Bindings.add id v lbs) gstate.letbinds (complete_bindings bindings);
          }
        with _ -> gstate
      )
    | _ -> gstate
  in
  function def :: defs -> initialize_registers allow_registers undef_registers (process_def def) defs | [] -> gstate

let initial_state ?(registers = true) ?(undef_registers = true) ast env primops =
  let gstate = initial_gstate primops ast.defs env in
  let add_function gstate = function
    | DEF_aux (DEF_fundef fdef, _) -> { gstate with fundefs = Bindings.add (id_of_fundef fdef) fdef gstate.fundefs }
    | _ -> gstate
  in
  let gstate = List.fold_left add_function gstate ast.defs in
  let gstate = { (initialize_registers registers undef_registers gstate ast.defs) with allow_registers = registers } in
  (initial_lstate, gstate)
