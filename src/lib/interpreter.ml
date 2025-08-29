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

let value_of_lit (L_aux (l_aux, _)) =
  match l_aux with
  | L_unit -> V_unit
  | L_zero -> V_bit B0
  | L_one -> V_bit B1
  | L_true -> V_bool true
  | L_false -> V_bool false
  | L_string str -> V_string str
  | L_num n -> V_int n
  | L_hex str ->
      Util.string_to_list str |> List.map (fun c -> List.map (fun b -> V_bit b) (Sail_lib.hex_char c)) |> List.concat
      |> fun v -> V_vector v
  | L_bin str -> Util.string_to_list str |> List.map (fun c -> V_bit (Sail_lib.bin_char c)) |> fun v -> V_vector v
  | L_real str -> begin
      match Util.split_on_char '.' str with
      | [whole; frac] ->
          let whole = Rational.of_big_int (Big_int.of_string whole) in
          let frac =
            Rational.div
              (Rational.of_big_int (Big_int.of_string frac))
              (Rational.of_int (Util.power 10 (String.length frac)))
          in
          V_real (Rational.add whole frac)
      | _ -> failwith "could not parse real literal"
    end
  | L_undef -> failwith "value_of_lit of undefined"

let is_value = function E_aux (E_internal_value _, _) -> true | _ -> false

let is_true = function E_aux (E_internal_value (V_bool b), annot) -> b | _ -> false

let is_false = function E_aux (E_internal_value (V_bool b), _) -> not b | _ -> false

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

(**************************************************************************)
(* 1. Interpreter Monad                                                   *)
(**************************************************************************)

type return_value = Return_ok of value | Return_exception of value

module Monad = struct
  (* when changing effect arms remember to also update effect_request type below *)
  type 'a response =
    | Early_return of value
    | Exception of value
    | Assertion_failed of string
    | Call of id * value list * (return_value -> 'a)
    | Fail of string
    | Read_reg of string * (value -> 'a)
    | Write_reg of string * value * (unit -> 'a)
    | Get_primop of string * ((value list -> value) -> 'a)
    | Get_local of string * (value -> 'a)
    | Put_local of string * value * (unit -> 'a)

  and 'a t = Pure of 'a | Yield of 'a t response

  let map_response f = function
    | Early_return v -> Early_return v
    | Exception v -> Exception v
    | Assertion_failed str -> Assertion_failed str
    | Call (id, vals, cont) -> Call (id, vals, fun v -> f (cont v))
    | Fail s -> Fail s
    | Read_reg (name, cont) -> Read_reg (name, fun v -> f (cont v))
    | Write_reg (name, v, cont) -> Write_reg (name, v, fun () -> f (cont ()))
    | Get_primop (name, cont) -> Get_primop (name, fun op -> f (cont op))
    | Get_local (name, cont) -> Get_local (name, fun v -> f (cont v))
    | Put_local (name, v, cont) -> Put_local (name, v, fun () -> f (cont ()))

  let rec liftM f = function Pure x -> Pure (f x) | Yield g -> Yield (map_response (liftM f) g)

  let ( let+ ) = liftM

  let return x = Pure x

  let rec bind m f = match m with Pure x -> f x | Yield m -> Yield (map_response (fun m -> bind m f) m)

  let ( >>= ) m f = bind m f

  let ( let* ) = bind

  let ( >> ) m1 m2 = bind m1 (function () -> m2)

  (* Support for interpreting exceptions *)

  let catch m =
    match m with
    | Pure x -> Pure (Ok x)
    | Yield (Exception v) -> Pure (Error v)
    | Yield resp -> Yield (map_response (fun m -> liftM (fun r -> Ok r) m) resp)

  let throw v = Yield (Exception v)

  let call f args = Yield (Call (f, args, fun v -> Pure v))

  let read_reg name = Yield (Read_reg (name, fun v -> Pure v))

  let write_reg name v = Yield (Write_reg (name, v, fun () -> Pure ()))

  let fail s = Yield (Fail s)

  let get_primop name = Yield (Get_primop (name, fun op -> Pure op))

  let get_local name = Yield (Get_local (name, fun v -> Pure v))

  let put_local name v = Yield (Put_local (name, v, fun () -> Pure ()))

  let early_return v = Yield (Early_return v)

  let assertion_failed msg = Yield (Assertion_failed msg)

  let expect_ok ~error = function Ok v -> Pure v | Error e -> Yield (Fail (error e))

  let expect_some ~none = function Some v -> Pure v | None -> Yield (Fail none)
end

open Monad

let letbind_pat_ids (LB_aux (LB_val (pat, _), _)) = pat_ids pat

let subst id value exp = Ast_util.subst id (exp_of_value value) exp

(**************************************************************************)
(* 2. Expression Evaluation                                               *)
(**************************************************************************)

let unit_exp = E_lit (L_aux (L_unit, Parse_ast.Unknown))

let is_value_fexp (FE_aux (FE_fexp (id, exp), _)) = is_value exp
let value_of_fexp (FE_aux (FE_fexp (id, exp), _)) = (string_of_id id, value_of_exp exp)

let rec build_letchain id lbs (E_aux (_, annot) as exp) =
  match lbs with
  | [] -> exp
  | lb :: lbs when IdSet.mem id (letbind_pat_ids lb) ->
      let exp = E_aux (E_let (lb, exp), annot) in
      build_letchain id lbs exp
  | _ :: lbs -> build_letchain id lbs exp

let is_interpreter_extern id env =
  let open Type_check in
  Env.is_extern id env "interpreter"

let get_interpreter_extern id env =
  let open Type_check in
  Env.get_extern id env "interpreter"

type partial_binding = Complete_binding of value | Partial_binding of (value * Big_int.num * Big_int.num) list

let combine _ v1 v2 =
  match (v1, v2) with
  | None, None -> None
  | Some v1, None -> Some v1
  | None, Some v2 -> Some v2
  | Some (Partial_binding p1), Some (Partial_binding p2) -> Some (Partial_binding (p1 @ p2))
  | Some (Complete_binding _), Some (Complete_binding _) -> failwith "Tried to bind same identifier twice!"
  | Some _, Some _ -> failwith "Tried to mix partial and complete binding!"

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

let complete_bindings =
  Bindings.map (function
    | Complete_binding v -> v
    | Partial_binding ((v1, n1, m1) :: partial_values) ->
        let max, min =
          List.fold_left
            (fun (max, min) (_, n, m) -> (Big_int.max max (Big_int.max n m), Big_int.min min (Big_int.min n m)))
            (n1, m1) partial_values
        in
        let len = Big_int.sub (Big_int.succ max) min in
        List.fold_left
          (fun bv (slice, n, m) -> value_update_subrange [bv; V_int n; V_int m; slice])
          (value_zeros [V_int len]) ((v1, n1, m1) :: partial_values)
    | Partial_binding [] -> Reporting.unreachable Parse_ast.Unknown __POS__ "Empty partial binding set"
    )

let rec split_list_exact acc ns xs =
  match (ns, xs) with
  | [], [] -> Some []
  | [], _ -> None
  | n :: ns, _ when Big_int.equal n Big_int.zero -> (
      match split_list_exact [] ns xs with Some split -> Some (List.rev acc :: split) | None -> None
    )
  | n :: ns, x :: xs -> split_list_exact (x :: acc) (Big_int.pred n :: ns) xs
  | _, [] -> None

let lexp_vector_concat_widths env lexps =
  let open Type_check in
  let get_length lexp =
    let l = lexp_loc lexp in
    let typ = typ_of_lexp lexp in
    match destruct_vector env typ with
    | Some (nexp, _) -> Option.to_result ~none:l (solve_unique env nexp)
    | None -> (
        match destruct_bitvector env typ with
        | Some nexp -> Option.to_result ~none:l (solve_unique env nexp)
        | None -> Error l
      )
  in
  Util.result_all (List.map get_length lexps)

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

let rec adapt env = function
  | Interpret.Monad.Pure exp -> Pure exp
  | Interpret.Monad.Early_return v -> Yield (Early_return v)
  | Interpret.Monad.Exception v -> Yield (Exception v)
  | Interpret.Monad.Match_failure l -> fail "Pattern match failure"
  | Interpret.Monad.Assertion_failed s -> Yield (Assertion_failed s)
  | Interpret.Monad.Read_var (place, cont) -> read_var env place cont
  | Interpret.Monad.Write_var (place, value, cont) -> write_var env place value cont
  | Interpret.Monad.Call (id, args, cont) ->
      if Type_check.Env.is_union_constructor id env then
        adapt env (cont (Interpret.Return_ok (V_ctor (string_of_id id, args))))
      else if is_interpreter_extern id env then (
        let extern = get_interpreter_extern id env in
        if extern = "reg_deref" then (
          let regname = coerce_ref (List.hd args) in
          let* v = read_reg regname in
          adapt env (cont (Interpret.Return_ok v))
        )
        else
          get_primop extern >>= fun op ->
          try adapt env (cont (Interpret.Return_ok (op args)))
          with _ as exc -> fail ("Exception calling primop '" ^ extern ^ "': " ^ Printexc.to_string exc)
      )
      else
        Yield
          (Call
             ( id,
               args,
               function
               | Return_ok v -> adapt env (cont (Interpret.Return_ok v))
               | Return_exception v -> adapt env (cont (Interpret.Return_exception v))
             )
          )
  | Interpret.Monad.Get_undefined (typ, cont) ->
      let undef_exp = Ast_util.undefined_of_typ false Parse_ast.Unknown (fun _ -> empty_uannot) typ in
      let undef_exp = Type_check.check_exp env undef_exp typ in
      return undef_exp
  | Interpret.Monad.Runtime_type_error l -> Reporting.unreachable l __POS__ "Runtime type error in interpreter"

and read_var env place cont =
  let open Interpret in
  match place with
  | PL_id (name, var_type) -> (
      match var_type with
      | Var_register -> Yield (Read_reg (string_of_id name, fun v -> adapt env (cont v)))
      | Var_local -> Yield (Get_local (string_of_id name, fun v -> adapt env (cont v)))
    )
  | PL_register name -> Yield (Read_reg (name, fun v -> adapt env (cont v)))
  | _ -> failwith "Unsupported read"

and write_var env place value cont =
  let open Interpret in
  match place with
  | PL_id (name, var_type) -> (
      match var_type with
      | Var_register -> Yield (Write_reg (string_of_id name, value, fun () -> adapt env (cont ())))
      | Var_local -> Yield (Put_local (string_of_id name, value, fun () -> adapt env (cont ())))
    )
  | PL_register name -> Yield (Write_reg (name, value, fun () -> adapt env (cont ())))
  | _ -> failwith "Unsupported write"

let step env exp = adapt env (RocqSemantics.step exp)

let rec pattern_match env (P_aux (p_aux, (l, _))) value =
  match p_aux with
  | P_lit lit -> (eq_value (value_of_lit lit) value, Bindings.empty)
  | P_wild -> (true, Bindings.empty)
  | P_or (pat1, pat2) ->
      let m1, b1 = pattern_match env pat1 value in
      let m2, b2 = pattern_match env pat2 value in
      (* todo: maybe add assertion that bindings are consistent or empty? *)
      (m1 || m2, Bindings.merge combine b1 b2)
  | P_not pat ->
      let m, b = pattern_match env pat value in
      (* todo: maybe add assertion that binding is empty *)
      (not m, b)
  | P_as (pat, id) ->
      let matched, bindings = pattern_match env pat value in
      (matched, Bindings.add id (Complete_binding value) bindings)
  | P_typ (_, pat) -> pattern_match env pat value
  | P_id id ->
      let open Type_check in
      begin
        match Env.lookup_id id env with
        | Enum _ ->
            if is_member value && string_of_id id = coerce_member value then (true, Bindings.empty)
            else (false, Bindings.empty)
        | _ -> (true, Bindings.singleton id (Complete_binding value))
      end
  | P_vector_subrange (id, n, m) -> (true, Bindings.singleton id (Partial_binding [(value, n, m)]))
  | P_var (pat, _) -> pattern_match env pat value
  | P_app (id, pats) ->
      let ctor, vals = coerce_ctor value in
      if Id.compare id (mk_id ctor) = 0 then (
        let matches = List.map2 (pattern_match env) pats vals in
        (List.for_all fst matches, List.fold_left (Bindings.merge combine) Bindings.empty (List.map snd matches))
      )
      else (false, Bindings.empty)
  | P_vector pats ->
      let matches = List.map2 (pattern_match env) pats (coerce_gv value) in
      (List.for_all fst matches, List.fold_left (Bindings.merge combine) Bindings.empty (List.map snd matches))
  | P_vector_concat [] -> (eq_value (V_vector []) value, Bindings.empty)
  | P_vector_concat (pat :: pats) ->
      (* We have to use the annotation on each member of the
         vector_concat pattern to figure out its length. Due to the
         recursive call that has an empty_tannot we must not use the
         annotation in the whole vector_concat pattern. *)
      let open Type_check in
      let vector_concat_match n =
        let init, rest =
          (Util.take (Big_int.to_int n) (coerce_gv value), Util.drop (Big_int.to_int n) (coerce_gv value))
        in
        let init_match, init_bind = pattern_match env pat (V_vector init) in
        let rest_match, rest_bind =
          pattern_match env (P_aux (P_vector_concat pats, (l, empty_tannot))) (V_vector rest)
        in
        (init_match && rest_match, Bindings.merge combine init_bind rest_bind)
      in
      begin
        match destruct_vector (env_of_pat pat) (typ_of_pat pat) with
        | Some (Nexp_aux (Nexp_constant n, _), _) -> vector_concat_match n
        | None -> begin
            match destruct_bitvector (env_of_pat pat) (typ_of_pat pat) with
            | Some (Nexp_aux (Nexp_constant n, _)) -> vector_concat_match n
            | _ ->
                failwith
                  ("Bad bitvector annotation for bitvector concatenation pattern "
                  ^ string_of_typ (Type_check.typ_of_pat pat)
                  )
          end
        | _ ->
            failwith
              ("Bad vector annotation for vector concatenation pattern " ^ string_of_typ (Type_check.typ_of_pat pat))
      end
  | P_tuple [pat] -> pattern_match env pat value
  | P_tuple pats | P_list pats ->
      let values = coerce_listlike value in
      if List.compare_lengths pats values = 0 then (
        let matches = List.map2 (pattern_match env) pats values in
        (List.for_all fst matches, List.fold_left (Bindings.merge combine) Bindings.empty (List.map snd matches))
      )
      else (false, Bindings.empty)
  | P_cons (hd_pat, tl_pat) -> begin
      match coerce_cons value with
      | Some (hd_value, tl_values) ->
          let hd_match, hd_bind = pattern_match env hd_pat hd_value in
          let tl_match, tl_bind = pattern_match env tl_pat (V_list tl_values) in
          (hd_match && tl_match, Bindings.merge combine hd_bind tl_bind)
      | None -> (false, Bindings.empty)
    end
  | P_struct (_, fpats, _) ->
      List.fold_left
        (fun (matches, binds) (field, pat) ->
          match StringMap.find_opt (string_of_id field) (coerce_record value) with
          | Some value ->
              let field_match, field_binds = pattern_match env pat value in
              (matches && field_match, Bindings.merge combine field_binds binds)
          | None -> (false, Bindings.empty)
        )
        (true, Bindings.empty) fpats
  | P_string_append _ -> assert false (* TODO *)

let exp_of_fundef (FD_aux (FD_function (_, _, funcls), annot)) value =
  let pexp_of_funcl (FCL_aux (FCL_funcl (_, pexp), _)) = pexp in
  E_aux (E_match (exp_of_value value, List.map pexp_of_funcl funcls), annot)

let rec defs_letbinds defs =
  match defs with
  | [] -> []
  | DEF_aux (DEF_let lb, _) :: defs -> lb :: defs_letbinds defs
  | _ :: defs -> defs_letbinds defs

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
      * (string Lazy.t * lstate * (return_value -> Type_check.tannot exp Monad.t)) list
  | Break of frame
  | Effect_request of
      string Lazy.t
      * state
      * (string Lazy.t * lstate * (return_value -> Type_check.tannot exp Monad.t)) list
      * effect_request
  | Fail of
      string Lazy.t
      * state
      * Type_check.tannot exp Monad.t
      * (string Lazy.t * lstate * (return_value -> Type_check.tannot exp Monad.t)) list
      * string

and effect_request =
  | Read_reg of string * (value -> state -> frame)
  | Write_reg of string * value * (unit -> state -> frame)
  | Outcome of id * value list * (return_value -> Type_check.tannot exp Monad.t)

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
      | Yield (Call (id, vals, cont)), _ when string_of_id id = "break" -> begin
          let arg = if List.length vals != 1 then tuple_value vals else List.hd vals in
          try
            let body = exp_of_fundef (Bindings.find id gstate.fundefs) arg in
            Break (Step (lazy (string_of_exp body), (initial_lstate, gstate), return body, (out, lstate, cont) :: stack))
          with Not_found -> Step (out, state, fail ("Fundef not found: " ^ string_of_id id), stack)
        end
      | Yield (Call (id, vals, cont)), _ when Type_check.Env.is_outcome id gstate.typecheck_env -> begin
          Effect_request (out, state, stack, Outcome (id, vals, cont))
        end
      | Yield (Call (id, vals, cont)), _ -> begin
          let arg = if List.length vals != 1 then tuple_value vals else List.hd vals in
          try
            let body = exp_of_fundef (Bindings.find id gstate.fundefs) arg in
            Step (lazy (string_of_exp body), (initial_lstate, gstate), return body, (out, lstate, cont) :: stack)
          with Not_found -> Step (out, state, fail ("Fundef not found: " ^ string_of_id id), stack)
        end
      | Yield (Read_reg (name, cont)), _ ->
          Effect_request
            (out, state, stack, Read_reg (name, fun v state' -> eval_frame' (Step (out, state', cont v, stack))))
      | Yield (Write_reg (name, v, cont)), _ ->
          Effect_request
            (out, state, stack, Write_reg (name, v, fun () state' -> eval_frame' (Step (out, state', cont (), stack))))
      | Yield (Get_primop (name, cont)), _ -> begin
          try
            (* If we are in the toplevel interactive interpreter allow the set of primops to be changed dynamically *)
            let op = StringMap.find name (if !Interactive.opt_interactive then !Value.primops else gstate.primops) in
            eval_frame' (Step (out, state, cont op, stack))
          with Not_found -> eval_frame' (Step (out, state, fail ("No such primop: " ^ name), stack))
        end
      | Yield (Get_local (name, cont)), _ -> begin
          try eval_frame' (Step (out, state, cont (read_variable (mk_id name) lstate gstate), stack))
          with Not_found -> eval_frame' (Step (out, state, fail ("Local not found: " ^ name), stack))
        end
      | Yield (Put_local (name, v, cont)), _ ->
          let state' = ({ locals = Bindings.add (mk_id name) v lstate.locals }, gstate) in
          eval_frame' (Step (out, state', cont (), stack))
      | Yield (Early_return v), [] -> Done (state, v)
      | Yield (Early_return v), head :: stack' ->
          Step (stack_string head, (stack_state head, gstate), stack_cont head (Return_ok v), stack')
      | Yield (Assertion_failed msg), _ | Yield (Fail msg), _ -> Fail (out, state, m, stack, msg)
      | Yield (Exception v), [] -> Fail (out, state, m, stack, "Uncaught exception: " ^ string_of_value v)
      | Yield (Exception v), head :: stack' ->
          Step (stack_string head, (stack_state head, gstate), stack_cont head (Return_exception v), stack')
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
          Step (lazy "", (initial_lstate, gstate), return body, (out, lstate, cont) :: stack)
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

let eval_exp state exp = run_frame (Step (lazy "", state, return exp, []))

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
            (* prerr_endline ("EVAL " ^ string_of_exp exp); *)
            let evaluated = eval_exp (initial_lstate, gstate) exp in
            (* prerr_endline ("GOT " ^ string_of_value evaluated); *)
            { gstate with registers = Bindings.add id evaluated gstate.registers }
      end
    | DEF_aux (DEF_let (LB_aux (LB_val (pat, exp), annot)), def_annot) ->
        let evaluated = eval_exp (initial_lstate, gstate) exp in
        let _, bindings = pattern_match def_annot.env pat evaluated in
        {
          gstate with
          letbinds = Bindings.fold (fun id v lbs -> Bindings.add id v lbs) (complete_bindings bindings) gstate.letbinds;
        }
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
