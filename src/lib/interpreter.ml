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
open Value

type gstate = {
  registers : value Bindings.t;
  allow_registers : bool; (* For some uses we want to forbid touching any registers. *)
  primops : (value list -> value) StringMap.t;
  letbinds : Type_check.tannot letbind list;
  fundefs : Type_check.tannot fundef Bindings.t;
  last_write_ea : (value * value * value) option;
  typecheck_env : Type_check.Env.t;
}

type lstate = { locals : value Bindings.t }

type state = lstate * gstate

let value_of_lit (L_aux (l_aux, _)) =
  match l_aux with
  | L_unit -> V_unit
  | L_zero -> V_bit Sail_lib.B0
  | L_one -> V_bit Sail_lib.B1
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
  with Type_error (l, err) -> Reporting.unreachable l __POS__ (string_of_type_error err)

(**************************************************************************)
(* 1. Interpreter Monad                                                   *)
(**************************************************************************)

type return_value = Return_ok of value | Return_exception of value

(* when changing effect arms remember to also update effect_request type below *)
type 'a response =
  | Early_return of value
  | Exception of value
  | Assertion_failed of string
  | Call of id * value list * (return_value -> 'a)
  | Fail of string
  | Read_mem of (* read_kind : *) value * (* address : *) value * (* length : *) value * (value -> 'a)
  | Write_ea of (* write_kind : *) value * (* address : *) value * (* length : *) value * (unit -> 'a)
  | Excl_res of (bool -> 'a)
  | Write_mem of
      (* write_kind : *) value * (* address : *) value * (* length : *) value * (* value : *) value * (bool -> 'a)
  | Barrier of (* barrier_kind : *) value * (unit -> 'a)
  | Read_reg of string * (value -> 'a)
  | Write_reg of string * value * (unit -> 'a)
  | Get_primop of string * ((value list -> value) -> 'a)
  | Get_local of string * (value -> 'a)
  | Put_local of string * value * (unit -> 'a)
  | Get_global_letbinds of (Type_check.tannot letbind list -> 'a)

and 'a monad = Pure of 'a | Yield of 'a monad response

let map_response f = function
  | Early_return v -> Early_return v
  | Exception v -> Exception v
  | Assertion_failed str -> Assertion_failed str
  | Call (id, vals, cont) -> Call (id, vals, fun v -> f (cont v))
  | Fail s -> Fail s
  | Read_mem (rk, addr, len, cont) -> Read_mem (rk, addr, len, fun v -> f (cont v))
  | Write_ea (wk, addr, len, cont) -> Write_ea (wk, addr, len, fun () -> f (cont ()))
  | Excl_res cont -> Excl_res (fun b -> f (cont b))
  | Write_mem (wk, addr, len, v, cont) -> Write_mem (wk, addr, len, v, fun b -> f (cont b))
  | Barrier (bk, cont) -> Barrier (bk, fun () -> f (cont ()))
  | Read_reg (name, cont) -> Read_reg (name, fun v -> f (cont v))
  | Write_reg (name, v, cont) -> Write_reg (name, v, fun () -> f (cont ()))
  | Get_primop (name, cont) -> Get_primop (name, fun op -> f (cont op))
  | Get_local (name, cont) -> Get_local (name, fun v -> f (cont v))
  | Put_local (name, v, cont) -> Put_local (name, v, fun () -> f (cont ()))
  | Get_global_letbinds cont -> Get_global_letbinds (fun lbs -> f (cont lbs))

let rec liftM f = function Pure x -> Pure (f x) | Yield g -> Yield (map_response (liftM f) g)

let return x = Pure x

let rec bind m f = match m with Pure x -> f x | Yield m -> Yield (map_response (fun m -> bind m f) m)

let ( >>= ) m f = bind m f

let ( >> ) m1 m2 = bind m1 (function () -> m2)

type ('a, 'b) either = Left of 'a | Right of 'b

(* Support for interpreting exceptions *)

let catch m =
  match m with
  | Pure x -> Pure (Right x)
  | Yield (Exception v) -> Pure (Left v)
  | Yield resp -> Yield (map_response (fun m -> liftM (fun r -> Right r) m) resp)

let throw v = Yield (Exception v)

let call (f : id) (args : value list) : return_value monad = Yield (Call (f, args, fun v -> Pure v))

let read_mem rk addr len : value monad = Yield (Read_mem (rk, addr, len, fun v -> Pure v))

let write_ea wk addr len : unit monad = Yield (Write_ea (wk, addr, len, fun () -> Pure ()))

let excl_res () : bool monad = Yield (Excl_res (fun b -> Pure b))

let write_mem wk addr len v : bool monad = Yield (Write_mem (wk, addr, len, v, fun b -> Pure b))

let barrier bk : unit monad = Yield (Barrier (bk, fun () -> Pure ()))

let read_reg name : value monad = Yield (Read_reg (name, fun v -> Pure v))

let write_reg name v : unit monad = Yield (Write_reg (name, v, fun () -> Pure ()))

let fail s = Yield (Fail s)

let get_primop name : (value list -> value) monad = Yield (Get_primop (name, fun op -> Pure op))

let get_local name : value monad = Yield (Get_local (name, fun v -> Pure v))

let put_local name v : unit monad = Yield (Put_local (name, v, fun () -> Pure ()))

let get_global_letbinds () : Type_check.tannot letbind list monad = Yield (Get_global_letbinds (fun lbs -> Pure lbs))

let early_return v = Yield (Early_return v)

let assertion_failed msg = Yield (Assertion_failed msg)

let liftM2 f m1 m2 =
  m1 >>= fun x ->
  m2 >>= fun y -> return (f x y)

let letbind_pat_ids (LB_aux (LB_val (pat, _), _)) = pat_ids pat

let subst id value exp = Ast_util.subst id (exp_of_value value) exp

let local_variable id lstate gstate =
  try Bindings.find id lstate.locals |> exp_of_value
  with Not_found -> failwith ("Could not find local variable " ^ string_of_id id)

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
          (fun bv (slice, n, m) ->
            prerr_endline (string_of_value slice);
            value_update_subrange [bv; V_int n; V_int m; slice]
          )
          (value_zeros [V_int len]) ((v1, n1, m1) :: partial_values)
    | Partial_binding [] -> Reporting.unreachable Parse_ast.Unknown __POS__ "Empty partial binding set"
    )

let rec step (E_aux (e_aux, annot) as orig_exp) =
  let wrap e_aux' = return (E_aux (e_aux', annot)) in
  match e_aux with
  | E_block [] -> wrap (E_lit (L_aux (L_unit, Parse_ast.Unknown)))
  | E_block [exp] when is_value exp -> return exp
  | E_block [(E_aux (E_block _, _) as exp)] -> return exp
  | E_block (exp :: exps) when is_value exp -> wrap (E_block exps)
  | E_block (exp :: exps) -> step exp >>= fun exp' -> wrap (E_block (exp' :: exps))
  | E_lit (L_aux (L_undef, _)) -> begin
      let env = Type_check.env_of_annot annot in
      let typ = Type_check.typ_of_annot annot in
      let undef_exp = Ast_util.undefined_of_typ false Parse_ast.Unknown (fun _ -> empty_uannot) typ in
      let undef_exp = Type_check.check_exp env undef_exp typ in
      return undef_exp
    end
  | E_lit lit -> begin try return (exp_of_value (value_of_lit lit)) with Failure s -> fail ("Failure: " ^ s) end
  | E_if (exp, then_exp, else_exp) when is_true exp -> return then_exp
  | E_if (exp, then_exp, else_exp) when is_false exp -> return else_exp
  | E_if (exp, then_exp, else_exp) -> step exp >>= fun exp' -> wrap (E_if (exp', then_exp, else_exp))
  | E_loop (While, _, exp, body) -> wrap (E_if (exp, E_aux (E_block [body; orig_exp], annot), exp_of_value V_unit))
  | E_loop (Until, _, exp, body) -> wrap (E_block [body; E_aux (E_if (exp, exp_of_value V_unit, orig_exp), annot)])
  | E_assert (exp, msg) when is_true exp -> wrap unit_exp
  | E_assert (exp, msg) when is_false exp && is_value msg -> assertion_failed (coerce_string (value_of_exp msg))
  | E_assert (exp, msg) when is_false exp -> step msg >>= fun msg' -> wrap (E_assert (exp, msg'))
  | E_assert (exp, msg) -> step exp >>= fun exp' -> wrap (E_assert (exp', msg))
  | E_vector exps ->
      let evaluated, unevaluated = Util.take_drop is_value exps in
      begin
        match unevaluated with
        | exp :: exps -> step exp >>= fun exp' -> wrap (E_vector (evaluated @ (exp' :: exps)))
        | [] -> return (exp_of_value (V_vector (List.map value_of_exp evaluated)))
      end
  | E_list exps ->
      let evaluated, unevaluated = Util.take_drop is_value exps in
      begin
        match unevaluated with
        | exp :: exps -> step exp >>= fun exp' -> wrap (E_list (evaluated @ (exp' :: exps)))
        | [] -> return (exp_of_value (V_list (List.map value_of_exp evaluated)))
      end
  (* Special rules for short circuting boolean operators *)
  | E_app (id, [x; y]) when (string_of_id id = "and_bool" || string_of_id id = "or_bool") && not (is_value x) ->
      step x >>= fun x' -> wrap (E_app (id, [x'; y]))
  | E_app (id, [x; y]) when string_of_id id = "and_bool" && is_false x -> return (exp_of_value (V_bool false))
  | E_app (id, [x; y]) when string_of_id id = "or_bool" && is_true x -> return (exp_of_value (V_bool true))
  | E_let (LB_aux (LB_val (pat, bind), lb_annot), body) when not (is_value bind) ->
      step bind >>= fun bind' -> wrap (E_let (LB_aux (LB_val (pat, bind'), lb_annot), body))
  | E_let (LB_aux (LB_val (pat, bind), lb_annot), body) ->
      let matched, bindings = pattern_match (Type_check.env_of orig_exp) pat (value_of_exp bind) in
      if matched then
        return
          (List.fold_left (fun body (id, v) -> subst id v body) body (Bindings.bindings (complete_bindings bindings)))
      else fail "Match failure"
  | E_vector_subrange (vec, n, m) -> wrap (E_app (mk_id "vector_subrange_dec", [vec; n; m]))
  | E_vector_access (vec, n) -> wrap (E_app (mk_id "vector_access_dec", [vec; n]))
  | E_vector_update (vec, n, x) -> wrap (E_app (mk_id "vector_update", [vec; n; x]))
  | E_vector_update_subrange (vec, n, m, x) ->
      (* FIXME: Currently not general enough *)
      wrap (E_app (mk_id "vector_update_subrange_dec", [vec; n; m; x]))
  (* otherwise left-to-right evaluation order for function applications *)
  | E_app (id, exps) ->
      let evaluated, unevaluated = Util.take_drop is_value exps in
      begin
        let open Type_check in
        match unevaluated with
        | exp :: exps -> step exp >>= fun exp' -> wrap (E_app (id, evaluated @ (exp' :: exps)))
        | [] when Env.is_union_constructor id (env_of_annot annot) ->
            return (exp_of_value (V_ctor (string_of_id id, List.map value_of_exp evaluated)))
        | [] when is_interpreter_extern id (env_of_annot annot) -> begin
            let extern = get_interpreter_extern id (env_of_annot annot) in
            match extern with
            | "reg_deref" ->
                let regname = List.hd evaluated |> value_of_exp |> coerce_ref in
                read_reg regname >>= fun v -> return (exp_of_value v)
            | "read_mem" -> begin
                match evaluated with
                | [rk; addrsize; addr; len] ->
                    read_mem (value_of_exp rk) (value_of_exp addr) (value_of_exp len) >>= fun v ->
                    return (exp_of_value v)
                | _ -> fail "Wrong number of parameters to read_mem intrinsic"
              end
            | "write_mem_ea" -> begin
                match evaluated with
                | [wk; addrsize; addr; len] ->
                    write_ea (value_of_exp wk) (value_of_exp addr) (value_of_exp len) >> wrap unit_exp
                | _ -> fail "Wrong number of parameters to write_ea intrinsic"
              end
            | "excl_res" -> begin
                match evaluated with
                | [_] -> excl_res () >>= fun b -> return (exp_of_value (V_bool b))
                | _ -> fail "Wrong number of parameters to excl_res intrinsic"
              end
            | "write_mem" -> begin
                match evaluated with
                | [wk; addrsize; addr; len; v] ->
                    write_mem (value_of_exp wk) (value_of_exp addr) (value_of_exp len) (value_of_exp v) >>= fun b ->
                    return (exp_of_value (V_bool b))
                | _ -> fail "Wrong number of parameters to write_memv intrinsic"
              end
            | "barrier" -> begin
                match evaluated with
                | [bk] -> barrier (value_of_exp bk) >> wrap unit_exp
                | _ -> fail "Wrong number of parameters to barrier intrinsic"
              end
            | _ -> (
                get_primop extern >>= fun op ->
                try return (exp_of_value (op (List.map value_of_exp evaluated)))
                with _ as exc -> fail ("Exception calling primop '" ^ extern ^ "': " ^ Printexc.to_string exc)
              )
          end
        | [] -> (
            call id (List.map value_of_exp evaluated) >>= function
            | Return_ok v -> return (exp_of_value v)
            | Return_exception v -> wrap (E_throw (exp_of_value v))
          )
      end
  | E_app_infix (x, id, y) when is_value x && is_value y -> (
      call id [value_of_exp x; value_of_exp y] >>= function
      | Return_ok v -> return (exp_of_value v)
      | Return_exception v -> wrap (E_throw (exp_of_value v))
    )
  | E_app_infix (x, id, y) when is_value x -> step y >>= fun y' -> wrap (E_app_infix (x, id, y'))
  | E_app_infix (x, id, y) -> step x >>= fun x' -> wrap (E_app_infix (x', id, y))
  | E_return exp when is_value exp -> early_return (value_of_exp exp)
  | E_return exp -> step exp >>= fun exp' -> wrap (E_return exp')
  | E_tuple exps ->
      let evaluated, unevaluated = Util.take_drop is_value exps in
      begin
        match unevaluated with
        | exp :: exps -> step exp >>= fun exp' -> wrap (E_tuple (evaluated @ (exp' :: exps)))
        | [] -> return (exp_of_value (tuple_value (List.map value_of_exp exps)))
      end
  | E_match (exp, pexps) when not (is_value exp) -> step exp >>= fun exp' -> wrap (E_match (exp', pexps))
  | E_match (_, []) -> fail "Pattern matching failed"
  | E_match (exp, Pat_aux (Pat_exp (pat, body), _) :: pexps) -> begin
      try
        let matched, bindings = pattern_match (Type_check.env_of body) pat (value_of_exp exp) in
        if matched then
          return
            (List.fold_left (fun body (id, v) -> subst id v body) body (Bindings.bindings (complete_bindings bindings)))
        else wrap (E_match (exp, pexps))
      with Failure s -> fail ("Failure: " ^ s)
    end
  | E_match (exp, Pat_aux (Pat_when (pat, guard, body), pat_annot) :: pexps) when not (is_value guard) -> begin
      try
        let matched, bindings = pattern_match (Type_check.env_of body) pat (value_of_exp exp) in
        let bindings = complete_bindings bindings in
        if matched then (
          let guard = List.fold_left (fun guard (id, v) -> subst id v guard) guard (Bindings.bindings bindings) in
          let body = List.fold_left (fun body (id, v) -> subst id v body) body (Bindings.bindings bindings) in
          step guard >>= fun guard' -> wrap (E_match (exp, Pat_aux (Pat_when (pat, guard', body), pat_annot) :: pexps))
        )
        else wrap (E_match (exp, pexps))
      with Failure s -> fail ("Failure: " ^ s)
    end
  | E_match (exp, Pat_aux (Pat_when (pat, guard, body), pat_annot) :: pexps) when is_true guard -> return body
  | E_match (exp, Pat_aux (Pat_when (pat, guard, body), pat_annot) :: pexps) when is_false guard ->
      wrap (E_match (exp, pexps))
  | E_typ (typ, exp) -> return exp
  | E_throw exp when is_value exp -> throw (value_of_exp exp)
  | E_throw exp -> step exp >>= fun exp' -> wrap (E_throw exp')
  | E_exit exp when is_value exp -> throw (V_ctor ("Exit", [value_of_exp exp]))
  | E_exit exp -> step exp >>= fun exp' -> wrap (E_exit exp')
  | E_ref id -> return (exp_of_value (V_ref (string_of_id id)))
  | E_id id -> begin
      let open Type_check in
      match Env.lookup_id id (env_of_annot annot) with
      | Register _ -> read_reg (string_of_id id) >>= fun v -> return (exp_of_value v)
      | Local (Mutable, _) -> get_local (string_of_id id) >>= fun v -> return (exp_of_value v)
      | Local (Immutable, _) ->
          (* if we get here without already having substituted, it must be a top-level letbind *)
          get_global_letbinds () >>= fun lbs ->
          let chain = build_letchain id lbs orig_exp in
          return chain
      | Enum _ -> return (exp_of_value (V_ctor (string_of_id id, [])))
      | _ -> fail ("Couldn't find id " ^ string_of_id id)
    end
  | E_struct fexps ->
      let evaluated, unevaluated = Util.take_drop is_value_fexp fexps in
      begin
        match unevaluated with
        | FE_aux (FE_fexp (id, exp), fe_annot) :: fexps ->
            step exp >>= fun exp' -> wrap (E_struct (evaluated @ (FE_aux (FE_fexp (id, exp'), fe_annot) :: fexps)))
        | [] ->
            List.map value_of_fexp fexps
            |> List.fold_left (fun record (field, v) -> StringMap.add field v record) StringMap.empty
            |> (fun record -> V_record record)
            |> exp_of_value |> return
      end
  | E_struct_update (exp, fexps) when not (is_value exp) -> step exp >>= fun exp' -> wrap (E_struct_update (exp', fexps))
  | E_struct_update (record, fexps) ->
      let evaluated, unevaluated = Util.take_drop is_value_fexp fexps in
      begin
        match unevaluated with
        | FE_aux (FE_fexp (id, exp), fe_annot) :: fexps ->
            step exp >>= fun exp' ->
            wrap (E_struct_update (record, evaluated @ (FE_aux (FE_fexp (id, exp'), fe_annot) :: fexps)))
        | [] ->
            List.map value_of_fexp fexps
            |> List.fold_left
                 (fun record (field, v) -> StringMap.add field v record)
                 (coerce_record (value_of_exp record))
            |> (fun record -> V_record record)
            |> exp_of_value |> return
      end
  | E_field (exp, id) when not (is_value exp) -> step exp >>= fun exp' -> wrap (E_field (exp', id))
  | E_field (exp, id) ->
      let record = coerce_record (value_of_exp exp) in
      return (exp_of_value (StringMap.find (string_of_id id) record))
  | E_var (lexp, exp, E_aux (E_block body, _)) -> wrap (E_block (E_aux (E_assign (lexp, exp), annot) :: body))
  | E_var (lexp, exp, body) -> wrap (E_block [E_aux (E_assign (lexp, exp), annot); body])
  | E_assign (lexp, exp) when not (is_value exp) -> step exp >>= fun exp' -> wrap (E_assign (lexp, exp'))
  | E_assign (LE_aux (LE_app (id, args), _), exp) -> wrap (E_app (id, args @ [exp]))
  | E_assign (LE_aux (LE_field (lexp, id), ul), exp) -> begin
      try
        let open Type_check in
        let lexp_exp = infer_exp (env_of_annot annot) (exp_of_lexp (strip_lexp lexp)) in
        let exp' = E_aux (E_struct_update (lexp_exp, [FE_aux (FE_fexp (id, exp), ul)]), ul) in
        wrap (E_assign (lexp, exp'))
      with Failure s -> fail ("Failure: " ^ s)
    end
  | E_assign (LE_aux (LE_vector (vec, n), lexp_annot), exp) -> begin
      try
        let open Type_check in
        let vec_exp = infer_exp (env_of_annot annot) (exp_of_lexp (strip_lexp vec)) in
        let exp' = E_aux (E_vector_update (vec_exp, n, exp), lexp_annot) in
        wrap (E_assign (vec, exp'))
      with Failure s -> fail ("Failure: " ^ s)
    end
  | E_assign (LE_aux (LE_vector_range (vec, n, m), lexp_annot), exp) -> begin
      try
        let open Type_check in
        let vec_exp = infer_exp (env_of_annot annot) (exp_of_lexp (strip_lexp vec)) in
        (* FIXME: let the type checker check this *)
        let exp' = E_aux (E_vector_update_subrange (vec_exp, n, m, exp), lexp_annot) in
        wrap (E_assign (vec, exp'))
      with Failure s -> fail ("Failure: " ^ s)
    end
  | E_assign (LE_aux (LE_id id, _), exp) | E_assign (LE_aux (LE_typ (_, id), _), exp) -> begin
      let open Type_check in
      let name = string_of_id id in
      match Env.lookup_id id (env_of_annot annot) with
      | Register _ -> write_reg name (value_of_exp exp) >> wrap unit_exp
      | Local (Mutable, _) | Unbound _ -> put_local name (value_of_exp exp) >> wrap unit_exp
      | Local (Immutable, _) -> fail ("Assignment to immutable local: " ^ name)
      | Enum _ -> fail ("Assignment to union constructor: " ^ name)
    end
  | E_assign (LE_aux (LE_deref reference, annot), exp) when not (is_value reference) ->
      step reference >>= fun reference' -> wrap (E_assign (LE_aux (LE_deref reference', annot), exp))
  | E_assign (LE_aux (LE_deref reference, annot), exp) ->
      let name = coerce_ref (value_of_exp reference) in
      write_reg name (value_of_exp exp) >> wrap unit_exp
  | E_assign (LE_aux (LE_tuple lexps, annot), exp) -> fail "Tuple assignment"
  | E_assign (LE_aux (LE_vector_concat lexps, annot), exp) ->
      fail "Vector concat assignment"
      (*
     let values = coerce_tuple (value_of_exp exp) in
     wrap (E_block (List.map2 (fun lexp v -> E_aux (E_assign (lexp, exp_of_value v), (Parse_ast.Unknown, None))) lexps values))
      *)
  | E_try (exp, pexps) when is_value exp -> return exp
  | E_try (exp, pexps) -> begin
      catch (step exp) >>= fun exp' ->
      match exp' with
      | Left exn -> wrap (E_match (exp_of_value exn, pexps @ [fallthrough]))
      | Right exp' -> wrap (E_try (exp', pexps))
    end
  | E_for (id, exp_from, exp_to, exp_step, ord, body) when is_value exp_from && is_value exp_to && is_value exp_step ->
      let v_from = value_of_exp exp_from in
      let v_to = value_of_exp exp_to in
      let v_step = value_of_exp exp_step in
      begin
        match ord with
        | Ord_aux (Ord_inc, _) -> begin
            match value_gt [v_from; v_to] with
            | V_bool true -> wrap (E_lit (L_aux (L_unit, Parse_ast.Unknown)))
            | V_bool false ->
                wrap
                  (E_block
                     [
                       subst id v_from body;
                       E_aux
                         (E_for (id, exp_of_value (value_add_int [v_from; v_step]), exp_to, exp_step, ord, body), annot);
                     ]
                  )
            | _ -> assert false
          end
        | Ord_aux (Ord_dec, _) -> begin
            match value_lt [v_from; v_to] with
            | V_bool true -> wrap (E_lit (L_aux (L_unit, Parse_ast.Unknown)))
            | V_bool false ->
                wrap
                  (E_block
                     [
                       subst id v_from body;
                       E_aux
                         (E_for (id, exp_of_value (value_sub_int [v_from; v_step]), exp_to, exp_step, ord, body), annot);
                     ]
                  )
            | _ -> assert false
          end
      end
  | E_for (id, exp_from, exp_to, exp_step, ord, body) when is_value exp_to && is_value exp_step ->
      step exp_from >>= fun exp_from' -> wrap (E_for (id, exp_from', exp_to, exp_step, ord, body))
  | E_for (id, exp_from, exp_to, exp_step, ord, body) when is_value exp_step ->
      step exp_to >>= fun exp_to' -> wrap (E_for (id, exp_from, exp_to', exp_step, ord, body))
  | E_for (id, exp_from, exp_to, exp_step, ord, body) ->
      step exp_step >>= fun exp_step' -> wrap (E_for (id, exp_from, exp_to, exp_step', ord, body))
  | E_sizeof nexp -> begin
      match Type_check.big_int_of_nexp nexp with
      | Some n -> return (exp_of_value (V_int n))
      | None -> fail "Sizeof unevaluable nexp"
    end
  | E_cons (hd, tl) when is_value hd && is_value tl ->
      let hd = value_of_exp hd in
      let tl = coerce_listlike (value_of_exp tl) in
      return (exp_of_value (V_list (hd :: tl)))
  | E_cons (hd, tl) when is_value hd -> step tl >>= fun tl' -> wrap (E_cons (hd, tl'))
  | E_cons (hd, tl) -> step hd >>= fun hd' -> wrap (E_cons (hd', tl))
  | _ -> raise (Invalid_argument ("Unimplemented " ^ string_of_exp orig_exp))

and exp_of_lexp (LE_aux (lexp_aux, _)) =
  match lexp_aux with
  | LE_id id -> mk_exp (E_id id)
  | LE_app (f, args) -> mk_exp (E_app (f, args))
  | LE_typ (typ, id) -> mk_exp (E_typ (typ, mk_exp (E_id id)))
  | LE_deref exp -> mk_exp (E_app (mk_id "_reg_deref", [exp]))
  | LE_tuple lexps -> mk_exp (E_tuple (List.map exp_of_lexp lexps))
  | LE_vector (lexp, exp) -> mk_exp (E_vector_access (exp_of_lexp lexp, exp))
  | LE_vector_range (lexp, exp1, exp2) -> mk_exp (E_vector_subrange (exp_of_lexp lexp, exp1, exp2))
  | LE_vector_concat [] -> failwith "Empty LE_vector_concat node in exp_of_lexp"
  | LE_vector_concat [lexp] -> exp_of_lexp lexp
  | LE_vector_concat (lexp :: lexps) ->
      mk_exp (E_vector_append (exp_of_lexp lexp, exp_of_lexp (mk_lexp (LE_vector_concat lexps))))
  | LE_field (lexp, id) -> mk_exp (E_field (exp_of_lexp lexp, id))

and pattern_match env (P_aux (p_aux, (l, _))) value =
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
            if is_ctor value && string_of_id id = fst (coerce_ctor value) then (true, Bindings.empty)
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
              ("Bad vector annotation for vector concatentation pattern " ^ string_of_typ (Type_check.typ_of_pat pat))
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
  | P_struct (fpats, _) ->
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
      * Type_check.tannot exp monad
      * (string Lazy.t * lstate * (return_value -> Type_check.tannot exp monad)) list
  | Break of frame
  | Effect_request of
      string Lazy.t
      * state
      * (string Lazy.t * lstate * (return_value -> Type_check.tannot exp monad)) list
      * effect_request
  | Fail of
      string Lazy.t
      * state
      * Type_check.tannot exp monad
      * (string Lazy.t * lstate * (return_value -> Type_check.tannot exp monad)) list
      * string

(* when changing effect_request remember to also update response type above *)
and effect_request =
  | Read_mem of (* read_kind : *) value * (* address : *) value * (* length : *) value * (value -> state -> frame)
  | Write_ea of (* write_kind : *) value * (* address : *) value * (* length : *) value * (unit -> state -> frame)
  | Excl_res of (bool -> state -> frame)
  | Write_mem of
      (* write_kind : *) value
      * (* address : *) value
      * (* length : *) value
      * (* value : *) value
      * (bool -> state -> frame)
  | Barrier of (* barrier_kind : *) value * (unit -> state -> frame)
  | Read_reg of string * (value -> state -> frame)
  | Write_reg of string * value * (unit -> state -> frame)

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
          let out' = lazy (Pretty_print_sail.to_string (Pretty_print_sail.doc_exp (Type_check.strip_exp exp'))) in
          Step (out', state, step exp', stack)
      | Yield (Call (id, vals, cont)), _ when string_of_id id = "break" -> begin
          let arg = if List.length vals != 1 then tuple_value vals else List.hd vals in
          try
            let body = exp_of_fundef (Bindings.find id gstate.fundefs) arg in
            Break (Step (lazy "", (initial_lstate, gstate), return body, (out, lstate, cont) :: stack))
          with Not_found -> Step (out, state, fail ("Fundef not found: " ^ string_of_id id), stack)
        end
      | Yield (Call (id, vals, cont)), _ -> begin
          let arg = if List.length vals != 1 then tuple_value vals else List.hd vals in
          try
            let body = exp_of_fundef (Bindings.find id gstate.fundefs) arg in
            Step (lazy "", (initial_lstate, gstate), return body, (out, lstate, cont) :: stack)
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
          try eval_frame' (Step (out, state, cont (Bindings.find (mk_id name) lstate.locals), stack))
          with Not_found -> eval_frame' (Step (out, state, fail ("Local not found: " ^ name), stack))
        end
      | Yield (Put_local (name, v, cont)), _ ->
          let state' = ({ locals = Bindings.add (mk_id name) v lstate.locals }, gstate) in
          eval_frame' (Step (out, state', cont (), stack))
      | Yield (Get_global_letbinds cont), _ -> eval_frame' (Step (out, state, cont gstate.letbinds, stack))
      | Yield (Read_mem (rk, addr, len, cont)), _ ->
          Effect_request
            ( out,
              state,
              stack,
              Read_mem (rk, addr, len, fun result state' -> eval_frame' (Step (out, state', cont result, stack)))
            )
      | Yield (Write_ea (wk, addr, len, cont)), _ ->
          Effect_request
            ( out,
              state,
              stack,
              Write_ea (wk, addr, len, fun () state' -> eval_frame' (Step (out, state', cont (), stack)))
            )
      | Yield (Excl_res cont), _ ->
          Effect_request (out, state, stack, Excl_res (fun b state' -> eval_frame' (Step (out, state', cont b, stack))))
      | Yield (Write_mem (wk, addr, len, v, cont)), _ ->
          Effect_request
            ( out,
              state,
              stack,
              Write_mem (wk, addr, len, v, fun b state' -> eval_frame' (Step (out, state', cont b, stack)))
            )
      | Yield (Barrier (bk, cont)), _ ->
          Effect_request
            (out, state, stack, Barrier (bk, fun () state' -> eval_frame' (Step (out, state', cont (), stack))))
      | Yield (Early_return v), [] -> Done (state, v)
      | Yield (Early_return v), head :: stack' ->
          Step (stack_string head, (stack_state head, gstate), stack_cont head (Return_ok v), stack')
      | Yield (Assertion_failed msg), _ | Yield (Fail msg), _ -> Fail (out, state, m, stack, msg)
      | Yield (Exception v), [] -> Fail (out, state, m, stack, "Uncaught exception: " ^ string_of_value v)
      | Yield (Exception v), head :: stack' ->
          Step (stack_string head, (stack_state head, gstate), stack_cont head (Return_exception v), stack')
    )

let eval_frame frame =
  try eval_frame' frame
  with Type_error.Type_error (l, err) -> raise (Reporting.err_typ l (Type_error.string_of_type_error err))

let default_effect_interp state eff =
  let lstate, gstate = state in
  match eff with
  | Read_mem (rk, addr, len, cont) ->
      (* all read-kinds treated the same in single-threaded interpreter *)
      let addr' = coerce_bv addr in
      let len' = coerce_int len in
      let result = mk_vector (Sail_lib.read_ram (List.length addr', len', [], addr')) in
      cont result state
  | Write_ea (wk, addr, len, cont) ->
      (* just store the values for the next Write_memv *)
      let state' = (lstate, { gstate with last_write_ea = Some (wk, addr, len) }) in
      cont () state'
  | Excl_res cont ->
      (* always succeeds in single-threaded interpreter *)
      cont true state
  | Write_mem (wk, addr, len, v, cont) -> begin
      match gstate.last_write_ea with
      | Some (wk', addr', len') ->
          let state' = (lstate, { gstate with last_write_ea = None }) in
          (* all write-kinds treated the same in single-threaded interpreter *)
          let addr' = coerce_bv addr in
          let len' = coerce_int len in
          let v' = coerce_bv v in
          if Big_int.mul len' (Big_int.of_int 8) = Big_int.of_int (List.length v') then (
            let b = Sail_lib.write_ram (List.length addr', len', [], addr', v') in
            cont b state'
          )
          else failwith "Write_memv with length mismatch to preceding Write_ea"
      | None -> failwith "Write_memv without preceding Write_ea"
    end
  | Barrier (bk, cont) ->
      (* no-op in single-threaded interpreter *)
      cont () state
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

let effect_interp = ref default_effect_interp

let set_effect_interp interp = effect_interp := interp

let rec run_frame frame =
  match frame with
  | Done (state, v) -> v
  | Fail (_, _, _, _, msg) -> failwith ("run_frame got Fail: " ^ msg)
  | Step (_, _, _, _) -> run_frame (eval_frame frame)
  | Break frame -> run_frame (eval_frame frame)
  | Effect_request (_, state, _, eff) -> run_frame (!effect_interp state eff)

let eval_exp state exp = run_frame (Step (lazy "", state, return exp, []))

let initial_gstate primops defs env =
  {
    registers = Bindings.empty;
    allow_registers = true;
    primops;
    letbinds = defs_letbinds defs;
    fundefs = Bindings.empty;
    last_write_ea = None;
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
            { gstate with registers = Bindings.add id (eval_exp (initial_lstate, gstate) exp) gstate.registers }
      end
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

type value_result = Value_success of value | Value_error of exn

let decode_instruction state bv =
  try
    let env = (snd state).typecheck_env in
    let untyped = mk_exp (E_app (mk_id "decode", [mk_exp (E_vector (List.map mk_lit_exp bv))])) in
    let typed =
      Type_check.check_exp env untyped
        (app_typ (mk_id "option") [A_aux (A_typ (mk_typ (Typ_id (mk_id "ast"))), Parse_ast.Unknown)])
    in
    let evaled = eval_exp state typed in
    match evaled with
    | V_ctor ("Some", [v]) -> Value_success v
    | V_ctor ("None", _) -> failwith "decode returned None"
    | _ -> failwith "decode returned wrong value type"
  with _ as exn -> Value_error exn

let annot_exp_effect e_aux l env typ = E_aux (e_aux, (l, Type_check.mk_tannot env typ))
let annot_exp e_aux l env typ = annot_exp_effect e_aux l env typ
let id_typ id = mk_typ (Typ_id (mk_id id))

let analyse_instruction state ast =
  let env = (snd state).typecheck_env in
  let unk = Parse_ast.Unknown in
  let typed =
    annot_exp
      (E_app (mk_id "initial_analysis", [annot_exp (E_internal_value ast) unk env (id_typ "ast")]))
      unk env
      (tuple_typ
         [id_typ "regfps"; id_typ "regfps"; id_typ "regfps"; id_typ "niafps"; id_typ "diafp"; id_typ "instruction_kind"]
      )
  in
  Step
    ( lazy (Pretty_print_sail.to_string (Pretty_print_sail.doc_exp (Type_check.strip_exp typed))),
      state,
      return typed,
      []
    )

let execute_instruction state ast =
  let env = (snd state).typecheck_env in
  let unk = Parse_ast.Unknown in
  let typed =
    annot_exp (E_app (mk_id "execute", [annot_exp (E_internal_value ast) unk env (id_typ "ast")])) unk env unit_typ
  in
  Step
    ( lazy (Pretty_print_sail.to_string (Pretty_print_sail.doc_exp (Type_check.strip_exp typed))),
      state,
      return typed,
      []
    )
