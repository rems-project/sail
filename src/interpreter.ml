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
open Value

type gstate =
  { registers : value Bindings.t;
    allow_registers : bool; (* For some uses we want to forbid touching any registers. *)
    primops : (value list -> value) StringMap.t;
    letbinds : (Type_check.tannot letbind) list;
    fundefs : (Type_check.tannot fundef) Bindings.t;
  }

type lstate =
  { locals : value Bindings.t }

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
     Util.string_to_list str
     |> List.map (fun c -> List.map (fun b -> V_bit b) (Sail_lib.hex_char c))
     |> List.concat
     |> (fun v -> V_vector v)
  | L_bin str ->
     Util.string_to_list str
     |> List.map (fun c -> V_bit (Sail_lib.bin_char c))
     |> (fun v -> V_vector v)
  | L_real str ->
     begin match Util.split_on_char '.' str with
     | [whole; frac] ->
        let whole = Rational.of_int (int_of_string whole) in
        let frac = Rational.div (Rational.of_int (int_of_string frac)) (Rational.of_int (Util.power 10 (String.length frac)))  in
        V_real (Rational.add whole frac)
     | _ -> failwith "could not parse real literal"
     end
  | _ -> failwith "Unimplemented value_of_lit" (* TODO *)

let is_value = function
  | (E_aux (E_internal_value _, _)) -> true
  | _ -> false

let is_true = function
  | (E_aux (E_internal_value (V_bool b), _)) -> b == true
  | _ -> false

let is_false = function
  | (E_aux (E_internal_value (V_bool b), _)) -> b == false
  | _ -> false

let exp_of_value v = (E_aux (E_internal_value v, (Parse_ast.Unknown, Type_check.empty_tannot)))
let value_of_exp = function
  | (E_aux (E_internal_value v, _)) -> v
  | _ -> failwith "value_of_exp coerction failed"

(**************************************************************************)
(* 1. Interpreter Monad                                                   *)
(**************************************************************************)

type return_value =
  | Return_ok of value
  | Return_exception of value

type 'a response =
  | Early_return of value
  | Exception of value
  | Assertion_failed of string
  | Call of id * value list * (return_value -> 'a)
  | Gets of (state -> 'a)
  | Puts of state * (unit -> 'a)

and 'a monad =
  | Pure of 'a
  | Yield of ('a monad response)

let map_response f = function
  | Early_return v -> Early_return v
  | Exception v -> Exception v
  | Assertion_failed str -> Assertion_failed str
  | Gets g -> Gets (fun s -> f (g s))
  | Puts (s, cont) -> Puts (s, fun () -> f (cont ()))
  | Call (id, vals, cont) -> Call (id, vals, fun v -> f (cont v))

let rec liftM f = function
  | Pure x -> Pure (f x)
  | Yield g -> Yield (map_response (liftM f) g)

let return x = Pure x

let rec bind m f =
  match m with
  | Pure x -> f x
  | Yield m -> Yield (map_response (fun m -> bind m f) m)

let ( >>= ) m f = bind m f

let ( >> ) m1 m2 = bind m1 (function () -> m2)

type ('a, 'b) either =
  | Left of 'a
  | Right of 'b

(* Support for interpreting exceptions *)

let catch m =
  match m with
  | Pure x -> Pure (Right x)
  | Yield (Exception v) -> Pure (Left v)
  | Yield resp -> Yield (map_response (fun m -> liftM (fun r -> Right r) m) resp)

let throw v = Yield (Exception v)

let call (f : id) (args : value list) : return_value monad =
  Yield (Call (f, args, fun v -> Pure v))

let gets : state monad =
  Yield (Gets (fun s -> Pure s))

let puts (s : state) : unit monad =
  Yield (Puts (s, fun () -> Pure ()))

let early_return v = Yield (Early_return v)

let assertion_failed msg = Yield (Assertion_failed msg)

let liftM2 f m1 m2 = m1 >>= fun x -> m2 >>= fun y -> return (f x y)

let letbind_pat_ids (LB_aux (LB_val (pat, _), _)) = pat_ids pat

let subst id value exp = Ast_util.subst id (exp_of_value value) exp

let local_variable id lstate gstate =
  try
    Bindings.find id lstate.locals |> exp_of_value
  with
  | Not_found -> failwith ("Could not find local variable " ^ string_of_id id)

(**************************************************************************)
(* 2. Expression Evaluation                                               *)
(**************************************************************************)

let unit_exp = E_lit (L_aux (L_unit, Parse_ast.Unknown))

let is_value_fexp (FE_aux (FE_Fexp (id, exp), _)) = is_value exp
let value_of_fexp (FE_aux (FE_Fexp (id, exp), _)) = (string_of_id id, value_of_exp exp)

let rec build_letchain id lbs (E_aux (_, annot) as exp) =
  match lbs with
  | [] -> exp
  | lb :: lbs when IdSet.mem id (letbind_pat_ids lb)->
     let exp = E_aux (E_let (lb, exp), annot) in
     build_letchain id lbs exp
  | _ :: lbs -> build_letchain id lbs exp

let is_interpreter_extern id env =
  let open Type_check in
  Env.is_extern id env "interpreter" || Env.is_extern id env "ocaml"

let get_interpreter_extern id env =
  let open Type_check in
  try Env.get_extern id env "interpreter" with
  | Type_error _ -> Env.get_extern id env "ocaml"

let rec step (E_aux (e_aux, annot) as orig_exp) =
  let wrap e_aux' = return (E_aux (e_aux', annot)) in
  match e_aux with
  | E_block [] -> wrap (E_lit (L_aux (L_unit, Parse_ast.Unknown)))
  | E_block [exp] when is_value exp -> return exp
  | E_block (exp :: exps) when is_value exp -> wrap (E_block exps)
  | E_block (exp :: exps) ->
     step exp >>= fun exp' -> wrap (E_block (exp' :: exps))

  | E_lit lit -> return (exp_of_value (value_of_lit lit))

  | E_if (exp, then_exp, else_exp) when is_true exp -> return then_exp
  | E_if (exp, then_exp, else_exp) when is_false exp -> return else_exp
  | E_if (exp, then_exp, else_exp) ->
     step exp >>= fun exp' -> wrap (E_if (exp', then_exp, else_exp))

  | E_loop (While, exp, body) -> wrap (E_if (exp, E_aux (E_block [body; orig_exp], annot), exp_of_value V_unit))
  | E_loop (Until, exp, body) -> wrap (E_block [body; E_aux (E_if (exp, exp_of_value V_unit, orig_exp), annot)])

  | E_assert (exp, msg) when is_true exp -> wrap unit_exp
  | E_assert (exp, msg) when is_false exp && is_value msg ->
     failwith (coerce_string (value_of_exp msg))
  | E_assert (exp, msg) when is_false exp ->
     step msg >>= fun msg' -> wrap (E_assert (exp, msg'))
  | E_assert (exp, msg) ->
     step exp >>= fun exp' -> wrap (E_assert (exp', msg))

  | E_vector exps ->
     let evaluated, unevaluated = Util.take_drop is_value exps in
     begin
       match unevaluated with
       | exp :: exps ->
          step exp >>= fun exp' -> wrap (E_vector (evaluated @ exp' :: exps))
       | [] -> return (exp_of_value (V_vector (List.map value_of_exp evaluated)))
     end

  | E_list exps ->
     let evaluated, unevaluated = Util.take_drop is_value exps in
     begin
       match unevaluated with
       | exp :: exps ->
          step exp >>= fun exp' -> wrap (E_list (evaluated @ exp' :: exps))
       | [] -> return (exp_of_value (V_list (List.map value_of_exp evaluated)))
     end

  (* Special rules for short circuting boolean operators *)
  | E_app (id, [x; y]) when (string_of_id id = "and_bool" || string_of_id id = "or_bool") && not (is_value x) ->
     step x >>= fun x' -> wrap (E_app (id, [x'; y]))
  | E_app (id, [x; y]) when string_of_id id = "and_bool" && is_false x ->
     return (exp_of_value (V_bool false))
  | E_app (id, [x; y]) when string_of_id id = "or_bool" && is_true x ->
     return (exp_of_value (V_bool true))

  | E_let (LB_aux (LB_val (pat, bind), lb_annot), body) when not (is_value bind) ->
     step bind >>= fun bind' -> wrap (E_let (LB_aux (LB_val (pat, bind'), lb_annot), body))
  | E_let (LB_aux (LB_val (pat, bind), lb_annot), body) ->
     let matched, bindings = pattern_match (Type_check.env_of orig_exp) pat (value_of_exp bind) in
     if matched then
       return  (List.fold_left (fun body (id, v) -> subst id v body) body (Bindings.bindings bindings))
     else
       failwith "Match failure"

  | E_vector_subrange (vec, n, m) ->
     wrap (E_app (mk_id "vector_subrange_dec", [vec; n; m]))
  | E_vector_access (vec, n) ->
     wrap (E_app (mk_id "vector_access_dec", [vec; n]))

  | E_vector_update (vec, n, x) ->
     wrap (E_app (mk_id "vector_update", [vec; n; x]))
  | E_vector_update_subrange (vec, n, m, x) ->
     (* FIXME: Currently not general enough *)
     wrap (E_app (mk_id "vector_update_subrange_dec", [vec; n; m; x]))

  (* otherwise left-to-right evaluation order for function applications *)
  | E_app (id, exps) ->
     let evaluated, unevaluated = Util.take_drop is_value exps in
     begin
       let open Type_check in
       match unevaluated with
       | exp :: exps ->
          step exp >>= fun exp' -> wrap (E_app (id, evaluated @ exp' :: exps))
       | [] when Env.is_union_constructor id (env_of_annot annot) ->
          return (exp_of_value (V_ctor (string_of_id id, List.map value_of_exp evaluated)))
       | [] when is_interpreter_extern id (env_of_annot annot) ->
          begin
            let extern = get_interpreter_extern id (env_of_annot annot) in
            if extern = "reg_deref" then
              let regname = List.hd evaluated |> value_of_exp |> coerce_ref in
              gets >>= fun (_, gstate) ->
              if gstate.allow_registers
              then return (exp_of_value (Bindings.find (mk_id regname) gstate.registers))
              else raise Not_found
            else
              gets >>= fun (_, gstate) ->
              let primop = try StringMap.find extern gstate.primops with Not_found -> failwith ("No primop " ^ extern) in
              return (exp_of_value (primop (List.map value_of_exp evaluated)))
          end
       | [] ->
          call id (List.map value_of_exp evaluated) >>=
            (function Return_ok v -> return (exp_of_value v)
                    | Return_exception v -> wrap (E_throw (exp_of_value v)))
     end
  | E_app_infix (x, id, y) when is_value x && is_value y ->
     call id [value_of_exp x; value_of_exp y] >>=
       (function Return_ok v -> return (exp_of_value v)
               | Return_exception v -> wrap (E_throw (exp_of_value v)))
  | E_app_infix (x, id, y) when is_value x ->
     step y >>= fun y' -> wrap (E_app_infix (x, id, y'))
  | E_app_infix (x, id, y) ->
     step x >>= fun x' -> wrap (E_app_infix (x', id, y))

  | E_return exp when is_value exp -> early_return (value_of_exp exp)
  | E_return exp -> step exp >>= fun exp' -> wrap (E_return exp')

  | E_tuple exps ->
     let evaluated, unevaluated = Util.take_drop is_value exps in
     begin
       match unevaluated with
       | exp :: exps ->
          step exp >>= fun exp' -> wrap (E_tuple (evaluated @ exp' :: exps))
       | [] -> return (exp_of_value (tuple_value (List.map value_of_exp exps)))
     end

  | E_case (exp, pexps) when not (is_value exp) ->
     step exp >>= fun exp' -> wrap (E_case (exp', pexps))
  | E_case (_, []) -> failwith "Pattern matching failed"
  | E_case (exp, Pat_aux (Pat_exp (pat, body), _) :: pexps) ->
     let matched, bindings = pattern_match (Type_check.env_of body) pat (value_of_exp exp) in
     if matched then
       return  (List.fold_left (fun body (id, v) -> subst id v body) body (Bindings.bindings bindings))
     else
       wrap (E_case (exp, pexps))
  | E_case (exp, Pat_aux (Pat_when (pat, guard, body), pat_annot) :: pexps) when not (is_value guard) ->
     let matched, bindings = pattern_match (Type_check.env_of body) pat (value_of_exp exp) in
     if matched then
       let guard = List.fold_left (fun guard (id, v) -> subst id v guard) guard (Bindings.bindings bindings) in
       let body = List.fold_left (fun body (id, v) -> subst id v body) body (Bindings.bindings bindings) in
       step guard >>= fun guard' ->
       wrap (E_case (exp, Pat_aux (Pat_when (pat, guard', body), pat_annot) :: pexps))
     else
       wrap (E_case (exp, pexps))
  | E_case (exp, Pat_aux (Pat_when (pat, guard, body), pat_annot) :: pexps) when is_true guard -> return body
  | E_case (exp, Pat_aux (Pat_when (pat, guard, body), pat_annot) :: pexps) when is_false guard -> wrap (E_case (exp, pexps))

  | E_cast (typ, exp) -> return exp

  | E_throw exp when is_value exp -> throw (value_of_exp exp)
  | E_throw exp -> step exp >>= fun exp' -> wrap (E_throw exp')
  | E_exit exp when is_value exp -> throw (V_ctor ("Exit", [value_of_exp exp]))
  | E_exit exp -> step exp >>= fun exp' -> wrap (E_exit exp')

  | E_ref id ->
     gets >>= fun (lstate, gstate) ->
     if Bindings.mem id gstate.registers && gstate.allow_registers then
       return (exp_of_value (V_ref (string_of_id id)))
     else
       failwith ("Could not find register " ^ string_of_id id)

  | E_id id ->
     begin
       let open Type_check in
       gets >>= fun (lstate, gstate) ->
       match Env.lookup_id id (env_of_annot annot) with
       | Register _ when gstate.allow_registers ->
          let exp =
            try exp_of_value (Bindings.find id gstate.registers) with
            | Not_found ->
               (* Replace with error message? *)
               let exp = mk_exp (E_app (mk_id ("undefined_" ^ string_of_typ (typ_of orig_exp)), [mk_exp (E_lit (mk_lit (L_unit)))])) in
               Type_check.check_exp (env_of_annot annot) exp (typ_of orig_exp)
          in
          return exp
       | Register _ when not gstate.allow_registers ->
          return (exp_of_value (V_attempted_read (string_of_id id)))
       | Local (Mutable, _) -> return (local_variable id lstate gstate)
       | Local (Immutable, _) ->
          let chain = build_letchain id gstate.letbinds orig_exp in
          return chain
       | Enum _ ->
          return (exp_of_value (V_ctor (string_of_id id, [])))
       | _ -> failwith ("Couldn't find id " ^ string_of_id id)
     end

  | E_record fexps ->
     let evaluated, unevaluated = Util.take_drop is_value_fexp fexps in
     begin
       match unevaluated with
       | FE_aux (FE_Fexp (id, exp), fe_annot) :: fexps ->
          step exp >>= fun exp' ->
          wrap (E_record (evaluated @ FE_aux (FE_Fexp (id, exp'), fe_annot) :: fexps))
       | [] ->
          List.map value_of_fexp fexps
          |> List.fold_left (fun record (field, v) -> StringMap.add field v record) StringMap.empty
          |> (fun record -> V_record record)
          |> exp_of_value
          |> return
     end

  | E_record_update (exp, fexps) when not (is_value exp) ->
     step exp >>= fun exp' -> wrap (E_record_update (exp', fexps))
  | E_record_update (record, fexps) ->
     let evaluated, unevaluated = Util.take_drop is_value_fexp fexps in
     begin
       match unevaluated with
       | FE_aux (FE_Fexp (id, exp), fe_annot) :: fexps ->
          step exp >>= fun exp' ->
          wrap (E_record_update (record, evaluated @ FE_aux (FE_Fexp (id, exp'), fe_annot) :: fexps))
       | [] ->
          List.map value_of_fexp fexps
          |> List.fold_left (fun record (field, v) -> StringMap.add field v record) (coerce_record (value_of_exp record))
          |> (fun record -> V_record record)
          |> exp_of_value
          |> return
     end

  | E_field (exp, id) when not (is_value exp) ->
     step exp >>= fun exp' -> wrap (E_field (exp', id))
  | E_field (exp, id) ->
     let record = coerce_record (value_of_exp exp) in
     return (exp_of_value (StringMap.find (string_of_id id) record))

  | E_assign (lexp, exp) when not (is_value exp) -> step exp >>= fun exp' -> wrap (E_assign (lexp, exp'))
  | E_assign (LEXP_aux (LEXP_memory (id, args), _), exp) -> wrap (E_app (id, args @ [exp]))
  | E_assign (LEXP_aux (LEXP_field (lexp, id), ul), exp) ->
     let open Type_check in
     let lexp_exp = infer_exp (env_of_annot annot) (exp_of_lexp (strip_lexp lexp)) in
     let exp' = E_aux (E_record_update (lexp_exp, [FE_aux (FE_Fexp (id, exp), ul)]), ul) in
     wrap (E_assign (lexp, exp'))
  | E_assign (LEXP_aux (LEXP_vector (vec, n), lexp_annot), exp) ->
     let open Type_check in
     let vec_exp = infer_exp (env_of_annot annot) (exp_of_lexp (strip_lexp vec)) in
     let exp' = E_aux (E_vector_update (vec_exp, n, exp), lexp_annot) in
     wrap (E_assign (vec, exp'))
  | E_assign (LEXP_aux (LEXP_vector_range (vec, n, m), lexp_annot), exp) ->
     let open Type_check in
     let vec_exp = infer_exp (env_of_annot annot) (exp_of_lexp (strip_lexp vec)) in
     (* FIXME: let the type checker check this *)
     let exp' = E_aux (E_vector_update_subrange (vec_exp, n, m, exp), lexp_annot) in
     wrap (E_assign (vec, exp'))
  | E_assign (LEXP_aux (LEXP_id id, _), exp) | E_assign (LEXP_aux (LEXP_cast (_, id), _), exp) ->
     begin
       let open Type_check in
       gets >>= fun (lstate, gstate) ->
       match Env.lookup_id id (env_of_annot annot) with
       | Register _ when gstate.allow_registers ->
          puts (lstate, { gstate with registers = Bindings.add id (value_of_exp exp) gstate.registers }) >> wrap unit_exp
       | Local (Mutable, _) | Unbound ->
          begin
            puts ({ locals = Bindings.add id (value_of_exp exp) lstate.locals }, gstate) >> wrap unit_exp
          end
       | _ -> failwith "Assign"
     end
  | E_assign (LEXP_aux (LEXP_deref reference, annot), exp) when not (is_value reference) ->
     step reference >>= fun reference' -> wrap (E_assign (LEXP_aux (LEXP_deref reference', annot), exp))
  | E_assign (LEXP_aux (LEXP_deref reference, annot), exp) ->
     let name = coerce_ref (value_of_exp reference) in
     gets >>= fun (lstate, gstate) ->
     if Bindings.mem (mk_id name) gstate.registers && gstate.allow_registers then
       puts (lstate, { gstate with registers = Bindings.add (mk_id name) (value_of_exp exp) gstate.registers }) >> wrap unit_exp
     else
       failwith "Assign to nonexistent register"
  | E_assign (LEXP_aux (LEXP_tup lexps, annot), exp) -> failwith "Tuple assignment"
  | E_assign (LEXP_aux (LEXP_vector_concat lexps, annot), exp) -> failwith "Vector concat assignment"
     (*
     let values = coerce_tuple (value_of_exp exp) in
     wrap (E_block (List.map2 (fun lexp v -> E_aux (E_assign (lexp, exp_of_value v), (Parse_ast.Unknown, None))) lexps values))
      *)

  | E_try (exp, pexps) when is_value exp -> return exp
  | E_try (exp, pexps) ->
     begin
       catch (step exp) >>= fun exp' ->
       match exp' with
       | Left exn -> wrap (E_case (exp_of_value exn, pexps))
       | Right exp' -> wrap (E_try (exp', pexps))
     end

  | E_for (id, exp_from, exp_to, exp_step, ord, body) when is_value exp_from && is_value exp_to && is_value exp_step ->
     let v_from = value_of_exp exp_from in
     let v_to = value_of_exp exp_to in
     let v_step = value_of_exp exp_step in
     begin match ord with
     | Ord_aux (Ord_inc, _) ->
        begin match value_gt [v_from; v_to] with
        | V_bool true -> wrap (E_lit (L_aux (L_unit, Parse_ast.Unknown)))
        | V_bool false ->
           wrap (E_block [subst id v_from body; E_aux (E_for (id, exp_of_value (value_add_int [v_from; v_step]), exp_to, exp_step, ord, body), annot)])
        | _ -> assert false
        end
     | Ord_aux (Ord_dec, _) ->
        begin match value_lt [v_from; v_to] with
        | V_bool true -> wrap (E_lit (L_aux (L_unit, Parse_ast.Unknown)))
        | V_bool false ->
           wrap (E_block [subst id v_from body; E_aux (E_for (id, exp_of_value (value_sub_int [v_from; v_step]), exp_to, exp_step, ord, body), annot)])
        | _ -> assert false
        end
     | Ord_aux (Ord_var _, _) -> failwith "Polymorphic order in foreach"
     end
  | E_for (id, exp_from, exp_to, exp_step, ord, body) when is_value exp_to && is_value exp_step ->
     step exp_from >>= fun exp_from' -> wrap (E_for (id, exp_from', exp_to, exp_step, ord, body))
  | E_for (id, exp_from, exp_to, exp_step, ord, body) when is_value exp_step ->
     step exp_to >>= fun exp_to' -> wrap (E_for (id, exp_from, exp_to', exp_step, ord, body))
  | E_for (id, exp_from, exp_to, exp_step, ord, body) ->
     step exp_step >>= fun exp_step' -> wrap (E_for (id, exp_from, exp_to, exp_step', ord, body))

  | E_sizeof _ | E_constraint _ -> assert false (* Must be re-written before interpreting *)

  | _ -> failwith ("Unimplemented " ^ string_of_exp orig_exp)

and combine _ v1 v2 =
  match (v1, v2) with
  | None, None -> None
  | Some v1, None -> Some v1
  | None, Some v2 -> Some v2
  | Some v1, Some v2 -> failwith "Pattern binds same identifier twice!"

and exp_of_lexp (LEXP_aux (lexp_aux, _) as lexp) =
  match lexp_aux with
  | LEXP_id id -> mk_exp (E_id id)
  | LEXP_memory (f, args) -> mk_exp (E_app (f, args))
  | LEXP_cast (typ, id) -> mk_exp (E_cast (typ, mk_exp (E_id id)))
  | LEXP_deref exp -> mk_exp (E_app (mk_id "_reg_deref", [exp]))
  | LEXP_tup lexps -> mk_exp (E_tuple (List.map exp_of_lexp lexps))
  | LEXP_vector (lexp, exp) -> mk_exp (E_vector_access (exp_of_lexp lexp, exp))
  | LEXP_vector_range (lexp, exp1, exp2) -> mk_exp (E_vector_subrange (exp_of_lexp lexp, exp1, exp2))
  | LEXP_vector_concat [] -> failwith "Empty LEXP_vector_concat node in exp_of_lexp"
  | LEXP_vector_concat [lexp] -> exp_of_lexp lexp
  | LEXP_vector_concat (lexp :: lexps) -> mk_exp (E_vector_append (exp_of_lexp lexp, exp_of_lexp (mk_lexp (LEXP_vector_concat lexps))))
  | LEXP_field (lexp, id) -> mk_exp (E_field (exp_of_lexp lexp, id))

and pattern_match env (P_aux (p_aux, (l, _)) as pat) value =
  match p_aux with
  | P_lit lit -> eq_value (value_of_lit lit) value, Bindings.empty
  | P_wild -> true, Bindings.empty
  | P_or(pat1, pat2) ->
     let (m1, b1) = pattern_match env pat1 value in
     let (m2, b2) = pattern_match env pat2 value in
     (* todo: maybe add assertion that bindings are consistent or empty? *)
     (m1 || m2, Bindings.merge combine b1 b2)
  | P_not(pat) ->
     let (m, b) = pattern_match env pat value in
     (* todo: maybe add assertion that binding is empty *)
     (not m, b)
  | P_as (pat, id) ->
     let matched, bindings = pattern_match env pat value in
     matched, Bindings.add id value bindings
  | P_typ (_, pat) -> pattern_match env pat value
  | P_id id ->
     let open Type_check in
     begin
       match Env.lookup_id id env with
       | Enum _ ->
          if is_ctor value && string_of_id id = fst (coerce_ctor value)
          then true, Bindings.empty
          else false, Bindings.empty
       | _ -> true, Bindings.singleton id value
     end
  | P_var (pat, _) -> pattern_match env pat value
  | P_app (id, pats) ->
     let (ctor, vals) = coerce_ctor value in
     if Id.compare id (mk_id ctor) = 0 then
       let matches = List.map2 (pattern_match env) pats vals in
       List.for_all fst matches, List.fold_left (Bindings.merge combine) Bindings.empty (List.map snd matches)
     else
       false, Bindings.empty
  | P_record _ -> assert false (* TODO *)
  | P_vector pats ->
     let matches = List.map2 (pattern_match env) pats (coerce_gv value) in
     List.for_all fst matches, List.fold_left (Bindings.merge combine) Bindings.empty (List.map snd matches)
  | P_vector_concat [] -> eq_value (V_vector []) value, Bindings.empty
  | P_vector_concat (pat :: pats) ->
     (* We have to use the annotation on each member of the
        vector_concat pattern to figure out it's length. Due to the
        recursive call that has an empty_tannot we must not use the
        annotation in the whole vector_concat pattern. *)
     let open Type_check in
     begin match destruct_vector (env_of_pat pat) (typ_of_pat pat) with
     | Some (Nexp_aux (Nexp_constant n, _), _, _) ->
        let init, rest = Util.take (Big_int.to_int n) (coerce_gv value), Util.drop (Big_int.to_int n) (coerce_gv value) in
        let init_match, init_bind = pattern_match env pat (V_vector init) in
        let rest_match, rest_bind = pattern_match env (P_aux (P_vector_concat pats, (l, empty_tannot))) (V_vector rest) in
        init_match && rest_match, Bindings.merge combine init_bind rest_bind
     | _ -> failwith ("Bad vector annotation " ^ string_of_typ (Type_check.typ_of_pat pat))
     end
  | P_tup [pat] -> pattern_match env pat value
  | P_tup pats | P_list pats ->
     let matches = List.map2 (pattern_match env) pats (coerce_listlike value) in
     List.for_all fst matches, List.fold_left (Bindings.merge combine) Bindings.empty (List.map snd matches)
  | P_cons (hd_pat, tl_pat) ->
     begin match coerce_cons value with
     | Some (hd_value, tl_values) ->
        let hd_match, hd_bind = pattern_match env hd_pat hd_value in
        let tl_match, tl_bind = pattern_match env tl_pat (V_list tl_values) in
        hd_match && tl_match, Bindings.merge combine hd_bind tl_bind
     | None -> failwith "Cannot match cons pattern against non-list"
     end
  | P_string_append _ -> assert false (* TODO *)

let exp_of_fundef (FD_aux (FD_function (_, _, _, funcls), annot)) value =
  let pexp_of_funcl (FCL_aux (FCL_Funcl (_, pexp), _)) = pexp in
  E_aux (E_case (exp_of_value value, List.map pexp_of_funcl funcls), annot)

let rec ast_letbinds (Defs defs) =
  match defs with
  | [] -> []
  | DEF_val lb :: defs -> lb :: ast_letbinds (Defs defs)
  | _ :: defs -> ast_letbinds (Defs defs)

let initial_lstate =
  { locals = Bindings.empty }

let stack_cont (_, _, cont) = cont
let stack_string (str, _, _) = str
let stack_state (_, lstate, _) = lstate

type frame =
  | Done of state * value
  | Step of string Lazy.t * state * (Type_check.tannot exp) monad * (string Lazy.t * lstate * (return_value -> (Type_check.tannot exp) monad)) list
  | Break of frame

let rec eval_frame' = function
  | Done (state, v) -> Done (state, v)
  | Break frame -> Break frame
  | Step (out, state, m, stack) ->
     match (m, stack) with
     | Pure v, [] when is_value v -> Done (state, value_of_exp v)
     | Pure v, (head :: stack') when is_value v ->
        Step (stack_string head, (stack_state head, snd state), stack_cont head (Return_ok (value_of_exp v)), stack')
     | Pure exp', _ ->
        let out' = lazy (Pretty_print_sail.to_string (Pretty_print_sail.doc_exp exp')) in
        Step (out', state, step exp', stack)
     | Yield (Call(id, vals, cont)), _ when string_of_id id = "break" ->
        let arg = if List.length vals != 1 then tuple_value vals else List.hd vals in
        let body = exp_of_fundef (Bindings.find id (snd state).fundefs) arg in
        Break (Step (lazy "", (initial_lstate, snd state), return body, (out, fst state, cont) :: stack))
     | Yield (Call(id, vals, cont)), _ ->
        let arg = if List.length vals != 1 then tuple_value vals else List.hd vals in
        let body = exp_of_fundef (Bindings.find id (snd state).fundefs) arg in
        Step (lazy "", (initial_lstate, snd state), return body, (out, fst state, cont) :: stack)
     | Yield (Gets cont), _ ->
        eval_frame' (Step (out, state, cont state, stack))
     | Yield (Puts (state', cont)), _ ->
        eval_frame' (Step (out, state', cont (), stack))
     | Yield (Early_return v), [] -> Done (state, v)
     | Yield (Early_return v), (head :: stack') ->
        Step (stack_string head, (stack_state head, snd state), stack_cont head (Return_ok v), stack')
     | Yield (Assertion_failed msg), _ ->
        failwith msg
     | Yield (Exception v), [] ->
        failwith ("Uncaught Exception" |> Util.cyan |> Util.clear)
     | Yield (Exception v), (head :: stack') ->
        Step (stack_string head, (stack_state head, snd state), stack_cont head (Return_exception v), stack')

let eval_frame frame =
  try eval_frame' frame with
  | Type_check.Type_error (l, err) ->
     raise (Reporting.err_typ l (Type_error.string_of_type_error err))

let rec run_frame frame =
  match frame with
  | Done (state, v) -> v
  | Step (lazy_str, _, _, _) ->
     run_frame (eval_frame frame)
  | Break frame ->
     run_frame (eval_frame frame)

let eval_exp state exp =
  run_frame (Step (lazy "", state, return exp, []))

let initial_gstate primops ast =
  { registers = Bindings.empty;
    allow_registers = true;
    primops = primops;
    letbinds = ast_letbinds ast;
    fundefs = Bindings.empty;
  }

let rec initialize_registers gstate =
  let process_def = function
    | DEF_reg_dec (DEC_aux (DEC_config (id, typ, exp), _)) ->
       { gstate with registers = Bindings.add id (eval_exp (initial_lstate, gstate) exp) gstate.registers }
    | DEF_fundef fdef ->
       { gstate with fundefs = Bindings.add (id_of_fundef fdef) fdef gstate.fundefs }
    | _ -> gstate
  in
  function
  | Defs (def :: defs) ->
     initialize_registers (process_def def) (Defs defs)
  | Defs [] -> gstate

let initial_state ast primops = initial_lstate, initialize_registers (initial_gstate primops ast) ast
