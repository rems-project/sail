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
(* open Type_check *)

type state = St

let value_of_lit (L_aux (l_aux, _)) =
  match l_aux with
  | L_unit -> V_unit
  | L_zero -> V_bit B0
  | L_one -> V_bit B1
  | L_true -> V_bool true
  | L_false -> V_bool false
  | L_string str -> V_string str
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

let exp_of_value v = (E_aux (E_internal_value v, (Parse_ast.Unknown, None)))
let value_of_exp = function
  | (E_aux (E_internal_value v, _)) -> v
  | _ -> failwith "value_of_exp coerction failed"

(**************************************************************************)
(* 1. Interpreter Monad                                                   *)
(**************************************************************************)

type 'a response =
  | Final of value
  | Exception of value
  | Assertion_failed of string
  | Call of id * value list * (value -> 'a)
  | Gets of (state -> 'a)
  | Puts of state * 'a

and 'a monad =
  | Pure of 'a
  | Yield of ('a monad response)

let map_response f = function
  | Final v -> Final v
  | Exception v -> Exception v
  | Assertion_failed str -> Assertion_failed str
  | Gets g -> Gets (fun s -> f (g s))
  | Puts (s, x) -> Puts (s, f x)
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

let call (f : id) (args : value list) : value monad =
  Yield (Call (f, args, fun v -> Pure v))

let throw v = Yield (Exception v)

let gets : state monad =
  Yield (Gets (fun s -> Pure s))

let puts (s : state) : unit monad =
  Yield (Puts (s, Pure ()))

let final v = Yield (Final v)

let assertion_failed msg = Yield (Assertion_failed msg)

let liftM2 f m1 m2 = m1 >>= fun x -> m2 >>= fun y -> return (f x y)

let rec subst id value (E_aux (e_aux, annot) as exp) =
  let wrap e_aux = E_aux (e_aux, annot) in
  let e_aux = match e_aux with
    | E_block exps -> E_block (List.map (subst id value) exps)
    | E_nondet exps -> E_nondet (List.map (subst id value) exps)
    | E_id id' -> if Id.compare id id' = 0 then unaux_exp (exp_of_value value) else E_id id'
    | E_cast (typ, exp) -> E_cast (typ, subst id value exp)
    | E_app (fn, exps) -> E_app (fn, List.map (subst id value) exps)
    | _ -> assert false (* TODO *)
  in
  wrap e_aux


(**************************************************************************)
(* 2. Expression Evaluation                                               *)
(**************************************************************************)

let rec step (E_aux (e_aux, annot)) =
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

  | E_assert (exp, msg) when is_true exp -> wrap (E_lit (L_aux (L_unit, Parse_ast.Unknown)))
  | E_assert (exp, msg) when is_false exp -> assertion_failed "FIXME"
  | E_assert (exp, msg) ->
     step exp >>= fun exp' -> wrap (E_assert (exp', msg))

  | E_app (id, exps) ->
     let evaluated, unevaluated = Util.take_drop is_value exps in
     begin
       let open Type_check in
       match unevaluated with
       | exp :: exps ->
          step exp >>= fun exp' -> wrap (E_app (id, evaluated @ exp' :: exps))
       | [] when Env.is_union_constructor id (env_of_annot annot) ->
          return (exp_of_value (V_ctor (string_of_id id, List.map value_of_exp evaluated)))
       | [] when Env.is_extern id (env_of_annot annot) "interpreter" ->
          begin
            let primop = StringMap.find (Env.get_extern id (env_of_annot annot) "interpreter") primops in
            return (exp_of_value (primop (List.map value_of_exp evaluated)))
          end
       | [] -> liftM exp_of_value (call id (List.map value_of_exp evaluated))
     end
  | E_app_infix (x, id, y) when is_value x && is_value y ->
     liftM exp_of_value (call id [value_of_exp x; value_of_exp y])
  | E_app_infix (x, id, y) when is_value x ->
     step y >>= fun y' -> wrap (E_app_infix (x, id, y'))
  | E_app_infix (x, id, y) ->
     step x >>= fun x' -> wrap (E_app_infix (x', id, y))

  | E_return exp when is_value exp -> final (value_of_exp exp)
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
     let matched, bindings = pattern_match pat (value_of_exp exp) in
     if matched then
       return  (List.fold_left (fun body (id, v) -> subst id v body) body (Bindings.bindings bindings))
     else
       wrap (E_case (exp, pexps))

  | E_cast (typ, exp) -> return exp

  | E_throw exp when is_value exp -> throw (value_of_exp exp)
  | E_throw exp -> step exp >>= fun exp' -> wrap (E_throw exp')

  | E_try (exp, pexps) when is_value exp -> return exp
  | E_try (exp, pexps) ->
     begin
       catch (step exp) >>= fun exp' ->
       match exp' with
       | Left exn -> wrap (E_case (exp_of_value exn, pexps))
       | Right exp' -> wrap (E_try (exp', pexps))
     end

  | E_sizeof _ | E_constraint _ -> assert false (* Must be re-written before interpreting *)

  | _ -> assert false (* TODO *)

and combine _ v1 v2 =
  match (v1, v2) with
  | None, None -> None
  | Some v1, None -> Some v1
  | None, Some v2 -> Some v2
  | Some v1, Some v2 -> failwith "Pattern binds same identifier twice!"

and pattern_match (P_aux (p_aux, _) as pat) value =
  print_endline ("Matching: " ^ string_of_pat pat ^ " with " ^ string_of_value value |> Util.yellow |> Util.clear);
  match p_aux with
  | P_lit lit -> eq_value (value_of_lit lit) value, Bindings.empty
  | P_wild -> true, Bindings.empty
  | P_as (pat, id) ->
     let matched, bindings = pattern_match pat value in
     matched, Bindings.add id value bindings
  | P_typ (_, pat) -> pattern_match pat value
  | P_id id -> true, Bindings.singleton id value
  | P_var (pat, _) -> pattern_match pat value
  | P_app (id, pats) ->
     let (ctor, vals) = coerce_ctor value in
     if Id.compare id (mk_id ctor) = 0 then
       let matches = List.map2 pattern_match pats vals in
       List.for_all fst matches, List.fold_left (Bindings.merge combine) Bindings.empty (List.map snd matches)
     else
       false, Bindings.empty
  | P_record _ -> assert false (* TODO *)
  | P_vector _ -> assert false (* TODO *)
  | P_vector_concat _ -> assert false (* TODO *)
  | P_tup pats | P_list pats ->
     let matches = List.map2 pattern_match pats (coerce_listlike value) in
     List.for_all fst matches, List.fold_left (Bindings.merge combine) Bindings.empty (List.map snd matches)
  | P_cons _ -> assert false (* TODO *)

let exp_of_fundef (FD_aux (FD_function (_, _, _, funcls), _)) value =
  let pexp_of_funcl (FCL_aux (FCL_Funcl (_, pexp), _)) = pexp in
  E_aux (E_case (exp_of_value value, List.map pexp_of_funcl funcls), (Parse_ast.Unknown, None))

let rec get_fundef id (Defs defs) =
  match defs with
  | [] -> failwith (string_of_id id ^ " definition not found")
  | (DEF_fundef fdef) :: _ when Id.compare id (id_of_fundef fdef) = 0 -> fdef
  | _ :: defs -> get_fundef id (Defs defs)

let rec untilM p f x =
  if p x then
    return x
  else
    f (return x) >>= fun x' -> untilM p f x'

type trace =
  | Done of value
  | Step of (Type_check.tannot exp) monad * (value -> (Type_check.tannot exp) monad) list

let rec eval_exp ast m =
  match m with
  | Pure v when is_value v -> Done (value_of_exp v)
  | Pure exp' ->
     Pretty_print_sail2.pretty_sail stdout (Pretty_print_sail2.doc_exp exp');
     print_newline ();
     Step (step exp', [])
  | Yield (Call (id, vals, cont)) ->
     print_endline ("Calling " ^ string_of_id id |> Util.cyan |> Util.clear);
     let arg = if List.length vals != 1 then tuple_value vals else List.hd vals in
     let body = exp_of_fundef (get_fundef id ast) arg in
     Step (return body, [cont])
  | _ -> assert false

