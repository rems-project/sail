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
open Type_check
open PPrint

module Big_int = Nat_big_num

(**************************************************************************)
(* 1. Conversion to A-normal form (ANF)                                   *)
(**************************************************************************)

(* The first step in compiling sail is converting the Sail expression
   grammar into A-normal form. Essentially this converts expressions
   such as f(g(x), h(y)) into something like:

   let v0 = g(x) in let v1 = h(x) in f(v0, v1)

   Essentially the arguments to every function must be trivial, and
   complex expressions must be let bound to new variables, or used in
   a block, assignment, or control flow statement (if, for, and
   while/until loops). The aexp datatype represents these expressions,
   while aval represents the trivial values.

   The convention is that the type of an aexp is given by last
   argument to a constructor. It is omitted where it is obvious - for
   example all for loops have unit as their type. If some constituent
   part of the aexp has an annotation, the it refers to the previous
   argument, so in

   AE_let (id, typ1, _, body, typ2)

   typ1 is the type of the bound identifer, whereas typ2 is the type
   of the whole let expression (and therefore also the body).

   See Flanagan et al's 'The Essence of Compiling with Continuations'
   *)
type 'a aexp = AE_aux of 'a aexp_aux * Env.t * l

and 'a aexp_aux =
  | AE_val of 'a aval
  | AE_app of id * ('a aval) list * 'a
  | AE_cast of 'a aexp * 'a
  | AE_assign of id * 'a * 'a aexp
  | AE_let of mut * id * 'a * 'a aexp * 'a aexp * 'a
  | AE_block of ('a aexp) list * 'a aexp * 'a
  | AE_return of 'a aval * 'a
  | AE_throw of 'a aval * 'a
  | AE_if of 'a aval * 'a aexp * 'a aexp * 'a
  | AE_field of 'a aval * id * 'a
  | AE_case of 'a aval * ('a apat * 'a aexp * 'a aexp) list * 'a
  | AE_try of 'a aexp * ('a apat * 'a aexp * 'a aexp) list * 'a
  | AE_record_update of 'a aval * ('a aval) Bindings.t * 'a
  | AE_for of id * 'a aexp * 'a aexp * 'a aexp * order * 'a aexp
  | AE_loop of loop * 'a aexp * 'a aexp
  | AE_short_circuit of sc_op * 'a aval * 'a aexp

and sc_op = SC_and | SC_or

and 'a apat = AP_aux of 'a apat_aux * Env.t * l

and 'a apat_aux =
  | AP_tup of ('a apat) list
  | AP_id of id * 'a
  | AP_global of id * 'a
  | AP_app of id * 'a apat * 'a
  | AP_cons of 'a apat * 'a apat
  | AP_nil of 'a
  | AP_wild of 'a

and 'a aval =
  | AV_lit of lit * 'a
  | AV_id of id * 'a lvar
  | AV_ref of id * 'a lvar
  | AV_tuple of ('a aval) list
  | AV_list of ('a aval) list * 'a
  | AV_vector of ('a aval) list * 'a
  | AV_record of ('a aval) Bindings.t * 'a
  | AV_C_fragment of fragment * 'a * ctyp

(* Renaming variables in ANF expressions *)

let rec apat_bindings (AP_aux (apat_aux, _, _)) =
  match apat_aux with
  | AP_tup apats -> List.fold_left IdSet.union IdSet.empty (List.map apat_bindings apats)
  | AP_id (id, _) -> IdSet.singleton id
  | AP_global (id, _) -> IdSet.empty
  | AP_app (id, apat, _) -> apat_bindings apat
  | AP_cons (apat1, apat2) -> IdSet.union (apat_bindings apat1) (apat_bindings apat2)
  | AP_nil _ -> IdSet.empty
  | AP_wild _ -> IdSet.empty

(** This function returns the types of all bound variables in a
   pattern. It ignores AP_global, apat_globals is used for that. *)
let rec apat_types (AP_aux (apat_aux, _, _)) =
  let merge id b1 b2 =
    match b1, b2 with
    | None,   None   -> None
    | Some v, None   -> Some v
    | None, Some v   -> Some v
    | Some _, Some _ -> assert false
  in
  match apat_aux with
  | AP_tup apats -> List.fold_left (Bindings.merge merge) Bindings.empty (List.map apat_types apats)
  | AP_id (id, typ) -> Bindings.singleton id typ
  | AP_global (id, _) -> Bindings.empty
  | AP_app (id, apat, _) -> apat_types apat
  | AP_cons (apat1, apat2) -> (Bindings.merge merge) (apat_types apat1) (apat_types apat2)
  | AP_nil _ -> Bindings.empty
  | AP_wild _ -> Bindings.empty

let rec apat_rename from_id to_id (AP_aux (apat_aux, env, l)) =
  let apat_aux = match apat_aux with
    | AP_tup apats -> AP_tup (List.map (apat_rename from_id to_id) apats)
    | AP_id (id, typ) when Id.compare id from_id = 0 -> AP_id (to_id, typ)
    | AP_id (id, typ) -> AP_id (id, typ)
    | AP_global (id, typ) -> AP_global (id, typ)
    | AP_app (ctor, apat, typ) -> AP_app (ctor, apat_rename from_id to_id apat, typ)
    | AP_cons (apat1, apat2) -> AP_cons (apat_rename from_id to_id apat1, apat_rename from_id to_id apat2)
    | AP_nil typ -> AP_nil typ
    | AP_wild typ -> AP_wild typ
  in
  AP_aux (apat_aux, env, l)

let rec aval_rename from_id to_id = function
  | AV_lit (lit, typ) -> AV_lit (lit, typ)
  | AV_id (id, lvar) when Id.compare id from_id = 0 -> AV_id (to_id, lvar)
  | AV_id (id, lvar) -> AV_id (id, lvar)
  | AV_ref (id, lvar) when Id.compare id from_id = 0 -> AV_ref (to_id, lvar)
  | AV_ref (id, lvar) -> AV_ref (id, lvar)
  | AV_tuple avals -> AV_tuple (List.map (aval_rename from_id to_id) avals)
  | AV_list (avals, typ) -> AV_list (List.map (aval_rename from_id to_id) avals, typ)
  | AV_vector (avals, typ) -> AV_vector (List.map (aval_rename from_id to_id) avals, typ)
  | AV_record (avals, typ) -> AV_record (Bindings.map (aval_rename from_id to_id) avals, typ)
  | AV_C_fragment (fragment, typ, ctyp) -> AV_C_fragment (frag_rename from_id to_id fragment, typ, ctyp)

let rec aexp_rename from_id to_id (AE_aux (aexp, env, l)) =
  let recur = aexp_rename from_id to_id in
  let aexp = match aexp with
    | AE_val aval -> AE_val (aval_rename from_id to_id aval)
    | AE_app (id, avals, typ) -> AE_app (id, List.map (aval_rename from_id to_id) avals, typ)
    | AE_cast (aexp, typ) -> AE_cast (recur aexp, typ)
    | AE_assign (id, typ, aexp) when Id.compare from_id id = 0 -> AE_assign (to_id, typ, aexp_rename from_id to_id aexp)
    | AE_assign (id, typ, aexp) -> AE_assign (id, typ, aexp_rename from_id to_id aexp)
    | AE_let (mut, id, typ1, aexp1, aexp2, typ2) when Id.compare from_id id = 0 -> AE_let (mut, id, typ1, recur aexp1, aexp2, typ2)
    | AE_let (mut, id, typ1, aexp1, aexp2, typ2) -> AE_let (mut, id, typ1, recur aexp1, recur aexp2, typ2)
    | AE_block (aexps, aexp, typ) -> AE_block (List.map recur aexps, recur aexp, typ)
    | AE_return (aval, typ) -> AE_return (aval_rename from_id to_id aval, typ)
    | AE_throw (aval, typ) -> AE_throw (aval_rename from_id to_id aval, typ)
    | AE_if (aval, then_aexp, else_aexp, typ) -> AE_if (aval_rename from_id to_id aval, recur then_aexp, recur else_aexp, typ)
    | AE_field (aval, id, typ) -> AE_field (aval_rename from_id to_id aval, id, typ)
    | AE_case (aval, apexps, typ) -> AE_case (aval_rename from_id to_id aval, List.map (apexp_rename from_id to_id) apexps, typ)
    | AE_try (aexp, apexps, typ) -> AE_try (aexp_rename from_id to_id aexp, List.map (apexp_rename from_id to_id) apexps, typ)
    | AE_record_update (aval, avals, typ) -> AE_record_update (aval_rename from_id to_id aval, Bindings.map (aval_rename from_id to_id) avals, typ)
    | AE_for (id, aexp1, aexp2, aexp3, order, aexp4) when Id.compare from_id to_id = 0 -> AE_for (id, aexp1, aexp2, aexp3, order, aexp4)
    | AE_for (id, aexp1, aexp2, aexp3, order, aexp4) -> AE_for (id, recur aexp1, recur aexp2, recur aexp3, order, recur aexp4)
    | AE_loop (loop, aexp1, aexp2) -> AE_loop (loop, recur aexp1, recur aexp2)
    | AE_short_circuit (op, aval, aexp) -> AE_short_circuit (op, aval_rename from_id to_id aval, recur aexp)
  in
  AE_aux (aexp, env, l)

and apexp_rename from_id to_id (apat, aexp1, aexp2) =
  if IdSet.mem from_id (apat_bindings apat) then
    (apat, aexp1, aexp2)
  else
    (apat, aexp_rename from_id to_id aexp1, aexp_rename from_id to_id aexp2)

let shadow_counter = ref 0

let new_shadow id =
  let shadow_id = append_id id ("shadow#" ^ string_of_int !shadow_counter) in
  incr shadow_counter;
  shadow_id

let rec no_shadow ids (AE_aux (aexp, env, l)) =
  let aexp = match aexp with
    | AE_val aval -> AE_val aval
    | AE_app (id, avals, typ) -> AE_app (id, avals, typ)
    | AE_cast (aexp, typ) -> AE_cast (no_shadow ids aexp, typ)
    | AE_assign (id, typ, aexp) -> AE_assign (id, typ, no_shadow ids aexp)
    | AE_let (mut, id, typ1, aexp1, aexp2, typ2) when IdSet.mem id ids ->
       let shadow_id = new_shadow id in
       let aexp1 = no_shadow ids aexp1 in
       let ids = IdSet.add shadow_id ids in
       AE_let (mut, shadow_id, typ1, aexp1, no_shadow ids (aexp_rename id shadow_id aexp2), typ2)
    | AE_let (mut, id, typ1, aexp1, aexp2, typ2) ->
       AE_let (mut, id, typ1, no_shadow ids aexp1, no_shadow (IdSet.add id ids) aexp2, typ2)
    | AE_block (aexps, aexp, typ) -> AE_block (List.map (no_shadow ids) aexps, no_shadow ids aexp, typ)
    | AE_return (aval, typ) -> AE_return (aval, typ)
    | AE_throw (aval, typ) -> AE_throw (aval, typ)
    | AE_if (aval, then_aexp, else_aexp, typ) -> AE_if (aval, no_shadow ids then_aexp, no_shadow ids else_aexp, typ)
    | AE_field (aval, id, typ) -> AE_field (aval, id, typ)
    | AE_case (aval, apexps, typ) -> AE_case (aval, List.map (no_shadow_apexp ids) apexps, typ)
    | AE_try (aexp, apexps, typ) -> AE_try (no_shadow ids aexp, List.map (no_shadow_apexp ids) apexps, typ)
    | AE_record_update (aval, avals, typ) -> AE_record_update (aval, avals, typ)
    | AE_for (id, aexp1, aexp2, aexp3, order, aexp4) when IdSet.mem id ids ->
       let shadow_id = new_shadow id in
       let aexp1 = no_shadow ids aexp1 in
       let aexp2 = no_shadow ids aexp2 in
       let aexp3 = no_shadow ids aexp3 in
       let ids = IdSet.add shadow_id ids in
       AE_for (shadow_id, aexp1, aexp2, aexp3, order, no_shadow ids (aexp_rename id shadow_id aexp4))
    | AE_for (id, aexp1, aexp2, aexp3, order, aexp4) ->
       let ids = IdSet.add id ids in
       AE_for (id, no_shadow ids aexp1, no_shadow ids aexp2, no_shadow ids aexp3, order, no_shadow ids aexp4)
    | AE_loop (loop, aexp1, aexp2) -> AE_loop (loop, no_shadow ids aexp1, no_shadow ids aexp2)
    | AE_short_circuit (op, aval, aexp) -> AE_short_circuit (op, aval, no_shadow ids aexp)
  in
  AE_aux (aexp, env, l)

and no_shadow_apexp ids (apat, aexp1, aexp2) =
  let shadows = IdSet.inter (apat_bindings apat) ids in
  let shadows = List.map (fun id -> id, new_shadow id) (IdSet.elements shadows) in
  let rename aexp = List.fold_left (fun aexp (from_id, to_id) -> aexp_rename from_id to_id aexp) aexp shadows in
  let rename_apat apat = List.fold_left (fun apat (from_id, to_id) -> apat_rename from_id to_id apat) apat shadows in
  let ids = IdSet.union (apat_bindings apat) (IdSet.union ids (IdSet.of_list (List.map snd shadows))) in
  (rename_apat apat, no_shadow ids (rename aexp1), no_shadow ids (rename aexp2))

(* Map over all the avals in an aexp. *)
let rec map_aval f (AE_aux (aexp, env, l)) =
  let aexp = match aexp with
    | AE_val v -> AE_val (f env l v)
    | AE_cast (aexp, typ) -> AE_cast (map_aval f aexp, typ)
    | AE_assign (id, typ, aexp) -> AE_assign (id, typ, map_aval f aexp)
    | AE_app (id, vs, typ) -> AE_app (id, List.map (f env l) vs, typ)
    | AE_let (mut, id, typ1, aexp1, aexp2, typ2) ->
       AE_let (mut, id, typ1, map_aval f aexp1, map_aval f aexp2, typ2)
    | AE_block (aexps, aexp, typ) -> AE_block (List.map (map_aval f) aexps, map_aval f aexp, typ)
    | AE_return (aval, typ) -> AE_return (f env l aval, typ)
    | AE_throw (aval, typ) -> AE_throw (f env l aval, typ)
    | AE_if (aval, aexp1, aexp2, typ2) ->
       AE_if (f env l aval, map_aval f aexp1, map_aval f aexp2, typ2)
    | AE_loop (loop_typ, aexp1, aexp2) -> AE_loop (loop_typ, map_aval f aexp1, map_aval f aexp2)
    | AE_for (id, aexp1, aexp2, aexp3, order, aexp4) ->
       AE_for (id, map_aval f aexp1, map_aval f aexp2, map_aval f aexp3, order, map_aval f aexp4)
    | AE_record_update (aval, updates, typ) ->
       AE_record_update (f env l aval, Bindings.map (f env l) updates, typ)
    | AE_field (aval, field, typ) ->
       AE_field (f env l aval, field, typ)
    | AE_case (aval, cases, typ) ->
       AE_case (f env l aval, List.map (fun (pat, aexp1, aexp2) -> pat, map_aval f aexp1, map_aval f aexp2) cases, typ)
    | AE_try (aexp, cases, typ) ->
       AE_try (map_aval f aexp, List.map (fun (pat, aexp1, aexp2) -> pat, map_aval f aexp1, map_aval f aexp2) cases, typ)
    | AE_short_circuit (op, aval, aexp) -> AE_short_circuit (op, f env l aval, map_aval f aexp)
  in
  AE_aux (aexp, env, l)

(* Map over all the functions in an aexp. *)
let rec map_functions f (AE_aux (aexp, env, l)) =
  let aexp = match aexp with
    | AE_app (id, vs, typ) -> f env l id vs typ
    | AE_cast (aexp, typ) -> AE_cast (map_functions f aexp, typ)
    | AE_assign (id, typ, aexp) -> AE_assign (id, typ, map_functions f aexp)
    | AE_short_circuit (op, aval, aexp) -> AE_short_circuit (op, aval, map_functions f aexp)
    | AE_let (mut, id, typ1, aexp1, aexp2, typ2) -> AE_let (mut, id, typ1, map_functions f aexp1, map_functions f aexp2, typ2)
    | AE_block (aexps, aexp, typ) -> AE_block (List.map (map_functions f) aexps, map_functions f aexp, typ)
    | AE_if (aval, aexp1, aexp2, typ) ->
       AE_if (aval, map_functions f aexp1, map_functions f aexp2, typ)
    | AE_loop (loop_typ, aexp1, aexp2) -> AE_loop (loop_typ, map_functions f aexp1, map_functions f aexp2)
    | AE_for (id, aexp1, aexp2, aexp3, order, aexp4) ->
       AE_for (id, map_functions f aexp1, map_functions f aexp2, map_functions f aexp3, order, map_functions f aexp4)
    | AE_case (aval, cases, typ) ->
       AE_case (aval, List.map (fun (pat, aexp1, aexp2) -> pat, map_functions f aexp1, map_functions f aexp2) cases, typ)
    | AE_try (aexp, cases, typ) ->
       AE_try (map_functions f aexp, List.map (fun (pat, aexp1, aexp2) -> pat, map_functions f aexp1, map_functions f aexp2) cases, typ)
    | AE_field _ | AE_record_update _ | AE_val _ | AE_return _ | AE_throw _ as v -> v
  in
  AE_aux (aexp, env, l)

(* For debugging we provide a pretty printer for ANF expressions. *)

let pp_lvar lvar doc =
  match lvar with
  | Register (_, _, typ) ->
     string "[R/" ^^ string (string_of_typ typ |> Util.yellow |> Util.clear) ^^ string "]" ^^ doc
  | Local (Mutable, typ) ->
     string "[M/" ^^ string (string_of_typ typ |> Util.yellow |> Util.clear) ^^ string "]" ^^ doc
  | Local (Immutable, typ) ->
     string "[I/" ^^ string (string_of_typ typ |> Util.yellow |> Util.clear) ^^ string "]" ^^ doc
  | Enum typ ->
     string "[E/" ^^ string (string_of_typ typ |> Util.yellow |> Util.clear) ^^ string "]" ^^ doc
  | Unbound -> string "[?]" ^^ doc

let pp_annot typ doc =
  string "[" ^^ string (string_of_typ typ |> Util.yellow |> Util.clear) ^^ string "]" ^^ doc

let pp_order = function
  | Ord_aux (Ord_inc, _) -> string "inc"
  | Ord_aux (Ord_dec, _) -> string "dec"
  | _ -> assert false (* Order types have been specialised, so no polymorphism in C backend. *)

let rec pp_aexp (AE_aux (aexp, _, _)) =
  match aexp with
  | AE_val v -> pp_aval v
  | AE_cast (aexp, typ) ->
     pp_annot typ (string "$" ^^ pp_aexp aexp)
  | AE_assign (id, typ, aexp) ->
     pp_annot typ (pp_id id) ^^ string " := " ^^ pp_aexp aexp
  | AE_app (id, args, typ) ->
     pp_annot typ (pp_id id ^^ parens (separate_map (comma ^^ space) pp_aval args))
  | AE_short_circuit (SC_or, aval, aexp) ->
     pp_aval aval ^^ string " || " ^^ pp_aexp aexp
  | AE_short_circuit (SC_and, aval, aexp) ->
     pp_aval aval ^^ string " && " ^^ pp_aexp aexp
  | AE_let (mut, id, id_typ, binding, body, typ) -> group
     begin
       let let_doc = string (match mut with Immutable -> "let" | Mutable -> "let mut") in
       match binding with
       | AE_aux (AE_let _, _, _) ->
          (pp_annot typ (separate space [string "let"; pp_annot id_typ (pp_id id); string "="])
           ^^ hardline ^^ nest 2 (pp_aexp binding))
          ^^ hardline ^^ string "in" ^^ space ^^ pp_aexp body
       | _ ->
          pp_annot typ (separate space [string "let"; pp_annot id_typ (pp_id id); string "="; pp_aexp binding; string "in"])
          ^^ hardline ^^ pp_aexp body
     end
  | AE_if (cond, then_aexp, else_aexp, typ) ->
     pp_annot typ (separate space [ string "if"; pp_aval cond;
                                    string "then"; pp_aexp then_aexp;
                                    string "else"; pp_aexp else_aexp ])
  | AE_block (aexps, aexp, typ) ->
     pp_annot typ (surround 2 0 lbrace (pp_block (aexps @ [aexp])) rbrace)
  | AE_return (v, typ) -> pp_annot typ (string "return" ^^ parens (pp_aval v))
  | AE_throw (v, typ) -> pp_annot typ (string "throw" ^^ parens (pp_aval v))
  | AE_loop (While, aexp1, aexp2) ->
     separate space [string "while"; pp_aexp aexp1; string "do"; pp_aexp aexp2]
  | AE_loop (Until, aexp1, aexp2) ->
     separate space [string "repeat"; pp_aexp aexp2; string "until"; pp_aexp aexp1]
  | AE_for (id, aexp1, aexp2, aexp3, order, aexp4) ->
     let header =
       string "foreach" ^^ space ^^
         group (parens (separate (break 1)
                                 [ pp_id id;
                                   string "from " ^^ pp_aexp aexp1;
                                   string "to " ^^ pp_aexp aexp2;
                                   string "by " ^^ pp_aexp aexp3;
                                   string "in " ^^ pp_order order ]))
     in
     header ^//^ pp_aexp aexp4
  | AE_field (aval, field, typ) -> pp_annot typ (parens (pp_aval aval ^^ string "." ^^ pp_id field))
  | AE_case (aval, cases, typ) ->
     pp_annot typ (separate space [string "match"; pp_aval aval; pp_cases cases])
  | AE_try (aexp, cases, typ) ->
     pp_annot typ (separate space [string "try"; pp_aexp aexp; pp_cases cases])
  | AE_record_update (aval, updates, typ) ->
     braces (pp_aval aval ^^ string " with "
             ^^ separate (string ", ") (List.map (fun (id, aval) -> pp_id id ^^ string " = " ^^ pp_aval aval)
                                                 (Bindings.bindings updates)))

and pp_apat (AP_aux (apat_aux, _, _)) =
  match apat_aux with
  | AP_wild _ -> string "_"
  | AP_id (id, typ) -> pp_annot typ (pp_id id)
  | AP_global (id, _) -> pp_id id
  | AP_tup apats -> parens (separate_map (comma ^^ space) pp_apat apats)
  | AP_app (id, apat, typ) -> pp_annot typ (pp_id id ^^ parens (pp_apat apat))
  | AP_nil _ -> string "[||]"
  | AP_cons (hd_apat, tl_apat) -> pp_apat hd_apat ^^ string " :: " ^^ pp_apat tl_apat

and pp_cases cases = surround 2 0 lbrace (separate_map (comma ^^ hardline) pp_case cases) rbrace

and pp_case (apat, guard, body) =
  separate space [pp_apat apat; string "if"; pp_aexp guard; string "=>"; pp_aexp body]

and pp_block = function
  | [] -> string "()"
  | [aexp] -> pp_aexp aexp
  | aexp :: aexps -> pp_aexp aexp ^^ semi ^^ hardline ^^ pp_block aexps

and pp_aval = function
  | AV_lit (lit, typ) -> pp_annot typ (string (string_of_lit lit))
  | AV_id (id, lvar) -> pp_lvar lvar (pp_id id)
  | AV_tuple avals -> parens (separate_map (comma ^^ space) pp_aval avals)
  | AV_ref (id, lvar) -> string "ref" ^^ space ^^ pp_lvar lvar (pp_id id)
  | AV_C_fragment (frag, typ, ctyp) ->
     pp_annot typ (string ("(" ^ string_of_ctyp ctyp ^ ")" ^ string_of_fragment frag |> Util.cyan |> Util.clear))
  | AV_vector (avals, typ) ->
     pp_annot typ (string "[" ^^ separate_map (comma ^^ space) pp_aval avals ^^ string "]")
  | AV_list (avals, typ) ->
     pp_annot typ (string "[|" ^^ separate_map (comma ^^ space) pp_aval avals ^^ string "|]")
  | AV_record (fields, typ) ->
     pp_annot typ (string "struct {"
                   ^^ separate_map (comma ^^ space) (fun (id, field) -> pp_id id ^^ string " = " ^^ pp_aval field) (Bindings.bindings fields)
                   ^^ string "}")

let ae_lit lit typ = AE_val (AV_lit (lit, typ))

(** GLOBAL: gensym_counter is used to generate fresh identifiers where
   needed. It should be safe to reset between top level
   definitions. **)
let gensym_counter = ref 0

let gensym () =
  let id = mk_id ("gs#" ^ string_of_int !gensym_counter) in
  incr gensym_counter;
  id

let rec split_block l = function
  | [exp] -> [], exp
  | exp :: exps ->
     let exps, last = split_block l exps in
     exp :: exps, last
  | [] ->
     raise (Reporting.err_unreachable l __POS__ "empty block found when converting to ANF")

let rec anf_pat ?global:(global=false) (P_aux (p_aux, annot) as pat) =
  let mk_apat aux = AP_aux (aux, env_of_annot annot, fst annot) in
  match p_aux with
  | P_id id when global -> mk_apat (AP_global (id, typ_of_pat pat))
  | P_id id -> mk_apat (AP_id (id, typ_of_pat pat))
  | P_wild -> mk_apat (AP_wild (typ_of_pat pat))
  | P_tup pats -> mk_apat (AP_tup (List.map (fun pat -> anf_pat ~global:global pat) pats))
  | P_app (id, [subpat]) -> mk_apat (AP_app (id, anf_pat ~global:global subpat, typ_of_pat pat))
  | P_app (id, pats) -> mk_apat (AP_app (id, mk_apat (AP_tup (List.map (fun pat -> anf_pat ~global:global pat) pats)), typ_of_pat pat))
  | P_typ (_, pat) -> anf_pat ~global:global pat
  | P_var (pat, _) -> anf_pat ~global:global pat
  | P_cons (hd_pat, tl_pat) -> mk_apat (AP_cons (anf_pat ~global:global hd_pat, anf_pat ~global:global tl_pat))
  | P_list pats -> List.fold_right (fun pat apat -> mk_apat (AP_cons (anf_pat ~global:global pat, apat))) pats (mk_apat (AP_nil (typ_of_pat pat)))
  | P_lit (L_aux (L_unit, _)) -> mk_apat (AP_wild (typ_of_pat pat))
  | _ ->
     raise (Reporting.err_unreachable (fst annot) __POS__
       ("Could not convert pattern to ANF: " ^ string_of_pat pat))

let rec apat_globals (AP_aux (aux, _, _)) =
  match aux with
  | AP_nil _ | AP_wild _ | AP_id _ -> []
  | AP_global (id, typ) -> [(id, typ)]
  | AP_tup apats -> List.concat (List.map apat_globals apats)
  | AP_app (_, apat, _) -> apat_globals apat
  | AP_cons (hd_apat, tl_apat) -> apat_globals hd_apat @ apat_globals tl_apat

let rec anf (E_aux (e_aux, ((l, _) as exp_annot)) as exp) =
  let mk_aexp aexp = AE_aux (aexp, env_of_annot exp_annot, l) in

  let to_aval (AE_aux (aexp_aux, env, l) as aexp) =
    let mk_aexp aexp = AE_aux (aexp, env, l) in
    match aexp_aux with
    | AE_val v -> (v, fun x -> x)
    | AE_short_circuit (_, _, _) ->
       let id = gensym () in
       (AV_id (id, Local (Immutable, bool_typ)), fun x -> mk_aexp (AE_let (Immutable, id, bool_typ, aexp, x, typ_of exp)))
    | AE_app (_, _, typ)
      | AE_let (_, _, _, _, _, typ)
      | AE_return (_, typ)
      | AE_throw (_, typ)
      | AE_cast (_, typ)
      | AE_if (_, _, _, typ)
      | AE_field (_, _, typ)
      | AE_case (_, _, typ)
      | AE_try (_, _, typ)
      | AE_record_update (_, _, typ)
      | AE_block (_, _, typ) ->
       let id = gensym () in
       (AV_id (id, Local (Immutable, typ)), fun x -> mk_aexp (AE_let (Immutable, id, typ, aexp, x, typ_of exp)))
    | AE_assign _ | AE_for _ | AE_loop _ ->
       let id = gensym () in
       (AV_id (id, Local (Immutable, unit_typ)), fun x -> mk_aexp (AE_let (Immutable, id, unit_typ, aexp, x, typ_of exp)))
  in
  match e_aux with
  | E_lit lit -> mk_aexp (ae_lit lit (typ_of exp))

  | E_block [] ->
     Util.warn (Reporting.loc_to_string l
                ^ "\n\nTranslating empty block (possibly assigning to an uninitialized variable at the end of a block?)");
     mk_aexp (ae_lit (L_aux (L_unit, l)) (typ_of exp))
  | E_block exps ->
     let exps, last = split_block l exps in
     let aexps = List.map anf exps in
     let alast = anf last in
     mk_aexp (AE_block (aexps, alast, typ_of exp))

  | E_assign (LEXP_aux (LEXP_deref dexp, _), exp) ->
     let gs = gensym () in
     mk_aexp (AE_let (Mutable, gs, typ_of dexp, anf dexp, mk_aexp (AE_assign (gs, typ_of dexp, anf exp)), unit_typ))

  | E_assign (LEXP_aux (LEXP_id id, _), exp)
    | E_assign (LEXP_aux (LEXP_cast (_, id), _), exp) ->
     let aexp = anf exp in
     mk_aexp (AE_assign (id, lvar_typ (Env.lookup_id id (env_of exp)), aexp))

  | E_assign (lexp, _) ->
     raise (Reporting.err_unreachable l __POS__
       ("Encountered complex l-expression " ^ string_of_lexp lexp ^ " when converting to ANF"))

  | E_loop (loop_typ, cond, exp) ->
     let acond = anf cond in
     let aexp = anf exp in
     mk_aexp (AE_loop (loop_typ, acond, aexp))

  | E_for (id, exp1, exp2, exp3, order, body) ->
     let aexp1, aexp2, aexp3, abody = anf exp1, anf exp2, anf exp3, anf body in
     mk_aexp (AE_for (id, aexp1, aexp2, aexp3, order, abody))

  | E_if (cond, then_exp, else_exp) ->
     let cond_val, wrap = to_aval (anf cond) in
     let then_aexp = anf then_exp in
     let else_aexp = anf else_exp in
     wrap (mk_aexp (AE_if (cond_val, then_aexp, else_aexp, typ_of exp)))

  | E_app_infix (x, Id_aux (Id op, l), y) ->
     anf (E_aux (E_app (Id_aux (DeIid op, l), [x; y]), exp_annot))
  | E_app_infix (x, Id_aux (DeIid op, l), y) ->
     anf (E_aux (E_app (Id_aux (Id op, l), [x; y]), exp_annot))

  | E_vector exps ->
     let aexps = List.map anf exps in
     let avals = List.map to_aval aexps in
     let wrap = List.fold_left (fun f g x -> f (g x)) (fun x -> x) (List.map snd avals) in
     wrap (mk_aexp (AE_val (AV_vector (List.map fst avals, typ_of exp))))

  | E_list exps ->
     let aexps = List.map anf exps in
     let avals = List.map to_aval aexps in
     let wrap = List.fold_left (fun f g x -> f (g x)) (fun x -> x) (List.map snd avals) in
     wrap (mk_aexp (AE_val (AV_list (List.map fst avals, typ_of exp))))

  | E_field (field_exp, id) ->
     let aval, wrap = to_aval (anf field_exp) in
     wrap (mk_aexp (AE_field (aval, id, typ_of exp)))

  | E_record_update (exp, fexps) ->
     let anf_fexp (FE_aux (FE_Fexp (id, exp), _)) =
       let aval, wrap = to_aval (anf exp) in
       (id, aval), wrap
     in
     let aval, exp_wrap = to_aval (anf exp) in
     let fexps = List.map anf_fexp fexps in
     let wrap = List.fold_left (fun f g x -> f (g x)) (fun x -> x) (List.map snd fexps) in
     let record = List.fold_left (fun r (id, aval) -> Bindings.add id aval r) Bindings.empty (List.map fst fexps) in
     exp_wrap (wrap (mk_aexp (AE_record_update (aval, record, typ_of exp))))

  | E_app (id, [exp1; exp2]) when string_of_id id = "and_bool" ->
     let aexp1 = anf exp1 in
     let aexp2 = anf exp2 in
     let aval1, wrap = to_aval aexp1 in
     wrap (mk_aexp (AE_short_circuit (SC_and, aval1, aexp2)))

  | E_app (id, [exp1; exp2]) when string_of_id id = "or_bool" ->
     let aexp1 = anf exp1 in
     let aexp2 = anf exp2 in
     let aval1, wrap = to_aval aexp1 in
     wrap (mk_aexp (AE_short_circuit (SC_or, aval1, aexp2)))

  | E_app (id, exps) ->
     let aexps = List.map anf exps in
     let avals = List.map to_aval aexps in
     let wrap = List.fold_left (fun f g x -> f (g x)) (fun x -> x) (List.map snd avals) in
     wrap (mk_aexp (AE_app (id, List.map fst avals, typ_of exp)))

  | E_throw exn_exp ->
     let aexp = anf exn_exp in
     let aval, wrap = to_aval aexp in
     wrap (mk_aexp (AE_throw (aval, typ_of exp)))

  | E_exit exp ->
     let aexp = anf exp in
     let aval, wrap = to_aval aexp in
     wrap (mk_aexp (AE_app (mk_id "sail_exit", [aval], unit_typ)))

  | E_return ret_exp ->
     let aexp = anf ret_exp in
     let aval, wrap = to_aval aexp in
     wrap (mk_aexp (AE_return (aval, typ_of exp)))

  | E_assert (exp1, exp2) ->
     let aexp1 = anf exp1 in
     let aexp2 = anf exp2 in
     let aval1, wrap1 = to_aval aexp1 in
     let aval2, wrap2 = to_aval aexp2 in
     wrap1 (wrap2 (mk_aexp (AE_app (mk_id "sail_assert", [aval1; aval2], unit_typ))))

  | E_cons (exp1, exp2) ->
     let aexp1 = anf exp1 in
     let aexp2 = anf exp2 in
     let aval1, wrap1 = to_aval aexp1 in
     let aval2, wrap2 = to_aval aexp2 in
     wrap1 (wrap2 (mk_aexp (AE_app (mk_id "cons", [aval1; aval2], unit_typ))))

  | E_id id ->
     let lvar = Env.lookup_id id (env_of exp) in
     begin match lvar with
     | _ -> mk_aexp (AE_val (AV_id (id, lvar)))
     end

  | E_ref id ->
     let lvar = Env.lookup_id id (env_of exp) in
     mk_aexp (AE_val (AV_ref (id, lvar)))

  | E_case (match_exp, pexps) ->
     let match_aval, match_wrap = to_aval (anf match_exp) in
     let anf_pexp (Pat_aux (pat_aux, _)) =
       match pat_aux with
       | Pat_when (pat, guard, body) ->
          (anf_pat pat, anf guard, anf body)
       | Pat_exp (pat, body) ->
          (anf_pat pat, mk_aexp (AE_val (AV_lit (mk_lit (L_true), bool_typ))), anf body)
     in
     match_wrap (mk_aexp (AE_case (match_aval, List.map anf_pexp pexps, typ_of exp)))

  | E_try (match_exp, pexps) ->
     let match_aexp = anf match_exp in
     let anf_pexp (Pat_aux (pat_aux, _)) =
       match pat_aux with
       | Pat_when (pat, guard, body) ->
          (anf_pat pat, anf guard, anf body)
       | Pat_exp (pat, body) ->
          (anf_pat pat, mk_aexp (AE_val (AV_lit (mk_lit (L_true), bool_typ))), anf body)
     in
     mk_aexp (AE_try (match_aexp, List.map anf_pexp pexps, typ_of exp))

  | E_var (LEXP_aux (LEXP_id id, _), binding, body)
    | E_var (LEXP_aux (LEXP_cast (_, id), _), binding, body)
    | E_let (LB_aux (LB_val (P_aux (P_id id, _), binding), _), body) ->
     let env = env_of body in
     let lvar = Env.lookup_id id env in
     mk_aexp (AE_let (Mutable, id, lvar_typ lvar, anf binding, anf body, typ_of exp))

  | E_var (lexp, _, _) ->
     raise (Reporting.err_unreachable l __POS__
       ("Encountered complex l-expression " ^ string_of_lexp lexp ^ " when converting to ANF"))

  | E_let (LB_aux (LB_val (pat, binding), _), body) ->
     anf (E_aux (E_case (binding, [Pat_aux (Pat_exp (pat, body), (Parse_ast.Unknown, empty_tannot))]), exp_annot))

  | E_tuple exps ->
     let aexps = List.map anf exps in
     let avals = List.map to_aval aexps in
     let wrap = List.fold_left (fun f g x -> f (g x)) (fun x -> x) (List.map snd avals) in
     wrap (mk_aexp (AE_val (AV_tuple (List.map fst avals))))

  | E_record fexps ->
     let anf_fexp (FE_aux (FE_Fexp (id, exp), _)) =
       let aval, wrap = to_aval (anf exp) in
       (id, aval), wrap
     in
     let fexps = List.map anf_fexp fexps in
     let wrap = List.fold_left (fun f g x -> f (g x)) (fun x -> x) (List.map snd fexps) in
     let record = List.fold_left (fun r (id, aval) -> Bindings.add id aval r) Bindings.empty (List.map fst fexps) in
     wrap (mk_aexp (AE_val (AV_record (record, typ_of exp))))

  | E_cast (typ, exp) -> mk_aexp (AE_cast (anf exp, typ))

  | E_vector_access _ | E_vector_subrange _ | E_vector_update _ | E_vector_update_subrange _ | E_vector_append _ ->
     (* Should be re-written by type checker *)
     raise (Reporting.err_unreachable l __POS__ "encountered raw vector operation when converting to ANF")

  | E_internal_value _ ->
     (* Interpreter specific *)
     raise (Reporting.err_unreachable l __POS__ "encountered E_internal_value when converting to ANF")

  | E_sizeof _ | E_constraint _ ->
     (* Sizeof nodes removed by sizeof rewriting pass *)
     raise (Reporting.err_unreachable l __POS__ "encountered E_sizeof or E_constraint node when converting to ANF")

  | E_nondet _ ->
     (* We don't compile E_nondet nodes *)
     raise (Reporting.err_unreachable l __POS__ "encountered E_nondet node when converting to ANF")

  | E_internal_return _ | E_internal_plet _ ->
     raise (Reporting.err_unreachable l __POS__ "encountered unexpected internal node when converting to ANF")
