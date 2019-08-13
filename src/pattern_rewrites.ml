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

let rec irrefutable (P_aux (aux, annot)) =
  let open Type_check in
  match aux with
  | P_id id ->
     let open Type_check in
     let env = env_of_annot annot in
     begin match Env.lookup_id id env with
     | Enum (Typ_aux (Typ_id enum_id, _)) ->
        List.compare_length_with (Env.get_enum enum_id env) 1 = 0
     | _ -> true
     end
  | P_app (ctor, args) ->
     Env.is_singleton_union_constructor ctor (env_of_annot annot) && List.for_all irrefutable args
  | P_wild -> true
  | P_lit _ | P_string_append _ | P_cons _ -> false
  | P_as (pat, _) | P_typ (_, pat) | P_var (pat, _) | P_view (pat, _, _) -> irrefutable pat
  | P_vector pats | P_vector_concat pats | P_list pats | P_tup pats -> List.for_all irrefutable pats
  | P_or _ | P_not _ -> Reporting.unreachable (fst annot) __POS__ "Or or not pattern found in replace_views"

(** [replace_views n p] removes all P_view nodes from a pattern p. It
   returns a triple (p', views, n') where p' is the updated pattern
   and views is a map (Bindings.t) from the identifiers that replaced
   each pattern to each view. Each view is replaced by an identifier
   m__X where X is a number starting from n. n' is 1 + the highest
   value of X (i.e. the next X that would be used) *)
let replace_views n pat =
  let m = ref n in
  let views = ref Bindings.empty in
  let rec replace_views' (P_aux (aux, annot)) =
    let aux = match aux with
      | P_view (pat, id, args) ->
         let replaced_id = mk_id ("m__" ^ string_of_int !m) in
         views := Bindings.add replaced_id (pat, id, args) !views;
         incr m;
         P_id replaced_id
      | P_lit _ | P_wild | P_id _ -> aux
      | P_as (pat, id) -> P_as (replace_views' pat, id)
      | P_typ (typ, pat) -> P_typ (typ, replace_views' pat)
      | P_var (pat, typ_pat) -> P_var (replace_views' pat, typ_pat)
      | P_app (id, pats) -> P_app (id, List.map replace_views' pats)
      | P_vector pats -> P_vector (List.map replace_views' pats)
      | P_vector_concat pats -> P_vector_concat (List.map replace_views' pats)
      | P_tup pats -> P_tup (List.map replace_views' pats)
      | P_list pats -> P_list (List.map replace_views' pats)
      | P_cons (pat1, pat2) -> P_cons (replace_views' pat1, replace_views' pat2)
      | P_string_append pats -> P_string_append (List.map replace_views' pats)
      | P_or _ | P_not _ -> Reporting.unreachable (fst annot) __POS__ "Or or not pattern found in replace_views"
    in
    P_aux (aux, annot)
  in
  let pat = replace_views' pat in
  pat, !views, !m

let rec rewrite_views n = function
  | [] -> []
  | pexp :: pexps ->
     let pat, guard, exp, annot = destruct_pexp pexp in
     let pat, views, n' = replace_views n pat in
     if Bindings.is_empty views then (
       pexp :: rewrite_views n pexps
     ) else if Bindings.for_all (fun _ (pat, _, _) -> irrefutable pat) views && guard = None then (
       let wrap_view replaced_id (pat, id, args) exp =
         E_aux (E_let (LB_aux (LB_val (pat, E_aux (E_app (id, args @ [E_aux (E_id replaced_id, annot)]), annot)), annot), exp), annot)
       in
       construct_pexp (pat, guard, Bindings.fold wrap_view views exp, annot) :: rewrite_views n pexps
     ) else (
       Reporting.unreachable Parse_ast.Unknown __POS__ "Could not re-write view patterns"
     )
