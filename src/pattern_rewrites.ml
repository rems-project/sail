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

(**************************************************************************)
(* 1. Pattern rewrites                                                    *)
(**************************************************************************)

type action =
  | Subst_id of (id -> unit guard list)
  | No_change

(** The Pattern_rewriter module implements a bottom up traversal of
   all patterns with the AST, applying actions at each pattern. *)
module Pattern_rewriter = struct
  open Type_check

  module type Config = sig
    val generate_id : unit -> id
    val action : Type_check.tannot pat -> action
  end

  module Make (C : Config) : sig
    val rewrite : tannot pat -> tannot pat * tannot guard list
  end = struct

    let rec rewrite' env (P_aux (aux, annot)) =
      let wrap gs (P_aux (_, annot) as pat) =
        match C.action pat with
        | No_change -> pat, []
        | Subst_id to_guards ->
           let typ = typ_of_annot annot in
           let replaced_id = C.generate_id () in
           let env = Env.add_local replaced_id (Immutable, typ) env in
           let gs', env = check_guards env (to_guards replaced_id) in
           P_aux (P_typ (typ, P_aux (P_id replaced_id, annot)), annot), gs @ gs'
      in
      match aux with
      | P_view (pat, id, args) ->
         let pat, guards = rewrite' env pat in
         wrap guards (P_aux (P_view (pat, id, args), annot))
      | P_lit _ | P_wild | P_id _ ->
         wrap [] (P_aux (aux, annot))
      | P_as (pat, id) ->
         let pat, guards = rewrite' env pat in
         wrap guards (P_aux (P_as (pat, id), annot))
      | P_typ (typ, pat) ->
         let pat, guards = rewrite' env pat in
         wrap guards (P_aux (P_typ (typ, pat), annot))
      | P_app (id, pats) ->
         let rewritten = List.map (rewrite' env) pats in
         wrap (List.concat (List.map snd rewritten)) (P_aux (P_app (id, List.map fst rewritten), annot))
      | P_vector pats ->
         let rewritten = List.map (rewrite' env) pats in
         wrap (List.concat (List.map snd rewritten)) (P_aux (P_vector (List.map fst rewritten), annot))
      | P_vector_concat pats ->
         let rewritten = List.map (rewrite' env) pats in
         wrap (List.concat (List.map snd rewritten)) (P_aux (P_vector_concat (List.map fst rewritten), annot))
      | P_tup pats ->
         let rewritten = List.map (rewrite' env) pats in
         wrap (List.concat (List.map snd rewritten)) (P_aux (P_tup (List.map fst rewritten), annot))
      | P_list pats ->
         let rewritten = List.map (rewrite' env) pats in
         wrap (List.concat (List.map snd rewritten)) (P_aux (P_list (List.map fst rewritten), annot))
      | P_cons (pat1, pat2) ->
         let pat1, guards1 = rewrite' env pat1 in
         let pat2, guards2 = rewrite' env pat2 in
         wrap (guards1 @ guards2) (P_aux (P_cons (pat1, pat2), annot))
      | P_string_append pats ->
         let rewritten = List.map (rewrite' env) pats in
         wrap (List.concat (List.map snd rewritten)) (P_aux (P_string_append (List.map fst rewritten), annot))
      | P_var (pat, tpat) ->
         let pat, guards = rewrite' env pat in
         wrap guards (P_aux (P_var (pat, tpat), annot))
      | P_or _ | P_not _ -> Reporting.unreachable (fst annot) __POS__ "Or and not patterns are currently not implemented"

    let rewrite (P_aux (_, annot) as pat) = rewrite' (env_of_annot annot) pat

  end
end

(* Rewrite a view pattern of the form

   p <- f(x, y, z) => ...
   into
   id let p = f(x, y, z, id) => ...

   i.e. it turns view patterns into pattern guards. *)
module View_config = struct
  let generate_id () = mk_id "view"

  let action = function
    | P_aux (P_view (pat, id, args), (l, _)) ->
       let g_l = gen_loc l in
       let args = List.map Type_check.strip_exp args in
       Subst_id (fun s ->
           [G_aux (G_pattern (Type_check.strip_pat pat, mk_exp ~loc:g_l (E_app (id, args @ [mk_exp ~loc:g_l (E_id s)]))), g_l)]
         )
    | _ -> No_change
end

module View_rewriter = Pattern_rewriter.Make(View_config)

(* Rewrite a bitvector pattern of the form

   p_1 @ ... @ p_n => ...
   into
   id let p_1 = id[hi_1 .. lo_1], ... , let p_n = id[hi_n .. lo_n] => ... *)
module Bitvector_concat_config = struct
  let generate_id () = mk_id "v"

  let action = function
    | P_aux (P_vector_concat pats, annot) ->
       let open Type_check in
       let g_l = gen_loc (fst annot) in
       let env = env_of_annot annot in
       let typ = typ_of_annot annot in
       let lengths = List.map (fun pat ->
                         match destruct_bitvector env typ with
                         | Some (Nexp_aux (Nexp_constant n, _), _) -> n
                         | _ -> Reporting.unreachable g_l __POS__ "Non-constant width bitvector concat subpattern found in rewrite"
                       ) pats in
       let pats = List.map Type_check.strip_pat pats in
       Subst_id (fun s ->
           List.map2 (fun pat len -> G_aux (G_pattern (pat, mk_exp ~loc:g_l (E_vector_subrange (mk_exp ~loc:g_l (E_id s), assert false, assert false))), g_l)) pats lengths
         )
    | _ -> No_change
end

module Bitvector_concat_rewriter = Pattern_rewriter.Make(Bitvector_concat_config)

(* Rewrite a string append pattern of the form

   s_1 ^ ... ^ s_n => ...
   into
   id let (g_1, ... , g_n) = split(), let s_1 = g_1, ... , let s_n = g_n => ...

   where g_1 to g_n are the groups described by the regular expression that splits the string pattern, performed by split() *)
module String_append_config = struct
  let generate_id () = mk_id "s"

  let action _ = No_change
end

module String_append_rewriter = Pattern_rewriter.Make(String_append_config)

module Literal_config = struct
  let generate_id () = mk_id "l"

  let action _ = No_change
end

module Literal_rewriter = Pattern_rewriter.Make(Literal_config)

(**************************************************************************)
(* 2. Guard removal                                                       *)
(**************************************************************************)
