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
module Big_int = Nat_big_num

type ctx =
  { lookup_id : id -> typ lvar;
    enums : IdSet.t Bindings.t;
    variants : IdSet.t Bindings.t
  }

type gpat =
  | GP_lit of lit
  | GP_wild
  | GP_vector of gpat list
  | GP_vector_concat of gpat list
  | GP_tup of gpat list
  | GP_list of gpat list
  | GP_cons of gpat * gpat
  | GP_or of gpat * gpat
  | GP_app of (gpat Bindings.t)
  | GP_record of (gpat Bindings.t)
  | GP_string_append of gpat list

let rec string_of_gpat = function
  | GP_lit lit -> string_of_lit lit
  | GP_wild -> "_"
  | GP_vector gpats -> "[" ^ Util.string_of_list ", " string_of_gpat gpats ^ "]"
  | GP_vector_concat gpats -> Util.string_of_list " @ " string_of_gpat gpats
  | GP_tup gpats -> "(" ^ Util.string_of_list ", " string_of_gpat gpats ^ ")"
  | GP_list gpats -> "[|" ^ Util.string_of_list ", " string_of_gpat gpats ^ "|]"
  | GP_cons (gpat1, gpat2) -> string_of_gpat gpat1 ^ " :: " ^ string_of_gpat gpat2
  | GP_or (gpat1, gpat2) -> string_of_gpat gpat1 ^ " | " ^ string_of_gpat gpat2
  | GP_app app ->
     Util.string_of_list "|" (fun (id, gpat) -> string_of_id id ^ string_of_gpat gpat) (Bindings.bindings app)
  | GP_record _ -> "GP RECORD"
  | GP_string_append gpats -> Util.string_of_list " ^^ " string_of_gpat gpats

let is_wild = function
  | GP_wild -> true
  | _ -> false

let rec generalize ctx (P_aux (p_aux, _) as pat) =
  match p_aux with
  | P_lit (L_aux (L_unit, _)) ->
     (* Unit pattern always matches on unit, so generalize to wildcard *)
     GP_wild
  | P_lit lit -> GP_lit lit
  | P_wild -> GP_wild
  | P_or (pat1, pat2) -> GP_or (generalize ctx pat1, generalize ctx pat2)
  | P_not(pat)       -> GP_wild (* TODO: How to generalize negated patterns? *)
  | P_as (pat, _) -> generalize ctx pat
  | P_typ (_, pat) -> generalize ctx pat (* This will possibly overapproximate how general P_typ is *)
  | P_id id ->
     begin
       match ctx.lookup_id id with
       | Unbound -> GP_wild
       | Local (Immutable, _) -> GP_wild
       | Register _ | Local (Mutable, _) -> Util.warn "Matching on register or mutable variable"; GP_wild
       | Enum _ -> GP_app (Bindings.singleton id GP_wild)
     end
  | P_var (pat, _) -> generalize ctx pat
  | P_vector pats ->
     let gpats = List.map (generalize ctx) pats in
     if List.for_all is_wild gpats then GP_wild else GP_vector gpats
  | P_vector_concat pats ->
     let gpats = List.map (generalize ctx) pats in
     if List.for_all is_wild gpats then GP_wild else GP_vector_concat gpats
  | P_tup pats ->
     let gpats = List.map (generalize ctx) pats in
     if List.for_all is_wild gpats then GP_wild else GP_tup gpats
  | P_list pats ->
     let gpats = List.map (generalize ctx) pats in
     if List.for_all is_wild gpats then GP_wild else GP_list gpats
  | P_cons (hd_pat, tl_pat) ->
     let ghd_pat = generalize ctx hd_pat in
     let gtl_pat = generalize ctx tl_pat in
     if is_wild ghd_pat && is_wild gtl_pat then GP_wild else GP_cons (ghd_pat, gtl_pat)
  | P_string_append pats ->
     let gpats = List.map (generalize ctx) pats in
     if List.for_all is_wild gpats then GP_wild else GP_string_append gpats
  | P_app (f, pats) ->
     let gpats = List.map (generalize ctx) pats in
     if List.for_all is_wild gpats then
       GP_app (Bindings.singleton f GP_wild)
     else
       GP_app (Bindings.singleton f (GP_tup gpats))
  | P_record (fpats, flag) ->
     let gfpats = List.concat (List.map (generalize_fpat ctx) fpats) in
     GP_record (List.fold_left (fun m (fid, gpat) -> Bindings.add fid gpat m) Bindings.empty gfpats)

and generalize_fpat ctx (FP_aux (FP_Fpat (field_id, pat), annot)) =
  let gpat = generalize ctx pat in
  if is_wild gpat then []
  else
    [(field_id, gpat)]

let vector_pat bits =
  let bit_pat = function
    | '0' -> GP_lit (mk_lit L_zero)
    | '1' -> GP_lit (mk_lit L_one)
    | _ -> failwith "Invalid bit pattern"
  in
  GP_vector (List.map bit_pat (Util.string_to_list bits))

let join_bits bits1 bits2 =
  let join_bit bit1 bit2 = match bit1, bit2 with
    | '0', '0' -> GP_lit (mk_lit L_zero)
    | '1', '1' -> GP_lit (mk_lit L_one)
    | _, _ -> GP_wild
  in
  let joined = List.map2 join_bit (Util.string_to_list bits1) (Util.string_to_list bits2) in
  if List.for_all is_wild joined then GP_wild else GP_vector joined

(* The join_lit function takes two patterns and produces a pattern
   that matches both literals *)
let rec join_lit (L_aux (l_aux1, _) as lit1) (L_aux (l_aux2, _) as lit2) =
  match l_aux1, l_aux2 with
  (* The only literal with type unit is the unit literal *)
  | L_unit, _ -> GP_lit lit1
  | _, L_unit -> GP_lit lit2

  (* Bit literals don't change when they're the same, become wildcard
     when we match both *)
  | L_zero, L_zero -> GP_lit lit1
  | L_one, L_one -> GP_lit lit1
  | L_zero, L_one -> GP_wild
  | L_one, L_zero -> GP_wild

  (* Boolean literals work the same as bit literals *)
  | L_false, L_false -> GP_lit lit1
  | L_true, L_true -> GP_lit lit2
  | L_false, L_true -> GP_wild
  | L_true, L_false -> GP_wild

  | L_hex hex, _ -> join_lit (mk_lit (L_bin (hex_to_bin hex))) lit2
  | _, L_hex hex -> join_lit lit1 (mk_lit (L_bin (hex_to_bin hex)))
  | L_bin bits1, L_bin bits2 -> join_bits bits1 bits2

  (* The set of numbers is infinite, so no finite sequence of number
     literals can match all numbers. As such we need a wildcard, so
     the join lit function just returns one of the two numbers. *)
  | L_num _, L_num _ -> GP_lit lit1

  (* Strings are similar to number literals. *)
  | L_string _, L_string _ -> GP_lit lit1

  | L_real _, L_real _ -> GP_lit lit1

  | L_undef, _ -> GP_wild
  | _, L_undef -> GP_wild

  | _, _ ->
     (* This shouldn't happen if both patterns are well-typed, but we
        include it here to ensure that join_lit won't fail. *)
     let message =
       Printf.sprintf "Have two differently typed pattern literals %s and %s matching the same thing"
                      (string_of_lit lit1) (string_of_lit lit2)
     in
     Util.warn message;
     GP_wild

let rec join ctx gpat1 gpat2 =
  (* prerr_endline ("Join :" ^ string_of_gpat gpat1 ^ " with " ^ string_of_gpat gpat2); *)
  match gpat1, gpat2 with
  | GP_wild, _ -> GP_wild
  | _, GP_wild -> GP_wild

  | GP_lit lit1, GP_lit lit2 -> join_lit lit1 lit2

  | GP_tup gpats1, GP_tup gpats2 ->
     let joined = List.map2 (join ctx) gpats1 gpats2 in
     if List.for_all is_wild joined then GP_wild else GP_tup joined

  | GP_lit (L_aux (L_hex hex, _)), GP_vector _ ->
     join ctx (vector_pat (hex_to_bin hex)) gpat2
  | GP_lit (L_aux (L_bin bin, _)), GP_vector _ ->
     join ctx (vector_pat bin) gpat2
  | GP_vector _, GP_lit (L_aux (L_hex hex, annot)) ->
     join ctx gpat1 (vector_pat (hex_to_bin hex))
  | GP_vector _, GP_lit (L_aux (L_bin bin, _)) ->
     join ctx gpat1 (vector_pat bin)

  | GP_vector gpats1, GP_vector gpats2 ->
     let joined = List.map2 (join ctx) gpats1 gpats2 in
     if List.for_all is_wild joined then GP_wild else GP_vector joined

  | GP_list gpats1, GP_list gpats2 ->
     let joined = List.map2 (join ctx) gpats1 gpats2 in
     if List.for_all is_wild joined then GP_wild else GP_list joined

  | GP_app ctors1, GP_app ctors2 ->
     let ctor_merge ctor args1 args2 =
       match args1, args2 with
       | None, None -> None
       | Some args1, None -> Some args1
       | None, Some args2 -> Some args2
       | Some args1, Some args2 -> Some (join ctx args1 args2)
     in
     let ctors = Bindings.merge ctor_merge ctors1 ctors2 in
     if Bindings.for_all (fun _ gpat -> is_wild gpat) ctors then
       let ids = IdSet.of_list (List.map fst (Bindings.bindings ctors)) in
       let enums = List.map snd (Bindings.bindings ctx.enums) in
       let variants = List.map snd (Bindings.bindings ctx.variants) in
       if List.exists (fun ids' -> IdSet.equal ids ids') (enums @ variants) then
         GP_wild
       else
         GP_app ctors
     else
       GP_app ctors

  | GP_or (gpat1, gpat2), gpat3 -> join ctx (join ctx gpat1 gpat2) gpat3
  | gpat1, GP_or (gpat2, gpat3) -> join ctx gpat1 (join ctx gpat2 gpat3)

  | _, _ -> GP_wild

let combine ctx gpat (l, pat) =
  match gpat, generalize ctx pat with
  | GP_wild, GP_app _ ->
     (* This warning liable to false positives as join returns a
        pattern that overapproximates what can match, so we only
        report when the second match is a constructor. *)
     Util.warn (Printf.sprintf "Possible redundant pattern match at %s\n" (Reporting.loc_to_string l));
     GP_wild
  | _, gpat' -> join ctx gpat gpat'

let rec cases_to_pats = function
  | [] -> []
  | Pat_aux (Pat_exp (P_aux (_, (l, _)) as pat, _), _) :: cases -> (l, pat) :: cases_to_pats cases
  (* We don't consider guarded cases *)
  | Pat_aux (Pat_when _, _) :: cases -> cases_to_pats cases

(* Just highlight the match keyword and not the whole match block. *)
let shrink_loc = function
  | Parse_ast.Range (n, m) ->
     Lexing.(Parse_ast.Range (n, { n with pos_cnum = n.pos_cnum + 5 }))
  | l -> l

let check l ctx cases =
  match cases_to_pats cases with
  | [] -> Util.warn (Printf.sprintf "No non-guarded patterns at %s\n" (Reporting.loc_to_string (shrink_loc l)))
  | (_, pat) :: pats ->
     let top_pat = List.fold_left (combine ctx) (generalize ctx pat) pats in
     if is_wild top_pat then
       ()
     else
       let message =
         Printf.sprintf "Possible incomplete pattern match at %s\n\nMost general matched pattern is %s\n"
                        (Reporting.loc_to_string (shrink_loc l))
                        (string_of_gpat top_pat |> Util.cyan |> Util.clear)
       in
       Util.warn message
