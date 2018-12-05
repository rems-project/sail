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

let funcl_id (FCL_aux (FCL_Funcl (id, _), _)) = id

let rec last_scattered_funcl id = function
  | DEF_scattered (SD_aux (SD_funcl funcl, _)) :: _
       when Id.compare (funcl_id funcl) id = 0 -> false
  | _ :: defs -> last_scattered_funcl id defs
  | [] -> true

let rec last_scattered_mapcl id = function
  | DEF_scattered (SD_aux (SD_mapcl (mid, _), _)) :: _
       when Id.compare mid id = 0 -> false
  | _ :: defs -> last_scattered_mapcl id defs
  | [] -> true

(* Nothing cares about these and the AST should be changed *)
let fake_effect_opt l = Effect_opt_aux (Effect_opt_pure, gen_loc l)
let fake_rec_opt l = Rec_aux (Rec_rec, gen_loc l)

let no_tannot_opt l = Typ_annot_opt_aux (Typ_annot_opt_none, gen_loc l)

let rec get_union_clauses id = function
  | DEF_scattered (SD_aux (SD_unioncl (uid, tu), _)) :: defs when Id.compare id uid = 0 ->
     tu :: get_union_clauses id defs
  | def :: defs ->
     get_union_clauses id defs
  | [] -> []

let rec filter_union_clauses id = function
  | DEF_scattered (SD_aux (SD_unioncl (uid, tu), _)) :: defs when Id.compare id uid = 0 ->
     filter_union_clauses id defs
  | def :: defs ->
     def :: filter_union_clauses id defs
  | [] -> []

let rec descatter' funcls mapcls = function
  (* For scattered functions we collect all the seperate function
     clauses until we find the last one, then we turn that function
     clause into a DEF_fundef containing all the clauses. *)
  | DEF_scattered (SD_aux (SD_funcl funcl, (l, _))) :: defs
       when last_scattered_funcl (funcl_id funcl) defs ->
     let clauses = match Bindings.find_opt (funcl_id funcl) funcls with
       | Some clauses -> List.rev (funcl :: clauses)
       | None -> [funcl]
     in
     DEF_fundef (FD_aux (FD_function (fake_rec_opt l, no_tannot_opt l, fake_effect_opt l, clauses),
                         (gen_loc l, Type_check.empty_tannot)))
     :: descatter' funcls mapcls defs

  | DEF_scattered (SD_aux (SD_funcl funcl, _)) :: defs ->
     let id = funcl_id funcl in
     begin match Bindings.find_opt id funcls with
     | Some clauses -> descatter' (Bindings.add id (funcl :: clauses) funcls) mapcls defs
     | None -> descatter' (Bindings.add id [funcl] funcls) mapcls defs
     end

  (* Scattered mappings are handled the same way as scattered functions *)
  | DEF_scattered (SD_aux (SD_mapcl (id, mapcl), (l, tannot))) :: defs
       when last_scattered_mapcl id defs ->
     let clauses = match Bindings.find_opt id mapcls with
       | Some clauses -> List.rev (mapcl :: clauses)
       | None -> [mapcl]
     in
     DEF_mapdef (MD_aux (MD_mapping (id, no_tannot_opt l, clauses),
                         (gen_loc l, tannot)))
     :: descatter' funcls mapcls defs

  | DEF_scattered (SD_aux (SD_mapcl (id, mapcl), _)) :: defs ->
     begin match Bindings.find_opt id mapcls with
     | Some clauses -> descatter' funcls (Bindings.add id (mapcl :: clauses) mapcls) defs
     | None -> descatter' funcls (Bindings.add id [mapcl] mapcls) defs
     end

  (* For scattered unions, when we find a union declaration we
     immediately grab all the future clauses and turn it into a
     regular union declaration. *)
  | DEF_scattered (SD_aux (SD_variant (id, namescm, typq), (l, _))) :: defs ->
     let tus = get_union_clauses id defs in
     DEF_type (TD_aux (TD_variant (id, namescm, typq, tus, false), (gen_loc l, Type_check.empty_tannot)))
     :: descatter' funcls mapcls (filter_union_clauses id defs)

  (* Therefore we should never see SD_unioncl... *)
  | DEF_scattered (SD_aux (SD_unioncl _, (l, _))) :: defs ->
     raise (Reporting.err_unreachable l __POS__ "Found union clause during de-scattering")

  | def :: defs -> def :: descatter' funcls mapcls defs
  | [] -> []

let descatter (Defs defs) = Defs (descatter' Bindings.empty Bindings.empty defs)
