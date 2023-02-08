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

(* The code in this file was used to generate a first draft of the monad for
   the new concurrency interface in src/gen_lib/sail2_concurrency_interface.lem,
   but that has since been edited manually *)

open Libsail
open Ast
open Ast_defs
open Ast_util
open PPrint
open Pretty_print_common
open Pretty_print_lem
open Callgraph

let outcome_spec_of_def = function DEF_outcome (OV_aux (outcome, _), _) -> Some outcome | _ -> None

let outcome_specs_of_ast ast = Util.map_filter outcome_spec_of_def ast.defs

let id_of_outcome (OV_outcome (id, _, _)) = id

let gen_monad_def env ast =
  let specs = outcome_specs_of_ast ast in
  let kopts_of_typschm (TypSchm_aux (TypSchm_ts (tq, typ), _)) =
    KOptSet.union (KOptSet.of_list (quant_kopts tq)) (kopts_of_typ typ)
  in
  let kid_of_kopt (KOpt_aux (KOpt_kind (_, kid), _)) = kid in
  let type_kids_of_spec (OV_outcome (_, typschm, kids)) =
    kopts_of_typschm typschm |> KOptSet.inter (KOptSet.of_list kids)
  in
  let type_kopts =
    List.map type_kids_of_spec specs |> List.fold_left (fun kopts kopts' -> KOptSet.union kopts kopts') KOptSet.empty
  in
  let type_kids = KOptSet.fold (fun kopt kids -> KidSet.add (kid_of_kopt kopt) kids) type_kopts KidSet.empty in
  let default_kids = List.map mk_kid ["regval"; "a"; "e"] in
  let monad_typ_kids = KidSet.elements type_kids @ default_kids in
  let monad_typ_args = List.map (fun kid -> arg_typ (mk_typ (Typ_var kid))) monad_typ_kids in
  let monad_typq = mk_typquant (List.map (fun kid -> mk_qi_id K_type kid) monad_typ_kids) in
  let monad_typ = app_typ (mk_id "monad") monad_typ_args in
  let mk_variant ?(final = false) id args ret =
    let cont = if final then [] else if is_unit_typ ret then [monad_typ] else [function_typ [ret] monad_typ] in
    let outcome_typ = tuple_typ (args @ cont) in
    Tu_aux (Tu_ty_id (outcome_typ, id), Parse_ast.Unknown)
  in
  let outcome_of_spec (OV_outcome (id, typschm, _)) =
    let typ = match typschm with TypSchm_aux (TypSchm_ts (_, typ), _) -> typ in
    let args, ret = match typ with Typ_aux (Typ_fn (args, ret), _) -> (args, ret) | typ -> ([], typ) in
    mk_variant id args ret
  in
  let default_outcomes =
    [
      mk_variant ~final:true (mk_id "Done") [mk_typ (Typ_var (mk_kid "a"))] unit_typ;
      mk_variant ~final:true (mk_id "Fail") [string_typ] unit_typ;
      mk_variant ~final:true (mk_id "Exception") [mk_typ (Typ_var (mk_kid "e"))] unit_typ;
      mk_variant ~final:false (mk_id "Read_reg") [string_typ] (mk_typ (Typ_var (mk_kid "regval")));
      mk_variant ~final:false (mk_id "Write_reg") [string_typ; mk_typ (Typ_var (mk_kid "regval"))] unit_typ;
    ]
  in
  let outcomes = default_outcomes @ List.map outcome_of_spec specs in
  TD_aux (TD_variant (mk_id "monad", monad_typq, outcomes, false), no_annot)

let outcome_dependencies env ast =
  let module NodeSet = Set.Make (Node) in
  let module G = Graph.Make (Node) in
  let outcome_ids = List.map id_of_outcome (outcome_specs_of_ast ast) in
  let roots = List.map (fun id -> Outcome id) outcome_ids |> NodeSet.of_list in
  let cuts = NodeSet.empty in
  let g = graph_of_ast ast in
  let g = G.prune roots cuts g in
  filter_ast cuts g ast

let doc_dependencies effect_info env ast =
  let deps_ast = outcome_dependencies env ast in
  let type_defs = List.filter (function DEF_type _ -> true | _ -> false) deps_ast.defs in
  separate empty (List.map (doc_def_lem effect_info env) type_defs)

let doc_lem_monad env ast = doc_typdef_lem env (gen_monad_def env ast)

let output_lem_monad effect_info env ast =
  let imports = ["Pervasives_extra"; "Sail2_values"; "Sail2_string"] in
  List.iter (fun lib -> print_endline ("open import " ^ lib)) imports;
  print_endline "";
  print Stdlib.stdout (doc_dependencies effect_info env ast);
  print_endline "";
  print Stdlib.stdout (doc_lem_monad env ast);
  print_endline "";
  Stdlib.flush Stdlib.stdout
