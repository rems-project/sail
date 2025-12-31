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
open Coq_def_annot
open Arg


(** Command-line flags *)
let opt_enabled = ref false
let opt_strict = ref false

(** Naming styles *)
type naming_style = 
  | PascalCase
  | SnakeCase
  | ScreamingSnakeCase
  | TrainCase
  | Any

type naming_config = {
  type_style : naming_style;
  function_style : naming_style;
  variable_style : naming_style;
  constant_style : naming_style;
  variant_style : naming_style;
}

let default_config = {
  type_style = PascalCase;
  function_style = SnakeCase;
  variable_style = SnakeCase;
  constant_style = ScreamingSnakeCase;
  variant_style = TrainCase;
}

let is_pascal_case s =
  if String.length s = 0 then false
  else
    let first_char = s.[0] in
    first_char >= 'A' && first_char <= 'Z' &&
    not (String.contains s '_')

let is_snake_case s =
  if String.length s = 0 then false
  else
    let first_char = s.[0] in
    (first_char >= 'a' && first_char <= 'z') &&
    String.for_all (fun c ->
      (c >= 'a' && c <= 'z') || (c >= '0' && c <= '9') || c = '_'
    ) s

let is_screaming_snake_case s =
  if String.length s = 0 then false
  else
    let first_char = s.[0] in
    (first_char >= 'A' && first_char <= 'Z') &&
    String.for_all (fun c ->
      (c >= 'A' && c <= 'Z') || (c >= '0' && c <= '9') || c = '_'
    ) s

let is_train_case s =
  if String.length s =0 then false 
  else
    let first_char =s.[0] in
    (first_char>= 'A' && first_char <= 'Z') &&
    String.for_all (fun c ->
      (c >= 'A' && c <= 'Z') || (c >= 'a' && c <= 'z') || (c >= '0' && c <= '9') || c = '_'
    ) s

let matches_style s = function
  | PascalCase -> is_pascal_case s
  | SnakeCase -> is_snake_case s
  | ScreamingSnakeCase -> is_screaming_snake_case s
  | TrainCase -> is_train_case s
  | Any -> true

let string_of_style = function
  | PascalCase -> "PascalCase (e.g., MemoryAccess)"
  | SnakeCase -> "snake_case (e.g., execute_load)"
  | ScreamingSnakeCase -> "SCREAMING_SNAKE_CASE (e.g., MAX_XLEN)"
  | TrainCase -> "Train_Case (e.g. State_Stop)"
  | Any -> "any"

type identifier_category =
  | Category_type
  | Category_function
  | Category_variable
  | Category_constant
  | Category_variant

let string_of_category = function
  | Category_type -> "Type"
  | Category_function -> "Function"
  | Category_variable -> "Variable"
  | Category_constant -> "Constant"
  | Category_variant -> "Variant"

(** Warning/error report *)
let report_naming_issue l id expected_style category =
  let name = string_of_id id in
  if not (matches_style name expected_style) then begin
    let message = Printf.sprintf "%s '%s' should use %s" 
      (string_of_category category) name (string_of_style expected_style) in
    if !opt_strict then
      raise (Reporting.err_general l message)
    else
      Reporting.warn "Naming convention" l message
  end

(** AST check *)
let rec check_pat config l = function
  | P_aux (P_id id, _) -> 
      report_naming_issue l id config.variable_style Category_variable
  | P_aux (P_tuple pats, _) -> 
      List.iter (check_pat config l) pats
  | P_aux (P_app (_, pats), _) -> 
      List.iter (check_pat config l) pats
  | P_aux (P_as (pat, id), _) ->
      report_naming_issue l id config.variable_style Category_variable;
      check_pat config l pat
  | P_aux (P_typ (_, pat), _) -> 
      check_pat config l pat
  | P_aux (P_var (pat, _), _) -> 
      check_pat config l pat
  | P_aux (P_list pats, _) -> 
      List.iter (check_pat config l) pats
  | P_aux (P_cons (p1, p2), _) -> 
      check_pat config l p1; 
      check_pat config l p2
  | P_aux (P_string_append pats, _) -> 
      List.iter (check_pat config l) pats
  | P_aux (P_vector pats, _) -> 
      List.iter (check_pat config l) pats
  | P_aux (P_vector_concat pats, _) -> 
      List.iter (check_pat config l) pats
  | P_aux (P_or (p1, p2), _) -> 
      check_pat config l p1; 
      check_pat config l p2
  | P_aux (P_not pat, _) -> 
      check_pat config l pat
  | P_aux (P_struct (_, fpats, _), _) -> 
      List.iter (fun (_, pat) -> check_pat config l pat) fpats
  | P_aux (P_lit _, _)
  | P_aux (P_wild, _)
  | P_aux (P_vector_subrange (_, _, _), _) -> ()

and check_pat_as_constant config l = function
  | P_aux (P_id id, _) -> 
      report_naming_issue l id config.constant_style Category_constant
  | P_aux (P_tuple pats, _) -> 
      List.iter (check_pat_as_constant config l) pats
  | P_aux (P_typ (_, pat), _) -> 
      check_pat_as_constant config l pat
  | P_aux (P_wild, _)
  | P_aux (P_lit _, _)
  | P_aux (P_vector_subrange (_, _, _), _) -> ()
  | P_aux (P_string_append pats, _) -> List.iter (check_pat_as_constant config l) pats
  | P_aux (P_or (p1, p2), _) -> check_pat_as_constant config l p1; check_pat_as_constant config l p2
  | P_aux (P_not pat, _) -> check_pat_as_constant config l pat
  | P_aux (P_as (pat, id), _) -> report_naming_issue l id config.constant_style Category_constant; check_pat_as_constant config l pat
  | P_aux (P_var (pat, _), _) -> check_pat_as_constant config l pat
  | P_aux (P_app (_, pats), _) -> List.iter (check_pat_as_constant config l) pats
  | P_aux (P_vector pats, _) -> List.iter (check_pat_as_constant config l) pats
  | P_aux (P_vector_concat pats, _) -> List.iter (check_pat_as_constant config l) pats
  | P_aux (P_list pats, _) -> List.iter (check_pat_as_constant config l) pats
  | P_aux (P_cons (p1, p2), _) -> check_pat_as_constant config l p1; check_pat_as_constant config l p2
  | P_aux (P_struct (_, fpats, _), _) -> List.iter (fun (_, pat) -> check_pat_as_constant config l pat) fpats

let check_type_def config (TD_aux (td, annot)) =
  let l = fst annot in
  match td with
  | TD_abbrev (id, _, _)
  | TD_record (id, _, _, _)
  | TD_bitfield (id, _, _) ->
      report_naming_issue l id config.type_style Category_type
  | TD_variant (id, _, tus, _) ->
      report_naming_issue l id config.type_style Category_type;
      List.iter
        (fun (Tu_aux (Tu_ty_id (_, constructor_id), def_annot)) ->
          report_naming_issue def_annot.loc constructor_id config.type_style Category_type
        )
        tus
  | TD_enum (id, members, _) ->
      report_naming_issue l id config.type_style Category_type;
      List.iter (fun (member_id, def_annot) ->
        report_naming_issue def_annot.loc member_id config.variant_style Category_variant
      ) members
  | TD_abstract (id, _, _) ->
      report_naming_issue l id config.type_style Category_type

let check_fundef config (FD_aux (FD_function (_, _, funcls), _)) =
  List.iter (fun (FCL_aux (FCL_funcl (id, pexp), (def_annot, _))) ->
    report_naming_issue def_annot.loc id config.function_style Category_function;
    match pexp with
    | Pat_aux (Pat_exp (pat, _), (l, _)) | Pat_aux (Pat_when (pat, _, _), (l, _)) ->
        check_pat config l pat
  ) funcls

let check_val_spec config (VS_aux (VS_val_spec (_, id, _), l)) =
  report_naming_issue (fst l) id config.function_style Category_function

let check_letbind config (LB_aux (LB_val (pat, _), l)) =
  check_pat config (fst l) pat

let check_toplevel_let config (LB_aux (LB_val (pat, _), l)) =
  check_pat_as_constant config (fst l) pat

let is_constant_binding (LB_aux (LB_val (_, exp), _)) =
  let rec is_constant_exp (E_aux (e, _)) =
    match e with
    | E_lit _ -> true
    | E_sizeof _ -> true
    | E_constraint _ -> true
    | E_tuple exps -> List.for_all is_constant_exp exps
    | E_struct (_, fexps) -> 
        List.for_all (fun (FE_aux (FE_fexp (_, e), _)) -> is_constant_exp e) fexps
    | E_typ (_, e) -> is_constant_exp e
    | E_app (id, args) when is_constant_function id -> 
        List.for_all is_constant_exp args
    | _ -> false
  and is_constant_function id =
    let name = string_of_id id in
    List.mem name ["add_int"; "sub_int"; "mult_int"; "pow2"; "negate"]
  in
  is_constant_exp exp

let check_register config (DEC_aux (DEC_reg (_, id, _), l)) =
  (* Registers could optionally be checked - uncomment if needed *)
  ignore ((fst l), id, config)

let rec check_scattered config (SD_aux (sd, annot)) =
  let l = fst annot in
  match sd with
  | SD_function (id, _) ->
      report_naming_issue l id config.function_style Category_function
  | SD_funcl (FCL_aux (FCL_funcl (id, pexp), (def_annot, _))) ->
      report_naming_issue def_annot.loc id config.function_style Category_function;
      begin match pexp with
      | Pat_aux (Pat_exp (pat, _), (l, _)) | Pat_aux (Pat_when (pat, _, _), (l, _)) ->
          check_pat config l pat
      end
  | SD_variant (id, _) ->
      report_naming_issue l id config.type_style Category_type
  | SD_unioncl (id, _) ->
      report_naming_issue l id config.type_style Category_type
  | SD_mapping (id, _) ->
      report_naming_issue l id config.function_style Category_function
  | SD_mapcl (id, _) ->
      report_naming_issue l id config.function_style Category_function
  | SD_internal_unioncl_record (_, record_id, _, _) ->
      report_naming_issue l record_id config.type_style Category_type
  | SD_enum id ->
      report_naming_issue l id config.type_style Category_type
  | SD_enumcl (_, member_id) ->
      report_naming_issue l member_id config.variant_style Category_variant
  | SD_end _ -> ()

let check_outcome config (OV_aux (OV_outcome (id, _, _), l)) =
  report_naming_issue l id config.function_style Category_function

(** Main entry points *)
let rec check_defs config ast =
  List.iter (fun (DEF_aux (def, _)) ->
    match def with
    | DEF_type td -> 
        check_type_def config td
    | DEF_fundef fd -> 
        check_fundef config fd
    | DEF_val vs -> 
        check_val_spec config vs
    | DEF_let lb ->
        if is_constant_binding lb then
          check_toplevel_let config lb
        else
          check_letbind config lb
    | DEF_register dec ->
        check_register config dec
    | DEF_scattered sd ->
        check_scattered config sd
    | DEF_outcome (outcome, nested_defs) ->
        check_outcome config outcome;
        List.iter (fun def -> check_defs config { ast with defs = [def] }) nested_defs
    | DEF_instantiation (IN_aux (IN_id id, annot), _) ->
        let l = fst annot in
        report_naming_issue l id config.function_style Category_function
    | DEF_impl funcl ->
        let (FCL_aux (FCL_funcl (id, pexp), (def_annot, _))) = funcl in
        report_naming_issue def_annot.loc id config.function_style Category_function;
        begin match pexp with
        | Pat_aux (Pat_exp (pat, _), (l, _)) | Pat_aux (Pat_when (pat, _, _), (l, _)) ->
            check_pat config l pat
        end
    | DEF_overload _ 
    | DEF_fixity _ 
    | DEF_pragma _ 
    | DEF_default _ 
    | DEF_internal_mutrec _ 
    | DEF_measure _ 
    | DEF_loop_measures _ 
    | DEF_constraint _
    | DEF_mapdef _ ->
        ()
  ) ast.defs

let options = [
  ("-naming_check", Arg.Set opt_enabled, "Enable naming convention checks.");
  ("-naming_check_strict", Arg.Set opt_strict, "Treat naming convention violations as errors.");
]

let check ast =
  (* Enable check if strict mode is set *)
  if !opt_strict then opt_enabled := true;
  if !opt_enabled then check_defs default_config ast