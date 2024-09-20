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

val opt_ddump_initial_ast : bool ref
val opt_ddump_side_effect : bool ref
val opt_ddump_tc_ast : bool ref
val opt_list_files : bool ref
val opt_reformat : string option ref

val instantiate_abstract_types :
  Target.target option -> (kind_aux -> typ_arg) Bindings.t -> Type_check.typed_ast -> Type_check.typed_ast

(** The [FILE_HANDLER] module type allows plugins to define handlers
    for custom file types. It defines how those files are processed
    and eventually generate Sail AST types. *)
module type FILE_HANDLER = sig
  (** A parsed representation of the file. *)
  type parsed

  (** The file handler may do some arbitrary processing of the parsed
      file contents prior to generating Sail AST types. *)
  type processed

  val parse : Parse_ast.l option -> string -> parsed

  (** If the file will define any functions, we must inform Sail. *)
  val defines_functions : processed -> IdSet.t

  (** If the file generates registers without any initialized default
      value, we must inform Sail, i.e this would be a register like

      {@sail[
      register X : bits(32)
      ]}

      rather than

      {@sail[
      register X : bits(32) = 0x0000_0000
      ]}

      which does have a default value.
  *)
  val uninitialized_registers : processed -> (Ast.id * Ast.typ) list

  val process :
    default_sail_dir:string ->
    target_name:string option ->
    options:(Arg.key * Arg.spec * Arg.doc) list ->
    Initial_check.ctx ->
    parsed ->
    processed * Initial_check.ctx

  val check : Type_check.Env.t -> processed -> Type_check.typed_ast * Type_check.Env.t
end

(** Register a file handler module. The extension should be the
    extension for the file type we want to handle, e.g. ".json". *)
val register_file_handler : extension:string -> (module FILE_HANDLER) -> unit

val load_modules :
  ?target:Target.target ->
  string ->
  (Arg.key * Arg.spec * Arg.doc) list ->
  Type_check.Env.t ->
  Project.project_structure ->
  Project.mod_id list ->
  Initial_check.ctx * Type_check.typed_ast * Type_check.Env.t * Effects.side_effect_info

val load_files :
  ?target:Target.target ->
  string ->
  (Arg.key * Arg.spec * Arg.doc) list ->
  Type_check.Env.t ->
  string list ->
  Initial_check.ctx * Type_check.typed_ast * Type_check.Env.t * Effects.side_effect_info

val initial_rewrite :
  Effects.side_effect_info -> Type_check.Env.t -> Type_check.typed_ast -> Type_check.typed_ast * Type_check.Env.t
