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

open Libsail

open Ast
open Ast_defs
open Ast_util
open Jib
open Jib_util

val opt_debug_graphs : bool ref

module type CONFIG = sig
  val max_unknown_integer_width : int
  val max_unknown_bitvector_width : int
  val max_unknown_generic_vector_length : int
  val register_map : id list CTMap.t
  val ignore_overflow : bool
end

module Make (Config : CONFIG) : sig
  type generated_smt_info = {
    file_name : string;
    function_id : id;
    args : id list;
    arg_ctyps : ctyp list;
    arg_smt_names : (id * string option) list;
  }

  (** Generate SMT for all the $property and $counterexample pragmas
      provided, and write the generated SMT to appropriately named
      files. *)
  val generate_smt :
    properties:(string * string * l * 'a val_spec) Bindings.t (** See Property.find_properties *) ->
    name_file:(string -> string) (** Applied to each function name to generate the file name for the smtlib file *) ->
    smt_includes:string list (** Extra files to include in each generated SMT problem *) ->
    Jib_compile.ctx ->
    cdef list ->
    generated_smt_info list
end

val compile :
  unroll_limit:int ->
  Type_check.Env.t ->
  Effects.side_effect_info ->
  Type_check.typed_ast ->
  cdef list * Jib_compile.ctx * id list CTMap.t
