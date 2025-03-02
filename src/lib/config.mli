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
(*  Copyright (c) 2013-2025                                                 *)
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

(** Sail model configuration using JSON. *)

open Type_check

(** Rewrite any any configuration nodes in the AST, and gather
    configuration information.

    This rewrite performs two operations:

    First, It takes a JSON configuration file as input and replaces
    E_config nodes within the AST using information within that JSON.
    For example:

    {@sail[
    config a.b.c : T
    ]}

    will cause [a.b.c] to be looked up in the provided JSON and
    whatever JSON value is at that key will be interpreted as the type
    [T] and inserted in the AST.

    If [a.b.c] does not exist, then the E_config node will remain to
    be instantiated by a configuration value at runtime.

    Second, for each type [T] attached to a configuration node (which
    may have been inferred from context by the type system), we will
    also attempt to synthesise a JSON Schema. If [T] cannot be turned
    into a valid schema then this function raises a fatal type error
    exception. This schema cannot capture every possible invariant of
    an ISA configuration, but it does provide enough to guarantee that
    a configuration applied at runtime will not break type-safety
    assuming it validates against the schema.

    The function will return that JSON schema alongside the re-written
    AST. *)
val rewrite_ast : env -> Frontend.abstract_instantiation -> Yojson.Safe.t -> typed_ast -> Yojson.Safe.t * typed_ast
