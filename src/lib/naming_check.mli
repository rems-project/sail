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

(** Naming convention checker for Sail identifiers.
    
    This module provides static analysis to ensure identifiers follow
    consistent naming conventions:
    
    | Identifier Type           | Expected Style       | Example                      |
    |---------------------------|----------------------|------------------------------|
    | Types / Structs / Enums   | PascalCase           | MemoryAccess, Privilege      |
    | Functions                 | snake_case           | execute_load, get_csr_value  |
    | Variables / Let bindings  | snake_case           | mem_addr, reg_value          |
    | Constants                 | SCREAMING_SNAKE_CASE | MAX_XLEN, DEFAULT_VALUE      |
*)

type naming_style = 
  | PascalCase            (** PascalCase: MemoryAccess *)
  | SnakeCase             (** snake_case: execute_load *)
  | ScreamingSnakeCase    (** SCREAMING_SNAKE_CASE: MAX_XLEN *)
  | Any                   (** No check *)

type naming_config = {
  type_style : naming_style;
  function_style : naming_style;
  variable_style : naming_style;
  constant_style : naming_style;
}

(** Default configuration:
    - Types    : PascalCase
    - Functions: snake_case
    - Variables: snake_case
    - Constants: SCREAMING_SNAKE_CASE *)
val default_config : naming_config

(** Enable naming convention checks (default: false) *)
val opt_enabled : bool ref

(** Treat naming convention violations as errors instead of warnings *)
val opt_strict : bool ref

val options : (Arg.key * Arg.spec * Arg.doc) list

val is_pascal_case : string -> bool
val is_snake_case : string -> bool
val is_screaming_snake_case : string -> bool

val matches_style : string -> naming_style -> bool

val string_of_style : naming_style -> string

(** Check naming conventions for all definitions in the AST.
    Uses the current values of [opt_enabled] and [opt_strict].
    
    @param config Optional custom configuration (defaults to [default_config])
    @param ast The AST to check *)
val check : Type_check.typed_ast -> unit