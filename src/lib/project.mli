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

(** Definition of Sail project files, and functions for working with them. *)

(** Module identifiers are just integers, but we don't want to expose
    that representation to the world. *)
module ModId : sig
  type t = private int

  val to_int : t -> int
end

type mod_id = ModId.t

(** The global scope is for code not defined in any module. *)
val global_scope : mod_id

module ModSet : sig
  include Set.S with type elt = mod_id
end

type l = Lexing.position * Lexing.position

type 'a spanned = 'a * l

(** Convert a project file location to a full Parse_ast location *)
val to_loc : l -> Parse_ast.l

type value

val bool_value : bool -> value
val string_value : string -> value

val parse_assignment : variables:value Util.StringMap.t ref -> string -> bool

type exp =
  | E_app of string * exp spanned list
  | E_file of string
  | E_id of string
  | E_if of exp spanned * exp spanned * exp spanned
  | E_list of exp spanned list
  | E_op of exp spanned * string * exp spanned
  | E_parent
  | E_string of string
  | E_value of value
  | E_var of string

type 'a non_empty = 'a * 'a list

type dependency =
  | D_requires of exp spanned non_empty
  | D_after of exp spanned non_empty
  | D_before of exp spanned non_empty
  | D_default
  | D_optional

type mdl_def = M_dep of dependency | M_directory of exp spanned | M_module of mdl | M_files of exp spanned non_empty

and mdl = { name : string spanned; defs : mdl_def spanned list; span : l }

type def = Def_root of string | Def_var of string spanned * exp spanned | Def_module of mdl | Def_test of string list

val mk_root : string -> def spanned

type project_structure

val initialize_project_structure : variables:value Util.StringMap.t ref -> def spanned list -> project_structure

val get_module_id : project_structure -> string -> mod_id option

val get_children : mod_id -> project_structure -> ModSet.t

(** Create a predicate that returns true for any module that is
    (transitively) required by any module in the roots set of
    modules. *)
val required_modules : roots:ModSet.t -> project_structure -> mod_id -> bool

val module_name : project_structure -> mod_id -> string spanned

val valid_module_id : project_structure -> mod_id -> bool

val module_order : project_structure -> mod_id list

val module_files : project_structure -> mod_id -> string spanned list

val module_requires : project_structure -> mod_id -> mod_id list

val all_files : project_structure -> string spanned list

val all_modules : project_structure -> mod_id list
