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
(*    Louis-Emile Ploix                                                     *)
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

(** The SystemVerilog output can be customised via attributes attached to Sail source AST nodes. This module provides
    facilities for treating these attributes in a uniform way. *)

open Libsail

open Ast_util
open Jib
open Parse_ast.Attribute_data

module type ATTRIBUTE_INFO = sig
  val loc : Ast.l
  val attribute_name : string
end

(** Get an attribute from a regular (inline) AST annotation. Returns the attribute data, i.e. for

    {v
    $[sv_attribute <data>]
    v}

    will return [Some <data>].

    Also returns a module which can be used to instantiate a parser to extract further information from the data fields.
    This module is primarily to ensure that parse errors are handled nicely with correct location information. *)
val get_sv_attribute : string -> uannot -> (string * attribute_data) list option * (module ATTRIBUTE_INFO)

(** The same as [get_sv_attribute], but for toplevel definition annotations *)
val get_sv_def_attribute :
  string -> unit Ast.def_annot -> (string * attribute_data) list option * (module ATTRIBUTE_INFO)

module AttributeParser (Info : ATTRIBUTE_INFO) : sig
  val get_bool : default:bool -> string -> (string * attribute_data) list option -> bool

  val get_string : default:string -> string -> (string * attribute_data) list option -> string

  val get_types : arity:int -> (string * attribute_data) list option -> ctyp option list option

  val get_return_type : (string * attribute_data) list option -> ctyp option

  val get_string_set : default:Util.StringSet.t -> string -> (string * attribute_data) list option -> Util.StringSet.t

  val get_dpi : Util.StringSet.t -> (string * attribute_data) list option -> bool option
end

val get_bool_attribute : string -> (string * attribute_data) list -> bool

val check_attribute : string -> (string * attribute_data) list -> (unit -> unit) -> unit
