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

open Libsail

open Ast_util

type spec_info

val collect_spec_info : Jib_compile.ctx -> Jib.cdef list -> spec_info

module type CONFIG = sig
  val max_unknown_integer_width : int
  val max_unknown_bitvector_width : int

  (** Output SystemVerilog line directives where possible *)
  val line_directives : bool

  (** If true, treat all strings as if they were the unit type.
      Obviously this is only sound when the semantics does not depend
      on strings, and they are only used for output. *)
  val nostrings : bool

  val nopacked : bool
  val never_pack_unions : bool
  val union_padding : bool
  val unreachable : string list
  val comb : bool
  val ignore : string list
end

module Make (Config : CONFIG) : sig
  module Primops : Generate_primop2.S

  type cdef_doc = {
    outside_module : PPrint.document;
    inside_module_prefix : PPrint.document;
    inside_module : PPrint.document;
  }

  val svir_cdef :
    spec_info ->
    Jib_compile.ctx ->
    (Jib.ctyp list * Libsail.Jib.ctyp) Bindings.t ->
    Jib.cdef ->
    Sv_ir.sv_def list * (Jib.ctyp list * Jib.ctyp) Bindings.t

  val pp_def : Sv_ir.sv_def -> PPrint.document

  val toplevel_module : spec_info -> Sv_ir.sv_module option

  val sv_cdef :
    spec_info ->
    Jib_compile.ctx ->
    (Jib.ctyp list * Libsail.Jib.ctyp) Bindings.t ->
    string list ->
    Jib.cdef ->
    cdef_doc * (Jib.ctyp list * Jib.ctyp) Bindings.t * string list

  val sv_register_references : spec_info -> PPrint.document * PPrint.document

  val sv_fundef_with :
    Jib_compile.ctx -> string -> Ast.id list -> Jib.ctyp list -> Jib.ctyp -> PPrint.document -> PPrint.document

  val sv_ctyp : Jib.ctyp -> string * string option

  val wrap_type : Jib.ctyp -> PPrint.document -> PPrint.document

  val pp_id_string : Ast.id -> string

  val pp_id : Ast.id -> PPrint.document

  val main_args :
    Jib.cdef option ->
    (Jib.ctyp list * Jib.ctyp) Bindings.t ->
    PPrint.document list * PPrint.document option * PPrint.document list

  val make_call_precise : Jib_compile.ctx -> Ast.id -> bool
end
