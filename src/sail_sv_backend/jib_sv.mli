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

open Libsail

open Ast_util

module type CONFIG = sig
  (** Set recursion depth for recursive SystemVerilog modules *)
  val recursion_depth : int

  (** If Sail does not know a precise bitwidth for an integer variable, it will use this width. *)
  val max_unknown_integer_width : int

  (** If Sail does not know the precise width for a bitvector variable, it will use a variable-length bitvector
      representation which can hold bitvectors of at most this length. *)
  val max_unknown_bitvector_width : int

  (** Prefix global signals with the provided name *)
  val global_prefix : string option

  (** Output SystemVerilog line directives where possible *)
  val line_directives : bool

  (** If true, treat all strings as if they were the unit type. Obviously this is only sound when the semantics does not
      depend on strings, and they are only used for output.

      This is intended for EDA tools that do not support strings in SystemVerilog. *)
  val no_strings : bool

  val no_packed : bool

  (** If true, then all assertions are treated as no-ops *)
  val no_assertions : bool

  val never_pack_unions : bool
  val union_padding : bool
  val no_unions : bool
  val unreachable : string list
  val no_write_flush : bool
  val comb : bool
  val ignore : string list

  val fun_to_wires : (string * int) list

  (** The SystemVerilog DPI (direct programming interface) lets the generated SystemVerilog directly call C functions. A
      Sail external function for the [systemverilog] target can be translated into a DPI binding using the [sv_function]
      attribute, for example:

      {@sail[
        $[sv_function { dpi = true }]
        val foo = pure "foo" : ...

        $[sv_function { dpi = "memory" }]
        val bar = pure "bar" : ...
      ]}

      In the above example [foo] will always generated a DPI binding, but [bar] will only generate a DPI binding when
      ["memory"] is included in [dpi_sets]. *)
  val dpi_sets : Util.StringSet.t

  (** If true we will simply skip generating the body of any cyclic (i.e. contains a loop that has not been unrolled)
      definitions, and print a warning instead. This allows generation to proceed for other parts of the spec. *)
  val skip_cyclic : bool

  val no_assert_fatal : bool
  val assert_as_property : bool
end

module Make (Config : CONFIG) : sig
  module Primops : Generate_primop2.S

  type cdef_doc = {
    outside_module : PPrint.document;
    inside_module_prefix : PPrint.document;
    inside_module : PPrint.document;
  }

  val svir_cdef :
    Sv_analysis.spec_info ->
    Jib_compile.ctx ->
    (unit Ast.def_annot * Jib.ctyp list * Libsail.Jib.ctyp) Bindings.t ->
    Jib.cdef ->
    Sv_ir.sv_def list * (unit Ast.def_annot * Jib.ctyp list * Jib.ctyp) Bindings.t

  val pp_def : Jib_compile.ctx -> Sv_ir.sv_name option -> Sv_ir.sv_def -> PPrint.document

  (** Create a SystemVerilog module that wraps the provided Sail function in a more convenient interface.

      Raises a general Sail exception if the function cannot be found, or has no footprint information contained within
      spec_info.

      The way this is generated is controlled by the sv_toplevel attribute, which is attached to the signature of the
      function. *)
  val toplevel_module :
    Sv_analysis.spec_info ->
    Jib_compile.ctx ->
    Ast.id ->
    (unit Ast.def_annot * Jib.ctyp list * Jib.ctyp) Bindings.t ->
    Sv_ir.sv_module

  val sv_cdef :
    Sv_analysis.spec_info ->
    Jib_compile.ctx ->
    (Jib.ctyp list * Libsail.Jib.ctyp) Bindings.t ->
    string list ->
    Jib.cdef ->
    cdef_doc * (Jib.ctyp list * Jib.ctyp) Bindings.t * string list

  val sv_register_references : Sv_analysis.spec_info -> PPrint.document * PPrint.document

  val sv_fundef_with :
    Jib_compile.ctx -> string -> Ast.id list -> Jib.ctyp list -> Jib.ctyp -> PPrint.document -> PPrint.document

  val sv_ctyp : ?two_state:bool -> Jib.ctyp -> string * string option

  val wrap_type : Jib.ctyp -> PPrint.document -> PPrint.document

  val pp_id_string : Ast.id -> string

  val pp_id : Ast.id -> PPrint.document

  val main_args :
    Jib.cdef option ->
    (Jib.ctyp list * Jib.ctyp) Bindings.t ->
    PPrint.document list * PPrint.document option * PPrint.document list

  val make_call_precise : Jib_compile.ctx -> Ast.id -> bool
end
