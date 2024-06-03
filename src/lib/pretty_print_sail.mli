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

open Ast
open Ast_util

(** The [PRINT_CONFIG] module type can be used to customise the
    behavior of the pretty-printer *)
module type PRINT_CONFIG = sig
  (** If true, then the printer will insert additional braces into the
      source (essentially creating additional E_block nodes). This
      will give the code a more normal imperative look, especially
      after re-writing passes that are on the path to the theorem
      prover targets that use a more functional style. *)
  val insert_braces : bool

  (** If true, the printer will attempt to reverse some
      transformations that are done to the source. It can do this
      where passes insert attributes into the AST that it can use to
      revert various changes. It will do the following:

      - Reintroduce [v[n]] for vector_access and [v[n..m]] for vector_subrange
      - Undo overloading
      - Turn [operator OP(x, y)] back into [x OP y]
      - Reintroduce setters [setter(x, y)] into [setter(x) = y]
  *)
  val resugar : bool

  (** If true, all attributes [$[attr ...]] will be hidden in the
      output. Note that [resugar] will remove any attributes it uses
      as hints for resugaring even when this is false. *)
  val hide_attributes : bool
end

(** The [Printer] functor defines the printing function based on the
    supplied printing configuration *)
module Printer (Config : PRINT_CONFIG) : sig
  val doc_id : id -> PPrint.document

  val doc_typ : typ -> PPrint.document

  val doc_binding : typquant * typ -> PPrint.document

  val doc_typschm : typschm -> PPrint.document

  val doc_exp : uannot exp -> PPrint.document

  val doc_block : uannot exp list -> PPrint.document

  val doc_letbind : uannot letbind -> PPrint.document

  val doc_funcl : uannot funcl -> PPrint.document

  val doc_mapcl : uannot mapcl -> PPrint.document

  val doc_spec : uannot val_spec -> PPrint.document

  val doc_type_def : uannot type_def -> PPrint.document

  val doc_register : uannot dec_spec -> PPrint.document

  val doc_def : (uannot, unit) def -> PPrint.document
end

(** This function is intended to reformat machine-generated Sail into
    something a bit more readable, it is not intended to be used as a
    general purpose code formatter. The output will be dumped as
    multiple files into the directory argument. *)
val reformat : into_directory:string -> (uannot, unit) Ast_defs.ast -> unit

(** The default [PRINT_CONFIG] sets all the options to false, so it
    prints the AST 'as is' without modifications. *)
module Default_print_config : PRINT_CONFIG

(** For convenience, other modules can get the default behavior by
    just importing this module. *)
include module type of Printer (Default_print_config)

(** This function is primarly used to dump the AST by debug options,
    such as [--ddump-tc-ast]. *)
val output_ast : ?line_width:int -> out_channel -> (uannot, unit) Ast_defs.ast -> unit

(** Some convenience functions for outputting PPrint documents *)
module Document : sig
  val to_channel : ?line_width:int -> out_channel -> PPrint.document -> unit

  val to_string : ?line_width:int -> PPrint.document -> string
end
