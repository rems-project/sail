(**************************************************************************)
(*                        Lem                                             *)
(*                                                                        *)
(*          Dominic Mulligan, University of Cambridge                     *)
(*          Francesco Zappa Nardelli, INRIA Paris-Rocquencourt            *)
(*          Gabriel Kerneis, University of Cambridge                      *)
(*          Kathy Gray, University of Cambridge                           *)
(*          Peter Boehm, University of Cambridge (while working on Lem)   *)
(*          Peter Sewell, University of Cambridge                         *)
(*          Scott Owens, University of Kent                               *)
(*          Thomas Tuerk, University of Cambridge                         *)
(*                                                                        *)
(*  The Lem sources are copyright 2010-2013                               *)
(*  by the UK authors above and Institut National de Recherche en         *)
(*  Informatique et en Automatique (INRIA).                               *)
(*                                                                        *)
(*  All files except ocaml-lib/pmap.{ml,mli} and ocaml-libpset.{ml,mli}   *)
(*  are distributed under the license below.  The former are distributed  *)
(*  under the LGPLv2, as in the LICENSE file.                             *)
(*                                                                        *)
(*                                                                        *)
(*  Redistribution and use in source and binary forms, with or without    *)
(*  modification, are permitted provided that the following conditions    *)
(*  are met:                                                              *)
(*  1. Redistributions of source code must retain the above copyright     *)
(*  notice, this list of conditions and the following disclaimer.         *)
(*  2. Redistributions in binary form must reproduce the above copyright  *)
(*  notice, this list of conditions and the following disclaimer in the   *)
(*  documentation and/or other materials provided with the distribution.  *)
(*  3. The names of the authors may not be used to endorse or promote     *)
(*  products derived from this software without specific prior written    *)
(*  permission.                                                           *)
(*                                                                        *)
(*  THIS SOFTWARE IS PROVIDED BY THE AUTHORS ``AS IS'' AND ANY EXPRESS    *)
(*  OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED     *)
(*  WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE    *)
(*  ARE DISCLAIMED. IN NO EVENT SHALL THE AUTHORS BE LIABLE FOR ANY       *)
(*  DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL    *)
(*  DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE     *)
(*  GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS         *)
(*  INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER  *)
(*  IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR       *)
(*  OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN   *)
(*  IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.                         *)
(**************************************************************************)

(* open Typed_ast *)

val parse_file : string -> Parse_ast.defs * Parse_ast.lex_skips

(* type instances = Types.instance list Types.Pfmap.t

val check_ast_as_module :
  Targetset.t ->
  Name.t list ->
  (Types.type_defs * instances) * env ->
  Ulib.Text.t ->
  Ast.defs * Ast.lex_skips ->
  (Types.type_defs * instances * instances) * env *
  (def list * Ast.lex_skips)

val check_ast :
  Targetset.t ->
  Name.t list ->
  (Types.type_defs * instances) * env ->
  Ast.defs * Ast.lex_skips ->
  (Types.type_defs * instances * instances) * env *
  (def list * Ast.lex_skips)

val output :
  string ->                           (* The path to the library *)
  string ->                           (* Isabelle Theory to be included *)
  target option ->                    (* Backend name (None for the identity backend) *)
  Typed_ast.var_avoid_f ->
  (Types.type_defs * instances) -> (* The full environment built after all typechecking, and transforming *)
  checked_module list ->              (* The typechecked modules *)
  Ulib.Text.t list ref ->               (* alldoc accumulator *)
  Ulib.Text.t list ref ->               (* alldoc-inc accumulator *)
  Ulib.Text.t list ref ->               (* alldoc-use_inc accumulator *)
  unit

val output_alldoc : string -> string -> Ulib.Text.t list ref -> Ulib.Text.t list ref -> Ulib.Text.t list ref -> unit

(** [always_replace_files] determines whether Lem only updates modified files.
    If it is set to [true], all output files are written, regardless of whether the
    files existed before. If it is set to [false] and an output file already exists,
    the output file is only updated, if its content really changes. For some
    backends like OCaml, HOL, Isabelle, this is benefitial, since it prevents them
    from reprocessing these unchanged files. *)
val always_replace_files : bool ref
*)
