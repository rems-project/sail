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

(** Compile Sail ASTs to Jib intermediate representation *)

open Anf
open Ast
open Ast_defs
open Ast_util
open Jib
open Type_check

(** This forces all integer struct fields to be represented as
   int64_t. Specifically intended for the various TLB structs in the
   ARM v8.5 spec. It is unsound in general. *)
val optimize_aarch64_fast_struct : bool ref

(** (WIP) [opt_memo_cache] will store the compiled function
   definitions in file _sbuild/ccacheDIGEST where DIGEST is the md5sum
   of the original function to be compiled. Enabled using the -memo
   flag. Uses Marshal so it's quite picky about the exact version of
   the Sail version. This cache can obviously become stale if the Sail
   changes - it'll load an old version compiled without said
   changes. *)
val opt_memo_cache : bool ref

(** {2 Jib context} *)

(** Dynamic context for compiling Sail to Jib. We need to pass a
   (global) typechecking environment given by checking the full
   AST. *)
type ctx = {
  records : (kid list * ctyp Bindings.t) Bindings.t;
  enums : IdSet.t Bindings.t;
  variants : (kid list * ctyp Bindings.t) Bindings.t;
  valspecs : (string option * ctyp list * ctyp) Bindings.t;
  quants : ctyp KBindings.t;
  local_env : Env.t;
  tc_env : Env.t;
  effect_info : Effects.side_effect_info;
  locals : (mut * ctyp) Bindings.t;
  letbinds : int list;
  letbind_ids : IdSet.t;
  no_raw : bool;
}

val ctx_is_extern : id -> ctx -> bool

val ctx_get_extern : id -> ctx -> string

val ctx_has_val_spec : id -> ctx -> bool

val initial_ctx : Env.t -> Effects.side_effect_info -> ctx

(** {2 Compilation functions} *)

(** The Config module specifies static configuration for compiling
   Sail into Jib.  We have to provide a conversion function from Sail
   types into Jib types, as well as a function that optimizes ANF
   expressions (which can just be the identity function) *)
module type CONFIG = sig
  val convert_typ : ctx -> typ -> ctyp

  val optimize_anf : ctx -> typ aexp -> typ aexp

  (** Unroll all for loops a bounded number of times. Used for SMT
       generation. *)
  val unroll_loops : int option

  (** A call is precise if the function arguments match the function
      type exactly. Leaving functions imprecise can allow later passes
      to specialize implementations. *)
  val make_call_precise : ctx -> id -> bool

  (** If false, will ensure that fixed size bitvectors are
       specifically less that 64-bits. If true this restriction will
       be ignored. *)
  val ignore_64 : bool

  (** If false we won't generate any V_struct values *)
  val struct_value : bool

  (** If false we won't generate any V_tuple values *)
  val tuple_value : bool

  (** Allow real literals *)
  val use_real : bool

  (** Insert branch coverage operations *)
  val branch_coverage : out_channel option

  (** If true track the location of the last exception thrown, useful
     for debugging C but we want to turn it off for SMT generation
     where we can't use strings *)
  val track_throw : bool
end

module IdGraph : sig
  include Graph.S with type node = id
end

val callgraph : cdef list -> IdGraph.graph

module Make (C : CONFIG) : sig
  (** Compile a Sail definition into a Jib definition. The first two
       arguments are is the current definition number and the total
       number of definitions, and can be used to drive a progress bar
       (see Util.progress). *)
  val compile_def : int -> int -> ctx -> tannot def -> cdef list * ctx

  val compile_ast : ctx -> tannot ast -> cdef list * ctx
end

(** Adds some special functions to the environment that are used to
   convert several Sail language features, these are sail_assert,
   sail_exit, and sail_cons. *)
val add_special_functions : Env.t -> Effects.side_effect_info -> Env.t * Effects.side_effect_info

val name_or_global : ctx -> id -> name
