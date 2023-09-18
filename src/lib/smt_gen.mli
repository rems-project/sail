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
(*  Copyright (c) 2013-2023                                                 *)
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

(** Compile Sail builtins to SMT bitvector expressions *)

open Ast_util
open Jib

(** The main limitiation when converting Sail into pure SMT bitvectors
    is that Sail has arbitrary precision types, as well as types like
    real and string that are not very SMT friendly. We can add dynamic
    assertions that effectivly check at runtime that we never exceed
    some upper bound on bitvector size, and log if we ever use
    features like strings or real numbers. *)
type checks

(** We generate primitives in a monad that accumulates any required
    dynamic checks, and contains the location information for any
    error messages. *)
type 'a check_writer

(** The SMT generation monad contains the location of the expression
    or definition we are generating SMT for *)
val current_location : Parse_ast.l check_writer

val return : 'a -> 'a check_writer

val bind : 'a check_writer -> ('a -> 'b check_writer) -> 'b check_writer

val fmap : ('a -> 'b) -> 'a check_writer -> 'b check_writer

val ( let* ) : 'a check_writer -> ('a -> 'b check_writer) -> 'b check_writer

val ( let+ ) : 'a check_writer -> ('a -> 'b) -> 'b check_writer

val mapM : ('a -> 'b check_writer) -> 'a list -> 'b list check_writer

val run : 'a check_writer -> Parse_ast.l -> 'a * checks

(** Convert a SMT bitvector expression of size [from] into a SMT
    bitvector expression of size [into] with the same signed
    value. When [into < from] inserts a dynamic check that the
    original value is representable at the new length. *)
val signed_size : ?checked:bool -> into:int -> from:int -> Smt_exp.smt_exp -> Smt_exp.smt_exp check_writer

(** Similar to [signed_size], except it assumes the bitvector is
    representing an unsigned value. *)
val unsigned_size :
  ?max_value:int -> ?checked:bool -> into:int -> from:int -> Smt_exp.smt_exp -> Smt_exp.smt_exp check_writer

(** [bvint sz n] Create a (two's complement) SMT bitvector
    representing a the number [n] in a bitvector of length
    [sz]. Raises an error if this is not possible. *)
val bvint : int -> Big_int.num -> Smt_exp.smt_exp

module type CONFIG = sig
  (** Sail has arbitrary precision integers, but in order to generate
      pure bitvectors we must constrain them to some upper bound. As
      described above, we can insert dynamic checks to ensure this
      constraint is never violated at runtime. *)
  val max_unknown_integer_width : int

  (** If we have a Sail type [bits('n)], where ['n] is unconstrained,
      then we cannot know how many bits to use to represent
      it. Instead we use a bitvector of this length, plus a width
      field. We will generate runtime checks to ensure this length is
      sufficient. *)
  val max_unknown_bitvector_width : int

  (** Some SystemVerilog implementations (e.g. Verilator), don't
      support unpacked union types, which forces us to generate
      different code for different unions depending on the types the
      contain. This is abstracted into a classify function that the
      instantiator of this module can supply. *)
  val union_ctyp_classify : ctyp -> bool
end

(** Some Sail primitives we can't directly convert to pure SMT
    bitvectors, either because they don't exist in SMTLIB (like
    count_leading_zeros), or they involve input/output. In these cases
    we provide a module so the backend can generate the required
    implementations for these primitives. *)
module type PRIMOP_GEN = sig
  val print_bits : Parse_ast.l -> ctyp -> string
  val string_of_bits : Parse_ast.l -> ctyp -> string
  val dec_str : Parse_ast.l -> ctyp -> string
  val hex_str : Parse_ast.l -> ctyp -> string
  val hex_str_upper : Parse_ast.l -> ctyp -> string
  val count_leading_zeros : Parse_ast.l -> int -> string
  val fvector_store : Parse_ast.l -> int -> ctyp -> string
  val is_empty : Parse_ast.l -> ctyp -> string
  val hd : Parse_ast.l -> ctyp -> string
  val tl : Parse_ast.l -> ctyp -> string
end

module Make (Config : CONFIG) (Primop_gen : PRIMOP_GEN) : sig
  (** Convert a Jib IR cval into an SMT expression *)
  val smt_cval : cval -> Smt_exp.smt_exp check_writer

  val int_size : ctyp -> int

  (** Create an SMT expression that converts an expression of the jib
      type [from] into an SMT expression for the jib type [into]. Note
      that this function assumes that the input is of the correct
      type. *)
  val smt_conversion : into:ctyp -> from:ctyp -> Smt_exp.smt_exp -> Smt_exp.smt_exp check_writer

  (** Compile a call to a Sail builtin function into an SMT expression
      implementing that call. Returns None if that builtin is
      unsupported by this module. *)
  val builtin : string -> (cval list -> ctyp -> Smt_exp.smt_exp check_writer) option
end
