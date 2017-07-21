(**************************************************************************)
(*     Sail                                                               *)
(*                                                                        *)
(*  Copyright (c) 2013-2017                                               *)
(*    Kathyrn Gray                                                        *)
(*    Shaked Flur                                                         *)
(*    Stephen Kell                                                        *)
(*    Gabriel Kerneis                                                     *)
(*    Robert Norton-Wright                                                *)
(*    Christopher Pulte                                                   *)
(*    Peter Sewell                                                        *)
(*    Alasdair Armstrong                                                  *)
(*                                                                        *)
(*  All rights reserved.                                                  *)
(*                                                                        *)
(*  This software was developed by the University of Cambridge Computer   *)
(*  Laboratory as part of the Rigorous Engineering of Mainstream Systems  *)
(*  (REMS) project, funded by EPSRC grant EP/K008528/1.                   *)
(*                                                                        *)
(*  Redistribution and use in source and binary forms, with or without    *)
(*  modification, are permitted provided that the following conditions    *)
(*  are met:                                                              *)
(*  1. Redistributions of source code must retain the above copyright     *)
(*     notice, this list of conditions and the following disclaimer.      *)
(*  2. Redistributions in binary form must reproduce the above copyright  *)
(*     notice, this list of conditions and the following disclaimer in    *)
(*     the documentation and/or other materials provided with the         *)
(*     distribution.                                                      *)
(*                                                                        *)
(*  THIS SOFTWARE IS PROVIDED BY THE AUTHOR AND CONTRIBUTORS ``AS IS''    *)
(*  AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED     *)
(*  TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A       *)
(*  PARTICULAR PURPOSE ARE DISCLAIMED.  IN NO EVENT SHALL THE AUTHOR OR   *)
(*  CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,          *)
(*  SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT      *)
(*  LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF      *)
(*  USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND   *)
(*  ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,    *)
(*  OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT    *)
(*  OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF    *)
(*  SUCH DAMAGE.                                                          *)
(**************************************************************************)

open Ast
open Ast_util

val opt_tc_debug : int ref

exception Type_error of l * string;;

type mut = Immutable | Mutable

type lvar = Register of typ | Enum of typ | Local of mut * typ | Union of typquant * typ | Unbound

module Env : sig
  (* Env.t is the type of environments *)
  type t

  (* Note: Most get_ functions assume the identifiers exist, and throw type
     errors if it doesn't. *)

  val get_val_spec : id -> t -> typquant * typ

  val get_register : id -> t -> typ

  val get_regtyp : id -> t -> int * int * (index_range * id) list

  (* Return all the identifiers in an enumeration. Throws a type error
     if the enumeration doesn't exist. *)
  val get_enum : id -> t -> id list

  (* Returns true if id is a register type, false otherwise *)
  val is_regtyp : id -> t -> bool

  (* Check if a local variable is mutable. Throws Type_error if it
     isn't a local variable. Probably best to use Env.lookup_id
     instead *)
  val is_mutable : id -> t -> bool

  (* Get the current set of constraints. *)
  val get_constraints : t -> n_constraint list

  val get_typ_var : kid -> t -> base_kind_aux

  val get_typ_vars : t -> base_kind_aux KBindings.t

  val is_record : id -> t -> bool

  val get_accessor : id -> t -> typquant * typ

  (* If the environment is checking a function, then this will get the
     expected return type of the function. It's useful for checking or
     inserting early returns. Returns an option type and won't throw
     any exceptions. *)
  val get_ret_typ : t -> typ option

  val get_typ_synonym : id -> t -> typ_arg list -> typ

  val get_overloads : id -> t -> id list

  (* Lookup id searchs for a specified id in the environment, and
     returns it's type and what kind of identifier it is, using the
     lvar type. Returns Unbound if the identifier is unbound, and
     won't throw any exceptions. *)
  val lookup_id : id -> t -> lvar

  (* Return a fresh kind identifier that doesn't exist in the environment *)
  val fresh_kid : t -> kid

  val expand_synonyms : t -> typ -> typ

  (* no_casts removes all the implicit type casts/coercions from the
     environment, so checking a term with such an environment will
     guarantee not to insert any casts. Not that this is only about
     the implicit casting and has nothing to do with the E_cast AST
     node. *)
  val no_casts : t -> t

  (* Is casting allowed by the environment? *)
  val allow_casts : t -> bool

  val empty : t

end

val add_typquant : typquant -> Env.t -> Env.t

(* Some handy utility functions for constructing types. *)
val mk_typ : typ_aux -> typ
val mk_typ_arg : typ_arg_aux -> typ_arg
val mk_id : string -> id
val mk_id_typ : id -> typ

val no_effect : effect
val mk_effect : base_effect_aux list -> effect

val union_effects : effect -> effect -> effect
val equal_effects : effect -> effect -> bool

val nconstant : int -> nexp
val nminus : nexp -> nexp -> nexp
val nsum : nexp -> nexp -> nexp
val ntimes : nexp -> nexp -> nexp
val npow2 : nexp -> nexp
val nvar : kid -> nexp

(* Sail builtin types. *)
val int_typ : typ
val nat_typ : typ
val atom_typ : nexp -> typ
val range_typ : nexp -> nexp -> typ
val bit_typ : typ
val bool_typ : typ
val unit_typ : typ
val string_typ : typ
val real_typ : typ
val vector_typ : nexp -> nexp -> order -> typ -> typ

val inc_ord : order
val dec_ord : order

(* Vector with default order. *)
val dvector_typ : Env.t -> nexp -> nexp -> typ -> typ

(* Vector of specific length with default order, i.e. lvector_typ env n bit_typ = bit[n]. *)
val lvector_typ : Env.t -> nexp -> typ -> typ

type tannot = (Env.t * typ * effect) option

(* Strip the type annotations from an expression. *)
val strip_exp : 'a exp -> unit exp
val strip_pat : 'a pat -> unit pat

(* Check an expression has some type. Returns a fully annotated
   version of the expression, where each subexpression is annotated
   with it's type and the Environment used while checking it. The can
   be used to re-start the typechecking process on any
   sub-expression. so local modifications to the AST can be
   re-checked. *)
val check_exp : Env.t -> unit exp -> typ -> tannot exp

(* Partial functions: The expressions and patterns passed to these
   functions must be guaranteed to have tannots of the form Some (env,
   typ) for these to work. *)
val typ_of : tannot exp -> typ
val typ_of_annot : Ast.l * tannot -> typ

val pat_typ_of : tannot pat -> typ

val effect_of : tannot exp -> effect
val effect_of_annot : tannot -> effect

val propagate_exp_effect : tannot exp -> tannot exp

(* Fully type-check an AST

Some invariants that will hold of a fully checked AST are:

 * No internal nodes, such as E_internal_exp, or E_comment nodes.

 * E_vector_access nodes and similar will be replaced by function
   calls E_app to vector access functions. This is different to the
   old type checker.

 * Every expressions type annotation (tannot) will be Some (typ, env).

 * Also every pattern will be annotated with the type it matches.

 * Toplevel expressions such as typedefs and some subexpressions such
   as letbinds may have None as their tannots if it doesn't make sense
   for them to have type annotations. *)
val check : Env.t -> 'a defs -> tannot defs * Env.t

val initial_env : Env.t
