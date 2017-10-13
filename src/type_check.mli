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
val opt_no_effects : bool ref

type type_error =
  | Err_no_casts of type_error * type_error list
  | Err_no_overloading of id * (id * type_error) list
  | Err_unresolved_quants of id * quant_item list
  | Err_subtype of typ * typ * n_constraint list
  | Err_no_num_ident of id
  | Err_other of string

exception Type_error of l * type_error;;

val string_of_type_error : type_error -> string

type mut = Immutable | Mutable

type lvar = Register of typ | Enum of typ | Local of mut * typ | Union of typquant * typ | Unbound

module Env : sig
  (* Env.t is the type of environments *)
  type t

  (* Note: Most get_ functions assume the identifiers exist, and throw type
     errors if it doesn't. *)

  val get_val_spec : id -> t -> typquant * typ

  val update_val_spec : id -> typquant * typ -> t -> t

  val get_register : id -> t -> typ

  val get_regtyp : id -> t -> int * int * (index_range * id) list

  (* Return all the identifiers in an enumeration. Throws a type error
     if the enumeration doesn't exist. *)
  val get_enum : id -> t -> id list

  (* Returns true if id is a register type, false otherwise *)
  val is_regtyp : id -> t -> bool

  val get_locals : t -> (mut * typ) Bindings.t

  (* Check if a local variable is mutable. Throws Type_error if it
     isn't a local variable. Probably best to use Env.lookup_id
     instead *)
  val is_mutable : id -> t -> bool

  (* Get the current set of constraints. *)
  val get_constraints : t -> n_constraint list

  val get_typ_var : kid -> t -> base_kind_aux

  val get_typ_vars : t -> base_kind_aux KBindings.t

  val add_typ_var : kid -> base_kind_aux -> t -> t

  val is_record : id -> t -> bool

  val get_accessor : id -> id -> t -> typquant * typ

  (* If the environment is checking a function, then this will get the
     expected return type of the function. It's useful for checking or
     inserting early returns. Returns an option type and won't throw
     any exceptions. *)
  val get_ret_typ : t -> typ option

  val get_typ_synonym : id -> t -> (t -> typ_arg list -> typ)

  val get_overloads : id -> t -> id list

  val get_num_def : id -> t -> nexp

  val is_extern : id -> t -> bool

  val get_extern : id -> t -> string

  (* Lookup id searchs for a specified id in the environment, and
     returns it's type and what kind of identifier it is, using the
     lvar type. Returns Unbound if the identifier is unbound, and
     won't throw any exceptions. *)
  val lookup_id : id -> t -> lvar

  val is_union_constructor : id -> t -> bool

  (* Return a fresh kind identifier that doesn't exist in the
     environment. The optional argument bases the new identifer on the
     old one. *)
  val fresh_kid : ?kid:kid -> t -> kid

  val expand_synonyms : t -> typ -> typ

  (* Expand type synonyms and remove register annotations (i.e. register<t> -> t)) *)
  val base_typ_of : t -> typ -> typ

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

(* Push all the type variables and constraints from a typquant into an environment *)
val add_typquant : typquant -> Env.t -> Env.t

(* When the typechecker creates new type variables it gives them fresh
   names of the form 'fvXXX#name, where XXX is a number (not
   necessarily three digits), and name is the original name when the
   type variable was created by renaming an exisiting type variable to
   avoid shadowing. orig_kid takes such a type variable and strips out
   the 'fvXXX# part. It returns the type variable unmodified if it is
   not of this form. *)
val orig_kid : kid -> kid

val union_effects : effect -> effect -> effect
val equal_effects : effect -> effect -> bool

(* Negate a n_constraint. Note that there's no NC_not constructor, so
   this flips all the inequalites a the n_constraint leaves and uses
   de-morgans to switch and to or and vice versa. *)
val nc_negate : n_constraint -> n_constraint

(* Vector with default order. *)
val dvector_typ : Env.t -> nexp -> nexp -> typ -> typ

(* Vector of specific length with default order, i.e. lvector_typ env n bit_typ = bit[n]. *)
val lvector_typ : Env.t -> nexp -> typ -> typ

val exist_typ : (kid -> n_constraint) -> (kid -> typ) -> typ

type tannot = (Env.t * typ * effect) option

(* Strip the type annotations from an expression. *)
val strip_exp : 'a exp -> unit exp
val strip_pat : 'a pat -> unit pat
val strip_lexp : 'a lexp -> unit lexp

(* Check an expression has some type. Returns a fully annotated
   version of the expression, where each subexpression is annotated
   with it's type and the Environment used while checking it. The can
   be used to re-start the typechecking process on any
   sub-expression. so local modifications to the AST can be
   re-checked. *)
val check_exp : Env.t -> unit exp -> typ -> tannot exp

val infer_exp : Env.t -> unit exp -> tannot exp

val prove : Env.t -> n_constraint -> bool

val subtype_check : Env.t -> typ -> typ -> bool

(* Partial functions: The expressions and patterns passed to these
   functions must be guaranteed to have tannots of the form Some (env,
   typ) for these to work. *)

val env_of : tannot exp -> Env.t
val env_of_annot : Ast.l * tannot -> Env.t

val typ_of : tannot exp -> typ
val typ_of_annot : Ast.l * tannot -> typ

val pat_typ_of : tannot pat -> typ
val pat_env_of : tannot pat -> Env.t

val effect_of : tannot exp -> effect
val effect_of_annot : tannot -> effect

val destruct_atom_nexp : Env.t -> typ -> nexp option

(* Safely destructure an existential type. Returns None if the type is
   not existential. This function will pick a fresh name for the
   existential to ensure that no name-clashes occur. *)
val destruct_exist : Env.t -> typ -> (kid list * n_constraint * typ) option

val destruct_vector : Env.t -> typ -> (nexp * nexp * order * typ) option

type uvar =
  | U_nexp of nexp
  | U_order of order
  | U_effect of effect
  | U_typ of typ

val string_of_uvar : uvar -> string

(* Throws Invalid_argument if the argument is not a E_app expression *)
val instantiation_of : tannot exp -> uvar KBindings.t

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

(* Like check but throws type_errors rather than Sail generic errors
   from Reporting_basic. *)
val check' : Env.t -> 'a defs -> tannot defs * Env.t

val initial_env : Env.t
