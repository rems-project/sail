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

(** The type checker API *)

open Ast
open Ast_defs
open Ast_util
module Big_int = Nat_big_num

(** [set_tc_debug] controls the verbosity of the type checker. 0 is
   silent, 1 prints a tree of the type derivation and 2 is like 1 but
   with much more debugging information. 3 is the highest level, and
   is even more verbose still. *)
val set_tc_debug : int -> unit

(** [opt_no_lexp_bounds_check] turns off the bounds checking in vector
   assignments in l-expressions. *)
val opt_no_lexp_bounds_check : bool ref

(** [opt_expand_valspec] expands typedefs in valspecs during type
   checking. We prefer not to do it for latex output but it is
   otherwise a good idea. *)
val opt_expand_valspec : bool ref

(** Don't expand bitfields (when using old syntax), used for LaTeX output *)
val opt_no_bitfield_expansion : bool ref

(** Only allow mutable variables to be declared with var *)
val opt_strict_var : bool ref

(** {2 Environments} *)

type env

(** The env module defines the internal type checking environment, and
   contains functions that operate on that state. *)
module Env : sig
  (** Env.t is the type of environments *)
  type t = env

  (** Note: Most get_ functions assume the identifiers exist, and throw
     type errors if they don't. *)

  (** Get the quantifier and type for a function identifier, freshening
      type variables. *)
  val get_val_spec : id -> t -> typquant * typ

  val get_val_specs : t -> (typquant * typ) Bindings.t

  val get_defined_val_specs : t -> IdSet.t

  (** Like get_val_spec, except that the original type variables are used.
      Useful when processing the body of the function. *)
  val get_val_spec_orig : id -> t -> typquant * typ

  val update_val_spec : id -> typquant * typ -> t -> t

  val get_register : id -> t -> typ
  val get_registers : t -> typ Bindings.t

  (** Return all the identifiers in an enumeration. Throws a type
     error if the enumeration doesn't exist. *)
  val get_enum : id -> t -> id list

  val get_enums : t -> IdSet.t Bindings.t

  val get_locals : t -> (mut * typ) Bindings.t

  val add_local : id -> mut * typ -> t -> t

  val get_default_order : t -> order

  val get_default_order_opt : t -> order option

  val add_scattered_variant : id -> typquant -> t -> t

  (** Check if a local variable is mutable. Throws Type_error if it
     isn't a local variable. Probably best to use Env.lookup_id
     instead *)
  val is_mutable : id -> t -> bool

  (** Get the current set of constraints. *)
  val get_constraints : t -> n_constraint list

  val add_constraint : ?reason:Ast.l * string -> n_constraint -> t -> t

  (** Push all the type variables and constraints from a typquant into
      an environment *)
  val add_typquant : Ast.l -> typquant -> t -> t

  val get_typ_var : kid -> t -> kind_aux

  val get_typ_vars : t -> kind_aux KBindings.t

  val get_typ_var_locs : t -> Ast.l KBindings.t

  (** Returns the shadowing depth for the given type variable *)
  val shadows : kid -> t -> int

  val get_typ_synonyms : t -> (typquant * typ_arg) Bindings.t

  (** Check whether the identifier is a type name *)
  val bound_typ_id : t -> id -> bool

  val add_typ_var : Ast.l -> kinded_id -> t -> t

  val is_record : id -> t -> bool

  (** Returns record quantifiers and fields *)
  val get_record : id -> t -> typquant * (typ * id) list

  val get_records : t -> (typquant * (typ * id) list) Bindings.t

  val get_variants : t -> (typquant * type_union list) Bindings.t

  (** Return type is: quantifier, argument type, return type *)
  val get_accessor : id -> id -> t -> typquant * typ * typ

  (** If the environment is checking a function, then this will get
     the expected return type of the function. It's useful for
     checking or inserting early returns. Returns an option type and
     won't throw any exceptions. *)
  val get_ret_typ : t -> typ option

  val get_overloads : id -> t -> id list

  val is_extern : id -> t -> string -> bool

  val get_extern : id -> t -> string -> string

  (** Lookup id searchs for a specified id in the environment, and
     returns its type and what kind of identifier it is, using the
     lvar type. Returns Unbound if the identifier is unbound, and
     won't throw any exceptions. *)
  val lookup_id : id -> t -> typ lvar

  val get_toplevel_lets : t -> IdSet.t

  val get_outcome_instantiation : t -> (Ast.l * typ) KBindings.t

  (** Check if id is a constructor, then if it is return a (n, m,
     id, type_union) triple where the values represent its position (n) in the
     list of (m) constructors, the union name, and the type_union entry itself *)
  val union_constructor_info : id -> t -> (int * int * id * type_union) option

  val is_union_constructor : id -> t -> bool

  (** Check if the id is both a constructor, and the only constructor of that
      type. *)
  val is_singleton_union_constructor : id -> t -> bool

  val is_mapping : id -> t -> bool

  val is_register : id -> t -> bool

  (** Check if the type with the given id is a bitfield type *)
  val is_bitfield : id -> t -> bool

  val get_bitfield : id -> t -> typ * index_range Bindings.t

  val expand_constraint_synonyms : t -> n_constraint -> n_constraint

  val expand_nexp_synonyms : t -> nexp -> nexp

  val expand_synonyms : t -> typ -> typ

  (** Expand type synonyms and remove register annotations (i.e. register<t> -> t)) *)
  val base_typ_of : t -> typ -> typ

  (** Note: Likely want use Type_check.initial_env instead. The empty
     environment is lacking even basic builtins. *)
  val empty : t

  val builtin_typs : typquant Bindings.t

  val get_union_id : id -> t -> typquant * typ

  val set_prover : (t -> n_constraint -> bool) option -> t -> t
end

(** {4 Environment helper functions} *)
val add_existential : Ast.l -> kinded_id list -> n_constraint -> Env.t -> Env.t

(** [get_bitfield_ranges id env] returns the index ranges of bitfield type [id],
    or raises [Not_found] if [id] is not a bitfield type. *)
val get_bitfield_ranges : id -> Env.t -> index_range Bindings.t

(** [get_bitfield_range id field env] returns the [index_range] of [field]
    in bitfield type [id], or [None] if the field does not exist. *)
val get_bitfield_range : id -> id -> Env.t -> index_range option

(** When the typechecker creates new type variables it gives them
   fresh names of the form 'fvXXX#name, where XXX is a number (not
   necessarily three digits), and name is the original name when the
   type variable was created by renaming an exisiting type variable to
   avoid shadowing. orig_kid takes such a type variable and strips out
   the 'fvXXX# part. It returns the type variable unmodified if it is
   not of this form. *)
val orig_kid : kid -> kid

val orig_nexp : nexp -> nexp

(** Vector with default order as set in environment by [default Order ord] *)
val dvector_typ : Env.t -> nexp -> typ -> typ

(** {2 Type annotations} *)

(** The type of type annotations *)
type tannot

(** The canonical view of a type annotation is that it is a tuple
   containing an environment (env), a type (typ), such that check_X
   env (strip_X X) typ succeeds, where X is typically exp (i.e an
   expression). Note that it is specifically not guaranteed that
   calling destruct_tannot followed by mk_tannot returns an identical
   type annotation. *)
val destruct_tannot : tannot -> (Env.t * typ) option

val mk_tannot : ?uannot:uannot -> Env.t -> typ -> tannot

val untyped_annot : tannot -> uannot

val map_uannot : (uannot -> uannot) -> tannot -> tannot

val get_instantiations : tannot -> typ_arg KBindings.t option

val empty_tannot : tannot
val is_empty_tannot : tannot -> bool

val string_of_tannot : tannot -> string (* For debugging only *)
val replace_typ : typ -> tannot -> tannot
val replace_env : Env.t -> tannot -> tannot

(** {2 Removing type annotations} *)

(** Strip the type annotations from an expression. *)
val strip_exp : tannot exp -> uannot exp

(** Strip the type annotations from a pattern *)
val strip_pat : tannot pat -> uannot pat

val strip_mpat : tannot mpat -> uannot mpat

(** Strip the type annotations from a pattern-expression *)
val strip_pexp : tannot pexp -> uannot pexp

(** Strip the type annotations from an l-expression *)
val strip_lexp : tannot lexp -> uannot lexp

val strip_mpexp : tannot mpexp -> uannot mpexp
val strip_mapcl : tannot mapcl -> uannot mapcl
val strip_letbind : tannot letbind -> uannot letbind
val strip_val_spec : tannot val_spec -> uannot val_spec
val strip_funcl : tannot funcl -> uannot funcl
val strip_register : tannot dec_spec -> uannot dec_spec
val strip_typedef : tannot type_def -> uannot type_def
val strip_def : tannot def -> uannot def
val strip_ast : tannot ast -> uannot ast

(** {2 Checking expressions and patterns} *)

(** Check an expression has some type. Returns a fully annotated
   version of the expression, where each subexpression is annotated
   with its type and the Environment used while checking it. The can
   be used to re-start the typechecking process on any
   sub-expression. so local modifications to the AST can be
   re-checked. *)
val check_exp : Env.t -> uannot exp -> typ -> tannot exp

val infer_exp : Env.t -> uannot exp -> tannot exp

val infer_pat : Env.t -> uannot pat -> tannot pat * Env.t * uannot exp list

val infer_lexp : Env.t -> uannot lexp -> tannot lexp

val check_case : Env.t -> typ -> uannot pexp -> typ -> tannot pexp

val check_funcl : Env.t -> uannot funcl -> typ -> tannot funcl

val check_fundef : Env.t -> def_annot -> uannot fundef -> tannot def list * Env.t

val check_val_spec : Env.t -> def_annot -> uannot val_spec -> tannot def list * Env.t

val assert_constraint : Env.t -> bool -> tannot exp -> n_constraint option

(** Use the pattern completeness checker to check completeness of a
   list of function clauses. This takes care of setting up the
   environment in the correct way. The type passed is the type of the
   function (Typ_fn), and the environment should be that attached to
   either the SD_funcl clause or the FD_function clause. Note that
   this is only exposed so that it can be used during descattering to
   check completeness of scattered functions, and should not be called
   otherwise. *)
val check_funcls_complete :
  Parse_ast.l -> Env.t -> tannot funcl list -> typ -> tannot funcl list * (def_annot -> def_annot)

(** Attempt to prove a constraint using z3. Returns true if z3 can
   prove that the constraint is true, returns false if z3 cannot prove
   the constraint true. Note that this does not guarantee that the
   constraint is actually false, as the constraint solver is somewhat
   untrustworthy. *)
val prove : string * int * int * int -> Env.t -> n_constraint -> bool

(** Returns Some c if there is a unique c such that nexp = c *)
val solve_unique : Env.t -> nexp -> Big_int.num option

val canonicalize : Env.t -> typ -> typ

val subtype_check : Env.t -> typ -> typ -> bool

val is_enum_member : id -> Env.t -> bool

val bind_pat : Env.t -> uannot pat -> typ -> tannot pat * Env.t * uannot Ast.exp list

(** Variant that doesn't introduce new guards for literal patterns,
   but raises a type error instead.  This should always be safe to use
   on patterns that have previously been type checked. *)
val bind_pat_no_guard : Env.t -> uannot pat -> typ -> tannot pat * Env.t

val tc_assume : n_constraint -> tannot exp -> tannot exp

(** {2 Destructuring type annotations}

   Partial functions: The expressions and patterns passed to these
   functions must be guaranteed to have tannots of the form Some (env,
   typ) for these to work. *)

val env_of : tannot exp -> Env.t
val env_of_annot : Ast.l * tannot -> Env.t
val env_of_tannot : tannot -> Env.t

val typ_of : tannot exp -> typ
val typ_of_annot : Ast.l * tannot -> typ
val typ_of_tannot : tannot -> typ

val typ_of_pat : tannot pat -> typ
val env_of_pat : tannot pat -> Env.t

val typ_of_pexp : tannot pexp -> typ
val env_of_pexp : tannot pexp -> Env.t

val typ_of_mpat : tannot mpat -> typ
val env_of_mpat : tannot mpat -> Env.t

val typ_of_mpexp : tannot mpexp -> typ
val env_of_mpexp : tannot mpexp -> Env.t

val effect_of : tannot exp -> effect
val effect_of_pat : tannot pat -> effect
val effect_of_annot : tannot -> effect
val add_effect_annot : tannot -> effect -> tannot

(* Returns the type that an expression was checked against, if any.
   Note that these may be removed if an expression is rewritten. *)
val expected_typ_of : Ast.l * tannot -> typ option

(** {2 Utilities } *)

(** Safely destructure an existential type. Returns None if the type
   is not existential. This function will pick a fresh name for the
   existential to ensure that no name-collisions occur, although we
   can optionally suggest a name for the case where it would not cause
   a collision. The "plain" version does not treat numeric types
   (i.e. range, int, nat) as existentials. *)
val destruct_exist_plain : ?name:string option -> typ -> (kinded_id list * n_constraint * typ) option

val destruct_exist : ?name:string option -> typ -> (kinded_id list * n_constraint * typ) option

val destruct_atom_nexp : Env.t -> typ -> nexp option

val destruct_atom_bool : Env.t -> typ -> n_constraint option

val destruct_range : Env.t -> typ -> (kid list * n_constraint * nexp * nexp) option

val destruct_numeric : ?name:string option -> typ -> (kid list * n_constraint * nexp) option

val destruct_vector : Env.t -> typ -> (nexp * typ) option
val destruct_bitvector : Env.t -> typ -> nexp option

val vector_start_index : Env.t -> typ -> nexp

(** Construct an existential type with a guaranteed fresh
   identifier. *)
val exist_typ : Parse_ast.l -> (kid -> n_constraint) -> (kid -> typ) -> typ

val subst_unifiers : typ_arg KBindings.t -> typ -> typ

(** [unify l env goals typ1 typ2] returns set of typ_arg bindings such
   that substituting those bindings using every type variable in goals
   will make typ1 and typ2 equal. Will throw a Unification_error if
   typ1 and typ2 cannot unification (although unification in Sail is
   not complete). Will throw a type error if any goals appear in in
   typ2 (occurs check). *)
val unify : l -> Env.t -> KidSet.t -> typ -> typ -> typ_arg KBindings.t

(** Check if two types are alpha equivalent *)
val alpha_equivalent : Env.t -> typ -> typ -> bool

(** Throws Invalid_argument if the argument is not a E_app expression *)
val instantiation_of : tannot exp -> typ_arg KBindings.t

(** Doesn't use the type of the expression when calculating instantiations.
    May fail if the arguments aren't sufficient to calculate all unifiers. *)
val instantiation_of_without_type : tannot exp -> typ_arg KBindings.t

(* Type variable instantiations that inference will extract from constraints *)
val instantiate_simple_equations : quant_item list -> typ_arg KBindings.t

val big_int_of_nexp : nexp -> Big_int.num option

(** {2 Checking full ASTs} *)

(** Fully type-check an AST

Some invariants that will hold of a fully checked AST are:

 - No internal nodes, such as E_internal_exp, or E_comment nodes.

 - E_vector_access nodes and similar will be replaced by function
   calls E_app to vector access functions. This is different to the
   old type checker.

 - Every expressions type annotation [tannot] will be Some (typ, env).

 - Also every pattern will be annotated with the type it matches.

 - Toplevel expressions such as typedefs and some subexpressions such
   as letbinds may have None as their tannots if it doesn't make sense
   for them to have type annotations.

   check throws type_errors rather than Sail generic errors from
   Reporting. For a function that uses generic errors, use
   Type_error.check *)
val check : Env.t -> uannot ast -> tannot ast * Env.t

val check_defs : Env.t -> uannot def list -> tannot def list * Env.t

(** The same as [check], but exposes the intermediate type-checking
   environments so we don't have to always re-check the entire AST *)
val check_with_envs : Env.t -> uannot def list -> (tannot def list * Env.t) list

(** The initial type checking environment *)
val initial_env : Env.t

val prove_smt : assumptions:n_constraint list -> n_constraint -> bool
