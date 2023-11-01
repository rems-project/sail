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

(** Linearize cases involving power where we would otherwise require
   the SMT solver to use non-linear arithmetic. *)
val opt_smt_linearize : bool ref

type global_env

type env

type t = env

val freshen_bind : t -> typquant * typ -> typquant * typ

val get_default_order : t -> order
val get_default_order_opt : t -> order option
val set_default_order : order -> t -> t

val add_val_spec : ?ignore_duplicate:bool -> id -> typquant * typ -> t -> t
val update_val_spec : id -> typquant * typ -> t -> t
val define_val_spec : id -> t -> t
val get_defined_val_specs : t -> IdSet.t
val get_val_spec : id -> t -> typquant * typ
val get_val_specs : t -> (typquant * typ) Bindings.t
val get_val_spec_orig : id -> t -> typquant * typ

val add_outcome : id -> typquant * typ * kinded_id list * id list * t -> t -> t
val get_outcome : l -> id -> t -> typquant * typ * kinded_id list * id list * t
val get_outcome_instantiation : t -> (Ast.l * typ) KBindings.t
val add_outcome_variable : l -> kid -> typ -> t -> t
val set_outcome_typschm : outcome_loc:l -> typquant * typ -> t -> t
val get_outcome_typschm_opt : t -> (typquant * typ) option

val is_variant : id -> t -> bool
val add_variant : id -> typquant * type_union list -> t -> t
val add_scattered_variant : id -> typquant -> t -> t
val add_variant_clause : id -> type_union -> t -> t
val get_variant : id -> t -> typquant * type_union list
val get_variants : t -> (typquant * type_union list) Bindings.t
val get_scattered_variant_env : id -> t -> t
val set_scattered_variant_env : variant_env:t -> id -> t -> t
val union_constructor_info : id -> t -> (int * int * id * type_union) option
val is_union_constructor : id -> t -> bool
val is_singleton_union_constructor : id -> t -> bool
val add_union_id : id -> typquant * typ -> t -> t
val get_union_id : id -> t -> typquant * typ

val is_mapping : id -> t -> bool

val add_record : id -> typquant -> (typ * id) list -> t -> t
val is_record : id -> t -> bool
val get_record : id -> t -> typquant * (typ * id) list
val get_records : t -> (typquant * (typ * id) list) Bindings.t
val get_accessor_fn : id -> id -> t -> typquant * typ
val get_accessor : id -> id -> t -> typquant * typ * typ

val add_local : id -> mut * typ -> t -> t
val get_locals : t -> (mut * typ) Bindings.t
val is_mutable : id -> t -> bool

val add_toplevel_lets : IdSet.t -> t -> t
val get_toplevel_lets : t -> IdSet.t

val is_register : id -> t -> bool
val get_register : id -> t -> typ
val get_registers : t -> typ Bindings.t
val add_register : id -> typ -> t -> t

val get_constraints : t -> n_constraint list
val get_constraint_reasons : t -> ((Ast.l * string) option * n_constraint) list
val add_constraint : ?reason:Ast.l * string -> n_constraint -> t -> t

val add_typquant : l -> typquant -> t -> t

val get_typ_var : kid -> t -> kind_aux
val get_typ_var_loc_opt : kid -> t -> Ast.l option
val get_typ_vars : t -> kind_aux KBindings.t
val get_typ_var_locs : t -> Ast.l KBindings.t

type type_variables = Type_internal.type_variables

val get_typ_vars_info : t -> type_variables
val lookup_typ_var : kid -> type_variables -> (Ast.l * kind_aux) option
val is_shadowed : kid -> type_variables -> bool

val shadows : kid -> t -> int
val add_typ_var_shadow : l -> kinded_id -> t -> t * kid option
val add_typ_var : l -> kinded_id -> t -> t

val get_ret_typ : t -> typ option
val add_ret_typ : typ -> t -> t

val add_typ_synonym : id -> typquant -> typ_arg -> t -> t
val get_typ_synonyms : t -> (typquant * typ_arg) Bindings.t

val bound_typ_id : t -> id -> bool

val add_overloads : l -> id -> id list -> t -> t
val get_overloads : id -> t -> id list

val is_extern : id -> t -> string -> bool
val add_extern : id -> extern -> t -> t
val get_extern : id -> t -> string -> string

val add_enum : id -> id list -> t -> t
val add_scattered_enum : id -> t -> t
val add_enum_clause : id -> id -> t -> t
val get_enum : id -> t -> id list
val get_enums : t -> IdSet.t Bindings.t

val allow_polymorphic_undefineds : t -> t
val polymorphic_undefineds : t -> bool

val lookup_id : id -> t -> typ lvar

val expand_synonyms : t -> typ -> typ
val expand_nexp_synonyms : t -> nexp -> nexp
val expand_constraint_synonyms : t -> n_constraint -> n_constraint

val base_typ_of : t -> typ -> typ

val allow_unknowns : t -> bool
val set_allow_unknowns : bool -> t -> t

val is_bitfield : id -> t -> bool
val add_bitfield : id -> typ -> index_range Bindings.t -> t -> t
val get_bitfield : id -> t -> typ * index_range Bindings.t

val no_bindings : t -> t

val is_toplevel : t -> l option

(* Well formedness-checks *)
val wf_typ : t -> typ -> unit
val wf_constraint : ?exs:KidSet.t -> t -> n_constraint -> unit

(** Some of the code in the environment needs to use the smt solver,
   which is defined below. To break the circularity this would cause
   (as the prove code depends on the environment), we add a reference
   to the prover to the initial environment. *)
val set_prover : (t -> n_constraint -> bool) option -> t -> t

(** This should not be used outside the type checker, as initial_env
   sets up a correct initial environment. *)
val empty : t

val builtin_typs : typquant Bindings.t
