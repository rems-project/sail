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
(*    Brian Campbell                                                      *)
(*    Thomas Bauereiss                                                    *)
(*    Anthony Fox                                                         *)
(*    Jon French                                                          *)
(*    Dominic Mulligan                                                    *)
(*    Stephen Kell                                                        *)
(*    Mark Wassell                                                        *)
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

(** Utilities for operating on Sail ASTs *)

open Ast
module Big_int = Nat_big_num

type mut = Immutable | Mutable

(** [lvar] is the type of variables - they can either be registers,
   local mutable or immutable variables, nullary union constructors
   (i.e. None in option), or unbound identifiers *)
type lvar = Register of typ | Enum of typ | Local of mut * typ | Union of typquant * typ | Unbound

val no_annot : unit annot
val gen_loc : Parse_ast.l -> Parse_ast.l

val mk_id : string -> id
val mk_kid : string -> kid
val mk_ord : order_aux -> order
val mk_nc : n_constraint_aux -> n_constraint
val mk_nexp : nexp_aux -> nexp
val mk_exp : unit exp_aux -> unit exp
val mk_pat : unit pat_aux -> unit pat
val mk_pexp : unit pexp_aux -> unit pexp
val mk_lexp : unit lexp_aux -> unit lexp
val mk_lit : lit_aux -> lit
val mk_lit_exp : lit_aux -> unit exp
val mk_funcl : id -> unit pat -> unit exp -> unit funcl
val mk_fundef : (unit funcl) list -> unit def
val mk_val_spec : val_spec_aux -> unit def
val mk_typschm : typquant -> typ -> typschm
val mk_typquant : quant_item list -> typquant
val mk_qi_id : base_kind_aux -> kid -> quant_item
val mk_qi_nc : n_constraint -> quant_item
val mk_qi_kopt : kinded_id -> quant_item
val mk_fexp : id -> unit exp -> unit fexp
val mk_fexps : (unit fexp) list -> unit fexps
val mk_letbind : unit pat -> unit exp -> unit letbind

val unaux_exp : 'a exp -> 'a exp_aux
val unaux_pat : 'a pat -> 'a pat_aux
val unaux_nexp : nexp -> nexp_aux
val unaux_order : order -> order_aux
val unaux_typ : typ -> typ_aux

val inc_ord : order
val dec_ord : order

(* Utilites for working with kinded_ids *)
val kopt_kid : kinded_id -> kid
val is_nat_kopt : kinded_id -> bool
val is_order_kopt : kinded_id -> bool
val is_typ_kopt : kinded_id -> bool

(* Some handy utility functions for constructing types. *)
val mk_typ : typ_aux -> typ
val mk_typ_arg : typ_arg_aux -> typ_arg
val mk_id_typ : id -> typ

(* Sail builtin types. *)
val int_typ : typ
val nat_typ : typ
val atom_typ : nexp -> typ
val range_typ : nexp -> nexp -> typ
val bit_typ : typ
val bool_typ : typ
val app_typ : id -> typ_arg list -> typ
val ref_typ : typ -> typ
val register_typ : typ -> typ
val unit_typ : typ
val string_typ : typ
val real_typ : typ
val vector_typ : nexp -> order -> typ -> typ
val list_typ : typ -> typ
val exc_typ : typ
val tuple_typ : typ list -> typ
val function_typ : typ -> typ -> effect -> typ

val no_effect : effect
val mk_effect : base_effect_aux list -> effect

val nexp_simp : nexp -> nexp

(* Utilities for building n-expressions *)
val nconstant : Big_int.num -> nexp
val nint : int -> nexp
val nminus : nexp -> nexp -> nexp
val nsum : nexp -> nexp -> nexp
val ntimes : nexp -> nexp -> nexp
val npow2 : nexp -> nexp
val nvar : kid -> nexp
val napp : id -> nexp list -> nexp
val nid : id -> nexp (* NOTE: Nexp_id's don't do anything currently *)

(* Numeric constraint builders *)
val nc_eq : nexp -> nexp -> n_constraint
val nc_neq : nexp -> nexp -> n_constraint
val nc_lteq : nexp -> nexp -> n_constraint
val nc_gteq : nexp -> nexp -> n_constraint
val nc_lt : nexp -> nexp -> n_constraint
val nc_gt : nexp -> nexp -> n_constraint
val nc_and : n_constraint -> n_constraint -> n_constraint
val nc_or : n_constraint -> n_constraint -> n_constraint
val nc_true : n_constraint
val nc_false : n_constraint
val nc_set : kid -> Big_int.num list -> n_constraint
val nc_int_set : kid -> int list -> n_constraint

(* Negate a n_constraint. Note that there's no NC_not constructor, so
   this flips all the inequalites a the n_constraint leaves and uses
   de-morgans to switch and to or and vice versa. *)
val nc_negate : n_constraint -> n_constraint

val quant_items : typquant -> quant_item list
val quant_kopts : typquant -> kinded_id list
val quant_split : typquant -> kinded_id list * n_constraint list

(* Functions to map over the annotations in sub-expressions *)
val map_exp_annot : ('a annot -> 'b annot) -> 'a exp -> 'b exp
val map_pat_annot : ('a annot -> 'b annot) -> 'a pat -> 'b pat
val map_pexp_annot : ('a annot -> 'b annot) -> 'a pexp -> 'b pexp
val map_lexp_annot : ('a annot -> 'b annot) -> 'a lexp -> 'b lexp
val map_letbind_annot : ('a annot -> 'b annot) -> 'a letbind -> 'b letbind

(* Extract locations from identifiers *)
val id_loc : id -> Parse_ast.l
val kid_loc : kid -> Parse_ast.l

val pat_loc : 'a pat -> Parse_ast.l
val exp_loc : 'a exp -> Parse_ast.l
val def_loc : 'a def -> Parse_ast.l

(* For debugging and error messages only: Not guaranteed to produce
   parseable SAIL, or even print all language constructs! *)
(* TODO: replace with existing pretty-printer *)
val string_of_id : id -> string
val string_of_kid : kid -> string
val string_of_base_effect_aux : base_effect_aux -> string
val string_of_base_kind_aux : base_kind_aux -> string
val string_of_base_kind : base_kind -> string
val string_of_kind : kind -> string
val string_of_base_effect : base_effect -> string
val string_of_effect : effect -> string
val string_of_order : order -> string
val string_of_nexp : nexp -> string
val string_of_typ : typ -> string
val string_of_typ_arg : typ_arg -> string
val string_of_typ_pat : typ_pat -> string
val string_of_annot : ('a * typ * effect) option -> string
val string_of_n_constraint : n_constraint -> string
val string_of_quant_item : quant_item -> string
val string_of_typquant : typquant -> string
val string_of_typschm : typschm -> string
val string_of_lit : lit -> string
val string_of_exp : 'a exp -> string
val string_of_pexp : 'a pexp -> string
val string_of_lexp : 'a lexp -> string
val string_of_pat : 'a pat -> string
val string_of_letbind : 'a letbind -> string
val string_of_index_range : index_range -> string

val id_of_fundef : 'a fundef -> id
val id_of_type_def : 'a type_def -> id

val id_of_kid : kid -> id
val kid_of_id : id -> kid

val prepend_id : string -> id -> id
val append_id : id -> string -> id
val prepend_kid : string -> kid -> kid

module Id : sig
  type t = id
  val compare : id -> id -> int
end

module Kid : sig
  type t = kid
  val compare : kid -> kid -> int
end

module Nexp : sig
  type t = nexp
  val compare : nexp -> nexp -> int
end

module BE : sig
  type t = base_effect
  val compare : base_effect -> base_effect -> int
end

module IdSet : sig
  include Set.S with type elt = id
end

module NexpSet : sig
  include Set.S with type elt = nexp
end

module BESet : sig
  include Set.S with type elt = base_effect
end

module KidSet : sig
  include Set.S with type elt = kid
end

module KBindings : sig
  include Map.S with type key = kid
end

module Bindings : sig
  include Map.S with type key = id
end

val nexp_frees : nexp -> KidSet.t
val nexp_identical : nexp -> nexp -> bool
val is_nexp_constant : nexp -> bool

val lexp_to_exp : 'a lexp -> 'a exp

val is_number : typ -> bool
val is_reftyp : typ -> bool
val is_vector_typ : typ -> bool
val is_bit_typ : typ -> bool
val is_bitvector_typ : typ -> bool

val typ_app_args_of : typ -> string * typ_arg_aux list * Ast.l
val vector_typ_args_of : typ -> nexp * nexp * order * typ
val destruct_range : typ -> (nexp * nexp) option

val is_order_inc : order -> bool

val has_effect : effect -> base_effect_aux -> bool

val effect_set : effect -> BESet.t

val equal_effects : effect -> effect -> bool
val union_effects : effect -> effect -> effect

val tyvars_of_nexp : nexp -> KidSet.t
val tyvars_of_typ : typ -> KidSet.t
val is_kid_generated : kid -> bool

val undefined_of_typ : bool -> Ast.l -> (typ -> 'annot) -> typ -> 'annot exp

val destruct_pexp : 'a pexp -> 'a pat * ('a exp) option * 'a exp * (Ast.l * 'a)
val construct_pexp : 'a pat * ('a exp) option * 'a exp * (Ast.l * 'a) ->  'a pexp

val is_valspec : id -> 'a def -> bool

val is_fundef : id -> 'a def -> bool

val rename_fundef : id -> 'a fundef -> 'a fundef

val split_defs : ('a def -> bool) -> 'a defs -> ('a defs * 'a def * 'a defs) option

val append_ast : 'a defs -> 'a defs -> 'a defs

val type_union_id : type_union -> id

val pat_ids : 'a pat -> IdSet.t
val subst : id -> 'a exp -> 'a exp -> 'a exp
