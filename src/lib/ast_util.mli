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

(** Utilities and helper functions for operating on Sail ASTs *)

open Ast
open Ast_defs
module Big_int = Nat_big_num

(** {1 Untyped AST annotations and locations} *)

(** The type of annotations for untyped AST nodes. When expressions
   are type-checked the untyped annotations are replaced with typed
   annotations {!Type_check.tannot}. *)
type uannot

val empty_uannot : uannot

(** Add an attribute to an annotation. Attributes are attached to expressions in Sail  via:
    {@sail[
    $[attribute argument] expression
    ]}
    The location argument should be a span that corresponds to the attribute itself, and not
    include the expression.
*)
val add_attribute : l -> string -> string -> uannot -> uannot

val remove_attribute : string -> uannot -> uannot

val get_attribute : string -> uannot -> (l * string) option

val get_attributes : uannot -> (l * string * string) list

val find_attribute_opt : string -> (l * string * string) list -> string option

val mk_def_annot : ?doc:string -> ?attrs:(l * string * string) list -> l -> def_annot

val add_def_attribute : l -> string -> string -> def_annot -> def_annot

val get_def_attribute : string -> def_annot -> (l * string) option

val def_annot_map_loc : (l -> l) -> def_annot -> def_annot

(** The empty annotation (as a location + uannot pair). Should be used
   carefully because it can result in unhelpful error messgaes. However
   a common pattern is generating code with [no_annot], then adding location
   information with the various [locate_] functions in this module. *)
val no_annot : l * uannot

(** [gen_loc l] takes a location l and generates a location which
   means 'generated/derived from location l'. This is useful for debugging
   errors that occur in generated code. *)
val gen_loc : Parse_ast.l -> Parse_ast.l

val is_gen_loc : Parse_ast.l -> bool

(** {1 Variable information} *)

type mut = Immutable | Mutable

(** [lvar] is the type of variables - they can either be registers,
   local mutable or immutable variables constructors or unbound
   identifiers. *)
type 'a lvar = Register of 'a | Enum of 'a | Local of mut * 'a | Unbound of id

val is_unbound : 'a lvar -> bool

(** Note: Partial function -- fails for {!Unbound} lvars *)
val lvar_typ : ?loc:l -> 'a lvar -> 'a

val is_order_inc : order -> bool
val is_order_dec : order -> bool

(** {1 Functions for building and destructuring untyped AST elements} *)

(** {2 Functions for building untyped AST elements} *)

val mk_id : string -> id
val mk_kid : string -> kid
val mk_nc : n_constraint_aux -> n_constraint
val mk_nexp : nexp_aux -> nexp
val mk_exp : ?loc:l -> uannot exp_aux -> uannot exp
val mk_pat : ?loc:l -> uannot pat_aux -> uannot pat
val mk_mpat : uannot mpat_aux -> uannot mpat
val mk_pexp : ?loc:l -> uannot pexp_aux -> uannot pexp
val mk_mpexp : uannot mpexp_aux -> uannot mpexp
val mk_lexp : uannot lexp_aux -> uannot lexp
val mk_lit : lit_aux -> lit
val mk_lit_exp : ?loc:l -> lit_aux -> uannot exp
val mk_typ_pat : typ_pat_aux -> typ_pat
val mk_funcl : ?loc:l -> id -> uannot pat -> uannot exp -> uannot funcl
val mk_fundef : uannot funcl list -> uannot def
val mk_val_spec : val_spec_aux -> uannot def
val mk_typschm : typquant -> typ -> typschm
val mk_typquant : quant_item list -> typquant
val mk_qi_id : kind_aux -> kid -> quant_item
val mk_qi_nc : n_constraint -> quant_item
val mk_qi_kopt : kinded_id -> quant_item
val mk_fexp : id -> uannot exp -> uannot fexp
val mk_letbind : uannot pat -> uannot exp -> uannot letbind
val mk_kopt : ?loc:l -> kind_aux -> kid -> kinded_id
val mk_def : ?loc:l -> 'a def_aux -> 'a def

(** Mapping patterns are a subset of patterns, so we can always convert one to the other *)
val pat_of_mpat : 'a mpat -> 'a pat

(** {2 Unwrap aux constructors} *)

val unaux_exp : 'a exp -> 'a exp_aux
val unaux_pat : 'a pat -> 'a pat_aux
val unaux_nexp : nexp -> nexp_aux
val unaux_typ : typ -> typ_aux
val unaux_kind : kind -> kind_aux
val unaux_constraint : n_constraint -> n_constraint_aux

(** {2 Destruct type annotated patterns and expressions} *)

(** [untyp_pat (P_aux (P_typ (typ, pat)), _)] returns [Some (pat,
   typ)] or [None] if the pattern does not match. *)
val untyp_pat : 'a pat -> 'a pat * typ option

(** Same as [untyp_pat], but for [E_typ] nodes *)
val uncast_exp : 'a exp -> 'a exp * typ option

(** {2 Utilites for working with kinded_ids} *)

val kopt_kid : kinded_id -> kid
val kopt_kind : kinded_id -> kind

val is_int_kopt : kinded_id -> bool
val is_typ_kopt : kinded_id -> bool
val is_bool_kopt : kinded_id -> bool

(** {2 Utility functions for constructing types} *)

val mk_typ : typ_aux -> typ
val mk_typ_arg : typ_arg_aux -> typ_arg
val mk_id_typ : id -> typ

val is_typ_arg_nexp : typ_arg -> bool
val is_typ_arg_typ : typ_arg -> bool
val is_typ_arg_bool : typ_arg -> bool

(** {2 Sail built-in types} *)

val unknown_typ : typ
val int_typ : typ
val nat_typ : typ
val atom_typ : nexp -> typ
val implicit_typ : nexp -> typ
val range_typ : nexp -> nexp -> typ
val bit_typ : typ
val bool_typ : typ
val atom_bool_typ : n_constraint -> typ
val app_typ : id -> typ_arg list -> typ
val register_typ : typ -> typ
val unit_typ : typ
val string_typ : typ
val real_typ : typ
val vector_typ : nexp -> typ -> typ
val bitvector_typ : nexp -> typ
val list_typ : typ -> typ
val exc_typ : typ
val tuple_typ : typ list -> typ
val function_typ : typ list -> typ -> typ

val is_unit_typ : typ -> bool
val is_number : typ -> bool
val is_ref_typ : typ -> bool
val is_vector_typ : typ -> bool
val is_bit_typ : typ -> bool
val is_bitvector_typ : typ -> bool

(** {1 Simplifcation of numeric expressions and constraints}

   These functions simplify nexps and n_constraints using various
   basic rules. In general they will guarantee to reduce constant
   numeric expressions like 2 + 5 into 7, although they will not
   simplify 2^constant, as that often leads to unreadable error
   messages containing huge numbers. *)

val nexp_simp : nexp -> nexp
val constraint_simp : n_constraint -> n_constraint

(** If a constraint is a conjunction, return a list of all the top-level conjuncts *)
val constraint_conj : n_constraint -> n_constraint list

(** Same as constraint_conj but for disjunctions *)
val constraint_disj : n_constraint -> n_constraint list

type effect

val no_effect : effect
val monadic_effect : effect

val effectful : effect -> bool

val equal_effects : effect -> effect -> bool
val subseteq_effects : effect -> effect -> bool
val union_effects : effect -> effect -> effect

(** {2 Functions for building numeric expressions} *)

val nconstant : Big_int.num -> nexp
val nint : int -> nexp
val nminus : nexp -> nexp -> nexp
val nsum : nexp -> nexp -> nexp
val ntimes : nexp -> nexp -> nexp
val npow2 : nexp -> nexp
val nvar : kid -> nexp
val napp : id -> nexp list -> nexp
val nid : id -> nexp

(** {2 Functions for building numeric constraints} *)

val nc_eq : nexp -> nexp -> n_constraint
val nc_neq : nexp -> nexp -> n_constraint
val nc_lteq : nexp -> nexp -> n_constraint
val nc_gteq : nexp -> nexp -> n_constraint
val nc_lt : nexp -> nexp -> n_constraint
val nc_gt : nexp -> nexp -> n_constraint
val nc_and : n_constraint -> n_constraint -> n_constraint
val nc_or : n_constraint -> n_constraint -> n_constraint
val nc_not : n_constraint -> n_constraint
val nc_true : n_constraint
val nc_false : n_constraint
val nc_set : kid -> Big_int.num list -> n_constraint
val nc_int_set : kid -> int list -> n_constraint
val nc_var : kid -> n_constraint

(** {2 Functions for building type arguments}*)

val arg_nexp : ?loc:l -> nexp -> typ_arg
val arg_typ : ?loc:l -> typ -> typ_arg
val arg_bool : ?loc:l -> n_constraint -> typ_arg
val arg_kopt : kinded_id -> typ_arg

(** {1 Set and Map modules for various AST elements} *)

module Id : sig
  type t = id
  val compare : id -> id -> int
end

module Kid : sig
  type t = kid
  val compare : kid -> kid -> int
end

module Kind : sig
  type t = kind
  val compare : kind -> kind -> int
end

module KOpt : sig
  type t = kinded_id
  val compare : kinded_id -> kinded_id -> int
end

module Nexp : sig
  type t = nexp
  val compare : nexp -> nexp -> int
end

module NC : sig
  type t = n_constraint
  val compare : n_constraint -> n_constraint -> int
end

(* NB: the comparison function does not expand synonyms *)
module Typ : sig
  type t = typ
  val compare : typ -> typ -> int
end

module IdSet : sig
  include Set.S with type elt = id
end

module NexpSet : sig
  include Set.S with type elt = nexp
end

module NexpMap : sig
  include Map.S with type key = nexp
end

module KOptSet : sig
  include Set.S with type elt = kinded_id
end

module KOptMap : sig
  include Map.S with type key = kinded_id
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

module NCMap : sig
  include Map.S with type key = n_constraint
end

module TypMap : sig
  include Map.S with type key = typ
end

(** {1 Functions for working with type quantifiers} *)

val quant_add : quant_item -> typquant -> typquant
val quant_items : typquant -> quant_item list
val quant_kopts : typquant -> kinded_id list
val quant_split : typquant -> kinded_id list * n_constraint list
val quant_map_items : (quant_item -> quant_item) -> typquant -> typquant

val is_quant_kopt : quant_item -> bool
val is_quant_constraint : quant_item -> bool

(** {1 Functions to map over annotations in sub-expressions} *)

val map_exp_annot : ('a annot -> 'b annot) -> 'a exp -> 'b exp
val map_pat_annot : ('a annot -> 'b annot) -> 'a pat -> 'b pat
val map_pexp_annot : ('a annot -> 'b annot) -> 'a pexp -> 'b pexp
val map_lexp_annot : ('a annot -> 'b annot) -> 'a lexp -> 'b lexp
val map_letbind_annot : ('a annot -> 'b annot) -> 'a letbind -> 'b letbind
val map_mpat_annot : ('a annot -> 'b annot) -> 'a mpat -> 'b mpat
val map_mpexp_annot : ('a annot -> 'b annot) -> 'a mpexp -> 'b mpexp
val map_mapcl_annot : ('a annot -> 'b annot) -> 'a mapcl -> 'b mapcl

val map_typedef_annot : ('a annot -> 'b annot) -> 'a type_def -> 'b type_def
val map_fundef_annot : ('a annot -> 'b annot) -> 'a fundef -> 'b fundef
val map_funcl_annot : ('a annot -> 'b annot) -> 'a funcl -> 'b funcl
val map_mapdef_annot : ('a annot -> 'b annot) -> 'a mapdef -> 'b mapdef
val map_valspec_annot : ('a annot -> 'b annot) -> 'a val_spec -> 'b val_spec
val map_register_annot : ('a annot -> 'b annot) -> 'a dec_spec -> 'b dec_spec
val map_scattered_annot : ('a annot -> 'b annot) -> 'a scattered_def -> 'b scattered_def

val map_def_annot : ('a annot -> 'b annot) -> 'a def -> 'b def
val map_ast_annot : ('a annot -> 'b annot) -> 'a ast -> 'b ast

(** {1 Extract locations from terms} *)
val id_loc : id -> Parse_ast.l

val kid_loc : kid -> Parse_ast.l
val kopt_loc : kinded_id -> Parse_ast.l
val typ_loc : typ -> Parse_ast.l
val pat_loc : 'a pat -> Parse_ast.l
val mpat_loc : 'a mpat -> Parse_ast.l
val exp_loc : 'a exp -> Parse_ast.l
val nexp_loc : nexp -> Parse_ast.l
val def_loc : 'a def -> Parse_ast.l

(** {1 Printing utilities}

   Note: For debugging and error messages only - not guaranteed to
   produce parseable Sail, or even print all language constructs! *)

val string_of_id : id -> string
val string_of_kid : kid -> string
val string_of_kind_aux : kind_aux -> string
val string_of_kind : kind -> string
val string_of_nexp : nexp -> string
val string_of_typ : typ -> string
val string_of_typ_arg : typ_arg -> string
val string_of_typ_pat : typ_pat -> string
val string_of_n_constraint : n_constraint -> string
val string_of_kinded_id : kinded_id -> string
val string_of_quant_item : quant_item -> string
val string_of_typquant : typquant -> string
val string_of_typschm : typschm -> string
val string_of_lit : lit -> string
val string_of_exp : 'a exp -> string
val string_of_pexp : 'a pexp -> string
val string_of_lexp : 'a lexp -> string
val string_of_pat : 'a pat -> string
val string_of_mpat : 'a mpat -> string
val string_of_letbind : 'a letbind -> string
val string_of_index_range : index_range -> string

(** {1 Functions for getting identifiers from toplevel definitions} *)

val id_of_fundef : 'a fundef -> id
val id_of_mapdef : 'a mapdef -> id
val id_of_type_def : 'a type_def -> id
val id_of_val_spec : 'a val_spec -> id
val id_of_dec_spec : 'a dec_spec -> id

(** {2 Functions for manipulating identifiers} *)

val deinfix : id -> id

val id_of_kid : kid -> id
val kid_of_id : id -> kid

val prepend_id : string -> id -> id
val append_id : id -> string -> id
val prepend_kid : string -> kid -> kid

(** {1 Misc functions} *)

val nexp_frees : nexp -> KidSet.t
val nexp_identical : nexp -> nexp -> bool
val is_nexp_constant : nexp -> bool
val int_of_nexp_opt : nexp -> Big_int.num option

val lexp_to_exp : 'a lexp -> 'a exp

val typ_app_args_of : typ -> string * typ_arg_aux list * Ast.l
val vector_typ_args_of : typ -> nexp * typ

val kopts_of_nexp : nexp -> KOptSet.t
val kopts_of_typ : typ -> KOptSet.t
val kopts_of_typ_arg : typ_arg -> KOptSet.t
val kopts_of_constraint : n_constraint -> KOptSet.t
val kopts_of_quant_item : quant_item -> KOptSet.t

val tyvars_of_nexp : nexp -> KidSet.t
val tyvars_of_typ : typ -> KidSet.t
val tyvars_of_typ_arg : typ_arg -> KidSet.t
val tyvars_of_constraint : n_constraint -> KidSet.t
val tyvars_of_quant_item : quant_item -> KidSet.t
val is_kid_generated : kid -> bool

val undefined_of_typ : bool -> Ast.l -> (typ -> 'annot) -> typ -> 'annot exp

val pattern_vector_subranges : 'a pat -> (Big_int.num * Big_int.num) list Bindings.t

val destruct_pexp : 'a pexp -> 'a pat * 'a exp option * 'a exp * (Ast.l * 'a)
val construct_pexp : 'a pat * 'a exp option * 'a exp * (Ast.l * 'a) -> 'a pexp

val destruct_mpexp : 'a mpexp -> 'a mpat * 'a exp option * (Ast.l * 'a)
val construct_mpexp : 'a mpat * 'a exp option * (Ast.l * 'a) -> 'a mpexp

val is_valspec : id -> 'a def -> bool
val is_fundef : id -> 'a def -> bool

val rename_valspec : id -> 'a val_spec -> 'a val_spec

val rename_fundef : id -> 'a fundef -> 'a fundef

val split_defs : ('a def -> bool) -> 'a def list -> ('a def list * 'a def * 'a def list) option

val append_ast : 'a ast -> 'a ast -> 'a ast
val append_ast_defs : 'a ast -> 'a def list -> 'a ast
val concat_ast : 'a ast list -> 'a ast

val type_union_id : type_union -> id

val ids_of_def : 'a def -> IdSet.t
val ids_of_defs : 'a def list -> IdSet.t
val ids_of_ast : 'a ast -> IdSet.t

val val_spec_ids : 'a def list -> IdSet.t

val record_ids : 'a def list -> IdSet.t

val get_scattered_union_clauses : id -> 'a def list -> type_union list
val get_scattered_enum_clauses : id -> 'a def list -> id list

val pat_ids : 'a pat -> IdSet.t

val subst : id -> 'a exp -> 'a exp -> 'a exp

val hex_to_bin : string -> string

val vector_string_to_bit_list : lit -> lit list

(** {1 Manipulating locations} *)

(** locate takes an expression and recursively sets the location in
   every subexpression using a function that takes the orginal
   location as an argument. Expressions build using mk_exp and similar
   do not have locations, so they can then be annotated as e.g. locate
   (gen_loc l) (mk_exp ...) where l is the location from which the
   code is being generated. *)
val locate : (l -> l) -> 'a exp -> 'a exp

val locate_pat : (l -> l) -> 'a pat -> 'a pat

val locate_lexp : (l -> l) -> 'a lexp -> 'a lexp

val locate_typ : (l -> l) -> typ -> typ

(** Make a unique location by giving it a Parse_ast.Unique wrapper with
   a generated number. *)
val unique : l -> l

val extern_assoc : string -> extern option -> string option

(** Try to find the annotation closest to the provided (simplified)
   location. Note that this function makes no guarantees about finding
   the closest annotation or even finding an annotation at all. This
   is used by the Emacs mode to provide type-at-cursor functionality
   and we don't mind if it's a bit fuzzy in that context. *)
val find_annot_ast : (Lexing.position * Lexing.position) option -> 'a ast -> (Ast.l * 'a) option

(** {1 Substitutions}

   The function X_subst substitutes a type argument into something of
   type X. The type of the type argument determines which kind of type
   variables will be replaced *)

val nexp_subst : kid -> typ_arg -> nexp -> nexp
val constraint_subst : kid -> typ_arg -> n_constraint -> n_constraint
val typ_subst : kid -> typ_arg -> typ -> typ
val typ_arg_subst : kid -> typ_arg -> typ_arg -> typ_arg

val subst_kid : (kid -> typ_arg -> 'a -> 'a) -> kid -> kid -> 'a -> 'a

(* Multiple type-level substitutions *)
val subst_kids_nexp : nexp KBindings.t -> nexp -> nexp
val subst_kids_nc : nexp KBindings.t -> n_constraint -> n_constraint
val subst_kids_typ : nexp KBindings.t -> typ -> typ
val subst_kids_typ_arg : nexp KBindings.t -> typ_arg -> typ_arg

val quant_item_subst_kid : kid -> kid -> quant_item -> quant_item
val typquant_subst_kid : kid -> kid -> typquant -> typquant

val simple_string_of_loc : Parse_ast.l -> string
