(* ************************************************************************ *)
(*  Sail and the Sail architecture models here, comprising all files and    *)
(*  directories except the ASL-derived Sail code in the aarch64 directory,  *)
(*  are subject to the BSD two-clause licence below.                        *)
(*                                                                          *)
(*  The ASL derived parts of the ARMv8.3 specification in                   *)
(*  aarch64/no_vector and aarch64/full are copyright ARM Ltd.               *)
(*                                                                          *)
(*  Copyright (c) 2013-2026                                                 *)
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
(*  This work was partially supported by EPSRC grant EP/K008528/1 REMS:     *)
(*  Rigorous Engineering for Mainstream Systems, an ARM iCASE award, EPSRC  *)
(*  IAA KTF funding, and donations from Arm. This project has received      *)
(*  funding from the European Research Council (ERC) under the European     *)
(*  Union's Horizon 2020 research and innovation programme (grant agreement *)
(*  No 789108, ELVER).                                                      *)
(*                                                                          *)
(*  This software was developed by SRI International and the University of  *)
(*  Cambridge Computer Laboratory (Department of Computer Science and       *)
(*  Technology) under DARPA/AFRL contracts FA8650-18-C-7809 ("CIFV")        *)
(*  and FA8750-10-C-0237 ("CTSRD").                                         *)
(*                                                                          *)
(*  SPDX-License-Identifier: BSD-2-Clause                                   *)
(* ************************************************************************ *)

(** This file defines the Sail abstract syntax tree (AST).

The general pattern is that for a type [exp] (for expressions) there
will be a wrapper constructor [E_aux] which attaches meta-data like
typing information and location information to the underlying actual
type [exp_aux]. *)

Require Extraction.

From Stdlib Require Import Unicode.Utf8.
From Stdlib Require Import String.
From Stdlib Require Import ZArith.
From Stdlib Require Import QArith.

From stdpp Require Import bitvector.definitions.

From Sail Require Import Bit.

(** * External types

We start by defining some external types that are not formalised in
Rocq. *)

Parameter loc : Set.

(** Locations are ultimately derived from OCamllex positions. Within
the Rocq semantics, we need to preserve them wherever possible for
error reporting, but otherwise we don't need to know anything about
them. *)

Definition l := loc.

Extract Inlined Constant loc => "Parse_ast.l".

Parameter ext_unknown_loc : loc.

Extract Inlined Constant ext_unknown_loc => "Parse_ast.Unknown".

(** Documentation comments. *)

Parameter ext_doc_comment : Set.

Extract Inlined Constant ext_doc_comment => "Parse_ast.doc_comment".

(** Sail attribute data. For an attribute like

<<
$[attr <foo>]
>>

we can detect whether << attr >> is present, but the attribute data << foo >>
is an external opaque type from the perspective of Rocq. *)

Parameter ext_attribute_data : Set.

Extract Inlined Constant ext_attribute_data => "Parse_ast.Attribute_data.attribute_data".

Definition attribute_data := ext_attribute_data.

Inductive visibility : Set :=
| Public : visibility
| Private : loc → visibility.

Module extern.
  Record record : Set := Build {
    pure : bool;
    bindings : list (string * string);
  }.

  Definition with_pure pure (r : record) :=
    Build pure r.(bindings).
  Definition with_bindings bindings (r : record) :=
    Build r.(pure) bindings.
End extern.

Definition extern := extern.record.

Module def_annot.
  Record record {A : Set} : Set := Build {
    doc_comment : option ext_doc_comment;
    attrs : list (loc * (string * option attribute_data));
    visibility : visibility;
    loc : loc;
    env : A;
  }.

  Arguments record : clear implicits.

  Definition with_doc_comment {A} doc_comment (r : record A) :=
    Build A doc_comment r.(attrs) r.(visibility) r.(loc) r.(env).
  Definition with_attrs {A} attrs (r : record A) :=
    Build A r.(doc_comment) attrs r.(visibility) r.(loc) r.(env).
  Definition with_visibility {A} visibility (r : record A) :=
    Build A r.(doc_comment) r.(attrs) visibility r.(loc) r.(env).
  Definition with_loc {A} loc (r : record A) :=
    Build A r.(doc_comment) r.(attrs) r.(visibility) loc r.(env).
  Definition with_env {A} env (r : record A) :=
    Build A r.(doc_comment) r.(attrs) r.(visibility) r.(loc) env.
End def_annot.

Definition def_annot := def_annot.record.

Definition clause_annot (A : Set) : Set := def_annot unit * A.

Definition annot (A : Set) : Set := loc * A.

Inductive non_empty (A : Set) : Set :=
| Non_empty : A → list A → non_empty A.

Arguments Non_empty {_}.

Inductive loop : Set :=
| While : loop
| Until : loop.

(** Sail has three kinds of types, denoted <<Type>>, <<Int>>, and
<<Bool>>.

<<Nat>> also exists in the syntax, but other than playing a role in
kind-inference it is essentially just sugar for <<Int>> combined with
a constraint that the type is zero or greater. *)

Inductive kind_aux : Set :=
| K_type : kind_aux
| K_int : kind_aux
| K_bool : kind_aux.

Inductive kind : Set :=
| K_aux : kind_aux → loc → kind.

(** Type variables *)

Inductive kid_aux : Set :=
| Var : string → kid_aux.

Inductive kid : Set :=
| Kid_aux : kid_aux → loc → kid.

(** A [kinded_id] is a type variable paired with an explicit [kind].
In the syntax this would be denoted as:

<<'n : Int>> or <<'a : Type>>.

Kind-inference happens during the desugaring performed by the OCaml
<<Initial_check>> module, so the source syntax the kinds will often be
implicit. *)

Inductive kinded_id_aux : Set :=
| KOpt_kind : kind → kid → kinded_id_aux.

Inductive kinded_id : Set :=
| KOpt_aux : kinded_id_aux → loc → kinded_id.

(** Identifiers. *)

Inductive id_aux : Set :=
| And_bool : id_aux
| Or_bool : id_aux
| Id : string → id_aux
| Operator : string → id_aux.

Inductive id : Set :=
| Id_aux : id_aux → loc → id.

Inductive value : Set :=
| V_bitvector : bvn → value
| V_vector : list value → value
| V_list : list value → value
| V_int : Z → value
| V_real : Q → value
| V_bool : bool → value
| V_tuple : list value → value
| V_unit : value
| V_string : string → value
| V_ref : id → value
| V_member : id → value
| V_ctor : id → list value → value
| V_record : list (id * value) → value.

(** * Literals

Note that the literal type preserves the presentation of bitvector
literals from the source code including underscores separating groups
of digits. Furthermore, we distinguish the binary digit type from the
underlying [bit] type. This is because in bitvectors ([V_bitvector]),
bits have significance - there is a least significant bit and a most
significant bit, whereas a list of [bin_digit] is just a sequence of
ones and zeros with no intrinsic meaning attached.

A [V_bitvector] holds a [bvn], a stdpp bitvector paired with its width.
It cannot name [PrimBits] here, since that module depends on this one;
the operations on these values live there. *)

Inductive hex_digit : Set :=
| Hex_0 : hex_digit
| Hex_1 : hex_digit
| Hex_2 : hex_digit
| Hex_3 : hex_digit
| Hex_4 : hex_digit
| Hex_5 : hex_digit
| Hex_6 : hex_digit
| Hex_7 : hex_digit
| Hex_8 : hex_digit
| Hex_9 : hex_digit
| Hex_A : hex_digit
| Hex_B : hex_digit
| Hex_C : hex_digit
| Hex_D : hex_digit
| Hex_E : hex_digit
| Hex_F : hex_digit.

Inductive bin_digit : Set :=
| Bin_0
| Bin_1.

Inductive lit_aux : Set :=
| L_unit : lit_aux
| L_true : lit_aux
| L_false : lit_aux
| L_num : Z → lit_aux
| L_hex : list (non_empty hex_digit) → lit_aux
| L_bin : list (non_empty bin_digit) → lit_aux
| L_string : string → lit_aux
| L_real : Q → lit_aux.

Inductive lit : Set :=
| L_aux : lit_aux → loc → lit.

(** * Types and constraints *)

Inductive nexp_aux : Set :=
| Nexp_id : id → nexp_aux
| Nexp_var : kid → nexp_aux
| Nexp_constant : Z → nexp_aux
| Nexp_app : id → list nexp → nexp_aux
| Nexp_if : n_constraint → nexp → nexp → nexp_aux
| Nexp_times : nexp → nexp → nexp_aux
| Nexp_sum : nexp → nexp → nexp_aux
| Nexp_minus : nexp → nexp → nexp_aux
| Nexp_exp : nexp → nexp_aux
| Nexp_neg : nexp → nexp_aux

with nexp : Set :=
| Nexp_aux : nexp_aux → loc → nexp

with typ_aux : Set :=
| Typ_internal_unknown : typ_aux
| Typ_id : id → typ_aux
| Typ_var : kid → typ_aux
| Typ_fn : list typ → typ → typ_aux
| Typ_bidir : typ → typ → typ_aux
| Typ_tuple : list typ → typ_aux
| Typ_app : id → list typ_arg → typ_aux
| Typ_exist : list kinded_id → n_constraint → typ → typ_aux

with typ : Set :=
| Typ_aux : typ_aux → loc → typ

with typ_arg_aux : Set :=
| A_nexp : nexp → typ_arg_aux
| A_typ : typ → typ_arg_aux
| A_bool : n_constraint → typ_arg_aux

with typ_arg : Set :=
| A_aux : typ_arg_aux → loc → typ_arg

with n_constraint_aux : Set :=
| NC_equal : typ_arg → typ_arg → n_constraint_aux
| NC_not_equal : typ_arg → typ_arg → n_constraint_aux
| NC_ge : nexp → nexp → n_constraint_aux
| NC_gt : nexp → nexp → n_constraint_aux
| NC_le : nexp → nexp → n_constraint_aux
| NC_lt : nexp → nexp → n_constraint_aux
| NC_set : nexp → list Z → n_constraint_aux
| NC_and : n_constraint → n_constraint → n_constraint_aux
| NC_or : n_constraint → n_constraint → n_constraint_aux
| NC_app : id → list typ_arg → n_constraint_aux
| NC_id : id → n_constraint_aux
| NC_var : kid → n_constraint_aux
| NC_true : n_constraint_aux
| NC_false : n_constraint_aux

with n_constraint : Set :=
| NC_aux : n_constraint_aux → loc → n_constraint.

Inductive order_aux : Set :=
| Ord_inc : order_aux
| Ord_dec : order_aux.

Inductive quant_item_aux : Set :=
| QI_id : kinded_id → quant_item_aux
| QI_constraint : n_constraint → quant_item_aux.

Inductive quant_item : Set :=
| QI_aux : quant_item_aux → loc → quant_item.

Inductive order : Set :=
| Ord_aux : order_aux → loc → order.

(** Struct constructs allow an optional struct name, which can
help disambiguate during type-checking. See [P_struct], [MP_struct] or
[E_struct] for examples of this. *)

Inductive struct_name : Set :=
| SN_id : id → struct_name
| SN_anon : struct_name.

(** * Patterns *)

(** This type represents the optional wildcard in a struct pattern ([P_struct]).

<<
struct { field = <pat>, _ }
>>

Note that it is not permitted in mappings ([MP_struct]). *)

Inductive field_pat_wildcard : Set :=
| FP_wild : loc → field_pat_wildcard
| FP_no_wild : field_pat_wildcard.

(** Type patterns are subset of type syntax, used to bind new type variables. *)

Inductive typ_pat_aux : Set :=
| TP_wild : typ_pat_aux
| TP_var : kid → typ_pat_aux
| TP_app : id → list typ_pat → typ_pat_aux

with typ_pat : Set :=
| TP_aux : typ_pat_aux → loc → typ_pat.

Inductive pat_aux {A : Set} : Set :=
| P_lit : lit → pat_aux
| P_wild : pat_aux
| P_or : pat → pat → pat_aux
| P_not : pat → pat_aux
| P_as : pat → id → pat_aux
| P_typ : typ → pat → pat_aux
| P_id : id → pat_aux
| P_var : pat → typ_pat → pat_aux
| P_app : id → list pat → pat_aux
| P_vector : list pat → pat_aux
| P_vector_concat : list pat → pat_aux
| P_vector_subrange : id → Z → Z → pat_aux
| P_tuple : list pat → pat_aux
| P_list : list pat → pat_aux
| P_cons : pat → pat → pat_aux
| P_string_append : list pat → pat_aux
| P_struct : struct_name → list (id * pat) → field_pat_wildcard → pat_aux

with pat {A : Set} : Set :=
| P_aux : pat_aux → annot A → pat.

Arguments pat_aux A : clear implicits.
Arguments pat A : clear implicits.

(** ** Mapping patterns

Mapping patterns are the subset of the pattern type that is permitted
to occur in bi-directional mapping clauses. *)

Inductive mpat_aux {A : Set} : Set :=
| MP_lit : lit → mpat_aux
| MP_id : id → mpat_aux
| MP_app : id → list mpat → mpat_aux
| MP_vector : list mpat → mpat_aux
| MP_vector_concat : list mpat → mpat_aux
| MP_vector_subrange : id → Z → Z → mpat_aux
| MP_tuple : list mpat → mpat_aux
| MP_list : list mpat → mpat_aux
| MP_cons : mpat → mpat → mpat_aux
| MP_string_append : list mpat → mpat_aux
| MP_typ : mpat → typ → mpat_aux
| MP_as : mpat → id → mpat_aux
| MP_struct : struct_name → list (id * mpat) → mpat_aux

with mpat {A : Set} : Set :=
| MP_aux : mpat_aux → annot A → mpat.

Arguments mpat_aux A : clear implicits.
Arguments mpat A : clear implicits.

(** * Expressions and L-expressions *)

Inductive in_place_loop_measure_aux {A : Set} : Set :=
| Measure_none : in_place_loop_measure_aux
| Measure_some : exp → in_place_loop_measure_aux

with in_place_loop_measure {A : Set} : Set :=
| Measure_aux : in_place_loop_measure_aux → loc → in_place_loop_measure

with exp_aux {A : Set} : Set :=
| E_block : list exp → exp_aux
| E_id : id → exp_aux
| E_lit : lit → exp_aux
| E_typ : typ → exp → exp_aux
| E_app : id → list exp → exp_aux
| E_tuple : list exp → exp_aux
| E_if : exp → exp → exp → exp_aux
| E_loop : loop → in_place_loop_measure → exp → exp → exp_aux
| E_for : id → exp → exp → exp → order → exp → exp_aux
| E_vector : list exp → exp_aux
| E_vector_append : exp → exp → exp_aux
| E_list : list exp → exp_aux
| E_cons : exp → exp → exp_aux
| E_struct : struct_name → list fexp → exp_aux
| E_struct_update : exp → list fexp → exp_aux
| E_field : exp → id → exp_aux
| E_match : exp → list pexp → exp_aux
| E_let : pat A → exp → exp → exp_aux
| E_assign : lexp → exp → exp_aux
| E_sizeof : nexp → exp_aux
| E_return : exp → exp_aux
| E_exit : exp → exp_aux
| E_config : list string → exp_aux
| E_ref : id → exp_aux
| E_throw : exp → exp_aux
| E_try : exp → list pexp → exp_aux
| E_assert : exp → exp → exp_aux
| E_var : lexp → exp → exp → exp_aux
| E_undef : exp_aux
| E_internal_plet : pat A → exp → exp → exp_aux
| E_internal_return : exp → exp_aux
| E_internal_value : value → exp_aux
| E_internal_assume : n_constraint → exp → exp_aux
| E_constraint : n_constraint → exp_aux

with exp {A : Set} : Set :=
| E_aux : exp_aux → annot A → exp

with lexp_aux {A : Set} : Set :=
| LE_id : id → lexp_aux
| LE_deref : exp → lexp_aux
| LE_typ : typ → id → lexp_aux
| LE_tuple : list lexp → lexp_aux
| LE_vector_concat : list lexp → lexp_aux
| LE_vector : lexp → exp → lexp_aux
| LE_vector_range : lexp → exp → exp → lexp_aux
| LE_field : lexp → id → lexp_aux

with lexp {A : Set} : Set :=
| LE_aux : lexp_aux → annot A → lexp

with fexp_aux {A : Set} : Set :=
| FE_fexp : id → exp → fexp_aux

with fexp {A : Set} : Set :=
| FE_aux : fexp_aux → annot A → fexp

with pexp_aux {A : Set} : Set :=
| Pat_exp : pat A → exp → pexp_aux
| Pat_when : pat A → exp → exp → pexp_aux

with pexp {A : Set} : Set :=
| Pat_aux : pexp_aux → annot A → pexp.

Arguments in_place_loop_measure_aux A : clear implicits.
Arguments in_place_loop_measure A : clear implicits.
Arguments exp_aux A : clear implicits.
Arguments exp A : clear implicits.
Arguments lexp_aux A : clear implicits.
Arguments lexp A : clear implicits.
Arguments fexp_aux A : clear implicits.
Arguments fexp A : clear implicits.
Arguments pexp_aux A : clear implicits.
Arguments pexp A : clear implicits.

(** * Top-level constructs *)

(** ** Type definitions *)

Definition typquant : Set := list quant_item.

Inductive type_union_aux : Set :=
| Tu_ty_id : typ → id → type_union_aux.

Inductive type_union : Set :=
| Tu_aux : type_union_aux → def_annot unit → type_union.

(** A field of a bitfield is either a single bit, a contiguous range of bits,

or a possibly non-contiguous concatenation of various ranges. *)

Inductive index_range_aux : Set :=
| BF_single : nexp → index_range_aux
| BF_range : nexp → nexp → index_range_aux
| BF_concat : index_range → index_range → index_range_aux

with index_range : Set :=
| BF_aux : index_range_aux → loc → index_range.

Inductive type_def_aux : Set :=
| TD_abbrev : id → typquant → typ_arg → type_def_aux
| TD_record : id → typquant → list (id * typ * def_annot unit) → type_def_aux
| TD_variant : id → typquant → list type_union → bool → type_def_aux
| TD_enum : id → list (id * def_annot unit) → type_def_aux
| TD_abstract : id → kind → option (list string) → type_def_aux
| TD_bitfield : id → typ → list (id * index_range * def_annot unit) → type_def_aux.

Inductive type_def (A : Set) : Set :=
| TD_aux : type_def_aux → annot A → type_def A.

(** ** Mapping clauses *)

Inductive mpexp_aux (A : Set) : Set :=
| MPat_pat : mpat A → mpexp_aux A
| MPat_when : mpat A → exp A → mpexp_aux A.

Inductive mpexp (A : Set) : Set :=
| MPat_aux : mpexp_aux A → annot A → mpexp A.

Inductive mapcl_aux (A : Set) : Set :=
| MCL_bidir : mpexp A → mpexp A → mapcl_aux A
| MCL_forwards : pexp A → mapcl_aux A
| MCL_backwards : pexp A → mapcl_aux A.

Inductive mapcl (A : Set) : Set :=
| MCL_aux : mapcl_aux A → clause_annot A → mapcl A.

(** ** Function clauses *)

Inductive funcl_aux (A : Set) : Set :=
| FCL_funcl : id → pexp A → funcl_aux A.

Inductive funcl (A : Set) : Set :=
| FCL_aux : funcl_aux A → clause_annot A → funcl A.

Inductive tannot_opt_aux : Set :=
| Typ_annot_opt_none : tannot_opt_aux
| Typ_annot_opt_some : typquant → typ → tannot_opt_aux.

(** ** Toplevel type annotations *)

Inductive rec_opt_aux (A : Set) : Set :=
| Rec_nonrec : rec_opt_aux A
| Rec_rec : rec_opt_aux A
| Rec_measure : pat A → exp A → rec_opt_aux A.

Inductive typschm_aux : Set :=
| TypSchm_ts : typquant → typ → typschm_aux.

Inductive typschm : Set :=
| TypSchm_aux : typschm_aux → loc → typschm.

Inductive tannot_opt : Set :=
| Typ_annot_opt_aux : tannot_opt_aux → loc → tannot_opt.

Inductive rec_opt (A : Set) : Set :=
| Rec_aux : rec_opt_aux A → loc → rec_opt A.

(** ** Outcomes and instantiations *)

Inductive outcome_spec_aux : Set :=
| OV_outcome : id → typschm → typquant → outcome_spec_aux.

Inductive outcome_spec : Set :=
| OV_aux : outcome_spec_aux → loc → outcome_spec.

Inductive instantiation_spec_aux (A : Set) : Set :=
| IN_id : id → instantiation_spec_aux A.

Inductive instantiation_spec (A : Set) : Set :=
| IN_aux : instantiation_spec_aux A → annot A → instantiation_spec A.

Inductive subst_aux : Set :=
| IS_typ : kid → typ_arg → subst_aux
| IS_id : id → id → subst_aux.

Inductive subst : Set :=
| IS_aux : subst_aux → loc → subst.

(** ** Scattered definitions *)

Inductive scattered_def_aux (A : Set) : Set :=
| SD_function : id → tannot_opt → scattered_def_aux A
| SD_funcl : funcl A → scattered_def_aux A
| SD_variant : id → typquant → scattered_def_aux A
| SD_unioncl : id → type_union → scattered_def_aux A
| SD_internal_unioncl_record :
  id → id → typquant → list (id * typ * def_annot unit) → scattered_def_aux A
| SD_mapping : id → tannot_opt → scattered_def_aux A
| SD_mapcl : id → mapcl A → scattered_def_aux A
| SD_enum : id → scattered_def_aux A
| SD_enumcl : id → id → scattered_def_aux A
| SD_end : id → scattered_def_aux A.

Inductive scattered_def (A : Set) : Set :=
| SD_aux : scattered_def_aux A → annot A → scattered_def A.

(** ** Definitions *)

Inductive val_spec_aux : Set :=
| VS_val_spec : typschm → id → option extern → val_spec_aux.

Inductive val_spec (A : Set) : Set :=
| VS_aux : val_spec_aux → annot A → val_spec A.

Inductive default_spec_aux : Set :=
| DT_order : order → default_spec_aux.

Inductive default_spec : Set :=
| DT_aux : default_spec_aux → loc → default_spec.

Inductive reg_spec_aux (A : Set) : Set :=
| Reg : typ → id → option (exp A) → reg_spec_aux A.

Inductive reg_spec (A : Set) : Set :=
| Reg_aux : reg_spec_aux A → annot A → reg_spec A.

Inductive prec : Set :=
| Infix : prec
| InfixL : prec
| InfixR : prec.

Definition loop_measure : Set := loop * exp unit.

Inductive pragma : Set :=
| Pragma_line : string → loc → pragma
| Pragma_structured : list (string * attribute_data) → pragma.

Inductive mapdef_aux (A : Set) : Set :=
| MD_mapping : id → tannot_opt → list (mapcl A) → mapdef_aux A.

Inductive mapdef (A : Set) : Set :=
| MD_aux : mapdef_aux A → annot A → mapdef A.

Inductive fundef_aux (A : Set) : Set :=
| FD_function : rec_opt A → tannot_opt → list (funcl A) → fundef_aux A.

Inductive fundef (A : Set) : Set :=
| FD_aux : fundef_aux A → annot A → fundef A.

Inductive def_aux (A B : Set) : Set :=
| Def_type : type_def A → def_aux A B
| Def_constraint : n_constraint → def_aux A B
| Def_fundef : fundef A → def_aux A B
| Def_mapdef : mapdef A → def_aux A B
| Def_impl : funcl A → def_aux A B
| Def_let : pat A → exp A → def_aux A B
| Def_val : val_spec A → def_aux A B
| Def_outcome : outcome_spec → list (def A B) → def_aux A B
| Def_instantiation : instantiation_spec A → list subst → def_aux A B
| Def_fixity : prec → Z → id → def_aux A B
| Def_overload : id → list id → def_aux A B
| Def_default : default_spec → def_aux A B
| Def_scattered : scattered_def A → def_aux A B
| Def_measure : id → pat A → exp A → def_aux A B
| Def_loop_measures : id → list loop_measure → def_aux A B
| Def_register : reg_spec A → def_aux A B
| Def_internal_mutrec : list (fundef A) → def_aux A B
| Def_pragma : string → pragma → def_aux A B

with def (A B : Set) : Set :=
| Def_aux : def_aux A B → def_annot B → def A B.
