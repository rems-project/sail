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

(** This file defines the Sail abstract syntax tree (AST) *)

Require Extraction.

From Stdlib Require Import Unicode.Utf8.
From Stdlib Require Import String.
From Stdlib Require Import ZArith.
From Stdlib Require Import QArith.

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

Inductive id_type : Set :=
| Local_variable : id_type
| Global_register : id_type
| Enum_member : id_type.

Inductive vector_concat_split : Set :=
| No_split : vector_concat_split
| Split : nat → vector_concat_split.

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

Inductive kind_aux : Set :=
| K_type : kind_aux
| K_int : kind_aux
| K_bool : kind_aux.

Inductive kid_aux : Set :=
| Var : string → kid_aux.

Inductive kind : Set :=
| K_aux : kind_aux → loc → kind.

Inductive kid : Set :=
| Kid_aux : kid_aux → loc → kid.

Inductive kinded_id_aux : Set :=
| KOpt_kind : kind → kid → kinded_id_aux.

Inductive id_aux : Set :=
| And_bool : id_aux
| Or_bool : id_aux
| Id : string → id_aux
| Operator : string → id_aux.

Inductive kinded_id : Set :=
| KOpt_aux : kinded_id_aux → loc → kinded_id.

Inductive id : Set :=
| Id_aux : id_aux → loc → id.

Inductive value : Set :=
| V_bitvector : list bit → value
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
ones and zeros with no intrinsic meaning attached. *)

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

(** Struct constructs often allow an optional struct name, which can
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
| LE_app : id → list exp → lexp_aux
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

Inductive mpexp_aux (a : Set) : Set :=
| MPat_pat : mpat a → mpexp_aux a
| MPat_when : mpat a → exp a → mpexp_aux a.

Inductive mpexp (a : Set) : Set :=
| MPat_aux : mpexp_aux a → annot a → mpexp a.

Definition pexp_funcl (a : Set) : Set := pexp a.

Definition typquant : Set := list quant_item.

Inductive typschm_aux : Set :=
| TypSchm_ts : typquant → typ → typschm_aux.

Inductive mapcl_aux (a : Set) : Set :=
| MCL_bidir : mpexp a → mpexp a → mapcl_aux a
| MCL_forwards : pexp a → mapcl_aux a
| MCL_backwards : pexp a → mapcl_aux a.

Inductive funcl_aux (a : Set) : Set :=
| FCL_funcl : id → pexp_funcl a → funcl_aux a.

Inductive tannot_opt_aux : Set :=
| Typ_annot_opt_none : tannot_opt_aux
| Typ_annot_opt_some : typquant → typ → tannot_opt_aux.

Inductive type_union_aux : Set :=
| Tu_ty_id : typ → id → type_union_aux.

Inductive rec_opt_aux (a : Set) : Set :=
| Rec_nonrec : rec_opt_aux a
| Rec_rec : rec_opt_aux a
| Rec_measure : pat a → exp a → rec_opt_aux a.

Inductive typschm : Set :=
| TypSchm_aux : typschm_aux → loc → typschm.

Inductive mapcl (a : Set) : Set :=
| MCL_aux : mapcl_aux a → clause_annot a → mapcl a.

Inductive funcl (a : Set) : Set :=
| FCL_aux : funcl_aux a → clause_annot a → funcl a.

Inductive tannot_opt : Set :=
| Typ_annot_opt_aux : tannot_opt_aux → loc → tannot_opt.

Inductive type_union : Set :=
| Tu_aux : type_union_aux → def_annot unit → type_union.

Inductive rec_opt (a : Set) : Set :=
| Rec_aux : rec_opt_aux a → loc → rec_opt a.

Inductive index_range_aux : Set :=
| BF_single : nexp → index_range_aux
| BF_range : nexp → nexp → index_range_aux
| BF_concat : index_range → index_range → index_range_aux

with index_range : Set :=
| BF_aux : index_range_aux → loc → index_range.

Inductive opt_abstract_config : Set :=
| TDC_key : list string → opt_abstract_config
| TDC_none : opt_abstract_config.

Inductive outcome_spec_aux : Set :=
| OV_outcome : id → typschm → typquant → outcome_spec_aux.

Inductive instantiation_spec_aux (a : Set) : Set :=
| IN_id : id → instantiation_spec_aux a.

Inductive val_spec_aux : Set :=
| VS_val_spec : typschm → id → option extern → val_spec_aux.

Inductive default_spec_aux : Set :=
| DT_order : order → default_spec_aux.

Inductive scattered_def_aux (a : Set) : Set :=
| SD_function : id → tannot_opt → scattered_def_aux a
| SD_funcl : funcl a → scattered_def_aux a
| SD_variant : id → typquant → scattered_def_aux a
| SD_unioncl : id → type_union → scattered_def_aux a
| SD_internal_unioncl_record :
  id → id → typquant → list (id * typ * def_annot unit) → scattered_def_aux a
| SD_mapping : id → tannot_opt → scattered_def_aux a
| SD_mapcl : id → mapcl a → scattered_def_aux a
| SD_enum : id → scattered_def_aux a
| SD_enumcl : id → id → scattered_def_aux a
| SD_end : id → scattered_def_aux a.

Inductive dec_spec_aux (a : Set) : Set :=
| DEC_reg : typ → id → option (exp a) → dec_spec_aux a.

Inductive subst_aux : Set :=
| IS_typ : kid → typ_arg → subst_aux
| IS_id : id → id → subst_aux.

Inductive mapdef_aux (a : Set) : Set :=
| MD_mapping : id → tannot_opt → list (mapcl a) → mapdef_aux a.

Inductive fundef_aux (a : Set) : Set :=
| FD_function : rec_opt a → tannot_opt → list (funcl a) → fundef_aux a.

Inductive type_def_aux : Set :=
| TD_abbrev : id → typquant → typ_arg → type_def_aux
| TD_record : id → typquant → list (id * typ * def_annot unit) → bool → type_def_aux
| TD_variant : id → typquant → list type_union → bool → type_def_aux
| TD_enum : id → list (id * def_annot unit) → bool → type_def_aux
| TD_abstract : id → kind → opt_abstract_config → type_def_aux
| TD_bitfield : id → typ → list (id * index_range * def_annot unit) → type_def_aux.

Inductive outcome_spec : Set :=
| OV_aux : outcome_spec_aux → loc → outcome_spec.

Inductive instantiation_spec (a : Set) : Set :=
| IN_aux : instantiation_spec_aux a → annot a → instantiation_spec a.

Inductive val_spec (a : Set) : Set :=
| VS_aux : val_spec_aux → annot a → val_spec a.

Inductive default_spec : Set :=
| DT_aux : default_spec_aux → loc → default_spec.

Inductive scattered_def (a : Set) : Set :=
| SD_aux : scattered_def_aux a → annot a → scattered_def a.

Inductive dec_spec (a : Set) : Set :=
| DEC_aux : dec_spec_aux a → annot a → dec_spec a.

Inductive prec : Set :=
| Infix : prec
| InfixL : prec
| InfixR : prec.

Definition loop_measure : Set := loop * exp unit.

Inductive pragma : Set :=
| Pragma_line : string → loc → pragma
| Pragma_structured : list (string * attribute_data) → pragma.

Inductive subst : Set :=
| IS_aux : subst_aux → loc → subst.

Inductive mapdef (a : Set) : Set :=
| MD_aux : mapdef_aux a → annot a → mapdef a.

Inductive fundef (a : Set) : Set :=
| FD_aux : fundef_aux a → annot a → fundef a.

Inductive type_def (a : Set) : Set :=
| TD_aux : type_def_aux → annot a → type_def a.

(** ** Definitions *)

Inductive def_aux (a b : Set) : Set :=
| DEF_type : type_def a → def_aux a b
| DEF_constraint : n_constraint → def_aux a b
| DEF_fundef : fundef a → def_aux a b
| DEF_mapdef : mapdef a → def_aux a b
| DEF_impl : funcl a → def_aux a b
| DEF_let : pat a → exp a → def_aux a b
| DEF_val : val_spec a → def_aux a b
| DEF_outcome : outcome_spec → list (def a b) → def_aux a b
| DEF_instantiation : instantiation_spec a → list subst → def_aux a b
| DEF_fixity : prec → Z → id → def_aux a b
| DEF_overload : id → list id → def_aux a b
| DEF_default : default_spec → def_aux a b
| DEF_scattered : scattered_def a → def_aux a b
| DEF_measure : id → pat a → exp a → def_aux a b
| DEF_loop_measures : id → list loop_measure → def_aux a b
| DEF_register : dec_spec a → def_aux a b
| DEF_internal_mutrec : list (fundef a) → def_aux a b
| DEF_pragma : string → pragma → def_aux a b

with def (a b : Set) : Set :=
| DEF_aux : def_aux a b → def_annot b → def a b.
