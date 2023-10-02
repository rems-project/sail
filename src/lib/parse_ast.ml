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

(* generated by Ott 0.25 from: l2_parse.ott *)

module Big_int = Nat_big_num

type text = string

type l =
  | Unknown
  | Unique of int * l
  | Generated of l
  | Hint of string * l * l
  | Range of Lexing.position * Lexing.position

type 'a annot = l * 'a

type extern = { pure : bool; bindings : (string * string) list }

exception Parse_error_locn of l * string

type x = text (* identifier *)
type ix = text (* infix identifier *)

type kind_aux =
  | (* base kind *)
    K_type (* kind of types *)
  | K_int (* kind of natural number size expressions *)
  | K_order (* kind of vector order specifications *)
  | K_bool (* kind of constraints *)

type kind = K_aux of kind_aux * l

type base_effect_aux =
  | (* effect *)
    BE_rreg (* read register *)
  | BE_wreg (* write register *)
  | BE_rmem (* read memory *)
  | BE_wmem (* write memory *)
  | BE_wmv (* write memory value *)
  | BE_eamem (* address for write signaled *)
  | BE_exmem (* determine if a store-exclusive (ARM) is going to succeed *)
  | BE_barr (* memory barrier *)
  | BE_depend (* dynamically dependent footprint *)
  | BE_undef (* undefined-instruction exception *)
  | BE_unspec (* unspecified values *)
  | BE_nondet (* nondeterminism from intra-instruction parallelism *)
  | BE_escape
  | BE_config

type kid_aux = (* identifiers with kind, ticked to differentiate from program variables *)
  | Var of x

type id_aux = (* Identifier *)
  | Id of x | Operator of x (* remove infix status *)

type base_effect = BE_aux of base_effect_aux * l

type kid = Kid_aux of kid_aux * l

type id = Id_aux of id_aux * l

type 'a infix_token = IT_primary of 'a | IT_op of id | IT_prefix of id

type lit_aux =
  | (* Literal constant *)
    L_unit (* $() : _$ *)
  | L_zero (* $_ : _$ *)
  | L_one (* $_ : _$ *)
  | L_true (* $_ : _$ *)
  | L_false (* $_ : _$ *)
  | L_num of Big_int.num (* natural number constant *)
  | L_hex of string (* bit vector constant, C-style *)
  | L_bin of string (* bit vector constant, C-style *)
  | L_undef (* undefined value *)
  | L_string of string (* string constant *)
  | L_real of string

type lit = L_aux of lit_aux * l

type atyp_aux =
  (* expressions of all kinds, to be translated to types, nats, orders, and effects after parsing *)
  | ATyp_id of id (* identifier *)
  | ATyp_var of kid (* ticked variable *)
  | ATyp_lit of lit (* literal *)
  | ATyp_nset of Big_int.num list (* set type *)
  | ATyp_in of atyp * atyp (* set type *)
  | ATyp_times of atyp * atyp (* product *)
  | ATyp_sum of atyp * atyp (* sum *)
  | ATyp_minus of atyp * atyp (* subtraction *)
  | ATyp_exp of atyp (* exponential *)
  | ATyp_neg of atyp (* Internal (but not M as I want a datatype constructor) negative nexp *)
  | ATyp_infix of (atyp infix_token * Lexing.position * Lexing.position) list
  | ATyp_inc (* increasing *)
  | ATyp_dec (* decreasing *)
  | ATyp_set of base_effect list (* effect set *)
  | ATyp_fn of atyp * atyp * atyp (* Function type, last atyp is an effect *)
  | ATyp_bidir of atyp * atyp * atyp (* Mapping type, last atyp is an effect *)
  | ATyp_wild
  | ATyp_tuple of atyp list (* Tuple type *)
  | ATyp_app of id * atyp list (* type constructor application *)
  | ATyp_exist of kinded_id list * atyp * atyp
  | ATyp_parens of atyp

and atyp = ATyp_aux of atyp_aux * l

and kinded_id_aux =
  (* optionally kind-annotated identifier *)
  | KOpt_kind of string option * kid list * kind option (* kind-annotated variable *)

and kinded_id = KOpt_aux of kinded_id_aux * l

type quant_item_aux =
  (* Either a kinded identifier or a nexp constraint for a typquant *)
  | QI_id of kinded_id (* An optionally kinded identifier *)
  | QI_constraint of atyp (* A constraint for this type *)

type quant_item = QI_aux of quant_item_aux * l

type typquant_aux =
  (* type quantifiers and constraints *)
  | TypQ_tq of quant_item list
  | TypQ_no_forall (* sugar, omitting quantifier and constraints *)

type typquant = TypQ_aux of typquant_aux * l

type typschm_aux = (* type scheme *)
  | TypSchm_ts of typquant * atyp

type typschm = TypSchm_aux of typschm_aux * l

type pat_aux =
  (* Pattern *)
  | P_lit of lit (* literal constant pattern *)
  | P_wild (* wildcard        - always matches *)
  | P_typ of atyp * pat (* typed pattern *)
  | P_id of id (* identifier *)
  | P_var of pat * atyp (* bind pat to type variable *)
  | P_app of id * pat list (* union constructor pattern *)
  | P_vector of pat list (* vector pattern *)
  | P_vector_concat of pat list (* concatenated vector pattern *)
  | P_vector_subrange of id * Big_int.num * Big_int.num
  | P_tuple of pat list (* tuple pattern *)
  | P_list of pat list (* list pattern *)
  | P_cons of pat * pat (* cons pattern *)
  | P_string_append of pat list (* string append pattern, x ^^ y *)
  | P_struct of fpat list (* struct pattern *)
  | P_attribute of string * string * pat

and pat = P_aux of pat_aux * l

and fpat_aux = (* Field pattern *)
  | FP_field of id * pat | FP_wild

and fpat = FP_aux of fpat_aux * l

type loop = While | Until

type if_loc = { if_loc : l; then_loc : l; else_loc : l option }

type measure_aux = (* optional termination measure for a loop *)
  | Measure_none | Measure_some of exp

and measure = Measure_aux of measure_aux * l

and exp_aux =
  (* Expression *)
  | E_block of exp list (* block (parsing conflict with structs?) *)
  | E_id of id (* identifier *)
  | E_ref of id
  | E_deref of exp
  | E_lit of lit (* literal constant *)
  | E_typ of atyp * exp (* cast *)
  | E_app of id * exp list (* function application *)
  | E_app_infix of exp * id * exp (* infix function application *)
  | E_infix of (exp infix_token * Lexing.position * Lexing.position) list
  | E_tuple of exp list (* tuple *)
  | E_if of exp * exp * exp * if_loc (* conditional *)
  | E_loop of loop * measure * exp * exp
  | E_for of id * exp * exp * exp * atyp * exp (* loop *)
  | E_vector of exp list (* vector (indexed from 0) *)
  | E_vector_access of exp * exp (* vector access *)
  | E_vector_subrange of exp * exp * exp (* subvector extraction *)
  | E_vector_update of exp * exp * exp (* vector functional update *)
  | E_vector_update_subrange of exp * exp * exp * exp (* vector subrange update (with vector) *)
  | E_vector_append of exp * exp (* vector concatenation *)
  | E_list of exp list (* list *)
  | E_cons of exp * exp (* cons *)
  | E_struct of exp list (* struct *)
  | E_struct_update of exp * exp list (* functional update of struct *)
  | E_field of exp * id (* field projection from struct *)
  | E_match of exp * pexp list (* pattern matching *)
  | E_let of letbind * exp (* let expression *)
  | E_assign of exp * exp (* imperative assignment *)
  | E_sizeof of atyp
  | E_constraint of atyp
  | E_exit of exp
  | E_throw of exp
  | E_try of exp * pexp list
  | E_return of exp
  | E_assert of exp * exp
  | E_var of exp * exp * exp
  | E_attribute of string * string * exp
  | E_internal_plet of pat * exp * exp
  | E_internal_return of exp
  | E_internal_assume of atyp * exp

and exp = E_aux of exp_aux * l

and opt_default_aux =
  | (* Optional default value for indexed vectors, to define a default value for any unspecified positions in a sparse map *)
    Def_val_empty
  | Def_val_dec of exp

and opt_default = Def_val_aux of opt_default_aux * l

and pexp_aux = (* Pattern match *)
  | Pat_exp of pat * exp | Pat_when of pat * exp * exp

and pexp = Pat_aux of pexp_aux * l

and letbind_aux = (* Let binding *)
  | LB_val of pat * exp (* value binding, implicit type (pat must be total) *)

and letbind = LB_aux of letbind_aux * l

type tannot_opt_aux =
  | (* Optional type annotation for functions *)
    Typ_annot_opt_none
  | Typ_annot_opt_some of typquant * atyp

type typschm_opt_aux = TypSchm_opt_none | TypSchm_opt_some of typschm

type typschm_opt = TypSchm_opt_aux of typschm_opt_aux * l

type effect_opt_aux =
  | (* Optional effect annotation for functions *)
    Effect_opt_none (* sugar for empty effect set *)
  | Effect_opt_effect of atyp

type rec_opt_aux =
  | (* Optional recursive annotation for functions *)
    Rec_none (* no termination measure *)
  | Rec_measure of pat * exp (* recursive with termination measure *)

type funcl = FCL_aux of funcl_aux * l

and funcl_aux =
  (* Function clause *)
  | FCL_attribute of string * string * funcl
  | FCL_doc of string * funcl
  | FCL_funcl of id * pexp

type type_union = Tu_aux of type_union_aux * l

and type_union_aux =
  (* Type union constructors *)
  | Tu_attribute of string * string * type_union
  | Tu_doc of string * type_union
  | Tu_ty_id of atyp * id
  | Tu_ty_anon_rec of (atyp * id) list * id

type tannot_opt = Typ_annot_opt_aux of tannot_opt_aux * l

type effect_opt = Effect_opt_aux of effect_opt_aux * l

type rec_opt = Rec_aux of rec_opt_aux * l

type subst_aux =
  (* instantiation substitution *)
  | IS_typ of kid * atyp (* instantiate a type variable with a type *)
  | IS_id of id * id (* instantiate an identifier with another identifier *)

type subst = IS_aux of subst_aux * l

type index_range_aux =
  (* index specification, for bitfields in register types *)
  | BF_single of atyp (* single index *)
  | BF_range of atyp * atyp (* index range *)
  | BF_concat of index_range * index_range (* concatenation of index ranges *)

and index_range = BF_aux of index_range_aux * l

type default_typing_spec_aux =
  (* Default kinding or typing assumption, and default order for literal vectors and vector shorthands *)
  | DT_order of kind * atyp

type mpat_aux =
  (* Mapping pattern. Mostly the same as normal patterns but only constructible parts *)
  | MP_lit of lit
  | MP_id of id
  | MP_app of id * mpat list
  | MP_vector of mpat list
  | MP_vector_concat of mpat list
  | MP_vector_subrange of id * Big_int.num * Big_int.num
  | MP_tuple of mpat list
  | MP_list of mpat list
  | MP_cons of mpat * mpat
  | MP_string_append of mpat list
  | MP_typ of mpat * atyp
  | MP_as of mpat * id
  | MP_struct of (id * mpat) list

and mpat = MP_aux of mpat_aux * l

type mpexp_aux = MPat_pat of mpat | MPat_when of mpat * exp

type mpexp = MPat_aux of mpexp_aux * l

type mapcl = MCL_aux of mapcl_aux * l

and mapcl_aux =
  (* mapping clause (bidirectional pattern-match) *)
  | MCL_attribute of string * string * mapcl
  | MCL_doc of string * mapcl
  | MCL_bidir of mpexp * mpexp
  | MCL_forwards of mpexp * exp
  | MCL_backwards of mpexp * exp

type mapdef_aux =
  (* mapping definition (bidirectional pattern-match function) *)
  | MD_mapping of id * typschm_opt * mapcl list

type mapdef = MD_aux of mapdef_aux * l

type outcome_spec_aux = (* outcome declaration *)
  | OV_outcome of id * typschm * kinded_id list

type outcome_spec = OV_aux of outcome_spec_aux * l

type fundef_aux = (* Function definition *)
  | FD_function of rec_opt * tannot_opt * effect_opt * funcl list

type type_def_aux =
  (* Type definition body *)
  | TD_abbrev of id * typquant * kind * atyp (* type abbreviation *)
  | TD_record of id * typquant * (atyp * id) list (* struct type definition *)
  | TD_variant of id * typquant * type_union list (* union type definition *)
  | TD_enum of id * (id * atyp) list * (id * exp option) list (* enumeration type definition *)
  | TD_bitfield of id * atyp * (id * index_range) list (* register mutable bitfield type definition *)

type val_spec_aux = (* Value type specification *)
  | VS_val_spec of typschm * id * extern option

type dec_spec_aux = (* Register declarations *)
  | DEC_reg of atyp * id * exp option

type scattered_def_aux =
  (* Function and type union definitions that can be spread across
     a file. Each one must end in $_$ *)
  | SD_function of rec_opt * tannot_opt * effect_opt * id (* scattered function definition header *)
  | SD_funcl of funcl (* scattered function definition clause *)
  | SD_enum of id (* scattered enumeration definition header *)
  | SD_enumcl of id * id (* scattered enumeration member clause *)
  | SD_variant of id * typquant (* scattered union definition header *)
  | SD_unioncl of id * type_union (* scattered union definition member *)
  | SD_mapping of id * tannot_opt
  | SD_mapcl of id * mapcl
  | SD_end of id (* scattered definition end *)

type default_typing_spec = DT_aux of default_typing_spec_aux * l

type fundef = FD_aux of fundef_aux * l

type type_def = TD_aux of type_def_aux * l

type val_spec = VS_aux of val_spec_aux * l

type dec_spec = DEC_aux of dec_spec_aux * l

type loop_measure = Loop of loop * exp

type scattered_def = SD_aux of scattered_def_aux * l

type prec = Infix | InfixL | InfixR

type fixity_token = prec * Big_int.num * string

type def_aux =
  (* Top-level definition *)
  | DEF_type of type_def (* type definition *)
  | DEF_fundef of fundef (* function definition *)
  | DEF_mapdef of mapdef (* mapping definition *)
  | DEF_impl of funcl (* impl definition *)
  | DEF_let of letbind (* value definition *)
  | DEF_overload of id * id list (* operator overload specifications *)
  | DEF_fixity of prec * Big_int.num * id (* fixity declaration *)
  | DEF_val of val_spec (* top-level type constraint *)
  | DEF_outcome of outcome_spec * def list (* top-level outcome definition *)
  | DEF_instantiation of id * subst list (* instantiation *)
  | DEF_default of default_typing_spec (* default kind and type assumptions *)
  | DEF_scattered of scattered_def (* scattered definition *)
  | DEF_measure of id * pat * exp (* separate termination measure declaration *)
  | DEF_loop_measures of id * loop_measure list (* separate termination measure declaration *)
  | DEF_register of dec_spec (* register declaration *)
  | DEF_pragma of string * string
  | DEF_attribute of string * string * def
  | DEF_doc of string * def
  | DEF_internal_mutrec of fundef list

and def = DEF_aux of def_aux * l

type lexp_aux =
  (* lvalue expression, can't occur out of the parser *)
  | LE_id of id (* identifier *)
  | LE_mem of id * exp list
  | LE_vector of lexp * exp (* vector element *)
  | LE_vector_range of lexp * exp * exp (* subvector *)
  | LE_vector_concat of lexp list
  | LE_field of lexp * id (* struct field *)

and lexp = LE_aux of lexp_aux * l

type defs = (* Definition sequence *)
  | Defs of (string * def list) list
