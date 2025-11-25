open Value_type

type l = Parse_ast.l

type attribute_data = Parse_ast.Attribute_data.attribute_data

type visibility =
| Public
| Private of Parse_ast.l

module Coq_extern =
 struct
  type record = { pure : bool; bindings : (string * string) list }
 end

type extern = Coq_extern.record

module Coq_def_annot =
 struct
  type 'a record = { doc_comment : Parse_ast.doc_comment option;
                     attrs : (Parse_ast.l * (string * attribute_data option))
                             list;
                     visibility : visibility; loc : Parse_ast.l; env : 
                     'a }
 end

type 'a non_empty =
| Non_empty of 'a * 'a list

type 'a def_annot = 'a Coq_def_annot.record

type 'a clause_annot = unit def_annot * 'a

type 'a annot = Parse_ast.l * 'a

type loop =
| While
| Until

type hex_digit =
| Hex_0
| Hex_1
| Hex_2
| Hex_3
| Hex_4
| Hex_5
| Hex_6
| Hex_7
| Hex_8
| Hex_9
| Hex_A
| Hex_B
| Hex_C
| Hex_D
| Hex_E
| Hex_F

type bin_digit =
| Bin_0
| Bin_1

type kind_aux =
| K_type
| K_int
| K_bool

type kid_aux =
| Var of string

type kind =
| K_aux of kind_aux * Parse_ast.l

type kid =
| Kid_aux of kid_aux * Parse_ast.l

type kinded_id_aux =
| KOpt_kind of kind * kid

type id_aux =
| And_bool
| Or_bool
| Id of string
| Operator of string

type kinded_id =
| KOpt_aux of kinded_id_aux * Parse_ast.l

type id =
| Id_aux of id_aux * Parse_ast.l

type lit_aux =
| L_unit
| L_true
| L_false
| L_num of Big_int_Z.big_int
| L_hex of hex_digit non_empty list
| L_bin of bin_digit non_empty list
| L_string of string
| L_undef
| L_real of string

type nexp_aux =
| Nexp_id of id
| Nexp_var of kid
| Nexp_constant of Big_int_Z.big_int
| Nexp_app of id * nexp list
| Nexp_if of n_constraint * nexp * nexp
| Nexp_times of nexp * nexp
| Nexp_sum of nexp * nexp
| Nexp_minus of nexp * nexp
| Nexp_exp of nexp
| Nexp_neg of nexp
and nexp =
| Nexp_aux of nexp_aux * Parse_ast.l
and typ_aux =
| Typ_internal_unknown
| Typ_id of id
| Typ_var of kid
| Typ_fn of typ list * typ
| Typ_bidir of typ * typ
| Typ_tuple of typ list
| Typ_app of id * typ_arg list
| Typ_exist of kinded_id list * n_constraint * typ
and typ =
| Typ_aux of typ_aux * Parse_ast.l
and typ_arg_aux =
| A_nexp of nexp
| A_typ of typ
| A_bool of n_constraint
and typ_arg =
| A_aux of typ_arg_aux * Parse_ast.l
and n_constraint_aux =
| NC_equal of typ_arg * typ_arg
| NC_not_equal of typ_arg * typ_arg
| NC_ge of nexp * nexp
| NC_gt of nexp * nexp
| NC_le of nexp * nexp
| NC_lt of nexp * nexp
| NC_set of nexp * Big_int_Z.big_int list
| NC_and of n_constraint * n_constraint
| NC_or of n_constraint * n_constraint
| NC_app of id * typ_arg list
| NC_id of id
| NC_var of kid
| NC_true
| NC_false
and n_constraint =
| NC_aux of n_constraint_aux * Parse_ast.l

type order_aux =
| Ord_inc
| Ord_dec

type struct_name =
| SN_id of id
| SN_anon

type lit =
| L_aux of lit_aux * Parse_ast.l

type field_pat_wildcard =
| FP_wild of Parse_ast.l
| FP_no_wild

type typ_pat_aux =
| TP_wild
| TP_var of kid
| TP_app of id * typ_pat list
and typ_pat =
| TP_aux of typ_pat_aux * Parse_ast.l

type quant_item_aux =
| QI_id of kinded_id
| QI_constraint of n_constraint

type order =
| Ord_aux of order_aux * Parse_ast.l

type 'a pat_aux =
| P_lit of lit
| P_wild
| P_or of 'a pat * 'a pat
| P_not of 'a pat
| P_as of 'a pat * id
| P_typ of typ * 'a pat
| P_id of id
| P_var of 'a pat * typ_pat
| P_app of id * 'a pat list
| P_vector of 'a pat list
| P_vector_concat of 'a pat list
| P_vector_subrange of id * Big_int_Z.big_int * Big_int_Z.big_int
| P_tuple of 'a pat list
| P_list of 'a pat list
| P_cons of 'a pat * 'a pat
| P_string_append of 'a pat list
| P_struct of struct_name * (id * 'a pat) list * field_pat_wildcard
and 'a pat =
| P_aux of 'a pat_aux * 'a annot

type quant_item =
| QI_aux of quant_item_aux * Parse_ast.l

type 'a mpat_aux =
| MP_lit of lit
| MP_id of id
| MP_app of id * 'a mpat list
| MP_vector of 'a mpat list
| MP_vector_concat of 'a mpat list
| MP_vector_subrange of id * Big_int_Z.big_int * Big_int_Z.big_int
| MP_tuple of 'a mpat list
| MP_list of 'a mpat list
| MP_cons of 'a mpat * 'a mpat
| MP_string_append of 'a mpat list
| MP_typ of 'a mpat * typ
| MP_as of 'a mpat * id
| MP_struct of struct_name * (id * 'a mpat) list
and 'a mpat =
| MP_aux of 'a mpat_aux * 'a annot

type 'a internal_loop_measure_aux =
| Measure_none
| Measure_some of 'a exp
and 'a internal_loop_measure =
| Measure_aux of 'a internal_loop_measure_aux * Parse_ast.l
and 'a exp_aux =
| E_block of 'a exp list
| E_id of id
| E_lit of lit
| E_typ of typ * 'a exp
| E_app of id * 'a exp list
| E_tuple of 'a exp list
| E_if of 'a exp * 'a exp * 'a exp
| E_loop of loop * 'a internal_loop_measure * 'a exp * 'a exp
| E_for of id * 'a exp * 'a exp * 'a exp * order * 'a exp
| E_vector of 'a exp list
| E_vector_append of 'a exp * 'a exp
| E_list of 'a exp list
| E_cons of 'a exp * 'a exp
| E_struct of struct_name * 'a fexp list
| E_struct_update of 'a exp * 'a fexp list
| E_field of 'a exp * id
| E_match of 'a exp * 'a pexp list
| E_let of 'a letbind * 'a exp
| E_assign of 'a lexp * 'a exp
| E_sizeof of nexp
| E_return of 'a exp
| E_exit of 'a exp
| E_config of string list
| E_ref of id
| E_throw of 'a exp
| E_try of 'a exp * 'a pexp list
| E_assert of 'a exp * 'a exp
| E_var of 'a lexp * 'a exp * 'a exp
| E_internal_plet of 'a pat * 'a exp * 'a exp
| E_internal_return of 'a exp
| E_internal_value of value
| E_internal_assume of n_constraint * 'a exp
| E_constraint of n_constraint
and 'a exp =
| E_aux of 'a exp_aux * 'a annot
and 'a lexp_aux =
| LE_id of id
| LE_deref of 'a exp
| LE_app of id * 'a exp list
| LE_typ of typ * id
| LE_tuple of 'a lexp list
| LE_vector_concat of 'a lexp list
| LE_vector of 'a lexp * 'a exp
| LE_vector_range of 'a lexp * 'a exp * 'a exp
| LE_field of 'a lexp * id
and 'a lexp =
| LE_aux of 'a lexp_aux * 'a annot
and 'a fexp_aux =
| FE_fexp of id * 'a exp
and 'a fexp =
| FE_aux of 'a fexp_aux * 'a annot
and 'a pexp_aux =
| Pat_exp of 'a pat * 'a exp
| Pat_when of 'a pat * 'a exp * 'a exp
and 'a pexp =
| Pat_aux of 'a pexp_aux * 'a annot
and 'a letbind_aux =
| LB_val of 'a pat * 'a exp
and 'a letbind =
| LB_aux of 'a letbind_aux * 'a annot

type typquant_aux =
| TypQ_tq of quant_item list
| TypQ_no_forall

type 'a mpexp_aux =
| MPat_pat of 'a mpat
| MPat_when of 'a mpat * 'a exp

type typquant =
| TypQ_aux of typquant_aux * Parse_ast.l

type 'a mpexp =
| MPat_aux of 'a mpexp_aux * 'a annot

type 'a pexp_funcl = 'a pexp

type typschm_aux =
| TypSchm_ts of typquant * typ

type 'a mapcl_aux =
| MCL_bidir of 'a mpexp * 'a mpexp
| MCL_forwards of 'a pexp
| MCL_backwards of 'a pexp

type 'a funcl_aux =
| FCL_funcl of id * 'a pexp_funcl

type tannot_opt_aux =
| Typ_annot_opt_none
| Typ_annot_opt_some of typquant * typ

type type_union_aux =
| Tu_ty_id of typ * id

type 'a rec_opt_aux =
| Rec_nonrec
| Rec_rec
| Rec_measure of 'a pat * 'a exp

type typschm =
| TypSchm_aux of typschm_aux * Parse_ast.l

type 'a mapcl =
| MCL_aux of 'a mapcl_aux * 'a clause_annot

type 'a funcl =
| FCL_aux of 'a funcl_aux * 'a clause_annot

type tannot_opt =
| Typ_annot_opt_aux of tannot_opt_aux * Parse_ast.l

type type_union =
| Tu_aux of type_union_aux * unit def_annot

type 'a rec_opt =
| Rec_aux of 'a rec_opt_aux * Parse_ast.l

type index_range_aux =
| BF_single of nexp
| BF_range of nexp * nexp
| BF_concat of index_range * index_range
and index_range =
| BF_aux of index_range_aux * Parse_ast.l

type opt_abstract_config =
| TDC_key of string list
| TDC_none

type outcome_spec_aux =
| OV_outcome of id * typschm * typquant

type 'a instantiation_spec_aux =
| IN_id of id

type val_spec_aux =
| VS_val_spec of typschm * id * extern option

type default_spec_aux =
| DT_order of order

type 'a scattered_def_aux =
| SD_function of id * tannot_opt
| SD_funcl of 'a funcl
| SD_variant of id * typquant
| SD_unioncl of id * type_union
| SD_internal_unioncl_record of id * id * typquant
   * ((id * typ) * unit def_annot) list
| SD_mapping of id * tannot_opt
| SD_mapcl of id * 'a mapcl
| SD_enum of id
| SD_enumcl of id * id
| SD_end of id

type 'a dec_spec_aux =
| DEC_reg of typ * id * 'a exp option

type subst_aux =
| IS_typ of kid * typ_arg
| IS_id of id * id

type 'a mapdef_aux =
| MD_mapping of id * tannot_opt * 'a mapcl list

type 'a fundef_aux =
| FD_function of 'a rec_opt * tannot_opt * 'a funcl list

type type_def_aux =
| TD_abbrev of id * typquant * typ_arg
| TD_record of id * typquant * ((id * typ) * unit def_annot) list * bool
| TD_variant of id * typquant * type_union list * bool
| TD_enum of id * (id * unit def_annot) list * bool
| TD_abstract of id * kind * opt_abstract_config
| TD_bitfield of id * typ * ((id * index_range) * unit def_annot) list

type outcome_spec =
| OV_aux of outcome_spec_aux * Parse_ast.l

type 'a instantiation_spec =
| IN_aux of 'a instantiation_spec_aux * 'a annot

type 'a val_spec =
| VS_aux of val_spec_aux * 'a annot

type default_spec =
| DT_aux of default_spec_aux * Parse_ast.l

type 'a scattered_def =
| SD_aux of 'a scattered_def_aux * 'a annot

type 'a dec_spec =
| DEC_aux of 'a dec_spec_aux * 'a annot

type prec =
| Infix
| InfixL
| InfixR

type loop_measure = loop * unit exp

type pragma =
| Pragma_line of string * Parse_ast.l
| Pragma_structured of (string * attribute_data) list

type subst =
| IS_aux of subst_aux * Parse_ast.l

type 'a mapdef =
| MD_aux of 'a mapdef_aux * 'a annot

type 'a fundef =
| FD_aux of 'a fundef_aux * 'a annot

type 'a type_def =
| TD_aux of type_def_aux * 'a annot

type 'a impldef_aux =
| Impl_impl of 'a funcl

type 'a opt_default_aux =
| Def_val_empty
| Def_val_dec of 'a exp

type ('a, 'b) def_aux =
| DEF_type of 'a type_def
| DEF_constraint of n_constraint
| DEF_fundef of 'a fundef
| DEF_mapdef of 'a mapdef
| DEF_impl of 'a funcl
| DEF_let of 'a letbind
| DEF_val of 'a val_spec
| DEF_outcome of outcome_spec * ('a, 'b) def list
| DEF_instantiation of 'a instantiation_spec * subst list
| DEF_fixity of prec * Big_int_Z.big_int * id
| DEF_overload of id * id list
| DEF_default of default_spec
| DEF_scattered of 'a scattered_def
| DEF_measure of id * 'a pat * 'a exp
| DEF_loop_measures of id * loop_measure list
| DEF_register of 'a dec_spec
| DEF_internal_mutrec of 'a fundef list
| DEF_pragma of string * pragma
and ('a, 'b) def =
| DEF_aux of ('a, 'b) def_aux * 'b def_annot

type 'a impldef =
| Impl_aux of 'a impldef_aux * l

type 'a opt_default =
| Def_val_aux of 'a opt_default_aux * 'a annot
