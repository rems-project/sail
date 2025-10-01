Require Extraction.

Set Extraction KeepSingleton.
Set Extraction Output Directory ".".

From Stdlib Require Import String.
From Stdlib Require Import ZArith.

Require Import Value_type.

Parameter loc : Set.

Definition l := loc.

Extract Inlined Constant loc => "Parse_ast.l".

Parameter ext_doc_comment : Set.

Extract Inlined Constant ext_doc_comment => "Parse_ast.doc_comment".

Parameter ext_attribute_data : Set.

Extract Inlined Constant ext_attribute_data => "Parse_ast.Attribute_data.attribute_data".

Definition attribute_data := ext_attribute_data.

Inductive visibility : Set :=
| Public : visibility
| Private : loc -> visibility.

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
  Record record {a : Set} : Set := Build {
    doc_comment : option ext_doc_comment;
    attrs : list (loc * (string * option attribute_data));
    visibility : visibility;
    loc : loc;
    env : a;
  }.
  Arguments record : clear implicits.
  Definition with_doc_comment {t_a} doc_comment (r : record t_a) :=
    Build t_a doc_comment r.(attrs) r.(visibility) r.(loc) r.(env).
  Definition with_attrs {t_a} attrs (r : record t_a) :=
    Build t_a r.(doc_comment) attrs r.(visibility) r.(loc) r.(env).
  Definition with_visibility {t_a} visibility (r : record t_a) :=
    Build t_a r.(doc_comment) r.(attrs) visibility r.(loc) r.(env).
  Definition with_loc {t_a} loc (r : record t_a) :=
    Build t_a r.(doc_comment) r.(attrs) r.(visibility) loc r.(env).
  Definition with_env {t_a} env (r : record t_a) :=
    Build t_a r.(doc_comment) r.(attrs) r.(visibility) r.(loc) env.
End def_annot.

Inductive non_empty (a : Set) : Set :=
| Non_empty : a -> list a -> non_empty a.

Arguments Non_empty {_}.

Definition def_annot := def_annot.record.

Definition clause_annot (a : Set) : Set := def_annot unit * a.

Definition annot (a : Set) : Set := loc * a.

Inductive loop : Set :=
| While : loop
| Until : loop.

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

Inductive kind_aux : Set :=
| K_type : kind_aux
| K_int : kind_aux
| K_bool : kind_aux.

Inductive kid_aux : Set :=
| Var : string -> kid_aux.

Inductive kind : Set :=
| K_aux : kind_aux -> loc -> kind.

Inductive kid : Set :=
| Kid_aux : kid_aux -> loc -> kid.

Inductive kinded_id_aux : Set :=
| KOpt_kind : kind -> kid -> kinded_id_aux.

Inductive id_aux : Set :=
| And_bool : id_aux
| Or_bool : id_aux
| Id : string -> id_aux
| Operator : string -> id_aux.

Inductive kinded_id : Set :=
| KOpt_aux : kinded_id_aux -> loc -> kinded_id.

Inductive id : Set :=
| Id_aux : id_aux -> loc -> id.

Inductive lit_aux : Set :=
| L_unit : lit_aux
| L_true : lit_aux
| L_false : lit_aux
| L_num : Z -> lit_aux
| L_hex : list (non_empty hex_digit) -> lit_aux
| L_bin : list (non_empty bin_digit) -> lit_aux
| L_string : string -> lit_aux
| L_undef : lit_aux
| L_real : string -> lit_aux.

Inductive nexp_aux : Set :=
| Nexp_id : id -> nexp_aux
| Nexp_var : kid -> nexp_aux
| Nexp_constant : Z -> nexp_aux
| Nexp_app : id -> list nexp -> nexp_aux
| Nexp_if : n_constraint -> nexp -> nexp -> nexp_aux
| Nexp_times : nexp -> nexp -> nexp_aux
| Nexp_sum : nexp -> nexp -> nexp_aux
| Nexp_minus : nexp -> nexp -> nexp_aux
| Nexp_exp : nexp -> nexp_aux
| Nexp_neg : nexp -> nexp_aux

with nexp : Set :=
| Nexp_aux : nexp_aux -> loc -> nexp

with typ_aux : Set :=
| Typ_internal_unknown : typ_aux
| Typ_id : id -> typ_aux
| Typ_var : kid -> typ_aux
| Typ_fn : list typ -> typ -> typ_aux
| Typ_bidir : typ -> typ -> typ_aux
| Typ_tuple : list typ -> typ_aux
| Typ_app : id -> list typ_arg -> typ_aux
| Typ_exist : list kinded_id -> n_constraint -> typ -> typ_aux

with typ : Set :=
| Typ_aux : typ_aux -> loc -> typ

with typ_arg_aux : Set :=
| A_nexp : nexp -> typ_arg_aux
| A_typ : typ -> typ_arg_aux
| A_bool : n_constraint -> typ_arg_aux

with typ_arg : Set :=
| A_aux : typ_arg_aux -> loc -> typ_arg

with n_constraint_aux : Set :=
| NC_equal : typ_arg -> typ_arg -> n_constraint_aux
| NC_not_equal : typ_arg -> typ_arg -> n_constraint_aux
| NC_ge : nexp -> nexp -> n_constraint_aux
| NC_gt : nexp -> nexp -> n_constraint_aux
| NC_le : nexp -> nexp -> n_constraint_aux
| NC_lt : nexp -> nexp -> n_constraint_aux
| NC_set : nexp -> list Z -> n_constraint_aux
| NC_and : n_constraint -> n_constraint -> n_constraint_aux
| NC_or : n_constraint -> n_constraint -> n_constraint_aux
| NC_app : id -> list typ_arg -> n_constraint_aux
| NC_id : id -> n_constraint_aux
| NC_var : kid -> n_constraint_aux
| NC_true : n_constraint_aux
| NC_false : n_constraint_aux

with n_constraint : Set :=
| NC_aux : n_constraint_aux -> loc -> n_constraint.

Inductive order_aux : Set :=
| Ord_inc : order_aux
| Ord_dec : order_aux.

Inductive struct_name : Set :=
| SN_id : id -> struct_name
| SN_anon : struct_name.

Inductive lit : Set :=
| L_aux : lit_aux -> loc -> lit.

Inductive field_pat_wildcard : Set :=
| FP_wild : loc -> field_pat_wildcard
| FP_no_wild : field_pat_wildcard.

Inductive typ_pat_aux : Set :=
| TP_wild : typ_pat_aux
| TP_var : kid -> typ_pat_aux
| TP_app : id -> list typ_pat -> typ_pat_aux

with typ_pat : Set :=
| TP_aux : typ_pat_aux -> loc -> typ_pat.

Inductive quant_item_aux : Set :=
| QI_id : kinded_id -> quant_item_aux
| QI_constraint : n_constraint -> quant_item_aux.

Inductive order : Set :=
| Ord_aux : order_aux -> loc -> order.

Inductive pat_aux (a : Set) : Set :=
| P_lit : lit -> pat_aux a
| P_wild : pat_aux a
| P_or : pat a -> pat a -> pat_aux a
| P_not : pat a -> pat_aux a
| P_as : pat a -> id -> pat_aux a
| P_typ : typ -> pat a -> pat_aux a
| P_id : id -> pat_aux a
| P_var : pat a -> typ_pat -> pat_aux a
| P_app : id -> list (pat a) -> pat_aux a
| P_vector : list (pat a) -> pat_aux a
| P_vector_concat : list (pat a) -> pat_aux a
| P_vector_subrange : id -> Z -> Z -> pat_aux a
| P_tuple : list (pat a) -> pat_aux a
| P_list : list (pat a) -> pat_aux a
| P_cons : pat a -> pat a -> pat_aux a
| P_string_append : list (pat a) -> pat_aux a
| P_struct : struct_name -> list (id * pat a) -> field_pat_wildcard -> pat_aux a

with pat (a : Set) : Set :=
| P_aux : pat_aux a -> annot a -> pat a.

Arguments P_aux {_}.

Arguments P_lit {_}.
Arguments P_wild {_}.
Arguments P_or {_}.
Arguments P_not {_}.
Arguments P_as {_}.
Arguments P_typ {_}.
Arguments P_id {_}.
Arguments P_var {_}.
Arguments P_app {_}.
Arguments P_vector {_}.
Arguments P_vector_concat {_}.
Arguments P_vector_subrange {_}.
Arguments P_tuple {_}.
Arguments P_list {_}.
Arguments P_cons {_}.
Arguments P_string_append {_}.
Arguments P_struct {_}.

Inductive quant_item : Set :=
| QI_aux : quant_item_aux -> loc -> quant_item.

Inductive mpat_aux (a : Set) : Set :=
| MP_lit : lit -> mpat_aux a
| MP_id : id -> mpat_aux a
| MP_app : id -> list (mpat a) -> mpat_aux a
| MP_vector : list (mpat a) -> mpat_aux a
| MP_vector_concat : list (mpat a) -> mpat_aux a
| MP_vector_subrange : id -> Z -> Z -> mpat_aux a
| MP_tuple : list (mpat a) -> mpat_aux a
| MP_list : list (mpat a) -> mpat_aux a
| MP_cons : mpat a -> mpat a -> mpat_aux a
| MP_string_append : list (mpat a) -> mpat_aux a
| MP_typ : mpat a -> typ -> mpat_aux a
| MP_as : mpat a -> id -> mpat_aux a
| MP_struct : struct_name -> list (id * mpat a) -> mpat_aux a

with mpat (a : Set) : Set :=
| MP_aux : mpat_aux a -> annot a -> mpat a.

Inductive internal_loop_measure_aux (a : Set) : Set :=
| Measure_none : internal_loop_measure_aux a
| Measure_some : exp a -> internal_loop_measure_aux a

with internal_loop_measure (a : Set) : Set :=
| Measure_aux : internal_loop_measure_aux a -> loc -> internal_loop_measure a

with exp_aux (a : Set) : Set :=
| E_block : list (exp a) -> exp_aux a
| E_id : id -> exp_aux a
| E_lit : lit -> exp_aux a
| E_typ : typ -> exp a -> exp_aux a
| E_app : id -> list (exp a) -> exp_aux a
| E_tuple : list (exp a) -> exp_aux a
| E_if : exp a -> exp a -> exp a -> exp_aux a
| E_loop : loop -> internal_loop_measure a -> exp a -> exp a -> exp_aux a
| E_for : id -> exp a -> exp a -> exp a -> order -> exp a -> exp_aux a
| E_vector : list (exp a) -> exp_aux a
| E_vector_append : exp a -> exp a -> exp_aux a
| E_list : list (exp a) -> exp_aux a
| E_cons : exp a -> exp a -> exp_aux a
| E_struct : struct_name -> list (fexp a) -> exp_aux a
| E_struct_update : exp a -> list (fexp a) -> exp_aux a
| E_field : exp a -> id -> exp_aux a
| E_match : exp a -> list (pexp a) -> exp_aux a
| E_let : letbind a -> exp a -> exp_aux a
| E_assign : lexp a -> exp a -> exp_aux a
| E_sizeof : nexp -> exp_aux a
| E_return : exp a -> exp_aux a
| E_exit : exp a -> exp_aux a
| E_config : list string -> exp_aux a
| E_ref : id -> exp_aux a
| E_throw : exp a -> exp_aux a
| E_try : exp a -> list (pexp a) -> exp_aux a
| E_assert : exp a -> exp a -> exp_aux a
| E_var : lexp a -> exp a -> exp a -> exp_aux a
| E_internal_plet : pat a -> exp a -> exp a -> exp_aux a
| E_internal_return : exp a -> exp_aux a
| E_internal_value : value -> exp_aux a
| E_internal_assume : n_constraint -> exp a -> exp_aux a
| E_constraint : n_constraint -> exp_aux a

with exp (a : Set) : Set :=
| E_aux : exp_aux a -> annot a -> exp a

with lexp_aux (a : Set) : Set :=
| LE_id : id -> lexp_aux a
| LE_deref : exp a -> lexp_aux a
| LE_app : id -> list (exp a) -> lexp_aux a
| LE_typ : typ -> id -> lexp_aux a
| LE_tuple : list (lexp a) -> lexp_aux a
| LE_vector_concat : list (lexp a) -> lexp_aux a
| LE_vector : lexp a -> exp a -> lexp_aux a
| LE_vector_range : lexp a -> exp a -> exp a -> lexp_aux a
| LE_field : lexp a -> id -> lexp_aux a

with lexp (a : Set) : Set :=
| LE_aux : lexp_aux a -> annot a -> lexp a

with fexp_aux (a : Set) : Set :=
| FE_fexp : id -> exp a -> fexp_aux a

with fexp (a : Set) : Set :=
| FE_aux : fexp_aux a -> annot a -> fexp a

with pexp_aux (a : Set) : Set :=
| Pat_exp : pat a -> exp a -> pexp_aux a
| Pat_when : pat a -> exp a -> exp a -> pexp_aux a

with pexp (a : Set) : Set :=
| Pat_aux : pexp_aux a -> annot a -> pexp a

with letbind_aux (a : Set) : Set :=
| LB_val : pat a -> exp a -> letbind_aux a

with letbind (a : Set) : Set :=
| LB_aux : letbind_aux a -> annot a -> letbind a.

Arguments E_block {_}.
Arguments E_id {_}.
Arguments E_lit {_}.
Arguments E_typ {_}.
Arguments E_app {_}.
Arguments E_tuple {_}.
Arguments E_if {_}.
Arguments E_loop {_}.
Arguments E_for {_}.
Arguments E_vector {_}.
Arguments E_vector_append {_}.
Arguments E_list {_}.
Arguments E_cons {_}.
Arguments E_struct {_}.
Arguments E_struct_update {_}.
Arguments E_field {_}.
Arguments E_match {_}.
Arguments E_let {_}.
Arguments E_assign {_}.
Arguments E_sizeof {_}.
Arguments E_return {_}.
Arguments E_exit {_}.
Arguments E_config {_}.
Arguments E_ref {_}.
Arguments E_throw {_}.
Arguments E_try {_}.
Arguments E_assert {_}.
Arguments E_var {_}.
Arguments E_internal_plet {_}.
Arguments E_internal_return {_}.
Arguments E_internal_value {_}.
Arguments E_internal_assume {_}.
Arguments E_constraint {_}.
Arguments E_aux {_}.

Arguments FE_aux {_}.
Arguments FE_fexp {_}.

Arguments Pat_aux {_}.
Arguments Pat_exp {_}.
Arguments Pat_when {_}.

Arguments LB_aux {_}.
Arguments LB_val {_}.

Arguments LE_aux {_}.
Arguments LE_id {_}.
Arguments LE_deref {_}.
Arguments LE_app {_}.
Arguments LE_typ {_}.
Arguments LE_tuple {_}.
Arguments LE_vector_concat {_}.
Arguments LE_vector {_}.
Arguments LE_vector_range {_}.
Arguments LE_field {_}.

Inductive typquant_aux : Set :=
| TypQ_tq : list quant_item -> typquant_aux
| TypQ_no_forall : typquant_aux.

Inductive mpexp_aux (a : Set) : Set :=
| MPat_pat : mpat a -> mpexp_aux a
| MPat_when : mpat a -> exp a -> mpexp_aux a.

Inductive typquant : Set :=
| TypQ_aux : typquant_aux -> loc -> typquant.

Inductive mpexp (a : Set) : Set :=
| MPat_aux : mpexp_aux a -> annot a -> mpexp a.

Definition pexp_funcl (a : Set) : Set := pexp a.

Inductive typschm_aux : Set :=
| TypSchm_ts : typquant -> typ -> typschm_aux.

Inductive mapcl_aux (a : Set) : Set :=
| MCL_bidir : mpexp a -> mpexp a -> mapcl_aux a
| MCL_forwards : pexp a -> mapcl_aux a
| MCL_backwards : pexp a -> mapcl_aux a.

Inductive funcl_aux (a : Set) : Set :=
| FCL_funcl : id -> pexp_funcl a -> funcl_aux a.

Inductive tannot_opt_aux : Set :=
| Typ_annot_opt_none : tannot_opt_aux
| Typ_annot_opt_some : typquant -> typ -> tannot_opt_aux.

Inductive type_union_aux : Set :=
| Tu_ty_id : typ -> id -> type_union_aux.

Inductive rec_opt_aux (a : Set) : Set :=
| Rec_nonrec : rec_opt_aux a
| Rec_rec : rec_opt_aux a
| Rec_measure : pat a -> exp a -> rec_opt_aux a.

Inductive typschm : Set :=
| TypSchm_aux : typschm_aux -> loc -> typschm.

Inductive mapcl (a : Set) : Set :=
| MCL_aux : mapcl_aux a -> clause_annot a -> mapcl a.

Inductive funcl (a : Set) : Set :=
| FCL_aux : funcl_aux a -> clause_annot a -> funcl a.

Inductive tannot_opt : Set :=
| Typ_annot_opt_aux : tannot_opt_aux -> loc -> tannot_opt.

Inductive type_union : Set :=
| Tu_aux : type_union_aux -> def_annot unit -> type_union.

Inductive rec_opt (a : Set) : Set :=
| Rec_aux : rec_opt_aux a -> loc -> rec_opt a.

Inductive index_range_aux : Set :=
| BF_single : nexp -> index_range_aux
| BF_range : nexp -> nexp -> index_range_aux
| BF_concat : index_range -> index_range -> index_range_aux

with index_range : Set :=
| BF_aux : index_range_aux -> loc -> index_range.

Inductive opt_abstract_config : Set :=
| TDC_key : list string -> opt_abstract_config
| TDC_none : opt_abstract_config.

Inductive outcome_spec_aux : Set :=
| OV_outcome : id -> typschm -> typquant -> outcome_spec_aux.

Inductive instantiation_spec_aux (a : Set) : Set :=
| IN_id : id -> instantiation_spec_aux a.

Inductive val_spec_aux : Set :=
| VS_val_spec : typschm -> id -> option extern -> val_spec_aux.

Inductive default_spec_aux : Set :=
| DT_order : order -> default_spec_aux.

Inductive scattered_def_aux (a : Set) : Set :=
| SD_function : id -> tannot_opt -> scattered_def_aux a
| SD_funcl : funcl a -> scattered_def_aux a
| SD_variant : id -> typquant -> scattered_def_aux a
| SD_unioncl : id -> type_union -> scattered_def_aux a
| SD_internal_unioncl_record :
  id -> id -> typquant -> list (id * typ * def_annot unit) -> scattered_def_aux a
| SD_mapping : id -> tannot_opt -> scattered_def_aux a
| SD_mapcl : id -> mapcl a -> scattered_def_aux a
| SD_enum : id -> scattered_def_aux a
| SD_enumcl : id -> id -> scattered_def_aux a
| SD_end : id -> scattered_def_aux a.

Inductive dec_spec_aux (a : Set) : Set :=
| DEC_reg : typ -> id -> option (exp a) -> dec_spec_aux a.

Inductive subst_aux : Set :=
| IS_typ : kid -> typ_arg -> subst_aux
| IS_id : id -> id -> subst_aux.

Inductive mapdef_aux (a : Set) : Set :=
| MD_mapping : id -> tannot_opt -> list (mapcl a) -> mapdef_aux a.

Inductive fundef_aux (a : Set) : Set :=
| FD_function : rec_opt a -> tannot_opt -> list (funcl a) -> fundef_aux a.

Inductive type_def_aux : Set :=
| TD_abbrev : id -> typquant -> typ_arg -> type_def_aux
| TD_record : id -> typquant -> list (id * typ * def_annot unit) -> bool -> type_def_aux
| TD_variant : id -> typquant -> list type_union -> bool -> type_def_aux
| TD_enum : id -> list (id * def_annot unit) -> bool -> type_def_aux
| TD_abstract : id -> kind -> opt_abstract_config -> type_def_aux
| TD_bitfield : id -> typ -> list (id * index_range * def_annot unit) -> type_def_aux.

Inductive outcome_spec : Set :=
| OV_aux : outcome_spec_aux -> loc -> outcome_spec.

Inductive instantiation_spec (a : Set) : Set :=
| IN_aux : instantiation_spec_aux a -> annot a -> instantiation_spec a.

Inductive val_spec (a : Set) : Set :=
| VS_aux : val_spec_aux -> annot a -> val_spec a.

Inductive default_spec : Set :=
| DT_aux : default_spec_aux -> loc -> default_spec.

Inductive scattered_def (a : Set) : Set :=
| SD_aux : scattered_def_aux a -> annot a -> scattered_def a.

Inductive dec_spec (a : Set) : Set :=
| DEC_aux : dec_spec_aux a -> annot a -> dec_spec a.

Inductive prec : Set :=
| Infix : prec
| InfixL : prec
| InfixR : prec.

Definition loop_measure : Set := loop * exp unit.

Inductive pragma : Set :=
| Pragma_line : string -> loc -> pragma
| Pragma_structured : list (string * attribute_data) -> pragma.

Inductive subst : Set :=
| IS_aux : subst_aux -> loc -> subst.

Inductive mapdef (a : Set) : Set :=
| MD_aux : mapdef_aux a -> annot a -> mapdef a.

Inductive fundef (a : Set) : Set :=
| FD_aux : fundef_aux a -> annot a -> fundef a.

Inductive type_def (a : Set) : Set :=
| TD_aux : type_def_aux -> annot a -> type_def a.

Inductive impldef_aux (a : Set) : Set :=
| Impl_impl : funcl a -> impldef_aux a.

Inductive opt_default_aux (a : Set) : Set :=
| Def_val_empty : opt_default_aux a
| Def_val_dec : exp a -> opt_default_aux a.

Inductive def_aux (a b : Set) : Set :=
| DEF_type : type_def a -> def_aux a b
| DEF_constraint : n_constraint -> def_aux a b
| DEF_fundef : fundef a -> def_aux a b
| DEF_mapdef : mapdef a -> def_aux a b
| DEF_impl : funcl a -> def_aux a b
| DEF_let : letbind a -> def_aux a b
| DEF_val : val_spec a -> def_aux a b
| DEF_outcome : outcome_spec -> list (def a b) -> def_aux a b
| DEF_instantiation : instantiation_spec a -> list subst -> def_aux a b
| DEF_fixity : prec -> Z -> id -> def_aux a b
| DEF_overload : id -> list id -> def_aux a b
| DEF_default : default_spec -> def_aux a b
| DEF_scattered : scattered_def a -> def_aux a b
| DEF_measure : id -> pat a -> exp a -> def_aux a b
| DEF_loop_measures : id -> list loop_measure -> def_aux a b
| DEF_register : dec_spec a -> def_aux a b
| DEF_internal_mutrec : list (fundef a) -> def_aux a b
| DEF_pragma : string -> pragma -> def_aux a b

with def (a b : Set) : Set :=
| DEF_aux : def_aux a b -> def_annot b -> def a b.

Inductive impldef (a : Set) : Set :=
| Impl_aux : impldef_aux a -> l -> impldef a.

Inductive opt_default (a : Set) : Set :=
| Def_val_aux : opt_default_aux a -> annot a -> opt_default a.
