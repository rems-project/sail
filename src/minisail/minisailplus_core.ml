open Minisailplus_ast
module Satis : sig
  val z3eq : Z3.z3_expr -> Z3.z3_expr -> Z3.z3_bool_expr
  val convert_x : SyntaxVCT.xp -> string
  val convert_l : SyntaxVCT.lit -> Z3.z3_expr
  val convert_v : SyntaxVCT.vp -> Z3.z3_expr
  val convert_ce : SyntaxVCT.cep -> Z3.z3_expr
  val z3and : Z3.z3_bool_expr list -> Z3.z3_bool_expr
  val convert_c : SyntaxVCT.cp -> Z3.z3_bool_expr
  val type_app : SyntaxVCT.bp -> SyntaxVCT.bp -> (string * SyntaxVCT.bp) list
  val type_app_lists :
    SyntaxVCT.bp list -> SyntaxVCT.bp list -> (string * SyntaxVCT.bp) list
  val type_app_tlists :
    (string * SyntaxVCT.tau) list ->
      (string * SyntaxVCT.tau) list -> (string * SyntaxVCT.bp) list
  val type_app_t :
    unit ContextsPiDelta.theta_ext ->
      ('a, unit) Contexts.gamma_ext ->
        SyntaxVCT.bp -> (string * SyntaxVCT.bp) list
  val convert_b :
    unit ContextsPiDelta.theta_ext ->
      ('a, unit) Contexts.gamma_ext ->
        SyntaxVCT.vp -> SyntaxVCT.bp -> Z3.z3_type * Z3.z3_bool_expr
  val convert_blist :
    unit ContextsPiDelta.theta_ext ->
      ('a, unit) Contexts.gamma_ext ->
        SyntaxVCT.vp ->
          SyntaxVCT.bp list -> Z3.z3_type list * Z3.z3_bool_expr list
  val convert_xbc :
    unit ContextsPiDelta.theta_ext ->
      ('a, unit) Contexts.gamma_ext ->
        SyntaxVCT.xp ->
          SyntaxVCT.bp -> SyntaxVCT.cp -> Z3.z3_decl list * Z3.z3_bool_expr
  val subst_c_z : SyntaxVCT.xp -> SyntaxVCT.cp -> SyntaxVCT.cp
  val convert_g_aux :
    unit ContextsPiDelta.theta_ext ->
      ('a, unit) Contexts.gamma_ext ->
        (SyntaxVCT.xp * Contexts.g_entry) list ->
          Z3.z3_decl list * Z3.z3_bool_expr list
  val convert_g :
    unit ContextsPiDelta.theta_ext ->
      ('a, unit) Contexts.gamma_ext -> Z3.z3_decl list * Z3.z3_bool_expr list
  val convert_smt_problem_valid :
    unit ContextsPiDelta.theta_ext ->
      ('a, unit) Contexts.gamma_ext ->
        (SyntaxVCT.xp * Contexts.g_entry) list ->
          SyntaxVCT.cp -> Z3.z3_decl list * (Z3.z3_decl list * Z3.z3_bool_expr)
  val pp_z3_expr : Z3.z3_expr -> string
  val pp_z3_bool_expr : Z3.z3_bool_expr -> string
  val z3_vector_sort : string
  val pp_bv_concats : Arith.int -> string list
  val t_t_vars : SyntaxVCT.tau -> string list
  val b_t_vars : SyntaxVCT.bp -> string list
  val pp_sort_decl :
    unit ContextsPiDelta.theta_ext ->
      ('a, unit) Contexts.gamma_ext -> string list
  val bv_consts_v : SyntaxVCT.vp -> SyntaxVCT.lit list
  val bv_consts_ce : SyntaxVCT.cep -> SyntaxVCT.lit list
  val bv_consts_c : SyntaxVCT.cp -> SyntaxVCT.lit list
  val c_of_e : Contexts.g_entry -> SyntaxVCT.cp
  val bv_consts_aux :
    (SyntaxVCT.xp * Contexts.g_entry) list -> SyntaxVCT.lit list
  val pp_bitvec : SyntaxVCT.lit -> string list
  val pp_bv_consts :
    ('a, unit) Contexts.gamma_ext ->
      (SyntaxVCT.xp * Contexts.g_entry) list -> SyntaxVCT.cp -> string list
  val pp_z3_vector_funs : string
  val pp_z3_type : Z3.z3_type -> string
  val pp_z3_type_var : Z3.z3_type_var -> string
  val pp_z3_fields : (string * Z3.z3_type_var) list -> string
  val pp_z3_ty_constr : Z3.z3_constr -> string
  val pp_z3_decl : Z3.z3_decl -> string
  val z3_declare_tuple : Arith.int -> Z3.z3_decl
  val pp_tuples : Arith.int -> string list
  val pp_builtins : Arith.int -> string list
  val convert_t :
    unit ContextsPiDelta.theta_ext ->
      ('a, unit) Contexts.gamma_ext ->
        SyntaxVCT.vp -> SyntaxVCT.tau -> Z3.z3_type * Z3.z3_bool_expr
  val convert_typedef :
    unit ContextsPiDelta.theta_ext ->
      ('a, unit) Contexts.gamma_ext ->
        SyntaxVCT.xp * SyntaxVCT.tau -> Z3.z3_decl option
  val pp_typedef :
    unit ContextsPiDelta.theta_ext ->
      ('a, unit) Contexts.gamma_ext -> SyntaxVCT.xp * SyntaxVCT.tau -> string
  val max_tuples : Arith.int
  val pp_smt_problem_valid :
    unit ContextsPiDelta.theta_ext ->
      ('a, unit) Contexts.gamma_ext ->
        (SyntaxVCT.xp * Contexts.g_entry) list -> SyntaxVCT.cp -> string list
  val has_no_t_var_b : SyntaxVCT.bp -> bool
  val b_of_e : Contexts.g_entry -> SyntaxVCT.bp
  val has_no_t_var_g : ('a, unit) Contexts.gamma_ext -> bool
  val has_t_var :
    ('a, unit) Contexts.gamma_ext ->
      (SyntaxVCT.xp * Contexts.g_entry) list -> bool
  val valid :
    string ->
      Location.loc ->
        unit ContextsPiDelta.theta_ext ->
          ('a, unit) Contexts.gamma_ext ->
            (SyntaxVCT.xp * Contexts.g_entry) list -> SyntaxVCT.cp -> bool
end = struct

let rec z3eq
  e1 e2 = match e1, e2 with
    Z3.Z3E_true, Z3.Z3E_eq (e1, e2) -> Z3.Z3BE_eq (e1, e2)
    | Z3.Z3E_true, Z3.Z3E_leq (e1, e2) -> Z3.Z3BE_leq (e1, e2)
    | Z3.Z3E_num v, e2 -> Z3.Z3BE_eq (Z3.Z3E_num v, e2)
    | Z3.Z3E_var v, e2 -> Z3.Z3BE_eq (Z3.Z3E_var v, e2)
    | Z3.Z3E_false, e2 -> Z3.Z3BE_eq (Z3.Z3E_false, e2)
    | Z3.Z3E_unit, e2 -> Z3.Z3BE_eq (Z3.Z3E_unit, e2)
    | Z3.Z3E_bitone, e2 -> Z3.Z3BE_eq (Z3.Z3E_bitone, e2)
    | Z3.Z3E_bitzero, e2 -> Z3.Z3BE_eq (Z3.Z3E_bitzero, e2)
    | Z3.Z3E_len v, e2 -> Z3.Z3BE_eq (Z3.Z3E_len v, e2)
    | Z3.Z3E_leq (v, va), e2 -> Z3.Z3BE_eq (Z3.Z3E_leq (v, va), e2)
    | Z3.Z3E_geq (v, va), e2 -> Z3.Z3BE_eq (Z3.Z3E_geq (v, va), e2)
    | Z3.Z3E_plus (v, va), e2 -> Z3.Z3BE_eq (Z3.Z3E_plus (v, va), e2)
    | Z3.Z3E_times (v, va), e2 -> Z3.Z3BE_eq (Z3.Z3E_times (v, va), e2)
    | Z3.Z3E_div (v, va), e2 -> Z3.Z3BE_eq (Z3.Z3E_div (v, va), e2)
    | Z3.Z3E_mod (v, va), e2 -> Z3.Z3BE_eq (Z3.Z3E_mod (v, va), e2)
    | Z3.Z3E_minus (v, va), e2 -> Z3.Z3BE_eq (Z3.Z3E_minus (v, va), e2)
    | Z3.Z3E_eq (v, va), e2 -> Z3.Z3BE_eq (Z3.Z3E_eq (v, va), e2)
    | Z3.Z3E_not v, e2 -> Z3.Z3BE_eq (Z3.Z3E_not v, e2)
    | Z3.Z3E_and (v, va), e2 -> Z3.Z3BE_eq (Z3.Z3E_and (v, va), e2)
    | Z3.Z3E_or (v, va), e2 -> Z3.Z3BE_eq (Z3.Z3E_or (v, va), e2)
    | Z3.Z3E_neq (v, va), e2 -> Z3.Z3BE_eq (Z3.Z3E_neq (v, va), e2)
    | Z3.Z3E_bitvec v, e2 -> Z3.Z3BE_eq (Z3.Z3E_bitvec v, e2)
    | Z3.Z3E_constr (v, va), e2 -> Z3.Z3BE_eq (Z3.Z3E_constr (v, va), e2)
    | Z3.Z3E_concat v, e2 -> Z3.Z3BE_eq (Z3.Z3E_concat v, e2)
    | Z3.Z3E_proj (v, va), e2 -> Z3.Z3BE_eq (Z3.Z3E_proj (v, va), e2)
    | Z3.Z3E_string v, e2 -> Z3.Z3BE_eq (Z3.Z3E_string v, e2)
    | e1, Z3.Z3E_num v -> Z3.Z3BE_eq (e1, Z3.Z3E_num v)
    | e1, Z3.Z3E_var v -> Z3.Z3BE_eq (e1, Z3.Z3E_var v)
    | e1, Z3.Z3E_true -> Z3.Z3BE_eq (e1, Z3.Z3E_true)
    | e1, Z3.Z3E_false -> Z3.Z3BE_eq (e1, Z3.Z3E_false)
    | e1, Z3.Z3E_unit -> Z3.Z3BE_eq (e1, Z3.Z3E_unit)
    | e1, Z3.Z3E_bitone -> Z3.Z3BE_eq (e1, Z3.Z3E_bitone)
    | e1, Z3.Z3E_bitzero -> Z3.Z3BE_eq (e1, Z3.Z3E_bitzero)
    | e1, Z3.Z3E_len v -> Z3.Z3BE_eq (e1, Z3.Z3E_len v)
    | e1, Z3.Z3E_geq (v, va) -> Z3.Z3BE_eq (e1, Z3.Z3E_geq (v, va))
    | e1, Z3.Z3E_plus (v, va) -> Z3.Z3BE_eq (e1, Z3.Z3E_plus (v, va))
    | e1, Z3.Z3E_times (v, va) -> Z3.Z3BE_eq (e1, Z3.Z3E_times (v, va))
    | e1, Z3.Z3E_div (v, va) -> Z3.Z3BE_eq (e1, Z3.Z3E_div (v, va))
    | e1, Z3.Z3E_mod (v, va) -> Z3.Z3BE_eq (e1, Z3.Z3E_mod (v, va))
    | e1, Z3.Z3E_minus (v, va) -> Z3.Z3BE_eq (e1, Z3.Z3E_minus (v, va))
    | e1, Z3.Z3E_not v -> Z3.Z3BE_eq (e1, Z3.Z3E_not v)
    | e1, Z3.Z3E_and (v, va) -> Z3.Z3BE_eq (e1, Z3.Z3E_and (v, va))
    | e1, Z3.Z3E_or (v, va) -> Z3.Z3BE_eq (e1, Z3.Z3E_or (v, va))
    | e1, Z3.Z3E_neq (v, va) -> Z3.Z3BE_eq (e1, Z3.Z3E_neq (v, va))
    | e1, Z3.Z3E_bitvec v -> Z3.Z3BE_eq (e1, Z3.Z3E_bitvec v)
    | e1, Z3.Z3E_constr (v, va) -> Z3.Z3BE_eq (e1, Z3.Z3E_constr (v, va))
    | e1, Z3.Z3E_concat v -> Z3.Z3BE_eq (e1, Z3.Z3E_concat v)
    | e1, Z3.Z3E_proj (v, va) -> Z3.Z3BE_eq (e1, Z3.Z3E_proj (v, va))
    | e1, Z3.Z3E_string v -> Z3.Z3BE_eq (e1, Z3.Z3E_string v);;

let rec convert_x = function SyntaxVCT.VNamed x -> Contexts.remove_tick x
                    | SyntaxVCT.VIndex -> "#0";;

let rec convert_l
  = function SyntaxVCT.L_num n -> Z3.Z3E_num n
    | SyntaxVCT.L_true -> Z3.Z3E_true
    | SyntaxVCT.L_false -> Z3.Z3E_false
    | SyntaxVCT.L_zero -> Z3.Z3E_bitzero
    | SyntaxVCT.L_one -> Z3.Z3E_bitone
    | SyntaxVCT.L_unit -> Z3.Z3E_unit
    | SyntaxVCT.L_real s -> Z3.Z3E_string s
    | SyntaxVCT.L_string s -> Z3.Z3E_string s
    | SyntaxVCT.L_undef -> Z3.Z3E_constr ("unexpected undef", []);;

let rec convert_v
  = function
    SyntaxVCT.V_var (SyntaxVCT.VNamed x) -> Z3.Z3E_var (Contexts.remove_tick x)
    | SyntaxVCT.V_var SyntaxVCT.VIndex -> Z3.Z3E_var "unexpected z variable"
    | SyntaxVCT.V_lit lit -> convert_l lit
    | SyntaxVCT.V_constr (v, va) -> Z3.Z3E_constr (v, [convert_v va])
    | SyntaxVCT.V_record v -> Z3.Z3E_constr ("record", [])
    | SyntaxVCT.V_tuple vs ->
        Z3.Z3E_constr
          ("mk-tuple" ^
             Utils.string_lit_of_int (Arith.int_of_nat (Lista.size_list vs)),
            Lista.map convert_v vs)
    | SyntaxVCT.V_proj (s, v) -> Z3.Z3E_proj (s, convert_v v)
    | SyntaxVCT.V_list vs ->
        Lista.fold (fun v tl -> Z3.Z3E_constr ("insert", [convert_v v; tl])) vs
          (Z3.Z3E_constr ("nil", []))
    | SyntaxVCT.V_cons (v, vs) ->
        Z3.Z3E_constr ("insert", [convert_v v; convert_v vs]);;

let rec convert_ce
  = function SyntaxVCT.CE_val v -> convert_v v
    | SyntaxVCT.CE_bop (SyntaxVCT.Plus, e1, e2) ->
        Z3.Z3E_plus (convert_ce e1, convert_ce e2)
    | SyntaxVCT.CE_bop (SyntaxVCT.LEq, e1, e2) ->
        Z3.Z3E_leq (convert_ce e1, convert_ce e2)
    | SyntaxVCT.CE_bop (SyntaxVCT.Times, e1, e2) ->
        Z3.Z3E_times (convert_ce e1, convert_ce e2)
    | SyntaxVCT.CE_bop (SyntaxVCT.Minus, e1, e2) ->
        Z3.Z3E_minus (convert_ce e1, convert_ce e2)
    | SyntaxVCT.CE_bop (SyntaxVCT.Div, e1, e2) ->
        Z3.Z3E_div (convert_ce e1, convert_ce e2)
    | SyntaxVCT.CE_bop (SyntaxVCT.Mod, e1, e2) ->
        Z3.Z3E_mod (convert_ce e1, convert_ce e2)
    | SyntaxVCT.CE_bop (SyntaxVCT.Eq, e1, e2) ->
        Z3.Z3E_eq (convert_ce e1, convert_ce e2)
    | SyntaxVCT.CE_bop (SyntaxVCT.NEq, e1, e2) ->
        Z3.Z3E_not (Z3.Z3E_eq (convert_ce e1, convert_ce e2))
    | SyntaxVCT.CE_bop (SyntaxVCT.LT, e1, e2) ->
        Z3.Z3E_leq
          (Z3.Z3E_plus (convert_ce e1, Z3.Z3E_num (Z.of_int 1)), convert_ce e2)
    | SyntaxVCT.CE_bop (SyntaxVCT.And, e1, e2) ->
        Z3.Z3E_and (convert_ce e1, convert_ce e2)
    | SyntaxVCT.CE_bop (SyntaxVCT.Or, e1, e2) ->
        Z3.Z3E_or (convert_ce e1, convert_ce e2)
    | SyntaxVCT.CE_bop (SyntaxVCT.GEq, e1, e2) ->
        Z3.Z3E_not
          (Z3.Z3E_leq
            (Z3.Z3E_plus (convert_ce e1, Z3.Z3E_num (Z.of_int 1)),
              convert_ce e2))
    | SyntaxVCT.CE_bop (SyntaxVCT.GT, e1, e2) ->
        Z3.Z3E_not (Z3.Z3E_leq (convert_ce e1, convert_ce e2))
    | SyntaxVCT.CE_uop (SyntaxVCT.Len, e) -> Z3.Z3E_len (convert_ce e)
    | SyntaxVCT.CE_uop (SyntaxVCT.Not, e) -> Z3.Z3E_not (convert_ce e)
    | SyntaxVCT.CE_many_plus v -> failwith "undefined"
    | SyntaxVCT.CE_uop (SyntaxVCT.Exp, va) -> failwith "undefined"
    | SyntaxVCT.CE_uop (SyntaxVCT.Neg, va) ->
        Z3.Z3E_minus (Z3.Z3E_num Z.zero, convert_ce va)
    | SyntaxVCT.CE_proj (v, va) -> Z3.Z3E_proj (v, convert_ce va)
    | SyntaxVCT.CE_field_access (v, va) -> failwith "undefined";;

let rec z3and
  es = (let esa =
          Lista.filter (fun e -> not (Z3.equal_z3_bool_expra e Z3.Z3BE_true)) es
          in
         (match esa with [] -> Z3.Z3BE_true | [e] -> e
           | _ :: _ :: _ -> Z3.Z3BE_and esa));;

let rec convert_c
  = function SyntaxVCT.C_true -> Z3.Z3BE_true
    | SyntaxVCT.C_false -> Z3.Z3BE_false
    | SyntaxVCT.C_conj (c1, c2) -> z3and [convert_c c1; convert_c c2]
    | SyntaxVCT.C_disj (c1, c2) -> Z3.Z3BE_or [convert_c c1; convert_c c2]
    | SyntaxVCT.C_not c -> Z3.Z3BE_not (convert_c c)
    | SyntaxVCT.C_imp (c1, c2) -> Z3.Z3BE_implies (convert_c c1, convert_c c2)
    | SyntaxVCT.C_eq (e1, e2) -> z3eq (convert_ce e1) (convert_ce e2)
    | SyntaxVCT.C_leq (e1, e2) -> Z3.Z3BE_leq (convert_ce e1, convert_ce e2)
    | SyntaxVCT.C_conj_many cs -> z3and (Lista.map convert_c cs);;

let rec type_app
  x0 b = match x0, b with SyntaxVCT.B_var v, b -> [(v, b)]
    | SyntaxVCT.B_tuple bs1, SyntaxVCT.B_tuple bs2 -> type_app_lists bs1 bs2
    | SyntaxVCT.B_vec (uu, b1), SyntaxVCT.B_vec (uv, b2) -> type_app b1 b2
    | SyntaxVCT.B_union (uw, branches1), SyntaxVCT.B_union (ux, branches2) ->
        type_app_tlists branches1 branches2
    | SyntaxVCT.B_tid v, uz -> []
    | SyntaxVCT.B_int, uz -> []
    | SyntaxVCT.B_bool, uz -> []
    | SyntaxVCT.B_bit, uz -> []
    | SyntaxVCT.B_unit, uz -> []
    | SyntaxVCT.B_real, uz -> []
    | SyntaxVCT.B_vec (v, va), SyntaxVCT.B_var vb -> []
    | SyntaxVCT.B_vec (v, va), SyntaxVCT.B_tid vb -> []
    | SyntaxVCT.B_vec (v, va), SyntaxVCT.B_int -> []
    | SyntaxVCT.B_vec (v, va), SyntaxVCT.B_bool -> []
    | SyntaxVCT.B_vec (v, va), SyntaxVCT.B_bit -> []
    | SyntaxVCT.B_vec (v, va), SyntaxVCT.B_unit -> []
    | SyntaxVCT.B_vec (v, va), SyntaxVCT.B_real -> []
    | SyntaxVCT.B_vec (v, va), SyntaxVCT.B_list vb -> []
    | SyntaxVCT.B_vec (v, va), SyntaxVCT.B_tuple vb -> []
    | SyntaxVCT.B_vec (v, va), SyntaxVCT.B_union (vb, vc) -> []
    | SyntaxVCT.B_vec (v, va), SyntaxVCT.B_record vb -> []
    | SyntaxVCT.B_vec (v, va), SyntaxVCT.B_undef -> []
    | SyntaxVCT.B_vec (v, va), SyntaxVCT.B_reg -> []
    | SyntaxVCT.B_vec (v, va), SyntaxVCT.B_string -> []
    | SyntaxVCT.B_vec (v, va), SyntaxVCT.B_exception -> []
    | SyntaxVCT.B_vec (v, va), SyntaxVCT.B_finite_set vb -> []
    | SyntaxVCT.B_list v, uz -> []
    | SyntaxVCT.B_tuple v, SyntaxVCT.B_var va -> []
    | SyntaxVCT.B_tuple v, SyntaxVCT.B_tid va -> []
    | SyntaxVCT.B_tuple v, SyntaxVCT.B_int -> []
    | SyntaxVCT.B_tuple v, SyntaxVCT.B_bool -> []
    | SyntaxVCT.B_tuple v, SyntaxVCT.B_bit -> []
    | SyntaxVCT.B_tuple v, SyntaxVCT.B_unit -> []
    | SyntaxVCT.B_tuple v, SyntaxVCT.B_real -> []
    | SyntaxVCT.B_tuple v, SyntaxVCT.B_vec (va, vb) -> []
    | SyntaxVCT.B_tuple v, SyntaxVCT.B_list va -> []
    | SyntaxVCT.B_tuple v, SyntaxVCT.B_union (va, vb) -> []
    | SyntaxVCT.B_tuple v, SyntaxVCT.B_record va -> []
    | SyntaxVCT.B_tuple v, SyntaxVCT.B_undef -> []
    | SyntaxVCT.B_tuple v, SyntaxVCT.B_reg -> []
    | SyntaxVCT.B_tuple v, SyntaxVCT.B_string -> []
    | SyntaxVCT.B_tuple v, SyntaxVCT.B_exception -> []
    | SyntaxVCT.B_tuple v, SyntaxVCT.B_finite_set va -> []
    | SyntaxVCT.B_union (v, va), SyntaxVCT.B_var vb -> []
    | SyntaxVCT.B_union (v, va), SyntaxVCT.B_tid vb -> []
    | SyntaxVCT.B_union (v, va), SyntaxVCT.B_int -> []
    | SyntaxVCT.B_union (v, va), SyntaxVCT.B_bool -> []
    | SyntaxVCT.B_union (v, va), SyntaxVCT.B_bit -> []
    | SyntaxVCT.B_union (v, va), SyntaxVCT.B_unit -> []
    | SyntaxVCT.B_union (v, va), SyntaxVCT.B_real -> []
    | SyntaxVCT.B_union (v, va), SyntaxVCT.B_vec (vb, vc) -> []
    | SyntaxVCT.B_union (v, va), SyntaxVCT.B_list vb -> []
    | SyntaxVCT.B_union (v, va), SyntaxVCT.B_tuple vb -> []
    | SyntaxVCT.B_union (v, va), SyntaxVCT.B_record vb -> []
    | SyntaxVCT.B_union (v, va), SyntaxVCT.B_undef -> []
    | SyntaxVCT.B_union (v, va), SyntaxVCT.B_reg -> []
    | SyntaxVCT.B_union (v, va), SyntaxVCT.B_string -> []
    | SyntaxVCT.B_union (v, va), SyntaxVCT.B_exception -> []
    | SyntaxVCT.B_union (v, va), SyntaxVCT.B_finite_set vb -> []
    | SyntaxVCT.B_record v, uz -> []
    | SyntaxVCT.B_undef, uz -> []
    | SyntaxVCT.B_reg, uz -> []
    | SyntaxVCT.B_string, uz -> []
    | SyntaxVCT.B_exception, uz -> []
    | SyntaxVCT.B_finite_set v, uz -> []
and type_app_lists
  va vb = match va, vb with
    b1 :: bs1, b2 :: bs2 -> type_app b1 b2 @ type_app_lists bs1 bs2
    | [], vb -> []
    | va, [] -> []
and type_app_tlists
  ve vf = match ve, vf with
    (vc, t1) :: ts1, (vd, t2) :: ts2 ->
      type_app (Contexts.b_of t1) (Contexts.b_of t2) @ type_app_tlists ts1 ts2
    | [], vf -> []
    | ve, [] -> [];;

let rec type_app_t
  pi gamma (SyntaxVCT.B_union (s, cs)) =
    (match
      Contexts.lookup SyntaxVCT.equal_xp (ContextsPiDelta.theta_T pi)
        (SyntaxVCT.VNamed s)
      with None -> []
      | Some tdef ->
        type_app (Contexts.b_of tdef) (SyntaxVCT.B_union (s, cs)));;

let rec convert_b
  uu uv uw x3 = match uu, uv, uw, x3 with
    uu, uv, uw, SyntaxVCT.B_int -> (Z3.Z3T_int, Z3.Z3BE_true)
    | ux, uy, uz, SyntaxVCT.B_bool -> (Z3.Z3T_bool, Z3.Z3BE_true)
    | p, g, v, SyntaxVCT.B_tuple blist ->
        (let (blist2, clist) = convert_blist p g v blist in
          (Z3.Z3T_dt
             ("Tuple" ^ Utils.string_lit_of_nat (Lista.size_list blist),
               blist2),
            z3and clist))
    | p, g, va, SyntaxVCT.B_record ((fid, vb) :: xs) ->
        (match ContextsPiDelta.lookup_record_name p fid
          with None -> (Z3.Z3T_dt ("unknownrecord", []), Z3.Z3BE_true)
          | Some s -> (Z3.Z3T_dt (s, []), Z3.Z3BE_true))
    | p, g, vc, SyntaxVCT.B_record [] ->
        (Z3.Z3T_dt ("unknownrecord", []), Z3.Z3BE_true)
    | vd, ve, vf, SyntaxVCT.B_bit -> (Z3.Z3T_bool, Z3.Z3BE_true)
    | p, g, v, SyntaxVCT.B_vec (vg, b) ->
        (let (t, _) = convert_b p g v b in
          (Z3.Z3T_array (Z3.Z3T_int, t), Z3.Z3BE_true))
    | p, vh, vi, SyntaxVCT.B_string -> (Z3.Z3T_string, Z3.Z3BE_true)
    | p, vj, vk, SyntaxVCT.B_unit -> (Z3.Z3T_dt ("Unit", []), Z3.Z3BE_true)
    | p, g, v, SyntaxVCT.B_union (s, cs) ->
        (Z3.Z3T_dt
           (s, Lista.map (fun b -> Product_Type.fst (convert_b p g v b))
                 (Lista.map Product_Type.snd
                   (type_app_t p g (SyntaxVCT.B_union (s, cs))))),
          Z3.Z3BE_true)
    | vl, vm, vn, SyntaxVCT.B_reg -> (Z3.Z3T_dt ("reg", []), Z3.Z3BE_true)
    | vo, vp, vq, SyntaxVCT.B_var v -> (Z3.Z3T_sort v, Z3.Z3BE_true)
    | vr, vs, vt, SyntaxVCT.B_tid v -> (Z3.Z3T_dt (v, []), Z3.Z3BE_true)
    | p, g, v, SyntaxVCT.B_list b ->
        (Z3.Z3T_dt ("List", [Product_Type.fst (convert_b p g v b)]),
          Z3.Z3BE_true)
    | vu, a, b, SyntaxVCT.B_real -> (Z3.Z3T_string, Z3.Z3BE_true)
and convert_blist
  p g v blist = Contexts.unzip (Lista.map (convert_b p g v) blist);;

let rec convert_xbc
  p g x b c =
    (let (t1, c1) = convert_b p g (SyntaxVCT.V_var x) b in
      ([Z3.Z3D_decl_const (convert_x x, t1)], z3and [c1; convert_c c]));;

let rec subst_c_z
  x c = SyntaxVCT.subst_cp (SyntaxVCT.V_var x) SyntaxVCT.VIndex c;;

let rec convert_g_aux
  p g x2 = match p, g, x2 with p, g, [] -> ([], [])
    | p, g, (x, Contexts.GEPair (b, c)) :: gamma ->
        (let (ds, es) = convert_g_aux p g gamma in
         let (d, e) = convert_xbc p g x b c in
          (d @ ds, e :: es))
    | p, g, (x, Contexts.GETyp t) :: gamma ->
        (let (ds, es) = convert_g_aux p g gamma in
         let (d, e) =
           convert_xbc p g x (Contexts.b_of t) (subst_c_z x (Contexts.c_of t))
           in
          (d @ ds, e :: es));;

let rec convert_g
  p gamma =
    convert_g_aux p gamma (Contexts.gamma_x gamma @ Contexts.gamma_u gamma);;

let rec convert_smt_problem_valid
  p g ev c =
    (let (d1, e1) = convert_g p g in
     let (d2, e2) = convert_g_aux p g ev in
     let ca = convert_c c in
      (d1, (d2, z3and (e1 @ [Z3.Z3BE_not (z3and (ca :: e2))]))));;

let rec pp_z3_expr
  = function Z3.Z3E_var s -> s
    | Z3.Z3E_true -> "true"
    | Z3.Z3E_false -> "false"
    | Z3.Z3E_num n -> Utils.string_lit_of_integer n
    | Z3.Z3E_plus (e1, e2) ->
        ((("(+ " ^ pp_z3_expr e1) ^ " ") ^ pp_z3_expr e2) ^ ")"
    | Z3.Z3E_leq (e1, e2) ->
        ((("(<= " ^ pp_z3_expr e1) ^ " ") ^ pp_z3_expr e2) ^ ")"
    | Z3.Z3E_geq (e1, e2) ->
        ((("(>= " ^ pp_z3_expr e1) ^ " ") ^ pp_z3_expr e2) ^ ")"
    | Z3.Z3E_times (e1, e2) ->
        ((("(* " ^ pp_z3_expr e1) ^ " ") ^ pp_z3_expr e2) ^ ")"
    | Z3.Z3E_div (e1, e2) ->
        ((("(div " ^ pp_z3_expr e1) ^ " ") ^ pp_z3_expr e2) ^ ")"
    | Z3.Z3E_mod (e1, e2) ->
        ((("(mod " ^ pp_z3_expr e1) ^ " ") ^ pp_z3_expr e2) ^ ")"
    | Z3.Z3E_minus (e1, e2) ->
        ((("(- " ^ pp_z3_expr e1) ^ " ") ^ pp_z3_expr e2) ^ ")"
    | Z3.Z3E_eq (e1, e2) ->
        ((("(= " ^ pp_z3_expr e1) ^ " ") ^ pp_z3_expr e2) ^ ")"
    | Z3.Z3E_neq (e1, e2) ->
        (((("not (" ^ "(= ") ^ pp_z3_expr e1) ^ " ") ^ pp_z3_expr e2) ^ "))"
    | Z3.Z3E_and (e1, e2) ->
        ((("(and " ^ pp_z3_expr e1) ^ " ") ^ pp_z3_expr e2) ^ ")"
    | Z3.Z3E_or (e1, e2) ->
        ((("(or " ^ pp_z3_expr e1) ^ " ") ^ pp_z3_expr e2) ^ ")"
    | Z3.Z3E_constr (s, vs) ->
        (if ((s : string) = "nil") then "nil"
          else ((("( " ^ s) ^ " ") ^
                 Lista.foldr (fun t -> (fun a -> (pp_z3_expr t ^ " ") ^ a)) vs
                   " ") ^
                 " ) ")
    | Z3.Z3E_concat es ->
        ((("( concat" ^
            Utils.string_lit_of_int (Arith.int_of_nat (Lista.size_list es))) ^
           " ") ^
          Lista.foldr (fun t -> (fun a -> (pp_z3_expr t ^ " ") ^ a)) es " ") ^
          " ) "
    | Z3.Z3E_bitone -> "true"
    | Z3.Z3E_bitzero -> "false"
    | Z3.Z3E_unit -> "unit"
    | Z3.Z3E_bitvec s -> "bitvec" ^ s
    | Z3.Z3E_proj (s, v) -> ((("(proj" ^ s) ^ " ") ^ pp_z3_expr v) ^ ")"
    | Z3.Z3E_len e -> ("(llen " ^ pp_z3_expr e) ^ " )"
    | Z3.Z3E_not e -> ("(not " ^ pp_z3_expr e) ^ " )"
    | Z3.Z3E_string s -> ("\034" ^ s) ^ "\034";;

let rec pp_z3_bool_expr
  = function Z3.Z3BE_true -> "true"
    | Z3.Z3BE_false -> "false"
    | Z3.Z3BE_not e -> ("( not " ^ pp_z3_bool_expr e) ^ ")"
    | Z3.Z3BE_and elist ->
        ("(and " ^
          Lista.foldr (fun t -> (fun a -> (pp_z3_bool_expr t ^ " ") ^ a)) elist
            " ") ^
          ")"
    | Z3.Z3BE_or elist ->
        ("(or " ^
          Lista.foldr (fun t -> (fun a -> (pp_z3_bool_expr t ^ " ") ^ a)) elist
            " ") ^
          ")"
    | Z3.Z3BE_eq (e1, e2) ->
        ((("(= " ^ pp_z3_expr e1) ^ " ") ^ pp_z3_expr e2) ^ ")"
    | Z3.Z3BE_leq (e1, e2) ->
        ((("(<= " ^ pp_z3_expr e1) ^ " ") ^ pp_z3_expr e2) ^ ")"
    | Z3.Z3BE_implies (c1, c2) ->
        ((("( => " ^ pp_z3_bool_expr c1) ^ " ") ^ pp_z3_bool_expr c2) ^ ")";;

let z3_vector_sort : string = "(Array Int Bool)";;

let rec pp_bv_concats
  n = Lista.maps
        (fun i ->
          [((((("(declare-fun concat" ^ Utils.string_lit_of_int i) ^ " (") ^
               Utils.string_lit_map " " (fun _ -> z3_vector_sort)
                 (Lista.upto Arith.one_int i)) ^
              ") ") ^
             z3_vector_sort) ^
             ")"])
        (Lista.upto Arith.one_int n);;

let rec t_t_vars (SyntaxVCT.T_refined_type (vIndex0, b, c)) = b_t_vars b
and b_t_vars
  = function SyntaxVCT.B_var s -> [s]
    | SyntaxVCT.B_tuple bs ->
        Lista.remdups Stringa.equal_literal (Lista.maps b_t_vars bs)
    | SyntaxVCT.B_union (uu, ts) ->
        Lista.remdups Stringa.equal_literal
          (Lista.maps (fun (_, a) -> t_t_vars a) ts)
    | SyntaxVCT.B_record ts ->
        Lista.remdups Stringa.equal_literal
          (Lista.maps (fun (_, a) -> b_t_vars a) ts)
    | SyntaxVCT.B_vec (uv, b) -> b_t_vars b
    | SyntaxVCT.B_list b -> b_t_vars b
    | SyntaxVCT.B_tid v -> []
    | SyntaxVCT.B_int -> []
    | SyntaxVCT.B_bool -> []
    | SyntaxVCT.B_bit -> []
    | SyntaxVCT.B_unit -> []
    | SyntaxVCT.B_real -> []
    | SyntaxVCT.B_undef -> []
    | SyntaxVCT.B_reg -> []
    | SyntaxVCT.B_string -> []
    | SyntaxVCT.B_exception -> []
    | SyntaxVCT.B_finite_set v -> [];;

let rec pp_sort_decl
  p g = Lista.maps
          (fun (_, t) ->
            Lista.map
              (fun s -> ("(declare-sort " ^ Contexts.remove_tick s) ^ ")")
              (t_t_vars t))
          (ContextsPiDelta.theta_T p);;

let rec bv_consts_v
  = function SyntaxVCT.V_tuple vs -> Lista.maps bv_consts_v vs
    | SyntaxVCT.V_lit v -> []
    | SyntaxVCT.V_var v -> []
    | SyntaxVCT.V_vec v -> []
    | SyntaxVCT.V_list v -> []
    | SyntaxVCT.V_cons (v, va) -> []
    | SyntaxVCT.V_constr (v, va) -> []
    | SyntaxVCT.V_record v -> []
    | SyntaxVCT.V_proj (v, va) -> [];;

let rec bv_consts_ce
  = function SyntaxVCT.CE_val v -> bv_consts_v v
    | SyntaxVCT.CE_bop (opp, v1, v2) -> bv_consts_ce v1 @ bv_consts_ce v2
    | SyntaxVCT.CE_uop (opp, v) -> bv_consts_ce v
    | SyntaxVCT.CE_many_plus v -> Lista.maps bv_consts_ce v
    | SyntaxVCT.CE_proj (v, va) -> bv_consts_ce va
    | SyntaxVCT.CE_field_access (v, va) -> [];;

let rec bv_consts_c
  = function SyntaxVCT.C_eq (e1, e2) -> bv_consts_ce e1 @ bv_consts_ce e2
    | SyntaxVCT.C_conj (e1, e2) -> bv_consts_c e1 @ bv_consts_c e2
    | SyntaxVCT.C_disj (e1, e2) -> bv_consts_c e1 @ bv_consts_c e2
    | SyntaxVCT.C_imp (e1, e2) -> bv_consts_c e1 @ bv_consts_c e2
    | SyntaxVCT.C_not e1 -> bv_consts_c e1
    | SyntaxVCT.C_true -> []
    | SyntaxVCT.C_false -> []
    | SyntaxVCT.C_conj_many v -> []
    | SyntaxVCT.C_leq (v, va) -> [];;

let rec c_of_e = function Contexts.GEPair (uu, c) -> c
                 | Contexts.GETyp t -> Contexts.c_of t;;

let rec bv_consts_aux
  xbc = Lista.maps (fun (_, e) -> bv_consts_c (c_of_e e)) xbc;;

let rec pp_bitvec uu = [];;

let rec pp_bv_consts
  g ev c =
    (let bvs =
       bv_consts_aux (Contexts.gamma_x g) @ bv_consts_aux ev @ bv_consts_c c in
      Lista.maps pp_bitvec (Lista.remdups SyntaxVCT.equal_lit bvs));;

let pp_z3_vector_funs : string = "";;

let rec pp_z3_type
  = function Z3.Z3T_int -> "Int"
    | Z3.Z3T_bool -> "Bool"
    | Z3.Z3T_unit -> "Unit"
    | Z3.Z3T_array (t1, t2) ->
        ((("(Array " ^ pp_z3_type t1) ^ " ") ^ pp_z3_type t2) ^ " )"
    | Z3.Z3T_dt (s, tlist) ->
        ((("( " ^ s) ^ " ") ^
          Lista.foldr (fun t -> (fun a -> (pp_z3_type t ^ " ") ^ a)) tlist
            " ") ^
          ") "
    | Z3.Z3T_sort s -> Contexts.remove_tick s
    | Z3.Z3T_string -> "String";;

let rec pp_z3_type_var
  = function Z3.Z3TV_tv_type t -> pp_z3_type t
    | Z3.Z3TV_tv_var n -> "T" ^ Utils.string_lit_of_integer n;;

let rec pp_z3_fields
  fs = Lista.foldr
         (fun (c, t) ->
           (fun a -> ((((" ( " ^ c) ^ " ") ^ pp_z3_type_var t) ^ " ) ") ^ a))
         fs "";;

let rec pp_z3_ty_constr
  (Z3.Z3C_ty_constr (c, x)) = (((" ( " ^ c) ^ " ") ^ pp_z3_fields x) ^ ")";;

let rec pp_z3_decl
  = function
    Z3.Z3D_decl_const (s, t) ->
      ((("(declare-const " ^ s) ^ " ") ^ pp_z3_type t) ^ ")"
    | Z3.Z3D_decl_fun -> "Unknown"
    | Z3.Z3D_decl_datatype (s, tvs, dt_list) ->
        (((((((("(declare-datatypes " ^ " (( ") ^ s) ^ " ") ^
              Utils.string_lit_of_nat (Lista.size_list tvs)) ^
             ")) (( par ( ") ^
            Utils.string_lit_map " " pp_z3_type_var tvs) ^
           " ) ( ") ^
          Lista.foldr (fun tc -> (fun a -> pp_z3_ty_constr tc ^ a)) dt_list
            "") ^
          "))))";;

let rec z3_declare_tuple
  n = Z3.Z3D_decl_datatype
        ("Tuple" ^ Utils.string_lit_of_int n,
          Lista.map (fun i -> Z3.Z3TV_tv_var (Arith.integer_of_int i))
            (Lista.upto Arith.one_int n),
          [Z3.Z3C_ty_constr
             ("mk-tuple" ^ Utils.string_lit_of_int n,
               Lista.map
                 (fun i ->
                   ((("proj" ^ Utils.string_lit_of_int n) ^ "X") ^
                      Utils.string_lit_of_int i,
                     Z3.Z3TV_tv_var (Arith.integer_of_int i)))
                 (Lista.upto Arith.one_int n))]);;

let rec pp_tuples
  n = Lista.map (fun i -> pp_z3_decl (z3_declare_tuple i))
        (Lista.upto Arith.one_int n);;

let rec pp_builtins
  n = pp_z3_vector_funs ::
        (("(declare-fun llen (" ^ z3_vector_sort) ^ ") Int)") ::
          pp_z3_decl
            (Z3.Z3D_decl_datatype
              ("Unit", [], [Z3.Z3C_ty_constr ("unit", [])])) ::
            pp_tuples n;;

let rec convert_t
  p g v (SyntaxVCT.T_refined_type (vIndex0, b, c)) =
    (let (t, e) = convert_b p g v b in
      (t, z3and [e; convert_c (SyntaxVCT.subst_cp v SyntaxVCT.VIndex c)]));;

let rec convert_typedef
  p g x2 = match p, g, x2 with
    p, g, (SyntaxVCT.VNamed x,
            SyntaxVCT.T_refined_type (uu, SyntaxVCT.B_union (s, clist), uv))
      -> Some (Z3.Z3D_decl_datatype
                (x, Lista.map (fun v -> Z3.Z3TV_tv_type (Z3.Z3T_sort v))
                      (Lista.maps (fun (_, a) -> t_t_vars a) clist),
                  Lista.map
                    (fun (sa, t) ->
                      (let (zt, _) =
                         convert_t p g (SyntaxVCT.V_var SyntaxVCT.VIndex) t in
                        Z3.Z3C_ty_constr
                          (sa, [((("proj" ^ x) ^ "x") ^ sa,
                                  Z3.Z3TV_tv_type zt)])))
                    clist))
    | p, g, (SyntaxVCT.VNamed x,
              SyntaxVCT.T_refined_type (uw, SyntaxVCT.B_record clist, ux))
        -> Some (Z3.Z3D_decl_datatype
                  (x, Lista.map (fun v -> Z3.Z3TV_tv_type (Z3.Z3T_sort v))
                        (Lista.maps (fun (_, a) -> b_t_vars a) clist),
                    [Z3.Z3C_ty_constr
                       ("mk-" ^ x,
                         Lista.map
                           (fun (s, t) ->
                             (let (zt, _) =
                                convert_b p g (SyntaxVCT.V_var SyntaxVCT.VIndex)
                                  t
                                in
                               ("proj" ^ s, Z3.Z3TV_tv_type zt)))
                           clist)]))
    | uy, uz, (SyntaxVCT.VIndex, vb) -> None
    | uy, uz, (v, SyntaxVCT.T_refined_type (vc, SyntaxVCT.B_var vf, ve)) -> None
    | uy, uz, (v, SyntaxVCT.T_refined_type (vc, SyntaxVCT.B_tid vf, ve)) -> None
    | uy, uz, (v, SyntaxVCT.T_refined_type (vc, SyntaxVCT.B_int, ve)) -> None
    | uy, uz, (v, SyntaxVCT.T_refined_type (vc, SyntaxVCT.B_bool, ve)) -> None
    | uy, uz, (v, SyntaxVCT.T_refined_type (vc, SyntaxVCT.B_bit, ve)) -> None
    | uy, uz, (v, SyntaxVCT.T_refined_type (vc, SyntaxVCT.B_unit, ve)) -> None
    | uy, uz, (v, SyntaxVCT.T_refined_type (vc, SyntaxVCT.B_real, ve)) -> None
    | uy, uz, (v, SyntaxVCT.T_refined_type (vc, SyntaxVCT.B_vec (vf, vg), ve))
        -> None
    | uy, uz, (v, SyntaxVCT.T_refined_type (vc, SyntaxVCT.B_list vf, ve)) ->
        None
    | uy, uz, (v, SyntaxVCT.T_refined_type (vc, SyntaxVCT.B_tuple vf, ve)) ->
        None
    | uy, uz, (v, SyntaxVCT.T_refined_type (vc, SyntaxVCT.B_undef, ve)) -> None
    | uy, uz, (v, SyntaxVCT.T_refined_type (vc, SyntaxVCT.B_reg, ve)) -> None
    | uy, uz, (v, SyntaxVCT.T_refined_type (vc, SyntaxVCT.B_string, ve)) -> None
    | uy, uz, (v, SyntaxVCT.T_refined_type (vc, SyntaxVCT.B_exception, ve)) ->
        None
    | uy, uz, (v, SyntaxVCT.T_refined_type (vc, SyntaxVCT.B_finite_set vf, ve))
        -> None;;

let rec pp_typedef
  p g td =
    (match convert_typedef p g td with None -> "" | Some a -> pp_z3_decl a);;

let max_tuples : Arith.int = Arith.Int_of_integer (Z.of_int 6);;

let rec pp_smt_problem_valid
  p g ev c =
    (let (d1, (d2, e1)) = convert_smt_problem_valid p g ev c in
      pp_bv_concats (Arith.Int_of_integer (Z.of_int 3)) @
        pp_builtins max_tuples @
          pp_bv_consts g ev c @
            pp_sort_decl p g @
              Lista.map (pp_typedef p g)
                (Lista.rev (ContextsPiDelta.theta_T p)) @
                Lista.map pp_z3_decl d1 @
                  [("(define-fun constraint () Bool " ^ pp_z3_bool_expr e1) ^
                     (if Arith.equal_nat (Lista.size_list d2) Arith.zero_nat
                       then ")" else "))")] @
                    ["(assert constraint)"; "(check-sat)"]);;

let rec has_no_t_var_b
  = function SyntaxVCT.B_var uu -> false
    | SyntaxVCT.B_tuple bs -> Lista.list_all has_no_t_var_b bs
    | SyntaxVCT.B_tid v -> true
    | SyntaxVCT.B_int -> true
    | SyntaxVCT.B_bool -> true
    | SyntaxVCT.B_bit -> true
    | SyntaxVCT.B_unit -> true
    | SyntaxVCT.B_real -> true
    | SyntaxVCT.B_vec (v, va) -> true
    | SyntaxVCT.B_list v -> true
    | SyntaxVCT.B_union (v, va) -> true
    | SyntaxVCT.B_record v -> true
    | SyntaxVCT.B_undef -> true
    | SyntaxVCT.B_reg -> true
    | SyntaxVCT.B_string -> true
    | SyntaxVCT.B_exception -> true
    | SyntaxVCT.B_finite_set v -> true;;

let rec b_of_e = function Contexts.GEPair (b, uu) -> b
                 | Contexts.GETyp t -> Contexts.b_of t;;

let rec has_no_t_var_g
  g = Lista.list_all (fun (_, t) -> has_no_t_var_b (b_of_e t))
        (Contexts.gamma_x g);;

let rec has_t_var
  g xbc =
    not (has_no_t_var_g g &&
          Lista.list_all (fun (_, t) -> has_no_t_var_b (b_of_e t)) xbc);;

let rec valid
  s loc p g xbc c =
    (let _ = Debug.trace ("satisfiable call" ^ Contexts.pp_G g) in
      has_t_var g xbc ||
        Smt2.traceG s g xbc c &&
          not (Smt2.satisfiable s loc (pp_smt_problem_valid p g xbc c) false));;

end;; (*struct Satis*)

module ConvertTypes : sig
  val elim :
    Arith.nat ->
      Z.t list * SyntaxVCT.cep ->
        Z.t list * SyntaxVCT.cep -> Z.t list * SyntaxVCT.cep
  val swap :
    Arith.nat ->
      Arith.nat ->
        (Z.t list * SyntaxVCT.cep) list -> (Z.t list * SyntaxVCT.cep) list
  val zipi : 'a list -> (Arith.nat * 'a) list
  val nonZeroElement :
    Arith.nat -> (Z.t list * SyntaxVCT.cep) list -> Arith.nat option
  val swap_if_0 :
    Arith.nat ->
      (Z.t list * SyntaxVCT.cep) list ->
        ((Z.t list * SyntaxVCT.cep) list) option
  val solve_jth :
    Arith.nat ->
      (Z.t list * SyntaxVCT.cep) list -> (Z.t list * SyntaxVCT.cep) list
  val solve : (Z.t list * SyntaxVCT.cep) list -> (Z.t list * SyntaxVCT.cep) list
  val is_const : Z.t list -> bool
  val extract_ce :
    Z.t -> Z.t -> SyntaxVCT.cep -> SyntaxVCT.cep * SyntaxVCT.cp list
  val solve_ce :
    (Z.t list * SyntaxVCT.cep) list -> SyntaxVCT.cep list * SyntaxVCT.cp list
  val coeff_mult_constant : Z.t -> (Z.t list) option -> (Z.t list) option
  val coeff_times : (Z.t list) option -> (Z.t list) option -> (Z.t list) option
  val coeff_plus : (Z.t list) option -> (Z.t list) option -> (Z.t list) option
  val linearise : SyntaxVCT.xp list -> SyntaxVCT.cep -> (Z.t list) option
  val linearise_A :
    SyntaxVCT.xp list ->
      (SyntaxVCT.cep * SyntaxVCT.cep) list ->
        ((Z.t list * SyntaxVCT.cep) list) option
  val solve_ce_ce :
    SyntaxVCT.xp list ->
      (SyntaxVCT.cep * SyntaxVCT.cep) list ->
        (SyntaxVCT.cep list * SyntaxVCT.cp list) option
end = struct

let rec elim
  j (cs1, ce1) (cs2, ce2) =
    (let cs1a =
       (if Z.equal (Lista.nth cs2 j) (Z.of_int 1) then cs1
         else Lista.map (fun x -> Z.mul x (Lista.nth cs2 j)) cs1)
       in
     let cs2a =
       (if Z.equal (Lista.nth cs1 j) (Z.of_int 1) then cs2
         else Lista.map (fun x -> Z.mul x (Lista.nth cs1 j)) cs2)
       in
     let ce1a =
       (if Z.equal (Lista.nth cs2 j) (Z.of_int 1) then ce1
         else SyntaxVCT.CE_bop
                (SyntaxVCT.Times, ce1,
                  SyntaxVCT.CE_val
                    (SyntaxVCT.V_lit (SyntaxVCT.L_num (Lista.nth cs2 j)))))
       in
     let ce2a =
       (if Z.equal (Lista.nth cs1 j) (Z.of_int 1) then ce2
         else SyntaxVCT.CE_bop
                (SyntaxVCT.Times, ce2,
                  SyntaxVCT.CE_val
                    (SyntaxVCT.V_lit (SyntaxVCT.L_num (Lista.nth cs1 j)))))
       in
     let cs2b = Lista.map (fun (a, b) -> Z.sub a b) (Lista.zip cs2a cs1a) in
     let a = SyntaxVCT.CE_bop (SyntaxVCT.Minus, ce2a, ce1a) in
      (cs2b, a));;

let rec swap
  i j a =
    (let b = Lista.nth a i in
      Lista.list_update (Lista.list_update a i (Lista.nth a j)) j b);;

let rec zipi xs = Lista.zip (Lista.upt Arith.zero_nat (Lista.size_list xs)) xs;;

let rec nonZeroElement
  j xs =
    (match
      Lista.filter
        (fun (i, (r, _)) ->
          Arith.less_eq_nat j i && not (Z.equal (Lista.nth r j) Z.zero))
        (zipi xs)
      with [] -> None | (x, _) :: _ -> Some x);;

let rec swap_if_0
  j a = (if Z.equal (Lista.nth (Product_Type.fst (Lista.nth a j)) j) Z.zero
          then (match nonZeroElement j a with None -> None
                 | Some i -> Some (swap i j a))
          else Some a);;

let rec solve_jth
  j a = (match swap_if_0 j a with None -> a
          | Some aa ->
            Lista.map
              (fun (i, (r, _)) ->
                (if Arith.equal_nat i j || Z.equal (Lista.nth r j) Z.zero
                  then Lista.nth aa i
                  else elim j (Lista.nth aa j) (Lista.nth aa i)))
              (zipi aa));;

let rec solve
  a = Lista.fold solve_jth
        (Lista.upt Arith.zero_nat
          (Arith.minus_nat
            (Lista.size_list (Product_Type.fst (Lista.nth a Arith.zero_nat)))
            Arith.one_nat))
        a;;

let rec is_const = function [x] -> true
                   | x :: v :: va -> Z.equal x Z.zero && is_const (v :: va);;

let rec extract_ce
  m n ce =
    (let cea =
       (if Z.equal m Z.zero then ce
         else SyntaxVCT.CE_bop
                (SyntaxVCT.Minus, ce,
                  SyntaxVCT.CE_val (SyntaxVCT.V_lit (SyntaxVCT.L_num m))))
       in
      (if Z.equal n (Z.of_int 1) then (cea, [])
        else (SyntaxVCT.CE_bop
                (SyntaxVCT.Div, cea,
                  SyntaxVCT.CE_val (SyntaxVCT.V_lit (SyntaxVCT.L_num n))),
               [SyntaxVCT.C_eq
                  (SyntaxVCT.CE_bop
                     (SyntaxVCT.Mod, cea,
                       SyntaxVCT.CE_val (SyntaxVCT.V_lit (SyntaxVCT.L_num n))),
                    SyntaxVCT.CE_val
                      (SyntaxVCT.V_lit (SyntaxVCT.L_num Z.zero)))])));;

let rec solve_ce
  a = (let aa = solve a in
       let (xs, ys) =
         Utils.unzip
           (Lista.map
             (fun (i, (ces, ce)) ->
               (if Arith.less_eq_nat
                     (Arith.minus_nat (Lista.size_list ces) Arith.one_nat) i
                 then extract_ce
                        (Lista.nth ces
                          (Arith.minus_nat (Lista.size_list ces) Arith.one_nat))
                        (Z.of_int 1) ce
                 else extract_ce
                        (Lista.nth ces
                          (Arith.minus_nat (Lista.size_list ces) Arith.one_nat))
                        (Lista.nth ces i) ce))
             (zipi aa))
         in
        (xs, Lista.concat ys));;

let rec coeff_mult_constant
  i x1 = match i, x1 with i, Some xs -> Some (Lista.map (fun x -> Z.mul x i) xs)
    | i, None -> None;;

let rec coeff_times
  x0 uu = match x0, uu with
    Some xs, Some ys ->
      (if is_const xs then coeff_mult_constant (Lista.last xs) (Some ys)
        else (if is_const ys then coeff_mult_constant (Lista.last ys) (Some xs)
               else None))
    | None, uu -> None
    | Some v, None -> None;;

let rec coeff_plus
  x0 uu = match x0, uu with
    Some xs, Some ys ->
      Some (Lista.map (fun (a, b) -> Z.add a b) (Lista.zip xs ys))
    | None, uu -> None
    | Some v, None -> None;;

let rec linearise
  ks x1 = match ks, x1 with
    ks, SyntaxVCT.CE_val (SyntaxVCT.V_lit (SyntaxVCT.L_num i)) ->
      Some (Lista.map (fun _ -> Z.zero) ks @ [i])
    | ks, SyntaxVCT.CE_val (SyntaxVCT.V_var x) ->
        Some (Lista.map
                (fun y ->
                  (if SyntaxVCT.equal_xpa x y then (Z.of_int 1) else Z.zero))
                ks @
               [Z.zero])
    | ks, SyntaxVCT.CE_bop (SyntaxVCT.Plus, ce1, ce2) ->
        coeff_plus (linearise ks ce1) (linearise ks ce2)
    | ks, SyntaxVCT.CE_bop (SyntaxVCT.Minus, ce1, ce2) ->
        coeff_plus (linearise ks ce1)
          (coeff_mult_constant (Z.neg (Z.of_int 1)) (linearise ks ce2))
    | ks, SyntaxVCT.CE_bop (SyntaxVCT.Times, ce1, ce2) ->
        coeff_times (linearise ks ce1) (linearise ks ce2)
    | ks, SyntaxVCT.CE_val (SyntaxVCT.V_lit SyntaxVCT.L_unit) -> Some []
    | ks, SyntaxVCT.CE_val (SyntaxVCT.V_lit SyntaxVCT.L_zero) -> Some []
    | ks, SyntaxVCT.CE_val (SyntaxVCT.V_lit SyntaxVCT.L_one) -> Some []
    | ks, SyntaxVCT.CE_val (SyntaxVCT.V_lit SyntaxVCT.L_true) -> Some []
    | ks, SyntaxVCT.CE_val (SyntaxVCT.V_lit SyntaxVCT.L_false) -> Some []
    | ks, SyntaxVCT.CE_val (SyntaxVCT.V_lit (SyntaxVCT.L_string vb)) -> Some []
    | ks, SyntaxVCT.CE_val (SyntaxVCT.V_lit SyntaxVCT.L_undef) -> Some []
    | ks, SyntaxVCT.CE_val (SyntaxVCT.V_lit (SyntaxVCT.L_real vb)) -> Some []
    | ks, SyntaxVCT.CE_val (SyntaxVCT.V_vec va) -> Some []
    | ks, SyntaxVCT.CE_val (SyntaxVCT.V_list va) -> Some []
    | ks, SyntaxVCT.CE_val (SyntaxVCT.V_cons (va, vb)) -> Some []
    | ks, SyntaxVCT.CE_val (SyntaxVCT.V_constr (va, vb)) -> Some []
    | ks, SyntaxVCT.CE_val (SyntaxVCT.V_record va) -> Some []
    | ks, SyntaxVCT.CE_val (SyntaxVCT.V_tuple va) -> Some []
    | ks, SyntaxVCT.CE_val (SyntaxVCT.V_proj (va, vb)) -> Some []
    | ks, SyntaxVCT.CE_bop (SyntaxVCT.Div, va, vb) -> Some []
    | ks, SyntaxVCT.CE_bop (SyntaxVCT.Mod, va, vb) -> Some []
    | ks, SyntaxVCT.CE_bop (SyntaxVCT.LEq, va, vb) -> Some []
    | ks, SyntaxVCT.CE_bop (SyntaxVCT.LT, va, vb) -> Some []
    | ks, SyntaxVCT.CE_bop (SyntaxVCT.GT, va, vb) -> Some []
    | ks, SyntaxVCT.CE_bop (SyntaxVCT.GEq, va, vb) -> Some []
    | ks, SyntaxVCT.CE_bop (SyntaxVCT.Eq, va, vb) -> Some []
    | ks, SyntaxVCT.CE_bop (SyntaxVCT.And, va, vb) -> Some []
    | ks, SyntaxVCT.CE_bop (SyntaxVCT.Or, va, vb) -> Some []
    | ks, SyntaxVCT.CE_bop (SyntaxVCT.NEq, va, vb) -> Some []
    | ks, SyntaxVCT.CE_many_plus v -> Some []
    | ks, SyntaxVCT.CE_uop (v, va) -> Some []
    | ks, SyntaxVCT.CE_proj (v, va) -> Some []
    | ks, SyntaxVCT.CE_field_access (v, va) -> Some [];;

let rec linearise_A
  ks x1 = match ks, x1 with ks, [] -> Some []
    | ks, (ce1, ce2) :: ces ->
        (match (linearise ks ce1, linearise_A ks ces) with (None, _) -> None
          | (Some _, None) -> None
          | (Some ce1a, Some cesa) -> Some ((ce1a, ce2) :: cesa));;

let rec solve_ce_ce
  ks ces =
    (match linearise_A ks ces with None -> None | Some a -> Some (solve_ce a));;

end;; (*struct ConvertTypes*)

module SyntaxPEDDecl : sig
  val tsubst_bp : SyntaxVCT.bp -> string -> SyntaxVCT.bp -> SyntaxVCT.bp
  val tsubst_tp : SyntaxVCT.bp -> string -> SyntaxVCT.tau -> SyntaxVCT.tau
  val tsubst_ctor_tau :
    SyntaxVCT.bp -> string -> string * SyntaxVCT.tau -> string * SyntaxVCT.tau
  val tsubst_ctor_tau_list :
    SyntaxVCT.bp ->
      string -> (string * SyntaxVCT.tau) list -> (string * SyntaxVCT.tau) list
  val tsubst_bp_list :
    SyntaxVCT.bp -> string -> SyntaxVCT.bp list -> SyntaxVCT.bp list
  val tsubst_field_bp :
    SyntaxVCT.bp -> string -> string * SyntaxVCT.bp -> string * SyntaxVCT.bp
  val tsubst_field_bp_list :
    SyntaxVCT.bp ->
      string -> (string * SyntaxVCT.bp) list -> (string * SyntaxVCT.bp) list
  val tsubst_bsub : SyntaxVCT.bp -> string -> SyntaxVCT.bsub -> SyntaxVCT.bsub
end = struct

let rec tsubst_bp
  bp_5 tvar5 x2 = match bp_5, tvar5, x2 with
    bp_5, tvar5, SyntaxVCT.B_var tvar ->
      (if ((tvar : string) = tvar5) then bp_5 else SyntaxVCT.B_var tvar)
    | bp_5, tvar5, SyntaxVCT.B_tid id -> SyntaxVCT.B_tid id
    | bp_5, tvar5, SyntaxVCT.B_int -> SyntaxVCT.B_int
    | bp_5, tvar5, SyntaxVCT.B_bool -> SyntaxVCT.B_bool
    | bp_5, tvar5, SyntaxVCT.B_bit -> SyntaxVCT.B_bit
    | bp_5, tvar5, SyntaxVCT.B_unit -> SyntaxVCT.B_unit
    | bp_5, tvar5, SyntaxVCT.B_real -> SyntaxVCT.B_real
    | bp_5, tvar5, SyntaxVCT.B_vec (order, bp) ->
        SyntaxVCT.B_vec (order, tsubst_bp bp_5 tvar5 bp)
    | bp_5, tvar5, SyntaxVCT.B_list bp ->
        SyntaxVCT.B_list (tsubst_bp bp_5 tvar5 bp)
    | bp_5, tvar5, SyntaxVCT.B_tuple bp_list ->
        SyntaxVCT.B_tuple (tsubst_bp_list bp_5 tvar5 bp_list)
    | bp_5, tvar5, SyntaxVCT.B_union (id, ctor_tau_list) ->
        SyntaxVCT.B_union (id, tsubst_ctor_tau_list bp_5 tvar5 ctor_tau_list)
    | bp_5, tvar5, SyntaxVCT.B_record field_bp_list ->
        SyntaxVCT.B_record (tsubst_field_bp_list bp_5 tvar5 field_bp_list)
    | bp_5, tvar5, SyntaxVCT.B_undef -> SyntaxVCT.B_undef
    | bp_5, tvar5, SyntaxVCT.B_reg -> SyntaxVCT.B_reg
    | bp_5, tvar5, SyntaxVCT.B_string -> SyntaxVCT.B_string
    | bp_5, tvar5, SyntaxVCT.B_exception -> SyntaxVCT.B_exception
    | bp_5, tvar5, SyntaxVCT.B_finite_set num_list ->
        SyntaxVCT.B_finite_set num_list
and tsubst_tp
  bp5 tvar5 (SyntaxVCT.T_refined_type (zp, bp, cp)) =
    SyntaxVCT.T_refined_type (zp, tsubst_bp bp5 tvar5 bp, cp)
and tsubst_ctor_tau bp_5 tvar5 (ctor1, tp1) = (ctor1, tsubst_tp bp_5 tvar5 tp1)
and tsubst_ctor_tau_list
  bp_5 tvar5 x2 = match bp_5, tvar5, x2 with bp_5, tvar5, [] -> []
    | bp_5, tvar5, ctor_tau_XXX :: ctor_tau_list_XXX ->
        tsubst_ctor_tau bp_5 tvar5 ctor_tau_XXX ::
          tsubst_ctor_tau_list bp_5 tvar5 ctor_tau_list_XXX
and tsubst_bp_list
  bp_5 tvar5 x2 = match bp_5, tvar5, x2 with bp_5, tvar5, [] -> []
    | bp_5, tvar5, bp_XXX :: bp_list_XXX ->
        tsubst_bp bp_5 tvar5 bp_XXX :: tsubst_bp_list bp_5 tvar5 bp_list_XXX
and tsubst_field_bp
  bp_5 tvar5 (field1, bp1) = (field1, tsubst_bp bp_5 tvar5 bp1)
and tsubst_field_bp_list
  bp_5 tvar5 x2 = match bp_5, tvar5, x2 with bp_5, tvar5, [] -> []
    | bp_5, tvar5, field_bp_XXX :: field_bp_list_XXX ->
        tsubst_field_bp bp_5 tvar5 field_bp_XXX ::
          tsubst_field_bp_list bp_5 tvar5 field_bp_list_XXX;;

let rec tsubst_bsub
  bp5 tvar5 x2 = match bp5, tvar5, x2 with
    bp5, tvar5, SyntaxVCT.BS_empty -> SyntaxVCT.BS_empty
    | bp5, tvar5, SyntaxVCT.BS_cons (bsub, bp, tvar) ->
        SyntaxVCT.BS_cons
          (tsubst_bsub bp5 tvar5 bsub, tsubst_bp bp5 tvar5 bp, tvar);;

end;; (*struct SyntaxPEDDecl*)

module TypingMonadFunction : sig
  val pp_b : SyntaxVCT.bp -> string
  val id_of : SyntaxVCT.xp -> string
  val unzip3 : ('a * ('b * 'c)) list -> 'a list * ('b list * 'c list)
  val infer_pat :
    (SyntaxPED.pexpp, unit) Contexts.gamma_ext ->
      Location.loc ->
        SyntaxPED.patp ->
          (SyntaxVCT.xp *
            ((SyntaxVCT.xp * (SyntaxVCT.bp * SyntaxVCT.cp)) list *
              (SyntaxVCT.tau option * SyntaxVCT.xp list)))
            Monad.checkM
  val kvars_of :
    SyntaxVCT.tau -> (SyntaxVCT.xp * (SyntaxVCT.bp * SyntaxVCT.cp)) list
  val tsubst_b_bs : SyntaxVCT.bp -> (string * SyntaxVCT.bp) list -> SyntaxVCT.bp
  val subtype :
    Location.loc ->
      unit ContextsPiDelta.theta_ext ->
        (SyntaxPED.pexpp, unit) Contexts.gamma_ext ->
          SyntaxVCT.tau -> SyntaxVCT.tau -> bool Monad.checkM
  val check_pat :
    bool ->
      unit ContextsPiDelta.theta_ext ->
        (SyntaxPED.pexpp, unit) ContextsPiDelta.phi_ext ->
          (SyntaxPED.pexpp, unit) Contexts.gamma_ext ->
            SyntaxPED.patp ->
              SyntaxVCT.tau ->
                (SyntaxVCT.xp *
                  ((SyntaxVCT.xp * (SyntaxVCT.bp * SyntaxVCT.cp)) list *
                    SyntaxVCT.xp list))
                  Monad.checkM
  val check_pat_list :
    bool ->
      unit ContextsPiDelta.theta_ext ->
        (SyntaxPED.pexpp, unit) ContextsPiDelta.phi_ext ->
          (SyntaxPED.pexpp, unit) Contexts.gamma_ext ->
            Location.loc ->
              SyntaxPED.patp list ->
                SyntaxVCT.tau list ->
                  (SyntaxVCT.xp list *
                    ((SyntaxVCT.xp * (SyntaxVCT.bp * SyntaxVCT.cp)) list *
                      SyntaxVCT.xp list))
                    Monad.checkM
  val check_pat_vec_list :
    bool ->
      unit ContextsPiDelta.theta_ext ->
        (SyntaxPED.pexpp, unit) ContextsPiDelta.phi_ext ->
          (SyntaxPED.pexpp, unit) Contexts.gamma_ext ->
            Location.loc ->
              SyntaxPED.patp list ->
                SyntaxVCT.order ->
                  SyntaxVCT.bp ->
                    (SyntaxVCT.xp list *
                      ((SyntaxVCT.xp * (SyntaxVCT.bp * SyntaxVCT.cp)) list *
                        SyntaxVCT.xp list))
                      Monad.checkM
  val mk_c_eq : SyntaxVCT.xp -> SyntaxVCT.xp -> SyntaxVCT.cp
  val kvars_of2 :
    SyntaxVCT.tau -> (SyntaxVCT.xp * (SyntaxVCT.bp * SyntaxVCT.cp)) list
  val convert_to_stM :
    SyntaxVCT.tau list ->
      ((SyntaxVCT.xp * (SyntaxVCT.bp * SyntaxVCT.cp)) list *
        (SyntaxVCT.bp list * SyntaxVCT.cp))
        Monad.checkM
  val check_varM :
    (SyntaxPED.pexpp, unit) Contexts.gamma_ext ->
      Location.loc -> SyntaxVCT.xp -> bool Monad.checkM
  val check_varsM :
    (SyntaxPED.pexpp, unit) Contexts.gamma_ext ->
      Location.loc -> SyntaxVCT.xp list -> bool Monad.checkM
  val check_bases : SyntaxVCT.tau list -> SyntaxVCT.bp option
  val mk_eq_proj :
    Location.loc -> SyntaxVCT.xp -> Arith.nat -> Arith.nat -> SyntaxVCT.cp
  val loc_lexp : SyntaxPED.lexpp -> Location.loc
  val check_lexp :
    unit ContextsPiDelta.theta_ext ->
      (SyntaxPED.pexpp, unit) ContextsPiDelta.phi_ext ->
        (SyntaxPED.pexpp, unit) Contexts.gamma_ext ->
          unit ContextsPiDelta.delta_ext ->
            SyntaxPED.lexpp ->
              SyntaxVCT.tau ->
                (SyntaxVCT.xp *
                  ((SyntaxVCT.xp * (SyntaxVCT.bp * SyntaxVCT.cp)) list *
                    SyntaxVCT.xp list))
                  Monad.checkM
  val infer_v :
    unit ContextsPiDelta.theta_ext ->
      (SyntaxPED.pexpp, unit) ContextsPiDelta.phi_ext ->
        (SyntaxPED.pexpp, unit) Contexts.gamma_ext ->
          unit ContextsPiDelta.delta_ext ->
            SyntaxVCT.vp ->
              (SyntaxVCT.xp *
                ((SyntaxVCT.xp * (SyntaxVCT.bp * SyntaxVCT.cp)) list *
                  SyntaxVCT.tau))
                Monad.checkM
  val check_s :
    unit ContextsPiDelta.theta_ext ->
      (SyntaxPED.pexpp, unit) ContextsPiDelta.phi_ext ->
        (SyntaxPED.pexpp, unit) Contexts.gamma_ext ->
          unit ContextsPiDelta.delta_ext ->
            SyntaxPED.ep ->
              SyntaxVCT.tau ->
                (SyntaxPED.pexpp, unit) Contexts.gamma_ext Monad.checkM
  val infer_e_lbind :
    Location.loc ->
      unit ContextsPiDelta.theta_ext ->
        (SyntaxPED.pexpp, unit) ContextsPiDelta.phi_ext ->
          (SyntaxPED.pexpp, unit) Contexts.gamma_ext ->
            unit ContextsPiDelta.delta_ext ->
              SyntaxPED.patp ->
                SyntaxPED.ep ->
                  (SyntaxVCT.xp *
                    ((SyntaxVCT.xp * (SyntaxVCT.bp * SyntaxVCT.cp)) list *
                      (SyntaxVCT.tau * SyntaxVCT.xp list)))
                    Monad.checkM
  val infer_e :
    unit ContextsPiDelta.theta_ext ->
      (SyntaxPED.pexpp, unit) ContextsPiDelta.phi_ext ->
        (SyntaxPED.pexpp, unit) Contexts.gamma_ext ->
          unit ContextsPiDelta.delta_ext ->
            SyntaxPED.ep ->
              (SyntaxVCT.xp *
                ((SyntaxVCT.xp * (SyntaxVCT.bp * SyntaxVCT.cp)) list *
                  SyntaxVCT.tau))
                Monad.checkM
  val infer_app :
    unit ContextsPiDelta.theta_ext ->
      (SyntaxPED.pexpp, unit) ContextsPiDelta.phi_ext ->
        (SyntaxPED.pexpp, unit) Contexts.gamma_ext ->
          unit ContextsPiDelta.delta_ext ->
            (SyntaxVCT.xp * (SyntaxVCT.ap * SyntaxPED.pexpp option)) list ->
              SyntaxPED.ep ->
                (SyntaxVCT.xp *
                  ((SyntaxVCT.xp * (SyntaxVCT.bp * SyntaxVCT.cp)) list *
                    SyntaxVCT.tau))
                  Monad.checkM
  val return_fun :
    SyntaxVCT.tau -> SyntaxVCT.xp * (SyntaxVCT.ap * SyntaxPED.pexpp option)
  val check_funcl :
    unit ContextsPiDelta.theta_ext ->
      (SyntaxPED.pexpp, unit) ContextsPiDelta.phi_ext ->
        (SyntaxPED.pexpp, unit) Contexts.gamma_ext ->
          SyntaxVCT.ap ->
            SyntaxPED.funclp ->
              (unit ContextsPiDelta.theta_ext *
                ((SyntaxPED.pexpp, unit) ContextsPiDelta.phi_ext *
                  (SyntaxPED.pexpp, unit) Contexts.gamma_ext))
                Monad.checkM
  val check_scattered :
    unit ContextsPiDelta.theta_ext ->
      (SyntaxPED.pexpp, unit) ContextsPiDelta.phi_ext ->
        (SyntaxPED.pexpp, unit) Contexts.gamma_ext ->
          SyntaxPED.scattered_defp ->
            (unit ContextsPiDelta.theta_ext *
              ((SyntaxPED.pexpp, unit) ContextsPiDelta.phi_ext *
                (SyntaxPED.pexpp, unit) Contexts.gamma_ext))
              Monad.checkM
  val check_def_funcl :
    unit ContextsPiDelta.theta_ext ->
      (SyntaxPED.pexpp, unit) ContextsPiDelta.phi_ext ->
        (SyntaxPED.pexpp, unit) Contexts.gamma_ext ->
          SyntaxVCT.ap ->
            SyntaxPED.funclp list ->
              (unit ContextsPiDelta.theta_ext *
                ((SyntaxPED.pexpp, unit) ContextsPiDelta.phi_ext *
                  (SyntaxPED.pexpp, unit) Contexts.gamma_ext))
                Monad.checkM
  val check_def :
    unit ContextsPiDelta.theta_ext ->
      (SyntaxPED.pexpp, unit) ContextsPiDelta.phi_ext ->
        (SyntaxPED.pexpp, unit) Contexts.gamma_ext ->
          SyntaxPED.def ->
            (unit ContextsPiDelta.theta_ext *
              ((SyntaxPED.pexpp, unit) ContextsPiDelta.phi_ext *
                (SyntaxPED.pexpp, unit) Contexts.gamma_ext))
              Monad.checkM
  val check_defs :
    unit ContextsPiDelta.theta_ext ->
      (SyntaxPED.pexpp, unit) ContextsPiDelta.phi_ext ->
        (SyntaxPED.pexpp, unit) Contexts.gamma_ext ->
          SyntaxPED.def list ->
            (SyntaxPED.pexpp, unit) Contexts.gamma_ext Monad.checkM
  val fix_defs_p : SyntaxPED.progp -> SyntaxPED.progp
  val check_p_emptyEnv :
    SyntaxPED.progp -> (SyntaxPED.pexpp, unit) Contexts.gamma_ext Monad.checkM
end = struct

let rec pp_b = function SyntaxVCT.B_int -> " int "
               | SyntaxVCT.B_bool -> " bool "
               | SyntaxVCT.B_union (uu, uv) -> " union "
               | SyntaxVCT.B_var v -> "(unknown)"
               | SyntaxVCT.B_tid v -> "(unknown)"
               | SyntaxVCT.B_bit -> "(unknown)"
               | SyntaxVCT.B_unit -> "(unknown)"
               | SyntaxVCT.B_real -> "(unknown)"
               | SyntaxVCT.B_vec (v, va) -> "(unknown)"
               | SyntaxVCT.B_list v -> "(unknown)"
               | SyntaxVCT.B_tuple v -> "(unknown)"
               | SyntaxVCT.B_record v -> "(unknown)"
               | SyntaxVCT.B_undef -> "(unknown)"
               | SyntaxVCT.B_reg -> "(unknown)"
               | SyntaxVCT.B_string -> "(unknown)"
               | SyntaxVCT.B_exception -> "(unknown)"
               | SyntaxVCT.B_finite_set v -> "(unknown)";;

let rec id_of (SyntaxVCT.VNamed s) = s;;

let rec unzip3
  = function [] -> ([], ([], []))
    | (x, (y, z)) :: xyzs ->
        (let (xs, (ys, zs)) = unzip3 xyzs in (x :: xs, (y :: ys, z :: zs)));;

let rec infer_pat
  g loc x2 = match g, loc, x2 with
    g, loc, SyntaxPED.Pp_typ (uu, t, SyntaxPED.Pp_id (uv, x)) ->
      Monad.return
        (SyntaxVCT.VNamed x,
          ([(SyntaxVCT.VNamed x,
              (Contexts.b_of t,
                Contexts.subst_c_x (Contexts.c_of t) (SyntaxVCT.VNamed x)))],
            (Some t, [SyntaxVCT.VNamed x])))
    | g, loc, SyntaxPED.Pp_typ (uw, t, SyntaxPED.Pp_wild ux) ->
        Monad.check_bind
          (Monad.mk_fresh
            [Stringa.Chara
               (false, false, false, false, true, true, true, false);
              Stringa.Chara
                (false, false, true, false, true, true, true, false);
              Stringa.Chara (true, false, false, true, true, true, true, false);
              Stringa.Chara
                (false, false, false, false, true, true, true, false)])
          (fun x ->
            Monad.return
              (x, ([(x, (Contexts.b_of t,
                          Contexts.subst_c_x (Contexts.c_of t) x))],
                    (Some t, [x]))))
    | g, loc, SyntaxPED.Pp_id (v, va) ->
        Monad.return (SyntaxVCT.VNamed "_", ([], (None, [])))
    | g, loc, SyntaxPED.Pp_wild v ->
        Monad.return (SyntaxVCT.VNamed "_", ([], (None, [])))
    | g, loc, SyntaxPED.Pp_lit (v, va) ->
        Monad.return (SyntaxVCT.VNamed "_", ([], (None, [])))
    | g, loc, SyntaxPED.Pp_typ (v, va, SyntaxPED.Pp_lit (vc, vd)) ->
        Monad.return (SyntaxVCT.VNamed "_", ([], (None, [])))
    | g, loc, SyntaxPED.Pp_typ (v, va, SyntaxPED.Pp_typ (vc, vd, ve)) ->
        Monad.return (SyntaxVCT.VNamed "_", ([], (None, [])))
    | g, loc, SyntaxPED.Pp_typ (v, va, SyntaxPED.Pp_app (vc, vd, ve)) ->
        Monad.return (SyntaxVCT.VNamed "_", ([], (None, [])))
    | g, loc, SyntaxPED.Pp_typ (v, va, SyntaxPED.Pp_tup (vc, vd)) ->
        Monad.return (SyntaxVCT.VNamed "_", ([], (None, [])))
    | g, loc, SyntaxPED.Pp_typ (v, va, SyntaxPED.Pp_vector_concat (vc, vd)) ->
        Monad.return (SyntaxVCT.VNamed "_", ([], (None, [])))
    | g, loc, SyntaxPED.Pp_typ (v, va, SyntaxPED.Pp_as_var (vc, vd, ve)) ->
        Monad.return (SyntaxVCT.VNamed "_", ([], (None, [])))
    | g, loc, SyntaxPED.Pp_typ (v, va, SyntaxPED.Pp_as_typ (vc, vd, ve)) ->
        Monad.return (SyntaxVCT.VNamed "_", ([], (None, [])))
    | g, loc, SyntaxPED.Pp_typ (v, va, SyntaxPED.Pp_cons (vc, vd, ve)) ->
        Monad.return (SyntaxVCT.VNamed "_", ([], (None, [])))
    | g, loc, SyntaxPED.Pp_typ (v, va, SyntaxPED.Pp_string_append (vc, vd)) ->
        Monad.return (SyntaxVCT.VNamed "_", ([], (None, [])))
    | g, loc, SyntaxPED.Pp_typ (v, va, SyntaxPED.Pp_vector (vc, vd)) ->
        Monad.return (SyntaxVCT.VNamed "_", ([], (None, [])))
    | g, loc, SyntaxPED.Pp_typ (v, va, SyntaxPED.Pp_list (vc, vd)) ->
        Monad.return (SyntaxVCT.VNamed "_", ([], (None, [])))
    | g, loc, SyntaxPED.Pp_typ (v, va, SyntaxPED.Pp_record (vc, vd)) ->
        Monad.return (SyntaxVCT.VNamed "_", ([], (None, [])))
    | g, loc, SyntaxPED.Pp_app (v, va, vb) ->
        Monad.return (SyntaxVCT.VNamed "_", ([], (None, [])))
    | g, loc, SyntaxPED.Pp_tup (v, va) ->
        Monad.return (SyntaxVCT.VNamed "_", ([], (None, [])))
    | g, loc, SyntaxPED.Pp_vector_concat (v, va) ->
        Monad.return (SyntaxVCT.VNamed "_", ([], (None, [])))
    | g, loc, SyntaxPED.Pp_as_var (v, va, vb) ->
        Monad.return (SyntaxVCT.VNamed "_", ([], (None, [])))
    | g, loc, SyntaxPED.Pp_as_typ (v, va, vb) ->
        Monad.return (SyntaxVCT.VNamed "_", ([], (None, [])))
    | g, loc, SyntaxPED.Pp_cons (v, va, vb) ->
        Monad.return (SyntaxVCT.VNamed "_", ([], (None, [])))
    | g, loc, SyntaxPED.Pp_string_append (v, va) ->
        Monad.return (SyntaxVCT.VNamed "_", ([], (None, [])))
    | g, loc, SyntaxPED.Pp_vector (v, va) ->
        Monad.return (SyntaxVCT.VNamed "_", ([], (None, [])))
    | g, loc, SyntaxPED.Pp_list (v, va) ->
        Monad.return (SyntaxVCT.VNamed "_", ([], (None, [])))
    | g, loc, SyntaxPED.Pp_record (v, va) ->
        Monad.return (SyntaxVCT.VNamed "_", ([], (None, [])));;

let rec kvars_of uu = [];;

let rec tsubst_b_bs
  b x1 = match b, x1 with b, [] -> b
    | ba, (x, b) :: bs -> SyntaxPED.tsubst_bp b x (tsubst_b_bs ba bs);;

let rec subtype
  uu p g x3 ux = match uu, p, g, x3, ux with
    uu, p, g, SyntaxVCT.T_refined_type (uv, SyntaxVCT.B_undef, uw), ux ->
      Monad.return true
    | loc, p, g, SyntaxVCT.T_refined_type (v, SyntaxVCT.B_var vc, vb), t2 ->
        Monad.check_bind
          (Monad.freshen_t
            (SyntaxVCT.T_refined_type (v, SyntaxVCT.B_var vc, vb)))
          (fun t1 ->
            Monad.check_bind (Monad.freshen_t t2)
              (fun t2a ->
                Monad.check_bind
                  (Monad.mk_fresh
                    [Stringa.Chara
                       (true, true, false, false, true, true, true, false);
                      Stringa.Chara
                        (true, false, false, false, false, true, true, false);
                      Stringa.Chara
                        (false, false, true, false, true, true, true, false)])
                  (fun z ->
                    (match
                      Contexts.unify_b (Contexts.b_of t1) (Contexts.b_of t2a)
                      with None ->
                        Monad.check_bind
                          (Monad.return
                            (Satis.valid
                              "Subtype check / Bases don\039t match. Printing G"
                              loc p
                              (Contexts.add_vars_ge g
                                [(z, (Contexts.b_of t1,
                                       Contexts.subst_c_v0 (Contexts.c_of t1)
 (Monad.mk_var z)))])
                              (Contexts.convert_ge [])
                              (Contexts.subst_c_v0 (Contexts.c_of t2a)
                                (Monad.mk_var z))))
                          (fun _ -> Monad.return false)
                      | Some bp ->
                        Monad.return
                          (Satis.valid "Subtype check / Bases match" loc p
                            (Contexts.add_vars_ge g
                              [(z, (tsubst_b_bs (Contexts.b_of t1) bp,
                                     Contexts.subst_c_v0 (Contexts.c_of t1)
                                       (Monad.mk_var z)))])
                            (Contexts.convert_ge [])
                            (Contexts.subst_c_v0 (Contexts.c_of t2a)
                              (Monad.mk_var z)))))))
    | loc, p, g, SyntaxVCT.T_refined_type (v, SyntaxVCT.B_tid vc, vb), t2 ->
        Monad.check_bind
          (Monad.freshen_t
            (SyntaxVCT.T_refined_type (v, SyntaxVCT.B_tid vc, vb)))
          (fun t1 ->
            Monad.check_bind (Monad.freshen_t t2)
              (fun t2a ->
                Monad.check_bind
                  (Monad.mk_fresh
                    [Stringa.Chara
                       (true, true, false, false, true, true, true, false);
                      Stringa.Chara
                        (true, false, false, false, false, true, true, false);
                      Stringa.Chara
                        (false, false, true, false, true, true, true, false)])
                  (fun z ->
                    (match
                      Contexts.unify_b (Contexts.b_of t1) (Contexts.b_of t2a)
                      with None ->
                        Monad.check_bind
                          (Monad.return
                            (Satis.valid
                              "Subtype check / Bases don\039t match. Printing G"
                              loc p
                              (Contexts.add_vars_ge g
                                [(z, (Contexts.b_of t1,
                                       Contexts.subst_c_v0 (Contexts.c_of t1)
 (Monad.mk_var z)))])
                              (Contexts.convert_ge [])
                              (Contexts.subst_c_v0 (Contexts.c_of t2a)
                                (Monad.mk_var z))))
                          (fun _ -> Monad.return false)
                      | Some bp ->
                        Monad.return
                          (Satis.valid "Subtype check / Bases match" loc p
                            (Contexts.add_vars_ge g
                              [(z, (tsubst_b_bs (Contexts.b_of t1) bp,
                                     Contexts.subst_c_v0 (Contexts.c_of t1)
                                       (Monad.mk_var z)))])
                            (Contexts.convert_ge [])
                            (Contexts.subst_c_v0 (Contexts.c_of t2a)
                              (Monad.mk_var z)))))))
    | loc, p, g, SyntaxVCT.T_refined_type (v, SyntaxVCT.B_int, vb), t2 ->
        Monad.check_bind
          (Monad.freshen_t (SyntaxVCT.T_refined_type (v, SyntaxVCT.B_int, vb)))
          (fun t1 ->
            Monad.check_bind (Monad.freshen_t t2)
              (fun t2a ->
                Monad.check_bind
                  (Monad.mk_fresh
                    [Stringa.Chara
                       (true, true, false, false, true, true, true, false);
                      Stringa.Chara
                        (true, false, false, false, false, true, true, false);
                      Stringa.Chara
                        (false, false, true, false, true, true, true, false)])
                  (fun z ->
                    (match
                      Contexts.unify_b (Contexts.b_of t1) (Contexts.b_of t2a)
                      with None ->
                        Monad.check_bind
                          (Monad.return
                            (Satis.valid
                              "Subtype check / Bases don\039t match. Printing G"
                              loc p
                              (Contexts.add_vars_ge g
                                [(z, (Contexts.b_of t1,
                                       Contexts.subst_c_v0 (Contexts.c_of t1)
 (Monad.mk_var z)))])
                              (Contexts.convert_ge [])
                              (Contexts.subst_c_v0 (Contexts.c_of t2a)
                                (Monad.mk_var z))))
                          (fun _ -> Monad.return false)
                      | Some bp ->
                        Monad.return
                          (Satis.valid "Subtype check / Bases match" loc p
                            (Contexts.add_vars_ge g
                              [(z, (tsubst_b_bs (Contexts.b_of t1) bp,
                                     Contexts.subst_c_v0 (Contexts.c_of t1)
                                       (Monad.mk_var z)))])
                            (Contexts.convert_ge [])
                            (Contexts.subst_c_v0 (Contexts.c_of t2a)
                              (Monad.mk_var z)))))))
    | loc, p, g, SyntaxVCT.T_refined_type (v, SyntaxVCT.B_bool, vb), t2 ->
        Monad.check_bind
          (Monad.freshen_t (SyntaxVCT.T_refined_type (v, SyntaxVCT.B_bool, vb)))
          (fun t1 ->
            Monad.check_bind (Monad.freshen_t t2)
              (fun t2a ->
                Monad.check_bind
                  (Monad.mk_fresh
                    [Stringa.Chara
                       (true, true, false, false, true, true, true, false);
                      Stringa.Chara
                        (true, false, false, false, false, true, true, false);
                      Stringa.Chara
                        (false, false, true, false, true, true, true, false)])
                  (fun z ->
                    (match
                      Contexts.unify_b (Contexts.b_of t1) (Contexts.b_of t2a)
                      with None ->
                        Monad.check_bind
                          (Monad.return
                            (Satis.valid
                              "Subtype check / Bases don\039t match. Printing G"
                              loc p
                              (Contexts.add_vars_ge g
                                [(z, (Contexts.b_of t1,
                                       Contexts.subst_c_v0 (Contexts.c_of t1)
 (Monad.mk_var z)))])
                              (Contexts.convert_ge [])
                              (Contexts.subst_c_v0 (Contexts.c_of t2a)
                                (Monad.mk_var z))))
                          (fun _ -> Monad.return false)
                      | Some bp ->
                        Monad.return
                          (Satis.valid "Subtype check / Bases match" loc p
                            (Contexts.add_vars_ge g
                              [(z, (tsubst_b_bs (Contexts.b_of t1) bp,
                                     Contexts.subst_c_v0 (Contexts.c_of t1)
                                       (Monad.mk_var z)))])
                            (Contexts.convert_ge [])
                            (Contexts.subst_c_v0 (Contexts.c_of t2a)
                              (Monad.mk_var z)))))))
    | loc, p, g, SyntaxVCT.T_refined_type (v, SyntaxVCT.B_bit, vb), t2 ->
        Monad.check_bind
          (Monad.freshen_t (SyntaxVCT.T_refined_type (v, SyntaxVCT.B_bit, vb)))
          (fun t1 ->
            Monad.check_bind (Monad.freshen_t t2)
              (fun t2a ->
                Monad.check_bind
                  (Monad.mk_fresh
                    [Stringa.Chara
                       (true, true, false, false, true, true, true, false);
                      Stringa.Chara
                        (true, false, false, false, false, true, true, false);
                      Stringa.Chara
                        (false, false, true, false, true, true, true, false)])
                  (fun z ->
                    (match
                      Contexts.unify_b (Contexts.b_of t1) (Contexts.b_of t2a)
                      with None ->
                        Monad.check_bind
                          (Monad.return
                            (Satis.valid
                              "Subtype check / Bases don\039t match. Printing G"
                              loc p
                              (Contexts.add_vars_ge g
                                [(z, (Contexts.b_of t1,
                                       Contexts.subst_c_v0 (Contexts.c_of t1)
 (Monad.mk_var z)))])
                              (Contexts.convert_ge [])
                              (Contexts.subst_c_v0 (Contexts.c_of t2a)
                                (Monad.mk_var z))))
                          (fun _ -> Monad.return false)
                      | Some bp ->
                        Monad.return
                          (Satis.valid "Subtype check / Bases match" loc p
                            (Contexts.add_vars_ge g
                              [(z, (tsubst_b_bs (Contexts.b_of t1) bp,
                                     Contexts.subst_c_v0 (Contexts.c_of t1)
                                       (Monad.mk_var z)))])
                            (Contexts.convert_ge [])
                            (Contexts.subst_c_v0 (Contexts.c_of t2a)
                              (Monad.mk_var z)))))))
    | loc, p, g, SyntaxVCT.T_refined_type (v, SyntaxVCT.B_unit, vb), t2 ->
        Monad.check_bind
          (Monad.freshen_t (SyntaxVCT.T_refined_type (v, SyntaxVCT.B_unit, vb)))
          (fun t1 ->
            Monad.check_bind (Monad.freshen_t t2)
              (fun t2a ->
                Monad.check_bind
                  (Monad.mk_fresh
                    [Stringa.Chara
                       (true, true, false, false, true, true, true, false);
                      Stringa.Chara
                        (true, false, false, false, false, true, true, false);
                      Stringa.Chara
                        (false, false, true, false, true, true, true, false)])
                  (fun z ->
                    (match
                      Contexts.unify_b (Contexts.b_of t1) (Contexts.b_of t2a)
                      with None ->
                        Monad.check_bind
                          (Monad.return
                            (Satis.valid
                              "Subtype check / Bases don\039t match. Printing G"
                              loc p
                              (Contexts.add_vars_ge g
                                [(z, (Contexts.b_of t1,
                                       Contexts.subst_c_v0 (Contexts.c_of t1)
 (Monad.mk_var z)))])
                              (Contexts.convert_ge [])
                              (Contexts.subst_c_v0 (Contexts.c_of t2a)
                                (Monad.mk_var z))))
                          (fun _ -> Monad.return false)
                      | Some bp ->
                        Monad.return
                          (Satis.valid "Subtype check / Bases match" loc p
                            (Contexts.add_vars_ge g
                              [(z, (tsubst_b_bs (Contexts.b_of t1) bp,
                                     Contexts.subst_c_v0 (Contexts.c_of t1)
                                       (Monad.mk_var z)))])
                            (Contexts.convert_ge [])
                            (Contexts.subst_c_v0 (Contexts.c_of t2a)
                              (Monad.mk_var z)))))))
    | loc, p, g, SyntaxVCT.T_refined_type (v, SyntaxVCT.B_real, vb), t2 ->
        Monad.check_bind
          (Monad.freshen_t (SyntaxVCT.T_refined_type (v, SyntaxVCT.B_real, vb)))
          (fun t1 ->
            Monad.check_bind (Monad.freshen_t t2)
              (fun t2a ->
                Monad.check_bind
                  (Monad.mk_fresh
                    [Stringa.Chara
                       (true, true, false, false, true, true, true, false);
                      Stringa.Chara
                        (true, false, false, false, false, true, true, false);
                      Stringa.Chara
                        (false, false, true, false, true, true, true, false)])
                  (fun z ->
                    (match
                      Contexts.unify_b (Contexts.b_of t1) (Contexts.b_of t2a)
                      with None ->
                        Monad.check_bind
                          (Monad.return
                            (Satis.valid
                              "Subtype check / Bases don\039t match. Printing G"
                              loc p
                              (Contexts.add_vars_ge g
                                [(z, (Contexts.b_of t1,
                                       Contexts.subst_c_v0 (Contexts.c_of t1)
 (Monad.mk_var z)))])
                              (Contexts.convert_ge [])
                              (Contexts.subst_c_v0 (Contexts.c_of t2a)
                                (Monad.mk_var z))))
                          (fun _ -> Monad.return false)
                      | Some bp ->
                        Monad.return
                          (Satis.valid "Subtype check / Bases match" loc p
                            (Contexts.add_vars_ge g
                              [(z, (tsubst_b_bs (Contexts.b_of t1) bp,
                                     Contexts.subst_c_v0 (Contexts.c_of t1)
                                       (Monad.mk_var z)))])
                            (Contexts.convert_ge [])
                            (Contexts.subst_c_v0 (Contexts.c_of t2a)
                              (Monad.mk_var z)))))))
    | loc, p, g, SyntaxVCT.T_refined_type (v, SyntaxVCT.B_vec (vc, vd), vb), t2
        -> Monad.check_bind
             (Monad.freshen_t
               (SyntaxVCT.T_refined_type (v, SyntaxVCT.B_vec (vc, vd), vb)))
             (fun t1 ->
               Monad.check_bind (Monad.freshen_t t2)
                 (fun t2a ->
                   Monad.check_bind
                     (Monad.mk_fresh
                       [Stringa.Chara
                          (true, true, false, false, true, true, true, false);
                         Stringa.Chara
                           (true, false, false, false, false, true, true,
                             false);
                         Stringa.Chara
                           (false, false, true, false, true, true, true,
                             false)])
                     (fun z ->
                       (match
                         Contexts.unify_b (Contexts.b_of t1) (Contexts.b_of t2a)
                         with None ->
                           Monad.check_bind
                             (Monad.return
                               (Satis.valid
                                 "Subtype check / Bases don\039t match. Printing G"
                                 loc p
                                 (Contexts.add_vars_ge g
                                   [(z, (Contexts.b_of t1,
  Contexts.subst_c_v0 (Contexts.c_of t1) (Monad.mk_var z)))])
                                 (Contexts.convert_ge [])
                                 (Contexts.subst_c_v0 (Contexts.c_of t2a)
                                   (Monad.mk_var z))))
                             (fun _ -> Monad.return false)
                         | Some bp ->
                           Monad.return
                             (Satis.valid "Subtype check / Bases match" loc p
                               (Contexts.add_vars_ge g
                                 [(z, (tsubst_b_bs (Contexts.b_of t1) bp,
Contexts.subst_c_v0 (Contexts.c_of t1) (Monad.mk_var z)))])
                               (Contexts.convert_ge [])
                               (Contexts.subst_c_v0 (Contexts.c_of t2a)
                                 (Monad.mk_var z)))))))
    | loc, p, g, SyntaxVCT.T_refined_type (v, SyntaxVCT.B_list vc, vb), t2 ->
        Monad.check_bind
          (Monad.freshen_t
            (SyntaxVCT.T_refined_type (v, SyntaxVCT.B_list vc, vb)))
          (fun t1 ->
            Monad.check_bind (Monad.freshen_t t2)
              (fun t2a ->
                Monad.check_bind
                  (Monad.mk_fresh
                    [Stringa.Chara
                       (true, true, false, false, true, true, true, false);
                      Stringa.Chara
                        (true, false, false, false, false, true, true, false);
                      Stringa.Chara
                        (false, false, true, false, true, true, true, false)])
                  (fun z ->
                    (match
                      Contexts.unify_b (Contexts.b_of t1) (Contexts.b_of t2a)
                      with None ->
                        Monad.check_bind
                          (Monad.return
                            (Satis.valid
                              "Subtype check / Bases don\039t match. Printing G"
                              loc p
                              (Contexts.add_vars_ge g
                                [(z, (Contexts.b_of t1,
                                       Contexts.subst_c_v0 (Contexts.c_of t1)
 (Monad.mk_var z)))])
                              (Contexts.convert_ge [])
                              (Contexts.subst_c_v0 (Contexts.c_of t2a)
                                (Monad.mk_var z))))
                          (fun _ -> Monad.return false)
                      | Some bp ->
                        Monad.return
                          (Satis.valid "Subtype check / Bases match" loc p
                            (Contexts.add_vars_ge g
                              [(z, (tsubst_b_bs (Contexts.b_of t1) bp,
                                     Contexts.subst_c_v0 (Contexts.c_of t1)
                                       (Monad.mk_var z)))])
                            (Contexts.convert_ge [])
                            (Contexts.subst_c_v0 (Contexts.c_of t2a)
                              (Monad.mk_var z)))))))
    | loc, p, g, SyntaxVCT.T_refined_type (v, SyntaxVCT.B_tuple vc, vb), t2 ->
        Monad.check_bind
          (Monad.freshen_t
            (SyntaxVCT.T_refined_type (v, SyntaxVCT.B_tuple vc, vb)))
          (fun t1 ->
            Monad.check_bind (Monad.freshen_t t2)
              (fun t2a ->
                Monad.check_bind
                  (Monad.mk_fresh
                    [Stringa.Chara
                       (true, true, false, false, true, true, true, false);
                      Stringa.Chara
                        (true, false, false, false, false, true, true, false);
                      Stringa.Chara
                        (false, false, true, false, true, true, true, false)])
                  (fun z ->
                    (match
                      Contexts.unify_b (Contexts.b_of t1) (Contexts.b_of t2a)
                      with None ->
                        Monad.check_bind
                          (Monad.return
                            (Satis.valid
                              "Subtype check / Bases don\039t match. Printing G"
                              loc p
                              (Contexts.add_vars_ge g
                                [(z, (Contexts.b_of t1,
                                       Contexts.subst_c_v0 (Contexts.c_of t1)
 (Monad.mk_var z)))])
                              (Contexts.convert_ge [])
                              (Contexts.subst_c_v0 (Contexts.c_of t2a)
                                (Monad.mk_var z))))
                          (fun _ -> Monad.return false)
                      | Some bp ->
                        Monad.return
                          (Satis.valid "Subtype check / Bases match" loc p
                            (Contexts.add_vars_ge g
                              [(z, (tsubst_b_bs (Contexts.b_of t1) bp,
                                     Contexts.subst_c_v0 (Contexts.c_of t1)
                                       (Monad.mk_var z)))])
                            (Contexts.convert_ge [])
                            (Contexts.subst_c_v0 (Contexts.c_of t2a)
                              (Monad.mk_var z)))))))
    | loc, p, g, SyntaxVCT.T_refined_type (v, SyntaxVCT.B_union (vc, vd), vb),
        t2
        -> Monad.check_bind
             (Monad.freshen_t
               (SyntaxVCT.T_refined_type (v, SyntaxVCT.B_union (vc, vd), vb)))
             (fun t1 ->
               Monad.check_bind (Monad.freshen_t t2)
                 (fun t2a ->
                   Monad.check_bind
                     (Monad.mk_fresh
                       [Stringa.Chara
                          (true, true, false, false, true, true, true, false);
                         Stringa.Chara
                           (true, false, false, false, false, true, true,
                             false);
                         Stringa.Chara
                           (false, false, true, false, true, true, true,
                             false)])
                     (fun z ->
                       (match
                         Contexts.unify_b (Contexts.b_of t1) (Contexts.b_of t2a)
                         with None ->
                           Monad.check_bind
                             (Monad.return
                               (Satis.valid
                                 "Subtype check / Bases don\039t match. Printing G"
                                 loc p
                                 (Contexts.add_vars_ge g
                                   [(z, (Contexts.b_of t1,
  Contexts.subst_c_v0 (Contexts.c_of t1) (Monad.mk_var z)))])
                                 (Contexts.convert_ge [])
                                 (Contexts.subst_c_v0 (Contexts.c_of t2a)
                                   (Monad.mk_var z))))
                             (fun _ -> Monad.return false)
                         | Some bp ->
                           Monad.return
                             (Satis.valid "Subtype check / Bases match" loc p
                               (Contexts.add_vars_ge g
                                 [(z, (tsubst_b_bs (Contexts.b_of t1) bp,
Contexts.subst_c_v0 (Contexts.c_of t1) (Monad.mk_var z)))])
                               (Contexts.convert_ge [])
                               (Contexts.subst_c_v0 (Contexts.c_of t2a)
                                 (Monad.mk_var z)))))))
    | loc, p, g, SyntaxVCT.T_refined_type (v, SyntaxVCT.B_record vc, vb), t2 ->
        Monad.check_bind
          (Monad.freshen_t
            (SyntaxVCT.T_refined_type (v, SyntaxVCT.B_record vc, vb)))
          (fun t1 ->
            Monad.check_bind (Monad.freshen_t t2)
              (fun t2a ->
                Monad.check_bind
                  (Monad.mk_fresh
                    [Stringa.Chara
                       (true, true, false, false, true, true, true, false);
                      Stringa.Chara
                        (true, false, false, false, false, true, true, false);
                      Stringa.Chara
                        (false, false, true, false, true, true, true, false)])
                  (fun z ->
                    (match
                      Contexts.unify_b (Contexts.b_of t1) (Contexts.b_of t2a)
                      with None ->
                        Monad.check_bind
                          (Monad.return
                            (Satis.valid
                              "Subtype check / Bases don\039t match. Printing G"
                              loc p
                              (Contexts.add_vars_ge g
                                [(z, (Contexts.b_of t1,
                                       Contexts.subst_c_v0 (Contexts.c_of t1)
 (Monad.mk_var z)))])
                              (Contexts.convert_ge [])
                              (Contexts.subst_c_v0 (Contexts.c_of t2a)
                                (Monad.mk_var z))))
                          (fun _ -> Monad.return false)
                      | Some bp ->
                        Monad.return
                          (Satis.valid "Subtype check / Bases match" loc p
                            (Contexts.add_vars_ge g
                              [(z, (tsubst_b_bs (Contexts.b_of t1) bp,
                                     Contexts.subst_c_v0 (Contexts.c_of t1)
                                       (Monad.mk_var z)))])
                            (Contexts.convert_ge [])
                            (Contexts.subst_c_v0 (Contexts.c_of t2a)
                              (Monad.mk_var z)))))))
    | loc, p, g, SyntaxVCT.T_refined_type (v, SyntaxVCT.B_reg, vb), t2 ->
        Monad.check_bind
          (Monad.freshen_t (SyntaxVCT.T_refined_type (v, SyntaxVCT.B_reg, vb)))
          (fun t1 ->
            Monad.check_bind (Monad.freshen_t t2)
              (fun t2a ->
                Monad.check_bind
                  (Monad.mk_fresh
                    [Stringa.Chara
                       (true, true, false, false, true, true, true, false);
                      Stringa.Chara
                        (true, false, false, false, false, true, true, false);
                      Stringa.Chara
                        (false, false, true, false, true, true, true, false)])
                  (fun z ->
                    (match
                      Contexts.unify_b (Contexts.b_of t1) (Contexts.b_of t2a)
                      with None ->
                        Monad.check_bind
                          (Monad.return
                            (Satis.valid
                              "Subtype check / Bases don\039t match. Printing G"
                              loc p
                              (Contexts.add_vars_ge g
                                [(z, (Contexts.b_of t1,
                                       Contexts.subst_c_v0 (Contexts.c_of t1)
 (Monad.mk_var z)))])
                              (Contexts.convert_ge [])
                              (Contexts.subst_c_v0 (Contexts.c_of t2a)
                                (Monad.mk_var z))))
                          (fun _ -> Monad.return false)
                      | Some bp ->
                        Monad.return
                          (Satis.valid "Subtype check / Bases match" loc p
                            (Contexts.add_vars_ge g
                              [(z, (tsubst_b_bs (Contexts.b_of t1) bp,
                                     Contexts.subst_c_v0 (Contexts.c_of t1)
                                       (Monad.mk_var z)))])
                            (Contexts.convert_ge [])
                            (Contexts.subst_c_v0 (Contexts.c_of t2a)
                              (Monad.mk_var z)))))))
    | loc, p, g, SyntaxVCT.T_refined_type (v, SyntaxVCT.B_string, vb), t2 ->
        Monad.check_bind
          (Monad.freshen_t
            (SyntaxVCT.T_refined_type (v, SyntaxVCT.B_string, vb)))
          (fun t1 ->
            Monad.check_bind (Monad.freshen_t t2)
              (fun t2a ->
                Monad.check_bind
                  (Monad.mk_fresh
                    [Stringa.Chara
                       (true, true, false, false, true, true, true, false);
                      Stringa.Chara
                        (true, false, false, false, false, true, true, false);
                      Stringa.Chara
                        (false, false, true, false, true, true, true, false)])
                  (fun z ->
                    (match
                      Contexts.unify_b (Contexts.b_of t1) (Contexts.b_of t2a)
                      with None ->
                        Monad.check_bind
                          (Monad.return
                            (Satis.valid
                              "Subtype check / Bases don\039t match. Printing G"
                              loc p
                              (Contexts.add_vars_ge g
                                [(z, (Contexts.b_of t1,
                                       Contexts.subst_c_v0 (Contexts.c_of t1)
 (Monad.mk_var z)))])
                              (Contexts.convert_ge [])
                              (Contexts.subst_c_v0 (Contexts.c_of t2a)
                                (Monad.mk_var z))))
                          (fun _ -> Monad.return false)
                      | Some bp ->
                        Monad.return
                          (Satis.valid "Subtype check / Bases match" loc p
                            (Contexts.add_vars_ge g
                              [(z, (tsubst_b_bs (Contexts.b_of t1) bp,
                                     Contexts.subst_c_v0 (Contexts.c_of t1)
                                       (Monad.mk_var z)))])
                            (Contexts.convert_ge [])
                            (Contexts.subst_c_v0 (Contexts.c_of t2a)
                              (Monad.mk_var z)))))))
    | loc, p, g, SyntaxVCT.T_refined_type (v, SyntaxVCT.B_exception, vb), t2 ->
        Monad.check_bind
          (Monad.freshen_t
            (SyntaxVCT.T_refined_type (v, SyntaxVCT.B_exception, vb)))
          (fun t1 ->
            Monad.check_bind (Monad.freshen_t t2)
              (fun t2a ->
                Monad.check_bind
                  (Monad.mk_fresh
                    [Stringa.Chara
                       (true, true, false, false, true, true, true, false);
                      Stringa.Chara
                        (true, false, false, false, false, true, true, false);
                      Stringa.Chara
                        (false, false, true, false, true, true, true, false)])
                  (fun z ->
                    (match
                      Contexts.unify_b (Contexts.b_of t1) (Contexts.b_of t2a)
                      with None ->
                        Monad.check_bind
                          (Monad.return
                            (Satis.valid
                              "Subtype check / Bases don\039t match. Printing G"
                              loc p
                              (Contexts.add_vars_ge g
                                [(z, (Contexts.b_of t1,
                                       Contexts.subst_c_v0 (Contexts.c_of t1)
 (Monad.mk_var z)))])
                              (Contexts.convert_ge [])
                              (Contexts.subst_c_v0 (Contexts.c_of t2a)
                                (Monad.mk_var z))))
                          (fun _ -> Monad.return false)
                      | Some bp ->
                        Monad.return
                          (Satis.valid "Subtype check / Bases match" loc p
                            (Contexts.add_vars_ge g
                              [(z, (tsubst_b_bs (Contexts.b_of t1) bp,
                                     Contexts.subst_c_v0 (Contexts.c_of t1)
                                       (Monad.mk_var z)))])
                            (Contexts.convert_ge [])
                            (Contexts.subst_c_v0 (Contexts.c_of t2a)
                              (Monad.mk_var z)))))))
    | loc, p, g, SyntaxVCT.T_refined_type (v, SyntaxVCT.B_finite_set vc, vb), t2
        -> Monad.check_bind
             (Monad.freshen_t
               (SyntaxVCT.T_refined_type (v, SyntaxVCT.B_finite_set vc, vb)))
             (fun t1 ->
               Monad.check_bind (Monad.freshen_t t2)
                 (fun t2a ->
                   Monad.check_bind
                     (Monad.mk_fresh
                       [Stringa.Chara
                          (true, true, false, false, true, true, true, false);
                         Stringa.Chara
                           (true, false, false, false, false, true, true,
                             false);
                         Stringa.Chara
                           (false, false, true, false, true, true, true,
                             false)])
                     (fun z ->
                       (match
                         Contexts.unify_b (Contexts.b_of t1) (Contexts.b_of t2a)
                         with None ->
                           Monad.check_bind
                             (Monad.return
                               (Satis.valid
                                 "Subtype check / Bases don\039t match. Printing G"
                                 loc p
                                 (Contexts.add_vars_ge g
                                   [(z, (Contexts.b_of t1,
  Contexts.subst_c_v0 (Contexts.c_of t1) (Monad.mk_var z)))])
                                 (Contexts.convert_ge [])
                                 (Contexts.subst_c_v0 (Contexts.c_of t2a)
                                   (Monad.mk_var z))))
                             (fun _ -> Monad.return false)
                         | Some bp ->
                           Monad.return
                             (Satis.valid "Subtype check / Bases match" loc p
                               (Contexts.add_vars_ge g
                                 [(z, (tsubst_b_bs (Contexts.b_of t1) bp,
Contexts.subst_c_v0 (Contexts.c_of t1) (Monad.mk_var z)))])
                               (Contexts.convert_ge [])
                               (Contexts.subst_c_v0 (Contexts.c_of t2a)
                                 (Monad.mk_var z)))))));;

let rec check_pat
  uu ta p gamma x4 t = match uu, ta, p, gamma, x4, t with
    uu, ta, p, gamma, SyntaxPED.Pp_wild uv, t ->
      Monad.check_bind
        (Monad.mk_fresh
          [Stringa.Chara (false, false, false, false, true, true, true, false);
            Stringa.Chara (true, false, false, false, false, true, true, false);
            Stringa.Chara (false, false, true, false, true, true, true, false)])
        (fun z ->
          Monad.check_bind (Monad.freshen_t t)
            (fun tb ->
              Monad.return
                (z, ([(z, (Contexts.b_of tb,
                            Contexts.subst_c_v0 (Contexts.c_of tb)
                              (Monad.mk_var z)))],
                      []))))
    | uw, ta, p, gamma, SyntaxPED.Pp_id (l1, x), t ->
        Monad.check_bind (Monad.freshen_t t)
          (fun tb ->
            (match ContextsPiDelta.lookup_constr_union ta x
              with None ->
                Monad.return
                  (SyntaxVCT.VNamed x,
                    ((SyntaxVCT.VNamed x,
                       (Contexts.b_of tb,
                         Contexts.subst_c_x (Contexts.c_of tb)
                           (SyntaxVCT.VNamed x))) ::
                       kvars_of tb,
                      [SyntaxVCT.VNamed x]))
              | Some tba ->
                Monad.check_bind (subtype Location.Loc_unknown ta gamma tb tba)
                  (fun b ->
                    (if b then Monad.check_bind
                                 (Monad.mk_fresh
                                   [Stringa.Chara
                                      (false, false, false, false, true, true,
true, false);
                                     Stringa.Chara
                                       (true, false, false, true, false, true,
 true, false);
                                     Stringa.Chara
                                       (false, false, true, false, false, true,
 true, false)])
                                 (fun xa ->
                                   Monad.return
                                     (xa, ((xa,
     (Contexts.b_of tb, Contexts.subst_c_x (Contexts.c_of tb) xa)) ::
     kvars_of tb,
    [])))
                      else Monad.fail
                             (Monad.CheckFail
                               (l1, gamma, "Pp_id / constructor", tba, tb))))))
    | litok, t, p, gamma, SyntaxPED.Pp_tup (loc, ps),
        SyntaxVCT.T_refined_type (zvarin, SyntaxVCT.B_tuple bs, c)
        -> Monad.check_bind
             (Monad.mk_fresh
               [Stringa.Chara
                  (false, false, false, false, true, true, true, false);
                 Stringa.Chara
                   (true, false, false, false, false, true, true, false);
                 Stringa.Chara
                   (false, false, true, false, true, true, true, false)])
             (fun z ->
               Monad.check_bind
                 (Monad.return
                   (Contexts.mapi
                     (fun i b ->
                       SyntaxVCT.T_refined_type
                         (SyntaxVCT.VIndex, b,
                           SyntaxVCT.C_eq
                             (SyntaxVCT.CE_val
                                (SyntaxVCT.V_var SyntaxVCT.VIndex),
                               SyntaxVCT.CE_val
                                 (Contexts.tuple_proj
                                   (Arith.plus_nat i Arith.one_nat)
                                   (Lista.size_list bs) (SyntaxVCT.V_var z)))))
                     bs))
                 (fun ts ->
                   Monad.check_bind
                     (check_pat_list litok t p
                       (Contexts.add_var (Contexts.add_vars_ge gamma [])
                         (z, Contexts.GEPair
                               (SyntaxVCT.B_tuple bs,
                                 Contexts.subst_c_v0 c (SyntaxVCT.V_var z))))
                       loc ps ts)
                     (fun (xs, (gs, vars)) ->
                       Monad.check_bind
                         (Monad.return
                           (SyntaxVCT.C_conj
                             (Contexts.mk_x_eq_c_tuple z xs,
                               Contexts.subst_c_v0 c (SyntaxVCT.V_var z))))
                         (fun tup_c ->
                           Monad.check_bind
                             (Monad.return
                               (Contexts.mk_x_eq_c_tuple SyntaxVCT.VIndex xs))
                             (fun tup_c2 ->
                               Monad.check_bind
                                 (subtype loc t
                                   (Contexts.add_var
                                     (Contexts.add_vars_ge gamma gs)
                                     (z, Contexts.GEPair
   (SyntaxVCT.B_tuple bs, Contexts.subst_c_v0 c (SyntaxVCT.V_var z))))
                                   (SyntaxVCT.T_refined_type
                                     (SyntaxVCT.VIndex, SyntaxVCT.B_tuple bs,
                                       tup_c2))
                                   (SyntaxVCT.T_refined_type
                                     (zvarin, SyntaxVCT.B_tuple bs, c)))
                                 (fun b ->
                                   (if b then Monad.return
        (z, ((z, (SyntaxVCT.B_tuple bs, tup_c)) :: gs @ [], vars))
                                     else Monad.fail
    (Monad.CheckFail
      (loc, gamma, "check_pat Tuple",
        SyntaxVCT.T_refined_type (zvarin, SyntaxVCT.B_tuple bs, c),
        SyntaxVCT.T_refined_type
          (SyntaxVCT.VIndex, SyntaxVCT.B_tuple bs, tup_c2))))))))))
    | ux, uy, uz, va, SyntaxPED.Pp_tup (loc, vb),
        SyntaxVCT.T_refined_type (v, SyntaxVCT.B_var ve, vd)
        -> Monad.fail (Monad.TypeError (loc, "check_pat Pp_tup"))
    | ux, uy, uz, va, SyntaxPED.Pp_tup (loc, vb),
        SyntaxVCT.T_refined_type (v, SyntaxVCT.B_tid ve, vd)
        -> Monad.fail (Monad.TypeError (loc, "check_pat Pp_tup"))
    | ux, uy, uz, va, SyntaxPED.Pp_tup (loc, vb),
        SyntaxVCT.T_refined_type (v, SyntaxVCT.B_int, vd)
        -> Monad.fail (Monad.TypeError (loc, "check_pat Pp_tup"))
    | ux, uy, uz, va, SyntaxPED.Pp_tup (loc, vb),
        SyntaxVCT.T_refined_type (v, SyntaxVCT.B_bool, vd)
        -> Monad.fail (Monad.TypeError (loc, "check_pat Pp_tup"))
    | ux, uy, uz, va, SyntaxPED.Pp_tup (loc, vb),
        SyntaxVCT.T_refined_type (v, SyntaxVCT.B_bit, vd)
        -> Monad.fail (Monad.TypeError (loc, "check_pat Pp_tup"))
    | ux, uy, uz, va, SyntaxPED.Pp_tup (loc, vb),
        SyntaxVCT.T_refined_type (v, SyntaxVCT.B_unit, vd)
        -> Monad.fail (Monad.TypeError (loc, "check_pat Pp_tup"))
    | ux, uy, uz, va, SyntaxPED.Pp_tup (loc, vb),
        SyntaxVCT.T_refined_type (v, SyntaxVCT.B_real, vd)
        -> Monad.fail (Monad.TypeError (loc, "check_pat Pp_tup"))
    | ux, uy, uz, va, SyntaxPED.Pp_tup (loc, vb),
        SyntaxVCT.T_refined_type (v, SyntaxVCT.B_vec (ve, vf), vd)
        -> Monad.fail (Monad.TypeError (loc, "check_pat Pp_tup"))
    | ux, uy, uz, va, SyntaxPED.Pp_tup (loc, vb),
        SyntaxVCT.T_refined_type (v, SyntaxVCT.B_list ve, vd)
        -> Monad.fail (Monad.TypeError (loc, "check_pat Pp_tup"))
    | ux, uy, uz, va, SyntaxPED.Pp_tup (loc, vb),
        SyntaxVCT.T_refined_type (v, SyntaxVCT.B_union (ve, vf), vd)
        -> Monad.fail (Monad.TypeError (loc, "check_pat Pp_tup"))
    | ux, uy, uz, va, SyntaxPED.Pp_tup (loc, vb),
        SyntaxVCT.T_refined_type (v, SyntaxVCT.B_record ve, vd)
        -> Monad.fail (Monad.TypeError (loc, "check_pat Pp_tup"))
    | ux, uy, uz, va, SyntaxPED.Pp_tup (loc, vb),
        SyntaxVCT.T_refined_type (v, SyntaxVCT.B_undef, vd)
        -> Monad.fail (Monad.TypeError (loc, "check_pat Pp_tup"))
    | ux, uy, uz, va, SyntaxPED.Pp_tup (loc, vb),
        SyntaxVCT.T_refined_type (v, SyntaxVCT.B_reg, vd)
        -> Monad.fail (Monad.TypeError (loc, "check_pat Pp_tup"))
    | ux, uy, uz, va, SyntaxPED.Pp_tup (loc, vb),
        SyntaxVCT.T_refined_type (v, SyntaxVCT.B_string, vd)
        -> Monad.fail (Monad.TypeError (loc, "check_pat Pp_tup"))
    | ux, uy, uz, va, SyntaxPED.Pp_tup (loc, vb),
        SyntaxVCT.T_refined_type (v, SyntaxVCT.B_exception, vd)
        -> Monad.fail (Monad.TypeError (loc, "check_pat Pp_tup"))
    | ux, uy, uz, va, SyntaxPED.Pp_tup (loc, vb),
        SyntaxVCT.T_refined_type (v, SyntaxVCT.B_finite_set ve, vd)
        -> Monad.fail (Monad.TypeError (loc, "check_pat Pp_tup"))
    | litok, ta, p, gamma, SyntaxPED.Pp_lit (loc, l), t ->
        (if SyntaxVCT.equal_bpa (Contexts.b_of t) (Contexts.literal_type l)
          then Monad.check_bind
                 (Monad.mk_fresh
                   [Stringa.Chara
                      (false, false, false, false, true, true, true, false);
                     Stringa.Chara
                       (true, false, false, false, false, true, true, false);
                     Stringa.Chara
                       (false, false, true, false, true, true, true, false)])
                 (fun z ->
                   Monad.return
                     (z, ([(z, (Contexts.b_of t, Contexts.mk_l_eq_c z l))],
                           [])))
          else Monad.fail
                 (Monad.TypeError
                   (loc, (("Literal base type mismatched. Expected " ^
                            pp_b (Contexts.b_of t)) ^
                           " Found: ") ^
                           pp_b (Contexts.literal_type l))))
    | litok, t, p, gamma, SyntaxPED.Pp_vector_concat (loc, vs),
        SyntaxVCT.T_refined_type (vc, SyntaxVCT.B_vec (odr, b), c)
        -> Monad.check_bind (check_pat_vec_list litok t p gamma loc vs odr b)
             (fun (_, (gs, vars)) ->
               Monad.check_bind
                 (Monad.mk_fresh
                   [Stringa.Chara
                      (false, false, false, false, true, true, true, false);
                     Stringa.Chara
                       (true, false, false, false, false, true, true, false);
                     Stringa.Chara
                       (false, false, true, false, true, true, true, false)])
                 (fun z ->
                   Monad.return
                     (z, ((z, (SyntaxVCT.B_vec (odr, b), SyntaxVCT.C_true)) ::
                            gs,
                           vars))))
    | vd, t, p, gamma, SyntaxPED.Pp_vector_concat (loc, vs),
        SyntaxVCT.T_refined_type (ve, SyntaxVCT.B_var v, c)
        -> Monad.fail (Monad.TypeError (loc, "Pp_vec_concat"))
    | vd, t, p, gamma, SyntaxPED.Pp_vector_concat (loc, vs),
        SyntaxVCT.T_refined_type (ve, SyntaxVCT.B_tid v, c)
        -> Monad.fail (Monad.TypeError (loc, "Pp_vec_concat"))
    | vd, t, p, gamma, SyntaxPED.Pp_vector_concat (loc, vs),
        SyntaxVCT.T_refined_type (ve, SyntaxVCT.B_int, c)
        -> Monad.fail (Monad.TypeError (loc, "Pp_vec_concat"))
    | vd, t, p, gamma, SyntaxPED.Pp_vector_concat (loc, vs),
        SyntaxVCT.T_refined_type (ve, SyntaxVCT.B_bool, c)
        -> Monad.fail (Monad.TypeError (loc, "Pp_vec_concat"))
    | vd, t, p, gamma, SyntaxPED.Pp_vector_concat (loc, vs),
        SyntaxVCT.T_refined_type (ve, SyntaxVCT.B_bit, c)
        -> Monad.fail (Monad.TypeError (loc, "Pp_vec_concat"))
    | vd, t, p, gamma, SyntaxPED.Pp_vector_concat (loc, vs),
        SyntaxVCT.T_refined_type (ve, SyntaxVCT.B_unit, c)
        -> Monad.fail (Monad.TypeError (loc, "Pp_vec_concat"))
    | vd, t, p, gamma, SyntaxPED.Pp_vector_concat (loc, vs),
        SyntaxVCT.T_refined_type (ve, SyntaxVCT.B_real, c)
        -> Monad.fail (Monad.TypeError (loc, "Pp_vec_concat"))
    | vd, t, p, gamma, SyntaxPED.Pp_vector_concat (loc, vs),
        SyntaxVCT.T_refined_type (ve, SyntaxVCT.B_list v, c)
        -> Monad.fail (Monad.TypeError (loc, "Pp_vec_concat"))
    | vd, t, p, gamma, SyntaxPED.Pp_vector_concat (loc, vs),
        SyntaxVCT.T_refined_type (ve, SyntaxVCT.B_tuple v, c)
        -> Monad.fail (Monad.TypeError (loc, "Pp_vec_concat"))
    | vd, t, p, gamma, SyntaxPED.Pp_vector_concat (loc, vs),
        SyntaxVCT.T_refined_type (ve, SyntaxVCT.B_union (v, va), c)
        -> Monad.fail (Monad.TypeError (loc, "Pp_vec_concat"))
    | vd, t, p, gamma, SyntaxPED.Pp_vector_concat (loc, vs),
        SyntaxVCT.T_refined_type (ve, SyntaxVCT.B_record v, c)
        -> Monad.fail (Monad.TypeError (loc, "Pp_vec_concat"))
    | vd, t, p, gamma, SyntaxPED.Pp_vector_concat (loc, vs),
        SyntaxVCT.T_refined_type (ve, SyntaxVCT.B_undef, c)
        -> Monad.fail (Monad.TypeError (loc, "Pp_vec_concat"))
    | vd, t, p, gamma, SyntaxPED.Pp_vector_concat (loc, vs),
        SyntaxVCT.T_refined_type (ve, SyntaxVCT.B_reg, c)
        -> Monad.fail (Monad.TypeError (loc, "Pp_vec_concat"))
    | vd, t, p, gamma, SyntaxPED.Pp_vector_concat (loc, vs),
        SyntaxVCT.T_refined_type (ve, SyntaxVCT.B_string, c)
        -> Monad.fail (Monad.TypeError (loc, "Pp_vec_concat"))
    | vd, t, p, gamma, SyntaxPED.Pp_vector_concat (loc, vs),
        SyntaxVCT.T_refined_type (ve, SyntaxVCT.B_exception, c)
        -> Monad.fail (Monad.TypeError (loc, "Pp_vec_concat"))
    | vd, t, p, gamma, SyntaxPED.Pp_vector_concat (loc, vs),
        SyntaxVCT.T_refined_type (ve, SyntaxVCT.B_finite_set v, c)
        -> Monad.fail (Monad.TypeError (loc, "Pp_vec_concat"))
    | litok, tb, pa, gamma, SyntaxPED.Pp_typ (loc, ta, p), t ->
        check_pat litok tb pa gamma p ta
    | litok, ta, pa, gamma, SyntaxPED.Pp_app (loc, ctor, [p]), t ->
        (match ContextsPiDelta.lookup_constr_union_type ta ctor
          with None -> Monad.fail (Monad.TypeError (loc, "Pp_constr"))
          | Some (t1, t2) ->
            Monad.check_bind (check_pat litok ta pa gamma p t2)
              (fun (x, (g, vars)) ->
                Monad.check_bind
                  (Monad.mk_fresh
                    [Stringa.Chara
                       (false, false, false, false, true, true, true, false);
                      Stringa.Chara
                        (true, false, false, false, false, true, true, false);
                      Stringa.Chara
                        (false, false, true, false, true, true, true, false)])
                  (fun z ->
                    Monad.check_bind (Monad.return true)
                      (fun st ->
                        (if st
                          then Monad.return
                                 (z, ((z,
(Contexts.b_of t1,
  Contexts.mk_v_eq_c z (SyntaxVCT.V_constr (ctor, SyntaxVCT.V_var x)))) ::
g,
                                       vars))
                          else Monad.fail
                                 (Monad.CheckFail
                                   (loc, gamma, "Pp_constr", t1, t)))))))
    | vg, ta, p, gamma, SyntaxPED.Pp_as_var (loc, vh, vi), t ->
        Monad.fail (Monad.TypeError (loc, "Pp_as_var"))
    | vj, ta, p, gamma, SyntaxPED.Pp_as_typ (loc, vk, vl), t ->
        Monad.fail (Monad.TypeError (loc, "Pp_as_var"))
    | vm, ta, p, gamma, SyntaxPED.Pp_vector (loc, vs), t ->
        Monad.fail (Monad.TypeError (loc, "Pp_vector"))
    | vn, ta, p, gamma, SyntaxPED.Pp_record (loc, vs), t ->
        Monad.fail (Monad.TypeError (loc, "Pp_record"))
    | litok, ta, p, gamma, SyntaxPED.Pp_cons (loc, p1, p2), t ->
        (match t
          with SyntaxVCT.T_refined_type (_, SyntaxVCT.B_var _, _) ->
            Monad.fail (Monad.TypeError (loc, "Pp_cons"))
          | SyntaxVCT.T_refined_type (_, SyntaxVCT.B_tid _, _) ->
            Monad.fail (Monad.TypeError (loc, "Pp_cons"))
          | SyntaxVCT.T_refined_type (_, SyntaxVCT.B_int, _) ->
            Monad.fail (Monad.TypeError (loc, "Pp_cons"))
          | SyntaxVCT.T_refined_type (_, SyntaxVCT.B_bool, _) ->
            Monad.fail (Monad.TypeError (loc, "Pp_cons"))
          | SyntaxVCT.T_refined_type (_, SyntaxVCT.B_bit, _) ->
            Monad.fail (Monad.TypeError (loc, "Pp_cons"))
          | SyntaxVCT.T_refined_type (_, SyntaxVCT.B_unit, _) ->
            Monad.fail (Monad.TypeError (loc, "Pp_cons"))
          | SyntaxVCT.T_refined_type (_, SyntaxVCT.B_real, _) ->
            Monad.fail (Monad.TypeError (loc, "Pp_cons"))
          | SyntaxVCT.T_refined_type (_, SyntaxVCT.B_vec (_, _), _) ->
            Monad.fail (Monad.TypeError (loc, "Pp_cons"))
          | SyntaxVCT.T_refined_type (_, SyntaxVCT.B_list b, _) ->
            Monad.check_bind
              (check_pat litok ta p gamma p1
                (SyntaxVCT.T_refined_type
                  (SyntaxVCT.VIndex, b, SyntaxVCT.C_true)))
              (fun (_, (ghd, vars1)) ->
                Monad.check_bind (check_pat litok ta p gamma p2 t)
                  (fun (xtl, (gtl, vars2)) ->
                    Monad.return (xtl, (ghd @ gtl, vars1 @ vars2))))
          | SyntaxVCT.T_refined_type (_, SyntaxVCT.B_tuple _, _) ->
            Monad.fail (Monad.TypeError (loc, "Pp_cons"))
          | SyntaxVCT.T_refined_type (_, SyntaxVCT.B_union (_, _), _) ->
            Monad.fail (Monad.TypeError (loc, "Pp_cons"))
          | SyntaxVCT.T_refined_type (_, SyntaxVCT.B_record _, _) ->
            Monad.fail (Monad.TypeError (loc, "Pp_cons"))
          | SyntaxVCT.T_refined_type (_, SyntaxVCT.B_undef, _) ->
            Monad.fail (Monad.TypeError (loc, "Pp_cons"))
          | SyntaxVCT.T_refined_type (_, SyntaxVCT.B_reg, _) ->
            Monad.fail (Monad.TypeError (loc, "Pp_cons"))
          | SyntaxVCT.T_refined_type (_, SyntaxVCT.B_string, _) ->
            Monad.fail (Monad.TypeError (loc, "Pp_cons"))
          | SyntaxVCT.T_refined_type (_, SyntaxVCT.B_exception, _) ->
            Monad.fail (Monad.TypeError (loc, "Pp_cons"))
          | SyntaxVCT.T_refined_type (_, SyntaxVCT.B_finite_set _, _) ->
            Monad.fail (Monad.TypeError (loc, "Pp_cons")))
    | litok, ta, p, gamma, SyntaxPED.Pp_string_append (loc, ps), t ->
        (if SyntaxVCT.equal_bpa (Contexts.b_of t) SyntaxVCT.B_string
          then Monad.check_bind
                 (check_pat_list litok ta p gamma loc ps
                   (Lista.map
                     (fun _ ->
                       SyntaxVCT.T_refined_type
                         (SyntaxVCT.VIndex, SyntaxVCT.B_string,
                           SyntaxVCT.C_true))
                     ps))
                 (fun (_, (gs, vars2)) ->
                   Monad.check_bind
                     (Monad.mk_fresh
                       [Stringa.Chara
                          (false, false, false, false, true, true, true, false);
                         Stringa.Chara
                           (true, true, false, false, true, true, true, false);
                         Stringa.Chara
                           (true, false, false, false, false, true, true,
                             false)])
                     (fun x ->
                       Monad.return
                         (x, (((x, (Contexts.b_of t,
                                     Contexts.subst_c_x (Contexts.c_of t) x)) ::
                                kvars_of t) @
                                gs,
                               vars2))))
          else Monad.fail (Monad.TypeError (loc, "Pp_string_append")))
    | litok, ta, p, gamma, SyntaxPED.Pp_list (loc, ps), t ->
        (match t
          with SyntaxVCT.T_refined_type (_, SyntaxVCT.B_var _, _) ->
            Monad.fail (Monad.TypeError (loc, "Pp_list"))
          | SyntaxVCT.T_refined_type (_, SyntaxVCT.B_tid _, _) ->
            Monad.fail (Monad.TypeError (loc, "Pp_list"))
          | SyntaxVCT.T_refined_type (_, SyntaxVCT.B_int, _) ->
            Monad.fail (Monad.TypeError (loc, "Pp_list"))
          | SyntaxVCT.T_refined_type (_, SyntaxVCT.B_bool, _) ->
            Monad.fail (Monad.TypeError (loc, "Pp_list"))
          | SyntaxVCT.T_refined_type (_, SyntaxVCT.B_bit, _) ->
            Monad.fail (Monad.TypeError (loc, "Pp_list"))
          | SyntaxVCT.T_refined_type (_, SyntaxVCT.B_unit, _) ->
            Monad.fail (Monad.TypeError (loc, "Pp_list"))
          | SyntaxVCT.T_refined_type (_, SyntaxVCT.B_real, _) ->
            Monad.fail (Monad.TypeError (loc, "Pp_list"))
          | SyntaxVCT.T_refined_type (_, SyntaxVCT.B_vec (_, _), _) ->
            Monad.fail (Monad.TypeError (loc, "Pp_list"))
          | SyntaxVCT.T_refined_type (_, SyntaxVCT.B_list b, _) ->
            Monad.check_bind
              (check_pat_list litok ta p gamma loc ps
                (Lista.map
                  (fun _ ->
                    SyntaxVCT.T_refined_type
                      (SyntaxVCT.VIndex, b, SyntaxVCT.C_true))
                  ps))
              (fun (xs, (gs, vars)) ->
                Monad.check_bind
                  (Monad.mk_fresh
                    [Stringa.Chara
                       (false, false, false, false, true, true, true, false);
                      Stringa.Chara
                        (false, false, true, true, false, true, true, false);
                      Stringa.Chara
                        (true, false, false, true, false, true, true, false);
                      Stringa.Chara
                        (true, true, false, false, true, true, true, false);
                      Stringa.Chara
                        (false, false, true, false, true, true, true, false)])
                  (fun x ->
                    Monad.return
                      (x, ((x, (SyntaxVCT.B_list b, Contexts.mk_list_c x xs)) ::
                             gs,
                            vars))))
          | SyntaxVCT.T_refined_type (_, SyntaxVCT.B_tuple _, _) ->
            Monad.fail (Monad.TypeError (loc, "Pp_list"))
          | SyntaxVCT.T_refined_type (_, SyntaxVCT.B_union (_, _), _) ->
            Monad.fail (Monad.TypeError (loc, "Pp_list"))
          | SyntaxVCT.T_refined_type (_, SyntaxVCT.B_record _, _) ->
            Monad.fail (Monad.TypeError (loc, "Pp_list"))
          | SyntaxVCT.T_refined_type (_, SyntaxVCT.B_undef, _) ->
            Monad.fail (Monad.TypeError (loc, "Pp_list"))
          | SyntaxVCT.T_refined_type (_, SyntaxVCT.B_reg, _) ->
            Monad.fail (Monad.TypeError (loc, "Pp_list"))
          | SyntaxVCT.T_refined_type (_, SyntaxVCT.B_string, _) ->
            Monad.fail (Monad.TypeError (loc, "Pp_list"))
          | SyntaxVCT.T_refined_type (_, SyntaxVCT.B_exception, _) ->
            Monad.fail (Monad.TypeError (loc, "Pp_list"))
          | SyntaxVCT.T_refined_type (_, SyntaxVCT.B_finite_set _, _) ->
            Monad.fail (Monad.TypeError (loc, "Pp_list")))
and check_pat_list
  vp t p g loc x5 x6 = match vp, t, p, g, loc, x5, x6 with
    vp, t, p, g, loc, [], [] -> Monad.return ([], ([], []))
    | litok, ta, pa, g, loc, p :: ps, t :: ts ->
        Monad.check_bind (check_pat litok ta pa g p t)
          (fun (x, (ga, vars1)) ->
            Monad.check_bind (check_pat_list litok ta pa g loc ps ts)
              (fun (xs, (gs, vars2)) ->
                Monad.return (x :: xs, (ga @ gs, vars1 @ vars2))))
    | vq, vr, vt, g, loc, v :: va, [] ->
        Monad.fail (Monad.TypeError (loc, "pat list"))
    | vq, vr, vt, g, loc, [], v :: va ->
        Monad.fail (Monad.TypeError (loc, "pat list"))
and check_pat_vec_list
  vo t p g loc x5 odr b = match vo, t, p, g, loc, x5, odr, b with
    vo, t, p, g, loc, [], odr, b -> Monad.return ([], ([], []))
    | litok, t, pa, g, loc, p :: ps, odr, b ->
        Monad.check_bind
          (check_pat litok t pa g p
            (SyntaxVCT.T_refined_type
              (SyntaxVCT.VIndex, SyntaxVCT.B_vec (odr, b), SyntaxVCT.C_true)))
          (fun (x, (ga, vars1)) ->
            Monad.check_bind (check_pat_vec_list litok t pa g loc ps odr b)
              (fun (xs, (gs, vars2)) ->
                Monad.return (x :: xs, (ga @ gs, vars1 @ vars2))));;

let rec mk_c_eq
  x y = SyntaxVCT.C_eq
          (SyntaxVCT.CE_val (Monad.mk_var x),
            SyntaxVCT.CE_val (Monad.mk_var y));;

let rec kvars_of2 (SyntaxVCT.T_refined_type (uu, uv, uw)) = [];;

let rec convert_to_stM
  ts = Monad.check_bind
         (Monad.mapM
           (fun t ->
             Monad.check_bind (Monad.freshen_t t)
               (fun ta -> Monad.return (ta, kvars_of2 ta)))
           ts)
         (fun tkvars ->
           Monad.check_bind (Monad.return (Contexts.unzip tkvars))
             (fun (tsa, kvars) ->
               Monad.return
                 (let (blist, clist) =
                    Contexts.unzip
                      (Lista.map
                        (fun (a, b) ->
                          Contexts.convert_to_bc (Lista.size_list tsa) a b)
                        (Lista.enumerate Arith.one_nat tsa))
                    in
                   (Lista.concat kvars, (blist, Contexts.conj clist)))));;

let rec check_varM
  g loc x =
    (match Finite_Map.fmlookup SyntaxVCT.equal_xp (Contexts.gamma_f g) x
      with None -> Monad.return true
      | Some _ ->
        Monad.fail
          (Monad.TypeError
            (loc, "Local variable already bound as function name")));;

let rec check_varsM
  g loc xs =
    Monad.check_bind (Monad.mapM (check_varM g loc) xs)
      (fun _ -> Monad.return true);;

let rec check_bases
  = function [] -> None
    | [t] -> Some (Contexts.b_of t)
    | t :: v :: va ->
        (match check_bases (v :: va) with None -> None
          | Some b ->
            (if SyntaxVCT.equal_bpa b (Contexts.b_of t) then Some b
              else None));;

let rec mk_eq_proj
  l x i n =
    SyntaxVCT.C_eq
      (SyntaxVCT.CE_val (SyntaxVCT.V_var SyntaxVCT.VIndex),
        SyntaxVCT.CE_val
          (SyntaxVCT.V_proj
            ((Utils.string_lit_of_nat n ^ "X") ^ Utils.string_lit_of_nat i,
              SyntaxVCT.V_var x)));;

let rec loc_lexp uu = Location.Loc_unknown;;

let rec check_lexp
  ta p g d x4 t = match ta, p, g, d, x4, t with
    ta, p, g, d, SyntaxPED.LEXPp_mvar (loc, x), t ->
      Monad.check_bind (Monad.freshen_t t)
        (fun tb ->
          Monad.check_bind (Monad.return (SyntaxVCT.VNamed x))
            (fun xx ->
              (match ContextsPiDelta.lookup_mvar d x
                with None ->
                  Monad.return
                    (xx, ([(xx, (Contexts.b_of tb,
                                  Contexts.subst_c_v0 (Contexts.c_of tb)
                                    (SyntaxVCT.V_var xx)))] @
                            kvars_of tb,
                           [xx]))
                | Some tt ->
                  Monad.check_bind
                    (subtype loc ta g tb
                      (SyntaxVCT.T_refined_type
                        (SyntaxVCT.VIndex, Contexts.b_of tt,
                          SyntaxPED.subst_cp (SyntaxVCT.V_var SyntaxVCT.VIndex)
                            xx (Contexts.c_of tt))))
                    (fun bs ->
                      (if bs
                        then Monad.return
                               (xx, ([(xx,
(Contexts.b_of tb,
  Contexts.subst_c_v0 (Contexts.c_of tb) (SyntaxVCT.V_var xx)))] @
                                       kvars_of tb,
                                      [xx]))
                        else Monad.fail
                               (Monad.CheckFail
                                 (loc, g, "lvalue pattern subtype", tb,
                                   SyntaxVCT.T_refined_type
                                     (SyntaxVCT.VIndex, Contexts.b_of tt,
                                       SyntaxPED.subst_cp
 (SyntaxVCT.V_var SyntaxVCT.VIndex) xx (Contexts.c_of tt)))))))))
    | t, p, g, d, SyntaxPED.LEXPp_tup (l1, es),
        SyntaxVCT.T_refined_type (vt, SyntaxVCT.B_tuple bs, c)
        -> Monad.check_bind
             (Monad.mk_fresh
               [Stringa.Chara
                  (false, false, true, true, false, true, true, false);
                 Stringa.Chara
                   (false, true, true, false, true, true, true, false)])
             (fun z ->
               (let ca = Contexts.subst_c_v0 c (SyntaxVCT.V_var z) in
                 Monad.check_bind
                   (Monad.return
                     (Contexts.add_var g
                       (z, Contexts.GEPair (SyntaxVCT.B_tuple bs, ca))))
                   (fun ga ->
                     Monad.check_bind
                       (Monad.map2iM
                         (fun x xa xaa ->
                           check_lexp t p ga d x
                             (SyntaxVCT.T_refined_type
                               (SyntaxVCT.VIndex, xa,
                                 mk_eq_proj l1 z
                                   (Arith.nat (Arith.int_of_nat xaa))
                                   (Lista.size_list bs))))
                         es bs)
                       (fun xx ->
                         Monad.check_bind (Monad.return (unzip3 xx))
                           (fun (_, (gs, vars)) ->
                             Monad.check_bind (Monad.return (Lista.concat gs))
                               (fun gsa ->
                                 Monad.return
                                   (z, (gsa @ [(z, (SyntaxVCT.B_tuple bs, ca))],
 Lista.concat vars))))))))
    | t, p, g, d, SyntaxPED.LEXPp_cast (loc, t1, x), t2 ->
        Monad.check_bind (subtype loc t g t2 t1)
          (fun b ->
            (if b then check_lexp t p g d (SyntaxPED.LEXPp_mvar (loc, x)) t1
              else Monad.fail
                     (Monad.CheckFail (loc, g, "lvalue with type", t2, t1))))
    | t, p, g, d, SyntaxPED.LEXPp_tup (v, va),
        SyntaxVCT.T_refined_type (vb, SyntaxVCT.B_var ve, vd)
        -> Monad.fail
             (Monad.NotImplemented
               (loc_lexp (SyntaxPED.LEXPp_tup (v, va)), "check_lexp"))
    | t, p, g, d, SyntaxPED.LEXPp_tup (v, va),
        SyntaxVCT.T_refined_type (vb, SyntaxVCT.B_tid ve, vd)
        -> Monad.fail
             (Monad.NotImplemented
               (loc_lexp (SyntaxPED.LEXPp_tup (v, va)), "check_lexp"))
    | t, p, g, d, SyntaxPED.LEXPp_tup (v, va),
        SyntaxVCT.T_refined_type (vb, SyntaxVCT.B_int, vd)
        -> Monad.fail
             (Monad.NotImplemented
               (loc_lexp (SyntaxPED.LEXPp_tup (v, va)), "check_lexp"))
    | t, p, g, d, SyntaxPED.LEXPp_tup (v, va),
        SyntaxVCT.T_refined_type (vb, SyntaxVCT.B_bool, vd)
        -> Monad.fail
             (Monad.NotImplemented
               (loc_lexp (SyntaxPED.LEXPp_tup (v, va)), "check_lexp"))
    | t, p, g, d, SyntaxPED.LEXPp_tup (v, va),
        SyntaxVCT.T_refined_type (vb, SyntaxVCT.B_bit, vd)
        -> Monad.fail
             (Monad.NotImplemented
               (loc_lexp (SyntaxPED.LEXPp_tup (v, va)), "check_lexp"))
    | t, p, g, d, SyntaxPED.LEXPp_tup (v, va),
        SyntaxVCT.T_refined_type (vb, SyntaxVCT.B_unit, vd)
        -> Monad.fail
             (Monad.NotImplemented
               (loc_lexp (SyntaxPED.LEXPp_tup (v, va)), "check_lexp"))
    | t, p, g, d, SyntaxPED.LEXPp_tup (v, va),
        SyntaxVCT.T_refined_type (vb, SyntaxVCT.B_real, vd)
        -> Monad.fail
             (Monad.NotImplemented
               (loc_lexp (SyntaxPED.LEXPp_tup (v, va)), "check_lexp"))
    | t, p, g, d, SyntaxPED.LEXPp_tup (v, va),
        SyntaxVCT.T_refined_type (vb, SyntaxVCT.B_vec (ve, vf), vd)
        -> Monad.fail
             (Monad.NotImplemented
               (loc_lexp (SyntaxPED.LEXPp_tup (v, va)), "check_lexp"))
    | t, p, g, d, SyntaxPED.LEXPp_tup (v, va),
        SyntaxVCT.T_refined_type (vb, SyntaxVCT.B_list ve, vd)
        -> Monad.fail
             (Monad.NotImplemented
               (loc_lexp (SyntaxPED.LEXPp_tup (v, va)), "check_lexp"))
    | t, p, g, d, SyntaxPED.LEXPp_tup (v, va),
        SyntaxVCT.T_refined_type (vb, SyntaxVCT.B_union (ve, vf), vd)
        -> Monad.fail
             (Monad.NotImplemented
               (loc_lexp (SyntaxPED.LEXPp_tup (v, va)), "check_lexp"))
    | t, p, g, d, SyntaxPED.LEXPp_tup (v, va),
        SyntaxVCT.T_refined_type (vb, SyntaxVCT.B_record ve, vd)
        -> Monad.fail
             (Monad.NotImplemented
               (loc_lexp (SyntaxPED.LEXPp_tup (v, va)), "check_lexp"))
    | t, p, g, d, SyntaxPED.LEXPp_tup (v, va),
        SyntaxVCT.T_refined_type (vb, SyntaxVCT.B_undef, vd)
        -> Monad.fail
             (Monad.NotImplemented
               (loc_lexp (SyntaxPED.LEXPp_tup (v, va)), "check_lexp"))
    | t, p, g, d, SyntaxPED.LEXPp_tup (v, va),
        SyntaxVCT.T_refined_type (vb, SyntaxVCT.B_reg, vd)
        -> Monad.fail
             (Monad.NotImplemented
               (loc_lexp (SyntaxPED.LEXPp_tup (v, va)), "check_lexp"))
    | t, p, g, d, SyntaxPED.LEXPp_tup (v, va),
        SyntaxVCT.T_refined_type (vb, SyntaxVCT.B_string, vd)
        -> Monad.fail
             (Monad.NotImplemented
               (loc_lexp (SyntaxPED.LEXPp_tup (v, va)), "check_lexp"))
    | t, p, g, d, SyntaxPED.LEXPp_tup (v, va),
        SyntaxVCT.T_refined_type (vb, SyntaxVCT.B_exception, vd)
        -> Monad.fail
             (Monad.NotImplemented
               (loc_lexp (SyntaxPED.LEXPp_tup (v, va)), "check_lexp"))
    | t, p, g, d, SyntaxPED.LEXPp_tup (v, va),
        SyntaxVCT.T_refined_type (vb, SyntaxVCT.B_finite_set ve, vd)
        -> Monad.fail
             (Monad.NotImplemented
               (loc_lexp (SyntaxPED.LEXPp_tup (v, va)), "check_lexp"))
    | t, p, g, d, SyntaxPED.LEXPp_field (v, va, vb), vu ->
        Monad.fail
          (Monad.NotImplemented
            (loc_lexp (SyntaxPED.LEXPp_field (v, va, vb)), "check_lexp"));;

let rec infer_v
  t p g d x4 = match t, p, g, d, x4 with
    t, p, g, d, SyntaxVCT.V_lit SyntaxVCT.L_undef ->
      Monad.fail
        (Monad.TypeError
          (Location.Loc_unknown, "Cannot infer type of undefined"))
    | t, p, g, d, SyntaxVCT.V_lit SyntaxVCT.L_unit ->
        Monad.check_bind (Monad.trace Monad.LitI)
          (fun _ ->
            Monad.check_bind
              (Monad.mk_fresh
                [Stringa.Chara
                   (false, false, true, true, false, true, true, false);
                  Stringa.Chara
                    (true, false, false, true, false, true, true, false);
                  Stringa.Chara
                    (false, false, true, false, true, true, true, false)])
              (fun x ->
                Monad.return
                  (x, ([(x, (Contexts.literal_type SyntaxVCT.L_unit,
                              Contexts.mk_l_eq_c x SyntaxVCT.L_unit))],
                        Contexts.mk_l_eq_t SyntaxVCT.L_unit))))
    | t, p, g, d, SyntaxVCT.V_lit SyntaxVCT.L_zero ->
        Monad.check_bind (Monad.trace Monad.LitI)
          (fun _ ->
            Monad.check_bind
              (Monad.mk_fresh
                [Stringa.Chara
                   (false, false, true, true, false, true, true, false);
                  Stringa.Chara
                    (true, false, false, true, false, true, true, false);
                  Stringa.Chara
                    (false, false, true, false, true, true, true, false)])
              (fun x ->
                Monad.return
                  (x, ([(x, (Contexts.literal_type SyntaxVCT.L_zero,
                              Contexts.mk_l_eq_c x SyntaxVCT.L_zero))],
                        Contexts.mk_l_eq_t SyntaxVCT.L_zero))))
    | t, p, g, d, SyntaxVCT.V_lit SyntaxVCT.L_one ->
        Monad.check_bind (Monad.trace Monad.LitI)
          (fun _ ->
            Monad.check_bind
              (Monad.mk_fresh
                [Stringa.Chara
                   (false, false, true, true, false, true, true, false);
                  Stringa.Chara
                    (true, false, false, true, false, true, true, false);
                  Stringa.Chara
                    (false, false, true, false, true, true, true, false)])
              (fun x ->
                Monad.return
                  (x, ([(x, (Contexts.literal_type SyntaxVCT.L_one,
                              Contexts.mk_l_eq_c x SyntaxVCT.L_one))],
                        Contexts.mk_l_eq_t SyntaxVCT.L_one))))
    | t, p, g, d, SyntaxVCT.V_lit SyntaxVCT.L_true ->
        Monad.check_bind (Monad.trace Monad.LitI)
          (fun _ ->
            Monad.check_bind
              (Monad.mk_fresh
                [Stringa.Chara
                   (false, false, true, true, false, true, true, false);
                  Stringa.Chara
                    (true, false, false, true, false, true, true, false);
                  Stringa.Chara
                    (false, false, true, false, true, true, true, false)])
              (fun x ->
                Monad.return
                  (x, ([(x, (Contexts.literal_type SyntaxVCT.L_true,
                              Contexts.mk_l_eq_c x SyntaxVCT.L_true))],
                        Contexts.mk_l_eq_t SyntaxVCT.L_true))))
    | t, p, g, d, SyntaxVCT.V_lit SyntaxVCT.L_false ->
        Monad.check_bind (Monad.trace Monad.LitI)
          (fun _ ->
            Monad.check_bind
              (Monad.mk_fresh
                [Stringa.Chara
                   (false, false, true, true, false, true, true, false);
                  Stringa.Chara
                    (true, false, false, true, false, true, true, false);
                  Stringa.Chara
                    (false, false, true, false, true, true, true, false)])
              (fun x ->
                Monad.return
                  (x, ([(x, (Contexts.literal_type SyntaxVCT.L_false,
                              Contexts.mk_l_eq_c x SyntaxVCT.L_false))],
                        Contexts.mk_l_eq_t SyntaxVCT.L_false))))
    | t, p, g, d, SyntaxVCT.V_lit (SyntaxVCT.L_num v) ->
        Monad.check_bind (Monad.trace Monad.LitI)
          (fun _ ->
            Monad.check_bind
              (Monad.mk_fresh
                [Stringa.Chara
                   (false, false, true, true, false, true, true, false);
                  Stringa.Chara
                    (true, false, false, true, false, true, true, false);
                  Stringa.Chara
                    (false, false, true, false, true, true, true, false)])
              (fun x ->
                Monad.return
                  (x, ([(x, (Contexts.literal_type (SyntaxVCT.L_num v),
                              Contexts.mk_l_eq_c x (SyntaxVCT.L_num v)))],
                        Contexts.mk_l_eq_t (SyntaxVCT.L_num v)))))
    | t, p, g, d, SyntaxVCT.V_lit (SyntaxVCT.L_string v) ->
        Monad.check_bind (Monad.trace Monad.LitI)
          (fun _ ->
            Monad.check_bind
              (Monad.mk_fresh
                [Stringa.Chara
                   (false, false, true, true, false, true, true, false);
                  Stringa.Chara
                    (true, false, false, true, false, true, true, false);
                  Stringa.Chara
                    (false, false, true, false, true, true, true, false)])
              (fun x ->
                Monad.return
                  (x, ([(x, (Contexts.literal_type (SyntaxVCT.L_string v),
                              Contexts.mk_l_eq_c x (SyntaxVCT.L_string v)))],
                        Contexts.mk_l_eq_t (SyntaxVCT.L_string v)))))
    | t, p, g, d, SyntaxVCT.V_lit (SyntaxVCT.L_real v) ->
        Monad.check_bind (Monad.trace Monad.LitI)
          (fun _ ->
            Monad.check_bind
              (Monad.mk_fresh
                [Stringa.Chara
                   (false, false, true, true, false, true, true, false);
                  Stringa.Chara
                    (true, false, false, true, false, true, true, false);
                  Stringa.Chara
                    (false, false, true, false, true, true, true, false)])
              (fun x ->
                Monad.return
                  (x, ([(x, (Contexts.literal_type (SyntaxVCT.L_real v),
                              Contexts.mk_l_eq_c x (SyntaxVCT.L_real v)))],
                        Contexts.mk_l_eq_t (SyntaxVCT.L_real v)))))
    | t, p, g, d, SyntaxVCT.V_var x ->
        (if Contexts.lookup_scope g x
          then (match Contexts.lookup_ivar g x
                 with None ->
                   (match ContextsPiDelta.lookup_mvar d (id_of x)
                     with None ->
                       (match ContextsPiDelta.lookup_constr_union_x t x
                         with None ->
                           Monad.fail
                             (Monad.VarUnknown (Location.Loc_unknown, x))
                         | Some ta -> Monad.return (x, ([], ta)))
                     | Some ta ->
                       Monad.check_bind (Monad.trace Monad.VarI)
                         (fun _ ->
                           Monad.return
                             (x, ([], SyntaxVCT.T_refined_type
(SyntaxVCT.VIndex, Contexts.b_of ta,
  SyntaxPED.subst_cp (SyntaxVCT.V_var SyntaxVCT.VIndex) x
    (Contexts.c_of ta))))))
                 | Some ge ->
                   Monad.check_bind (Monad.trace Monad.VarI)
                     (fun _ ->
                       Monad.return
                         (x, ([], Contexts.mk_v_eq_t (Satis.b_of_e ge)
                                    (SyntaxVCT.V_var x)))))
          else Monad.fail (Monad.ScopeError (Location.Loc_unknown, g, x)))
    | t, p, gamma, d, SyntaxVCT.V_tuple es ->
        Monad.check_bind (Monad.mapM (infer_v t p gamma d) es)
          (fun xx ->
            Monad.check_bind (Monad.return (unzip3 xx))
              (fun (_, (g, ts)) ->
                Monad.check_bind (Monad.return (Lista.concat g))
                  (fun _ ->
                    Monad.check_bind
                      (Monad.mk_fresh
                        [Stringa.Chara
                           (false, true, true, false, true, true, true, false);
                          Stringa.Chara
                            (false, false, true, false, true, true, true,
                              false);
                          Stringa.Chara
                            (true, false, true, false, true, true, true, false);
                          Stringa.Chara
                            (false, false, false, false, true, true, true,
                              false)])
                      (fun x ->
                        (let (bs, cs) = Contexts.convert_to_st ts in
                          Monad.check_bind (Monad.trace Monad.TupleI)
                            (fun _ ->
                              Monad.return
                                (x, ([(x,
(SyntaxVCT.B_tuple bs, Contexts.subst_c_x cs x))],
                                      SyntaxVCT.T_refined_type
(SyntaxVCT.VIndex, SyntaxVCT.B_tuple bs, cs)))))))))
    | t, p, g, d, SyntaxVCT.V_vec [] ->
        Monad.fail
          (Monad.NotImplemented (Location.Loc_unknown, "infer empty vector"))
    | t, p, g, d, SyntaxVCT.V_vec (v :: va) ->
        Monad.check_bind (Monad.mapM (infer_v t p g d) (v :: va))
          (fun xx ->
            Monad.check_bind (Monad.return (unzip3 xx))
              (fun (_, (ga, ts)) ->
                Monad.check_bind (Monad.return (Lista.concat ga))
                  (fun _ ->
                    Monad.check_bind
                      (Monad.mk_fresh
                        [Stringa.Chara
                           (false, true, true, false, true, true, true, false);
                          Stringa.Chara
                            (true, false, true, false, false, true, true,
                              false);
                          Stringa.Chara
                            (true, true, false, false, false, true, true,
                              false)])
                      (fun x ->
                        (let bs =
                           Lista.remdups SyntaxVCT.equal_bp
                             (Lista.map Contexts.b_of ts)
                           in
                          (if Arith.equal_nat (Lista.size_list bs) Arith.one_nat
                            then Monad.return
                                   (x, ([(x, (Lista.hd bs, SyntaxVCT.C_true))],
 SyntaxVCT.T_refined_type (SyntaxVCT.VIndex, Lista.hd bs, SyntaxVCT.C_true)))
                            else Monad.fail Monad.VectorElementsDiffType))))))
    | t, p, g, d, SyntaxVCT.V_constr (s, v) ->
        (match ContextsPiDelta.lookup_constr_union t s
          with None ->
            Monad.fail (Monad.UnknownConstructor (Location.Loc_unknown, s))
          | Some ta ->
            Monad.check_bind (Monad.freshen_t ta)
              (fun tb ->
                Monad.check_bind
                  (Monad.mk_fresh
                    [Stringa.Chara
                       (true, true, false, false, false, true, true, false);
                      Stringa.Chara
                        (false, false, true, false, true, true, true, false);
                      Stringa.Chara
                        (false, true, false, false, true, true, true, false)])
                  (fun x ->
                    Monad.return
                      (x, ((x, (Contexts.b_of tb,
                                 Contexts.subst_c_x (Contexts.c_of tb) x)) ::
                             kvars_of2 tb,
                            tb)))))
    | t, p, g, d, SyntaxVCT.V_record fs ->
        Monad.fail (Monad.NotImplemented (Location.Loc_unknown, "record"));;

let rec check_s
  ta pa g d x4 t = match ta, pa, g, d, x4, t with
    ta, pa, g, d, SyntaxPED.Ep_let (l, SyntaxPED.LBp_val (vv, p, e), s), t ->
      Monad.check_bind (infer_e_lbind l ta pa g d p e)
        (fun (z, (bs, (tb, vars))) ->
          Monad.check_bind (check_varsM g l vars)
            (fun _ ->
              Monad.check_bind
                (Monad.mk_fresh
                  [Stringa.Chara
                     (false, false, true, true, false, true, true, false);
                    Stringa.Chara
                      (true, false, true, false, false, true, true, false);
                    Stringa.Chara
                      (false, false, true, false, true, true, true, false);
                    Stringa.Chara
                      (true, true, true, true, true, false, true, false);
                    Stringa.Chara
                      (false, false, false, false, true, true, true, false);
                    Stringa.Chara
                      (true, false, false, false, false, true, true, false);
                    Stringa.Chara
                      (false, false, true, false, true, true, true, false)])
                (fun za ->
                  Monad.check_bind (Monad.freshen_t tb)
                    (fun tba ->
                      Monad.check_bind
                        (Monad.return (Contexts.add_to_scope g vars))
                        (fun ga ->
                          Monad.check_bind
                            (Monad.return
                              (Contexts.add_vars_ge ga
                                ((za, (Contexts.b_of tba,
SyntaxVCT.C_conj
  (mk_c_eq z za, Contexts.subst_c_v0 (Contexts.c_of tba) (Monad.mk_var z)))) ::
                                  bs)))
                            (fun gb ->
                              Monad.check_bind (check_s ta pa gb d s t)
                                (fun _ -> Monad.return gb)))))))
    | ta, p, g, d, SyntaxPED.Ep_assert (loc, e1, e2), t ->
        Monad.check_bind (infer_e ta p g d e1)
          (fun (z, (ga, t1)) ->
            Monad.check_bind
              (Monad.mk_fresh
                [Stringa.Chara
                   (true, false, false, false, false, true, true, false);
                  Stringa.Chara
                    (true, true, false, false, true, true, true, false);
                  Stringa.Chara
                    (true, true, false, false, true, true, true, false);
                  Stringa.Chara
                    (true, false, true, false, false, true, true, false);
                  Stringa.Chara
                    (false, true, false, false, true, true, true, false);
                  Stringa.Chara
                    (false, false, true, false, true, true, true, false)])
              (fun z2 ->
                (if SyntaxVCT.equal_bpa (Contexts.b_of t1) SyntaxVCT.B_bool
                  then Monad.return
                         (Contexts.add_vars_ge g
                           ((z2, (SyntaxVCT.B_bool,
                                   Contexts.mk_l_eq_c z SyntaxVCT.L_true)) ::
                             ga))
                  else Monad.fail
                         (Monad.CheckFail
                           (loc, g, "assert expression not boolean", t1,
                             SyntaxVCT.T_refined_type
                               (SyntaxVCT.VIndex, SyntaxVCT.B_bool,
                                 SyntaxVCT.C_true))))))
    | t, p, g, d, SyntaxPED.Ep_if (l, e, s1, s2),
        SyntaxVCT.T_refined_type (vw, b, c3)
        -> Monad.check_bind (infer_e t p g d e)
             (fun (_, (ga, ta)) ->
               (match ta
                 with SyntaxVCT.T_refined_type (_, SyntaxVCT.B_var _, _) ->
                   Monad.fail (Monad.IfCondType (l, ta))
                 | SyntaxVCT.T_refined_type (_, SyntaxVCT.B_tid _, _) ->
                   Monad.fail (Monad.IfCondType (l, ta))
                 | SyntaxVCT.T_refined_type (_, SyntaxVCT.B_int, _) ->
                   Monad.fail (Monad.IfCondType (l, ta))
                 | SyntaxVCT.T_refined_type (_, SyntaxVCT.B_bool, c1) ->
                   Monad.check_bind
                     (Monad.mk_fresh
                       [Stringa.Chara
                          (true, false, false, true, false, true, true, false);
                         Stringa.Chara
                           (false, true, true, false, false, true, true,
                             false)])
                     (fun z ->
                       Monad.check_bind
                         (check_s t p
                           (Contexts.add_vars_ge g
                             ((z, (SyntaxVCT.B_bool,
                                    SyntaxVCT.C_conj
                                      (SyntaxVCT.C_eq
 (SyntaxVCT.CE_val (SyntaxVCT.V_var z),
   SyntaxVCT.CE_val (SyntaxVCT.V_lit SyntaxVCT.L_true)),
SyntaxPED.subst_cp (SyntaxVCT.V_var z) SyntaxVCT.VIndex c1))) ::
                               ga))
                           d s1
                           (SyntaxVCT.T_refined_type
                             (SyntaxVCT.VIndex, b,
                               SyntaxVCT.C_imp
                                 (SyntaxVCT.C_eq
                                    (SyntaxVCT.CE_val (SyntaxVCT.V_var z),
                                      SyntaxVCT.CE_val
(SyntaxVCT.V_lit SyntaxVCT.L_true)),
                                   c3))))
                         (fun _ ->
                           check_s t p
                             (Contexts.add_vars_ge g
                               ((z, (SyntaxVCT.B_bool,
                                      SyntaxVCT.C_conj
(SyntaxVCT.C_eq
   (SyntaxVCT.CE_val (SyntaxVCT.V_var z),
     SyntaxVCT.CE_val (SyntaxVCT.V_lit SyntaxVCT.L_false)),
  SyntaxPED.subst_cp (SyntaxVCT.V_var z) SyntaxVCT.VIndex c1))) ::
                                 ga))
                             d s2
                             (SyntaxVCT.T_refined_type
                               (SyntaxVCT.VIndex, b,
                                 SyntaxVCT.C_imp
                                   (SyntaxVCT.C_eq
                                      (SyntaxVCT.CE_val (SyntaxVCT.V_var z),
SyntaxVCT.CE_val (SyntaxVCT.V_lit SyntaxVCT.L_false)),
                                     c3)))))
                 | SyntaxVCT.T_refined_type (_, SyntaxVCT.B_bit, _) ->
                   Monad.fail (Monad.IfCondType (l, ta))
                 | SyntaxVCT.T_refined_type (_, SyntaxVCT.B_unit, _) ->
                   Monad.fail (Monad.IfCondType (l, ta))
                 | SyntaxVCT.T_refined_type (_, SyntaxVCT.B_real, _) ->
                   Monad.fail (Monad.IfCondType (l, ta))
                 | SyntaxVCT.T_refined_type (_, SyntaxVCT.B_vec (_, _), _) ->
                   Monad.fail (Monad.IfCondType (l, ta))
                 | SyntaxVCT.T_refined_type (_, SyntaxVCT.B_list _, _) ->
                   Monad.fail (Monad.IfCondType (l, ta))
                 | SyntaxVCT.T_refined_type (_, SyntaxVCT.B_tuple _, _) ->
                   Monad.fail (Monad.IfCondType (l, ta))
                 | SyntaxVCT.T_refined_type (_, SyntaxVCT.B_union (_, _), _) ->
                   Monad.fail (Monad.IfCondType (l, ta))
                 | SyntaxVCT.T_refined_type (_, SyntaxVCT.B_record _, _) ->
                   Monad.fail (Monad.IfCondType (l, ta))
                 | SyntaxVCT.T_refined_type (_, SyntaxVCT.B_undef, _) ->
                   Monad.fail (Monad.IfCondType (l, ta))
                 | SyntaxVCT.T_refined_type (_, SyntaxVCT.B_reg, _) ->
                   Monad.fail (Monad.IfCondType (l, ta))
                 | SyntaxVCT.T_refined_type (_, SyntaxVCT.B_string, _) ->
                   Monad.fail (Monad.IfCondType (l, ta))
                 | SyntaxVCT.T_refined_type (_, SyntaxVCT.B_exception, _) ->
                   Monad.fail (Monad.IfCondType (l, ta))
                 | SyntaxVCT.T_refined_type (_, SyntaxVCT.B_finite_set _, _) ->
                   Monad.fail (Monad.IfCondType (l, ta))))
    | ta, p, g, d, SyntaxPED.Ep_block (loc, [e]), t -> check_s ta p g d e t
    | ta, p, g, d, SyntaxPED.Ep_block (loc, e :: v :: va), t ->
        Monad.check_bind
          (check_s ta p g d e
            (SyntaxVCT.T_refined_type
              (SyntaxVCT.VIndex, SyntaxVCT.B_unit, SyntaxVCT.C_true)))
          (fun ga -> check_s ta p ga d (SyntaxPED.Ep_block (loc, v :: va)) t)
    | ta, p, g, d, SyntaxPED.Ep_assign (loc, e1, e2, e3), t ->
        Monad.check_bind
          (subtype loc ta g t
            (SyntaxVCT.T_refined_type
              (SyntaxVCT.VIndex, SyntaxVCT.B_unit, SyntaxVCT.C_true)))
          (fun b ->
            (if b then Monad.check_bind (infer_e ta p g d e2)
                         (fun (_, (g1, t2)) ->
                           Monad.check_bind
                             (check_lexp ta p (Contexts.add_vars_ge g g1) d e1
                               t2)
                             (fun (_, (_, _)) -> Monad.return g))
              else Monad.fail
                     (Monad.CheckFail
                       (loc, g, "assign unit type", t,
                         SyntaxVCT.T_refined_type
                           (SyntaxVCT.VIndex, SyntaxVCT.B_unit,
                             SyntaxVCT.C_true)))))
    | t, p, g, d, SyntaxPED.Ep_record_update (loc, e, fes), t1 ->
        Monad.check_bind (infer_e t p g d e)
          (fun (_, (_, t2)) ->
            Monad.check_bind
              (Monad.mapM
                (fun (f, ea) ->
                  (let _ = ContextsPiDelta.lookup_field_in_type t2 f in
                    Monad.check_bind
                      (Monad.check_bind (infer_e t p g d ea)
                        (fun (z, (ga, ta)) ->
                          (match Contexts.b_of ta
                            with SyntaxVCT.B_var _ ->
                              Monad.fail (Monad.UnknownErrorLoc loc)
                            | SyntaxVCT.B_tid _ ->
                              Monad.fail (Monad.UnknownErrorLoc loc)
                            | SyntaxVCT.B_int ->
                              Monad.fail (Monad.UnknownErrorLoc loc)
                            | SyntaxVCT.B_bool ->
                              Monad.fail (Monad.UnknownErrorLoc loc)
                            | SyntaxVCT.B_bit ->
                              Monad.fail (Monad.UnknownErrorLoc loc)
                            | SyntaxVCT.B_unit ->
                              Monad.fail (Monad.UnknownErrorLoc loc)
                            | SyntaxVCT.B_real ->
                              Monad.fail (Monad.UnknownErrorLoc loc)
                            | SyntaxVCT.B_vec (_, _) ->
                              Monad.fail (Monad.UnknownErrorLoc loc)
                            | SyntaxVCT.B_list _ ->
                              Monad.fail (Monad.UnknownErrorLoc loc)
                            | SyntaxVCT.B_tuple _ ->
                              Monad.fail (Monad.UnknownErrorLoc loc)
                            | SyntaxVCT.B_union (_, _) ->
                              Monad.fail (Monad.UnknownErrorLoc loc)
                            | SyntaxVCT.B_record ft ->
                              (match Contexts.lookup Stringa.equal_literal ft f
                                with None ->
                                  Monad.fail (Monad.UnknownErrorLoc loc)
                                | Some b ->
                                  Monad.check_bind
                                    (Monad.mk_fresh
                                      [Stringa.Chara
 (false, false, false, false, true, true, true, false);
Stringa.Chara (false, true, false, false, true, true, true, false);
Stringa.Chara (true, true, true, true, false, true, true, false);
Stringa.Chara (false, true, false, true, false, true, true, false)])
                                    (fun za ->
                                      Monad.return
(za, ((za, (b, Contexts.mk_proj_eq_x z za f)) :: ga,
       SyntaxVCT.T_refined_type
         (SyntaxVCT.VIndex, b, Contexts.mk_proj_eq z f)))))
                            | SyntaxVCT.B_undef ->
                              Monad.fail (Monad.UnknownErrorLoc loc)
                            | SyntaxVCT.B_reg ->
                              Monad.fail (Monad.UnknownErrorLoc loc)
                            | SyntaxVCT.B_string ->
                              Monad.fail (Monad.UnknownErrorLoc loc)
                            | SyntaxVCT.B_exception ->
                              Monad.fail (Monad.UnknownErrorLoc loc)
                            | SyntaxVCT.B_finite_set _ ->
                              Monad.fail (Monad.UnknownErrorLoc loc))))
                      (fun (_, (_, t1a)) ->
                        Monad.check_bind (infer_e t p g d ea)
                          (fun (_, (_, t2a)) ->
                            Monad.check_bind (subtype loc t g t2a t1a)
                              (fun b ->
                                (if b then Monad.fail
     (Monad.CheckFail (SyntaxPED.loc_e ea, g, "record update", t2a, t1a))
                                  else Monad.return true))))))
                fes)
              (fun _ -> Monad.return g))
    | ta, p, g, d, SyntaxPED.Ep_case (loc, e, pes), t ->
        Monad.check_bind (infer_e ta p g d e)
          (fun (_, (_, t1)) ->
            Monad.check_bind
              (Monad.mapM
                (fun (SyntaxPED.PEXPp_exp (pa, s)) ->
                  Monad.check_bind (check_pat true ta p g pa t1)
                    (fun (z, (bs, vars)) ->
                      Monad.check_bind (check_varsM g Location.Loc_unknown vars)
                        (fun _ ->
                          Monad.check_bind (Monad.freshen_t t1)
                            (fun t1a ->
                              Monad.check_bind
                                (Monad.mk_fresh
                                  [Stringa.Chara
                                     (false, false, false, false, true, true,
                                       true, false);
                                    Stringa.Chara
                                      (true, false, false, false, false, true,
true, false);
                                    Stringa.Chara
                                      (false, false, true, false, true, true,
true, false)])
                                (fun za ->
                                  Monad.check_bind
                                    (Monad.return
                                      (Contexts.add_vars_ge g
((za, (Contexts.b_of t1a,
        SyntaxVCT.C_conj
          (mk_c_eq z za,
            Contexts.subst_c_v0 (Contexts.c_of t1a) (Monad.mk_var z)))) ::
  bs)))
                                    (fun ga ->
                                      Monad.check_bind
(check_s ta p (Contexts.add_to_scope ga vars) d s t)
(fun _ -> Monad.return g)))))))
                pes)
              (fun _ -> Monad.return g))
    | ta, p, g, d, SyntaxPED.Ep_return (loc, e), t ->
        Monad.check_bind
          (infer_e ta p g d
            (SyntaxPED.Ep_app (loc, SyntaxVCT.VNamed "return", e)))
          (fun (_, (_, _)) -> Monad.return g)
    | ta, p, g, d, SyntaxPED.Ep_loop (loc, vx, e1, e2), t ->
        Monad.check_bind
          (subtype loc ta g t
            (SyntaxVCT.T_refined_type
              (SyntaxVCT.VIndex, SyntaxVCT.B_unit, SyntaxVCT.C_true)))
          (fun b ->
            (if b then Monad.check_bind
                         (check_s ta p g d e1
                           (SyntaxVCT.T_refined_type
                             (SyntaxVCT.VIndex, SyntaxVCT.B_bool,
                               SyntaxVCT.C_true)))
                         (fun ga ->
                           check_s ta p ga d e2
                             (SyntaxVCT.T_refined_type
                               (SyntaxVCT.VIndex, SyntaxVCT.B_unit,
                                 SyntaxVCT.C_true)))
              else Monad.fail
                     (Monad.CheckFail
                       (loc, g, "While check unit ", t,
                         SyntaxVCT.T_refined_type
                           (SyntaxVCT.VIndex, SyntaxVCT.B_unit,
                             SyntaxVCT.C_true)))))
    | t, p, g, d, SyntaxPED.Ep_val (v, va), t1 ->
        Monad.check_bind (infer_e t p g d (SyntaxPED.Ep_val (v, va)))
          (fun (_, (ga, t2)) ->
            Monad.check_bind
              (subtype (SyntaxPED.loc_e (SyntaxPED.Ep_val (v, va))) t
                (Contexts.add_vars_ge g ga) t2 t1)
              (fun st ->
                (if st then Monad.return g
                  else Monad.fail
                         (Monad.CheckFail
                           (SyntaxPED.loc_e (SyntaxPED.Ep_val (v, va)), g,
                             "expr", t2, t1)))))
    | t, p, g, d, SyntaxPED.Ep_mvar (v, va), t1 ->
        Monad.check_bind (infer_e t p g d (SyntaxPED.Ep_mvar (v, va)))
          (fun (_, (ga, t2)) ->
            Monad.check_bind
              (subtype (SyntaxPED.loc_e (SyntaxPED.Ep_mvar (v, va))) t
                (Contexts.add_vars_ge g ga) t2 t1)
              (fun st ->
                (if st then Monad.return g
                  else Monad.fail
                         (Monad.CheckFail
                           (SyntaxPED.loc_e (SyntaxPED.Ep_mvar (v, va)), g,
                             "expr", t2, t1)))))
    | t, p, g, d, SyntaxPED.Ep_concat (v, va), t1 ->
        Monad.check_bind (infer_e t p g d (SyntaxPED.Ep_concat (v, va)))
          (fun (_, (ga, t2)) ->
            Monad.check_bind
              (subtype (SyntaxPED.loc_e (SyntaxPED.Ep_concat (v, va))) t
                (Contexts.add_vars_ge g ga) t2 t1)
              (fun st ->
                (if st then Monad.return g
                  else Monad.fail
                         (Monad.CheckFail
                           (SyntaxPED.loc_e (SyntaxPED.Ep_concat (v, va)), g,
                             "expr", t2, t1)))))
    | t, p, g, d, SyntaxPED.Ep_tuple (v, va), t1 ->
        Monad.check_bind (infer_e t p g d (SyntaxPED.Ep_tuple (v, va)))
          (fun (_, (ga, t2)) ->
            Monad.check_bind
              (subtype (SyntaxPED.loc_e (SyntaxPED.Ep_tuple (v, va))) t
                (Contexts.add_vars_ge g ga) t2 t1)
              (fun st ->
                (if st then Monad.return g
                  else Monad.fail
                         (Monad.CheckFail
                           (SyntaxPED.loc_e (SyntaxPED.Ep_tuple (v, va)), g,
                             "expr", t2, t1)))))
    | t, p, g, d, SyntaxPED.Ep_app (v, va, vb), t1 ->
        Monad.check_bind (infer_e t p g d (SyntaxPED.Ep_app (v, va, vb)))
          (fun (_, (ga, t2)) ->
            Monad.check_bind
              (subtype (SyntaxPED.loc_e (SyntaxPED.Ep_app (v, va, vb))) t
                (Contexts.add_vars_ge g ga) t2 t1)
              (fun st ->
                (if st then Monad.return g
                  else Monad.fail
                         (Monad.CheckFail
                           (SyntaxPED.loc_e (SyntaxPED.Ep_app (v, va, vb)), g,
                             "expr", t2, t1)))))
    | t, p, g, d, SyntaxPED.Ep_bop (v, va, vb, vc), t1 ->
        Monad.check_bind (infer_e t p g d (SyntaxPED.Ep_bop (v, va, vb, vc)))
          (fun (_, (ga, t2)) ->
            Monad.check_bind
              (subtype (SyntaxPED.loc_e (SyntaxPED.Ep_bop (v, va, vb, vc))) t
                (Contexts.add_vars_ge g ga) t2 t1)
              (fun st ->
                (if st then Monad.return g
                  else Monad.fail
                         (Monad.CheckFail
                           (SyntaxPED.loc_e (SyntaxPED.Ep_bop (v, va, vb, vc)),
                             g, "expr", t2, t1)))))
    | t, p, g, d, SyntaxPED.Ep_uop (v, va, vb), t1 ->
        Monad.check_bind (infer_e t p g d (SyntaxPED.Ep_uop (v, va, vb)))
          (fun (_, (ga, t2)) ->
            Monad.check_bind
              (subtype (SyntaxPED.loc_e (SyntaxPED.Ep_uop (v, va, vb))) t
                (Contexts.add_vars_ge g ga) t2 t1)
              (fun st ->
                (if st then Monad.return g
                  else Monad.fail
                         (Monad.CheckFail
                           (SyntaxPED.loc_e (SyntaxPED.Ep_uop (v, va, vb)), g,
                             "expr", t2, t1)))))
    | t, p, g, d, SyntaxPED.Ep_proj (v, va, vb), t1 ->
        Monad.check_bind (infer_e t p g d (SyntaxPED.Ep_proj (v, va, vb)))
          (fun (_, (ga, t2)) ->
            Monad.check_bind
              (subtype (SyntaxPED.loc_e (SyntaxPED.Ep_proj (v, va, vb))) t
                (Contexts.add_vars_ge g ga) t2 t1)
              (fun st ->
                (if st then Monad.return g
                  else Monad.fail
                         (Monad.CheckFail
                           (SyntaxPED.loc_e (SyntaxPED.Ep_proj (v, va, vb)), g,
                             "expr", t2, t1)))))
    | t, p, g, d, SyntaxPED.Ep_constr (v, va, vb), t1 ->
        Monad.check_bind (infer_e t p g d (SyntaxPED.Ep_constr (v, va, vb)))
          (fun (_, (ga, t2)) ->
            Monad.check_bind
              (subtype (SyntaxPED.loc_e (SyntaxPED.Ep_constr (v, va, vb))) t
                (Contexts.add_vars_ge g ga) t2 t1)
              (fun st ->
                (if st then Monad.return g
                  else Monad.fail
                         (Monad.CheckFail
                           (SyntaxPED.loc_e (SyntaxPED.Ep_constr (v, va, vb)),
                             g, "expr", t2, t1)))))
    | t, p, g, d, SyntaxPED.Ep_field_access (v, va, vb), t1 ->
        Monad.check_bind
          (infer_e t p g d (SyntaxPED.Ep_field_access (v, va, vb)))
          (fun (_, (ga, t2)) ->
            Monad.check_bind
              (subtype (SyntaxPED.loc_e (SyntaxPED.Ep_field_access (v, va, vb)))
                t (Contexts.add_vars_ge g ga) t2 t1)
              (fun st ->
                (if st then Monad.return g
                  else Monad.fail
                         (Monad.CheckFail
                           (SyntaxPED.loc_e
                              (SyntaxPED.Ep_field_access (v, va, vb)),
                             g, "expr", t2, t1)))))
    | t, p, g, d, SyntaxPED.Ep_sizeof (v, va), t1 ->
        Monad.check_bind (infer_e t p g d (SyntaxPED.Ep_sizeof (v, va)))
          (fun (_, (ga, t2)) ->
            Monad.check_bind
              (subtype (SyntaxPED.loc_e (SyntaxPED.Ep_sizeof (v, va))) t
                (Contexts.add_vars_ge g ga) t2 t1)
              (fun st ->
                (if st then Monad.return g
                  else Monad.fail
                         (Monad.CheckFail
                           (SyntaxPED.loc_e (SyntaxPED.Ep_sizeof (v, va)), g,
                             "expr", t2, t1)))))
    | t, p, g, d, SyntaxPED.Ep_cast (v, va, vb), t1 ->
        Monad.check_bind (infer_e t p g d (SyntaxPED.Ep_cast (v, va, vb)))
          (fun (_, (ga, t2)) ->
            Monad.check_bind
              (subtype (SyntaxPED.loc_e (SyntaxPED.Ep_cast (v, va, vb))) t
                (Contexts.add_vars_ge g ga) t2 t1)
              (fun st ->
                (if st then Monad.return g
                  else Monad.fail
                         (Monad.CheckFail
                           (SyntaxPED.loc_e (SyntaxPED.Ep_cast (v, va, vb)), g,
                             "expr", t2, t1)))))
    | t, p, g, d, SyntaxPED.Ep_record (v, va), t1 ->
        Monad.check_bind (infer_e t p g d (SyntaxPED.Ep_record (v, va)))
          (fun (_, (ga, t2)) ->
            Monad.check_bind
              (subtype (SyntaxPED.loc_e (SyntaxPED.Ep_record (v, va))) t
                (Contexts.add_vars_ge g ga) t2 t1)
              (fun st ->
                (if st then Monad.return g
                  else Monad.fail
                         (Monad.CheckFail
                           (SyntaxPED.loc_e (SyntaxPED.Ep_record (v, va)), g,
                             "expr", t2, t1)))))
    | t, p, g, d, SyntaxPED.Ep_let2 (v, va, vb, vc, vd), t1 ->
        Monad.check_bind
          (infer_e t p g d (SyntaxPED.Ep_let2 (v, va, vb, vc, vd)))
          (fun (_, (ga, t2)) ->
            Monad.check_bind
              (subtype (SyntaxPED.loc_e (SyntaxPED.Ep_let2 (v, va, vb, vc, vd)))
                t (Contexts.add_vars_ge g ga) t2 t1)
              (fun st ->
                (if st then Monad.return g
                  else Monad.fail
                         (Monad.CheckFail
                           (SyntaxPED.loc_e
                              (SyntaxPED.Ep_let2 (v, va, vb, vc, vd)),
                             g, "expr", t2, t1)))))
    | t, p, g, d, SyntaxPED.Ep_block (v, []), t1 ->
        Monad.check_bind (infer_e t p g d (SyntaxPED.Ep_block (v, [])))
          (fun (_, (ga, t2)) ->
            Monad.check_bind
              (subtype (SyntaxPED.loc_e (SyntaxPED.Ep_block (v, []))) t
                (Contexts.add_vars_ge g ga) t2 t1)
              (fun st ->
                (if st then Monad.return g
                  else Monad.fail
                         (Monad.CheckFail
                           (SyntaxPED.loc_e (SyntaxPED.Ep_block (v, [])), g,
                             "expr", t2, t1)))))
    | t, p, g, d, SyntaxPED.Ep_exit (v, va), t1 ->
        Monad.check_bind (infer_e t p g d (SyntaxPED.Ep_exit (v, va)))
          (fun (_, (ga, t2)) ->
            Monad.check_bind
              (subtype (SyntaxPED.loc_e (SyntaxPED.Ep_exit (v, va))) t
                (Contexts.add_vars_ge g ga) t2 t1)
              (fun st ->
                (if st then Monad.return g
                  else Monad.fail
                         (Monad.CheckFail
                           (SyntaxPED.loc_e (SyntaxPED.Ep_exit (v, va)), g,
                             "expr", t2, t1)))))
    | t, p, g, d, SyntaxPED.Ep_throw (v, va), t1 ->
        Monad.check_bind (infer_e t p g d (SyntaxPED.Ep_throw (v, va)))
          (fun (_, (ga, t2)) ->
            Monad.check_bind
              (subtype (SyntaxPED.loc_e (SyntaxPED.Ep_throw (v, va))) t
                (Contexts.add_vars_ge g ga) t2 t1)
              (fun st ->
                (if st then Monad.return g
                  else Monad.fail
                         (Monad.CheckFail
                           (SyntaxPED.loc_e (SyntaxPED.Ep_throw (v, va)), g,
                             "expr", t2, t1)))))
    | t, p, g, d, SyntaxPED.Ep_try (v, va, vb), t1 ->
        Monad.check_bind (infer_e t p g d (SyntaxPED.Ep_try (v, va, vb)))
          (fun (_, (ga, t2)) ->
            Monad.check_bind
              (subtype (SyntaxPED.loc_e (SyntaxPED.Ep_try (v, va, vb))) t
                (Contexts.add_vars_ge g ga) t2 t1)
              (fun st ->
                (if st then Monad.return g
                  else Monad.fail
                         (Monad.CheckFail
                           (SyntaxPED.loc_e (SyntaxPED.Ep_try (v, va, vb)), g,
                             "expr", t2, t1)))))
    | t, p, g, d, SyntaxPED.Ep_constraint (v, va), t1 ->
        Monad.check_bind (infer_e t p g d (SyntaxPED.Ep_constraint (v, va)))
          (fun (_, (ga, t2)) ->
            Monad.check_bind
              (subtype (SyntaxPED.loc_e (SyntaxPED.Ep_constraint (v, va))) t
                (Contexts.add_vars_ge g ga) t2 t1)
              (fun st ->
                (if st then Monad.return g
                  else Monad.fail
                         (Monad.CheckFail
                           (SyntaxPED.loc_e (SyntaxPED.Ep_constraint (v, va)),
                             g, "expr", t2, t1)))))
    | t, p, g, d, SyntaxPED.Ep_for (v, va, vb, vc, vd, ve, vf), t1 ->
        Monad.check_bind
          (infer_e t p g d (SyntaxPED.Ep_for (v, va, vb, vc, vd, ve, vf)))
          (fun (_, (ga, t2)) ->
            Monad.check_bind
              (subtype
                (SyntaxPED.loc_e (SyntaxPED.Ep_for (v, va, vb, vc, vd, ve, vf)))
                t (Contexts.add_vars_ge g ga) t2 t1)
              (fun st ->
                (if st then Monad.return g
                  else Monad.fail
                         (Monad.CheckFail
                           (SyntaxPED.loc_e
                              (SyntaxPED.Ep_for (v, va, vb, vc, vd, ve, vf)),
                             g, "expr", t2, t1)))))
    | t, p, g, d, SyntaxPED.Ep_vec (v, va), t1 ->
        Monad.check_bind (infer_e t p g d (SyntaxPED.Ep_vec (v, va)))
          (fun (_, (ga, t2)) ->
            Monad.check_bind
              (subtype (SyntaxPED.loc_e (SyntaxPED.Ep_vec (v, va))) t
                (Contexts.add_vars_ge g ga) t2 t1)
              (fun st ->
                (if st then Monad.return g
                  else Monad.fail
                         (Monad.CheckFail
                           (SyntaxPED.loc_e (SyntaxPED.Ep_vec (v, va)), g,
                             "expr", t2, t1)))))
    | t, p, g, d, SyntaxPED.Ep_list (v, va), t1 ->
        Monad.check_bind (infer_e t p g d (SyntaxPED.Ep_list (v, va)))
          (fun (_, (ga, t2)) ->
            Monad.check_bind
              (subtype (SyntaxPED.loc_e (SyntaxPED.Ep_list (v, va))) t
                (Contexts.add_vars_ge g ga) t2 t1)
              (fun st ->
                (if st then Monad.return g
                  else Monad.fail
                         (Monad.CheckFail
                           (SyntaxPED.loc_e (SyntaxPED.Ep_list (v, va)), g,
                             "expr", t2, t1)))))
    | t, p, g, d, SyntaxPED.Ep_cons (v, va, vb), t1 ->
        Monad.check_bind (infer_e t p g d (SyntaxPED.Ep_cons (v, va, vb)))
          (fun (_, (ga, t2)) ->
            Monad.check_bind
              (subtype (SyntaxPED.loc_e (SyntaxPED.Ep_cons (v, va, vb))) t
                (Contexts.add_vars_ge g ga) t2 t1)
              (fun st ->
                (if st then Monad.return g
                  else Monad.fail
                         (Monad.CheckFail
                           (SyntaxPED.loc_e (SyntaxPED.Ep_cons (v, va, vb)), g,
                             "expr", t2, t1)))))
and infer_e_lbind
  loc t pa g d p e =
    Monad.check_bind (infer_pat g loc p)
      (fun (x1, (g1, (t1, vars))) ->
        Monad.check_bind
          (match t1
            with None ->
              Monad.check_bind (infer_e t pa g d e)
                (fun (_, (g2, t2)) ->
                  Monad.check_bind
                    (check_pat true t pa (Contexts.add_vars_ge g g2) p t2)
                    (fun (x1a, (g1a, varsa)) ->
                      Monad.return (x1a, (g1a @ g2, (t2, varsa)))))
            | Some t1a ->
              Monad.check_bind (check_s t pa g d e t1a)
                (fun _ -> Monad.return (x1, (g1, (t1a, vars)))))
          (fun (z, (gs, (ta, varsa))) ->
            Monad.check_bind
              (Monad.mk_fresh
                [Stringa.Chara
                   (false, false, false, false, true, true, true, false);
                  Stringa.Chara
                    (true, false, false, false, false, true, true, false);
                  Stringa.Chara
                    (false, false, true, false, true, true, true, false)])
              (fun za ->
                Monad.check_bind (Monad.freshen_t ta)
                  (fun tb ->
                    Monad.return
                      (za, ((za, (Contexts.b_of tb,
                                   SyntaxVCT.C_conj
                                     (mk_c_eq z za,
                                       Contexts.subst_c_v0 (Contexts.c_of tb)
 (Monad.mk_var z)))) ::
                              gs,
                             (tb, varsa)))))))
and infer_e
  t p g d x4 = match t, p, g, d, x4 with
    t, p, g, d, SyntaxPED.Ep_val (uu, v) ->
      Monad.check_bind (infer_v t p g d v)
        (fun (z, (ga, ta)) -> Monad.return (z, (ga, ta)))
    | t, p, g, d, SyntaxPED.Ep_app (loc, f, e) ->
        Monad.check_bind (Monad.lookup_fun_and_convert_aux t p f)
          (fun a ->
            (match a
              with [] ->
                Monad.fail
                  (Monad.FunctionUnknown (SyntaxPED.Ep_app (loc, f, e), f))
              | aa :: lista -> infer_app t p g d (aa :: lista) e))
    | t, p, g, d, SyntaxPED.Ep_proj (loc, fid, e) ->
        Monad.check_bind (infer_e t p g d e)
          (fun (z, (ga, ta)) ->
            (match Contexts.b_of ta
              with SyntaxVCT.B_var _ -> Monad.fail (Monad.UnknownErrorLoc loc)
              | SyntaxVCT.B_tid _ -> Monad.fail (Monad.UnknownErrorLoc loc)
              | SyntaxVCT.B_int -> Monad.fail (Monad.UnknownErrorLoc loc)
              | SyntaxVCT.B_bool -> Monad.fail (Monad.UnknownErrorLoc loc)
              | SyntaxVCT.B_bit -> Monad.fail (Monad.UnknownErrorLoc loc)
              | SyntaxVCT.B_unit -> Monad.fail (Monad.UnknownErrorLoc loc)
              | SyntaxVCT.B_real -> Monad.fail (Monad.UnknownErrorLoc loc)
              | SyntaxVCT.B_vec (_, _) -> Monad.fail (Monad.UnknownErrorLoc loc)
              | SyntaxVCT.B_list _ -> Monad.fail (Monad.UnknownErrorLoc loc)
              | SyntaxVCT.B_tuple _ -> Monad.fail (Monad.UnknownErrorLoc loc)
              | SyntaxVCT.B_union (_, _) ->
                Monad.fail (Monad.UnknownErrorLoc loc)
              | SyntaxVCT.B_record ft ->
                (match Contexts.lookup Stringa.equal_literal ft fid
                  with None -> Monad.fail (Monad.UnknownErrorLoc loc)
                  | Some b ->
                    Monad.check_bind
                      (Monad.mk_fresh
                        [Stringa.Chara
                           (false, false, false, false, true, true, true,
                             false);
                          Stringa.Chara
                            (false, true, false, false, true, true, true,
                              false);
                          Stringa.Chara
                            (true, true, true, true, false, true, true, false);
                          Stringa.Chara
                            (false, true, false, true, false, true, true,
                              false)])
                      (fun za ->
                        Monad.return
                          (za, ((za, (b, Contexts.mk_proj_eq_x z za fid)) :: ga,
                                 SyntaxVCT.T_refined_type
                                   (SyntaxVCT.VIndex, b,
                                     Contexts.mk_proj_eq z fid)))))
              | SyntaxVCT.B_undef -> Monad.fail (Monad.UnknownErrorLoc loc)
              | SyntaxVCT.B_reg -> Monad.fail (Monad.UnknownErrorLoc loc)
              | SyntaxVCT.B_string -> Monad.fail (Monad.UnknownErrorLoc loc)
              | SyntaxVCT.B_exception -> Monad.fail (Monad.UnknownErrorLoc loc)
              | SyntaxVCT.B_finite_set _ ->
                Monad.fail (Monad.UnknownErrorLoc loc)))
    | ux, uy, uz, vg, SyntaxPED.Ep_bop (loc, vh, vi, vj) ->
        Monad.fail (Monad.NotImplemented (loc, "bop"))
    | vk, vl, vm, vn, SyntaxPED.Ep_uop (loc, vo, vp) ->
        Monad.fail (Monad.NotImplemented (loc, "uop"))
    | t, p, g, d, SyntaxPED.Ep_tuple (loc, es) ->
        Monad.check_bind (Monad.mapM (infer_e t p g d) es)
          (fun xx ->
            Monad.check_bind (Monad.return (unzip3 xx))
              (fun (_, (ga, ts)) ->
                Monad.check_bind (Monad.return (Lista.concat ga))
                  (fun gb ->
                    Monad.check_bind
                      (Monad.mk_fresh
                        [Stringa.Chara
                           (true, false, false, true, false, true, true, false);
                          Stringa.Chara
                            (false, false, true, false, true, true, true,
                              false);
                          Stringa.Chara
                            (true, false, true, false, true, true, true, false);
                          Stringa.Chara
                            (false, false, false, false, true, true, true,
                              false)])
                      (fun z ->
                        Monad.check_bind (convert_to_stM ts)
                          (fun (ks, (bs, cs)) ->
                            Monad.return
                              (z, ((z, (SyntaxVCT.B_tuple bs,
 Contexts.subst_c_x cs z)) ::
                                     ks @ gb,
                                    SyntaxVCT.T_refined_type
                                      (SyntaxVCT.VIndex, SyntaxVCT.B_tuple bs,
cs))))))))
    | t, p, g, d, SyntaxPED.Ep_record (loc, fs) ->
        Monad.fail (Monad.NotImplemented (loc, "infer record"))
    | t, p, g, d, SyntaxPED.Ep_constr (loc, c, e) ->
        (match ContextsPiDelta.lookup_constr_union t c
          with None -> Monad.fail (Monad.UnknownConstructor (loc, c))
          | Some ta ->
            Monad.check_bind
              (Monad.mk_fresh
                [Stringa.Chara
                   (true, false, false, true, false, true, true, false);
                  Stringa.Chara
                    (true, true, false, false, false, true, true, false)])
              (fun z ->
                Monad.check_bind (Monad.freshen_t ta)
                  (fun tb ->
                    Monad.return
                      (z, ((z, (Contexts.b_of tb,
                                 Contexts.subst_c_x (Contexts.c_of tb) z)) ::
                             kvars_of tb,
                            tb)))))
    | t, p, g, d, SyntaxPED.Ep_vec (loc, es) ->
        Monad.check_bind (Monad.mapM (infer_e t p g d) es)
          (fun xx ->
            Monad.check_bind (Monad.return (unzip3 xx))
              (fun (_, (ga, ts)) ->
                Monad.check_bind (Monad.return (Lista.concat ga))
                  (fun gb ->
                    Monad.check_bind
                      (Monad.mk_fresh
                        [Stringa.Chara
                           (true, false, false, true, false, true, true, false);
                          Stringa.Chara
                            (false, false, true, false, true, true, true,
                              false);
                          Stringa.Chara
                            (true, false, true, false, true, true, true, false);
                          Stringa.Chara
                            (false, false, false, false, true, true, true,
                              false)])
                      (fun z ->
                        (match check_bases ts
                          with None ->
                            Monad.fail
                              (Monad.TypeError (loc, "Incompatible elements"))
                          | Some b ->
                            (match ContextsPiDelta.theta_d t
                              with None ->
                                Monad.fail
                                  (Monad.TypeError
                                    (loc, "Default order not set"))
                              | Some ord ->
                                Monad.return
                                  (z, (gb,
SyntaxVCT.T_refined_type
  (SyntaxVCT.VIndex, SyntaxVCT.B_vec (ord, b), SyntaxVCT.C_true)))))))))
    | t, p, g, d, SyntaxPED.Ep_list (loc, es) ->
        Monad.fail (Monad.NotImplemented (loc, "list"))
    | ta, p, g, d, SyntaxPED.Ep_cast (loc, t, e) ->
        Monad.check_bind (infer_e ta p g d e)
          (fun (z, (ga, tb)) ->
            Monad.check_bind (subtype loc ta (Contexts.add_vars_ge g ga) tb t)
              (fun b ->
                (if b then Monad.return (z, (ga, t))
                  else Monad.fail
                         (Monad.CheckFail (loc, g, "cast expr", tb, t)))))
    | ta, p, g, d, SyntaxPED.Ep_sizeof (loc, t) ->
        Monad.check_bind
          (Monad.mk_fresh
            [Stringa.Chara (true, true, false, false, true, true, true, false);
              Stringa.Chara
                (false, true, false, true, true, true, true, false)])
          (fun z ->
            Monad.check_bind
              (subtype loc ta g
                (SyntaxVCT.T_refined_type
                  (SyntaxVCT.VIndex, SyntaxVCT.B_int,
                    SyntaxVCT.C_eq
                      (t, SyntaxVCT.CE_val (SyntaxVCT.V_var SyntaxVCT.VIndex))))
                (SyntaxVCT.T_refined_type
                  (SyntaxVCT.VIndex, SyntaxVCT.B_int, SyntaxVCT.C_true)))
              (fun b ->
                (if b then Monad.return
                             (z, ([(z, (SyntaxVCT.B_int,
 SyntaxVCT.C_eq (t, SyntaxVCT.CE_val (SyntaxVCT.V_var z))))],
                                   SyntaxVCT.T_refined_type
                                     (SyntaxVCT.VIndex, SyntaxVCT.B_int,
                                       SyntaxVCT.C_eq
 (t, SyntaxVCT.CE_val (SyntaxVCT.V_var SyntaxVCT.VIndex)))))
                  else Monad.fail
                         (Monad.CheckFail
                           (loc, g, "sizeof",
                             SyntaxVCT.T_refined_type
                               (SyntaxVCT.VIndex, SyntaxVCT.B_int,
                                 SyntaxVCT.C_eq
                                   (t, SyntaxVCT.CE_val
 (SyntaxVCT.V_var SyntaxVCT.VIndex))),
                             SyntaxVCT.T_refined_type
                               (SyntaxVCT.VIndex, SyntaxVCT.B_int,
                                 SyntaxVCT.C_true))))))
    | t, p, g, d, SyntaxPED.Ep_concat (loc, es) ->
        Monad.fail (Monad.NotImplemented (loc, " concat expr "))
    | t, p, g, d, SyntaxPED.Ep_if (loc, e, e1, e2) ->
        Monad.check_bind (infer_e t p g d e)
          (fun (_, (ga, ta)) ->
            (match ta
              with SyntaxVCT.T_refined_type (_, SyntaxVCT.B_var _, _) ->
                Monad.fail (Monad.IfCondType (loc, ta))
              | SyntaxVCT.T_refined_type (_, SyntaxVCT.B_tid _, _) ->
                Monad.fail (Monad.IfCondType (loc, ta))
              | SyntaxVCT.T_refined_type (_, SyntaxVCT.B_int, _) ->
                Monad.fail (Monad.IfCondType (loc, ta))
              | SyntaxVCT.T_refined_type (_, SyntaxVCT.B_bool, c1) ->
                Monad.check_bind
                  (Monad.mk_fresh
                    [Stringa.Chara
                       (true, false, false, true, false, true, true, false);
                      Stringa.Chara
                        (false, true, true, false, false, true, true, false)])
                  (fun z ->
                    Monad.check_bind
                      (infer_e t p
                        (Contexts.add_vars_ge g
                          ((z, (SyntaxVCT.B_bool,
                                 SyntaxVCT.C_conj
                                   (SyntaxVCT.C_eq
                                      (SyntaxVCT.CE_val (SyntaxVCT.V_var z),
SyntaxVCT.CE_val (SyntaxVCT.V_lit SyntaxVCT.L_true)),
                                     SyntaxPED.subst_cp (SyntaxVCT.V_var z)
                                       SyntaxVCT.VIndex c1))) ::
                            ga))
                        d e1)
                      (fun (_, (g1, t1)) ->
                        Monad.check_bind
                          (infer_e t p
                            (Contexts.add_vars_ge g
                              ((z, (SyntaxVCT.B_bool,
                                     SyntaxVCT.C_conj
                                       (SyntaxVCT.C_eq
  (SyntaxVCT.CE_val (SyntaxVCT.V_var z),
    SyntaxVCT.CE_val (SyntaxVCT.V_lit SyntaxVCT.L_false)),
 SyntaxPED.subst_cp (SyntaxVCT.V_var z) SyntaxVCT.VIndex c1))) ::
                                ga))
                            d e2)
                          (fun (_, (g2, t2)) ->
                            (if SyntaxVCT.equal_bpa (Contexts.b_of t1)
                                  (Contexts.b_of t2)
                              then Monad.return
                                     (z, (g1 @ g2,
   SyntaxVCT.T_refined_type
     (SyntaxVCT.VIndex, Contexts.b_of t1,
       SyntaxVCT.C_disj (Contexts.c_of t1, Contexts.c_of t2))))
                              else Monad.fail
                                     (Monad.CheckFail
                                       (loc, g,
 "if branches base type mismatch ", t2, t1))))))
              | SyntaxVCT.T_refined_type (_, SyntaxVCT.B_bit, _) ->
                Monad.fail (Monad.IfCondType (loc, ta))
              | SyntaxVCT.T_refined_type (_, SyntaxVCT.B_unit, _) ->
                Monad.fail (Monad.IfCondType (loc, ta))
              | SyntaxVCT.T_refined_type (_, SyntaxVCT.B_real, _) ->
                Monad.fail (Monad.IfCondType (loc, ta))
              | SyntaxVCT.T_refined_type (_, SyntaxVCT.B_vec (_, _), _) ->
                Monad.fail (Monad.IfCondType (loc, ta))
              | SyntaxVCT.T_refined_type (_, SyntaxVCT.B_list _, _) ->
                Monad.fail (Monad.IfCondType (loc, ta))
              | SyntaxVCT.T_refined_type (_, SyntaxVCT.B_tuple _, _) ->
                Monad.fail (Monad.IfCondType (loc, ta))
              | SyntaxVCT.T_refined_type (_, SyntaxVCT.B_union (_, _), _) ->
                Monad.fail (Monad.IfCondType (loc, ta))
              | SyntaxVCT.T_refined_type (_, SyntaxVCT.B_record _, _) ->
                Monad.fail (Monad.IfCondType (loc, ta))
              | SyntaxVCT.T_refined_type (_, SyntaxVCT.B_undef, _) ->
                Monad.fail (Monad.IfCondType (loc, ta))
              | SyntaxVCT.T_refined_type (_, SyntaxVCT.B_reg, _) ->
                Monad.fail (Monad.IfCondType (loc, ta))
              | SyntaxVCT.T_refined_type (_, SyntaxVCT.B_string, _) ->
                Monad.fail (Monad.IfCondType (loc, ta))
              | SyntaxVCT.T_refined_type (_, SyntaxVCT.B_exception, _) ->
                Monad.fail (Monad.IfCondType (loc, ta))
              | SyntaxVCT.T_refined_type (_, SyntaxVCT.B_finite_set _, _) ->
                Monad.fail (Monad.IfCondType (loc, ta))))
    | t, p, g, d, SyntaxPED.Ep_block (loc, [e]) -> infer_e t p g d e
    | t, p, g, d, SyntaxPED.Ep_block (loc, e :: v :: va) ->
        Monad.check_bind
          (check_s t p g d e
            (SyntaxVCT.T_refined_type
              (SyntaxVCT.VIndex, SyntaxVCT.B_unit, SyntaxVCT.C_true)))
          (fun ga -> infer_e t p ga d (SyntaxPED.Ep_block (loc, v :: va)))
    | t, pa, g, d, SyntaxPED.Ep_let (l, SyntaxPED.LBp_val (vr, p, e), s) ->
        Monad.check_bind (infer_e_lbind l t pa g d p e)
          (fun (_, (ga, (_, vars))) ->
            Monad.check_bind (check_varsM g l vars)
              (fun _ ->
                Monad.check_bind
                  (infer_e t pa
                    (Contexts.add_vars_ge (Contexts.add_to_scope g vars) ga) d
                    s)
                  (fun (x, (g2, t2)) -> Monad.return (x, (g2 @ ga, t2)))))
    | t, p, g, d, SyntaxPED.Ep_field_access (loc, va, vb) ->
        Monad.fail (Monad.NotImplemented (loc, " field access expr "))
    | t, p, g, d, SyntaxPED.Ep_record_update (loc, va, vb) ->
        Monad.fail (Monad.NotImplemented (loc, " record update "))
    | t, p, g, d, SyntaxPED.Ep_let2 (loc, va, vb, vc, vd) ->
        Monad.fail (Monad.NotImplemented (loc, " let2 expr "))
    | t, p, g, d, SyntaxPED.Ep_case (loc, va, vb) ->
        Monad.fail (Monad.NotImplemented (loc, " infer case  expr "))
    | t, p, g, d, SyntaxPED.Ep_assign (loc, e1, e2, e3) ->
        Monad.check_bind (infer_e t p g d e2)
          (fun (_, (g1, t2)) ->
            Monad.check_bind
              (check_lexp t p (Contexts.add_vars_ge g g1) d e1 t2)
              (fun (_, (ga, _)) ->
                Monad.check_bind
                  (Monad.mk_fresh
                    [Stringa.Chara
                       (true, false, false, false, false, true, true, false);
                      Stringa.Chara
                        (true, true, true, false, false, true, true, false);
                      Stringa.Chara
                        (false, true, true, true, false, true, true, false)])
                  (fun z ->
                    Monad.return
                      (z, ((z, (SyntaxVCT.B_unit, SyntaxVCT.C_true)) :: ga @ g1,
                            SyntaxVCT.T_refined_type
                              (SyntaxVCT.VIndex, SyntaxVCT.B_unit,
                                SyntaxVCT.C_true))))))
    | t, p, g, d, SyntaxPED.Ep_exit (loc, va) ->
        Monad.fail (Monad.NotImplemented (loc, " infer exit expr "))
    | t, p, g, d, SyntaxPED.Ep_return (loc, va) ->
        Monad.fail (Monad.NotImplemented (loc, " infer return expr "))
    | t, p, g, d, SyntaxPED.Ep_throw (loc, va) ->
        Monad.fail (Monad.NotImplemented (loc, " therow expr "))
    | t, p, g, d, SyntaxPED.Ep_try (loc, va, vb) ->
        Monad.fail (Monad.NotImplemented (loc, " try expr "))
    | t, p, g, d, SyntaxPED.Ep_constraint (loc, va) ->
        Monad.fail (Monad.NotImplemented (loc, " constraint expr "))
    | t, p, g, d, SyntaxPED.Ep_loop (loc, vs, e1, e2) ->
        Monad.check_bind
          (check_s t p g d e1
            (SyntaxVCT.T_refined_type
              (SyntaxVCT.VIndex, SyntaxVCT.B_bool, SyntaxVCT.C_true)))
          (fun ga ->
            Monad.check_bind
              (check_s t p ga d e2
                (SyntaxVCT.T_refined_type
                  (SyntaxVCT.VIndex, SyntaxVCT.B_unit, SyntaxVCT.C_true)))
              (fun _ ->
                Monad.check_bind
                  (Monad.mk_fresh
                    [Stringa.Chara
                       (true, false, false, true, false, true, true, false);
                      Stringa.Chara
                        (true, true, true, true, true, false, true, false);
                      Stringa.Chara
                        (false, false, true, true, false, true, true, false);
                      Stringa.Chara
                        (true, true, true, true, false, true, true, false);
                      Stringa.Chara
                        (true, true, true, true, false, true, true, false);
                      Stringa.Chara
                        (false, false, false, false, true, true, true, false)])
                  (fun z ->
                    Monad.return
                      (z, ([(z, (SyntaxVCT.B_unit, SyntaxVCT.C_true))],
                            SyntaxVCT.T_refined_type
                              (SyntaxVCT.VIndex, SyntaxVCT.B_unit,
                                SyntaxVCT.C_true))))))
    | t, p, g, d, SyntaxPED.Ep_assert (loc, va, vb) ->
        Monad.fail (Monad.NotImplemented (loc, " assert expr "))
    | t, p, g, d, SyntaxPED.Ep_cons (loc, va, vb) ->
        Monad.fail (Monad.NotImplemented (loc, " cons expr "))
and infer_app
  t p g d x4 e = match t, p, g, d, x4, e with
    t, p, g, d, [], e -> Monad.fail (Monad.UnknownErrorLoc (SyntaxPED.loc_e e))
    | t, p, g, d, (uv, (SyntaxVCT.A_function (z2, b2, c2, tau), uw)) :: asa, e
        -> Monad.check_bind (infer_e t p g d e)
             (fun (_, (ga, ta)) ->
               Monad.check_bind (Monad.freshen_t ta)
                 (fun taa ->
                   Monad.check_bind
                     (subtype (SyntaxPED.loc_e e) t (Contexts.add_vars_ge g ga)
                       taa (SyntaxVCT.T_refined_type
                             (SyntaxVCT.VIndex, b2,
                               SyntaxPED.subst_cp
                                 (SyntaxVCT.V_var SyntaxVCT.VIndex) z2 c2)))
                     (fun st ->
                       (if st
                         then Monad.check_bind
                                (Monad.return
                                  (Satis.type_app b2 (Contexts.b_of taa)))
                                (fun sub ->
                                  Monad.check_bind
                                    (Monad.mk_fresh
                                      [Stringa.Chara
 (true, false, false, false, false, true, true, false);
Stringa.Chara (false, false, false, false, true, true, true, false);
Stringa.Chara (false, false, false, false, true, true, true, false)])
                                    (fun z ->
                                      Monad.check_bind
(Monad.return
  (SyntaxVCT.T_refined_type
    (SyntaxVCT.VIndex, tsubst_b_bs (Contexts.b_of tau) sub, Contexts.c_of tau)))
(fun taua ->
  (let kv =
     (z, (Contexts.b_of taua,
           SyntaxVCT.C_conj_many
             [Contexts.subst_c_v0 (Contexts.c_of taa) (Monad.mk_var z2);
               Contexts.subst_c_v0 (Contexts.c_of taua) (Monad.mk_var z)]))
     in
    Monad.check_bind (Monad.trace (Monad.AppI Monad.VarI))
      (fun _ ->
        Monad.return
          (z, (kv :: [] @ ga @ [] @ [(z2, (tsubst_b_bs b2 sub, c2))],
                taua)))))))
                         else (if Arith.less_nat Arith.zero_nat
                                    (Lista.size_list asa)
                                then infer_app t p g d asa e
                                else Monad.fail
                                       (Monad.FunctionArgWrongType
 (SyntaxPED.loc_e e, taa,
   SyntaxVCT.T_refined_type
     (SyntaxVCT.VIndex, b2,
       SyntaxPED.subst_cp (SyntaxVCT.V_var SyntaxVCT.VIndex) z2 c2))))))))
    | t, p, g, d, (vb, (SyntaxVCT.A_monotype vf, ve)) :: va, vq ->
        Monad.fail Monad.UnknownError;;

let rec return_fun
  t = (let arg = SyntaxVCT.VNamed "return_arg" in
        (SyntaxVCT.VNamed "return",
          (SyntaxVCT.A_function
             (arg, Contexts.b_of t,
               SyntaxPED.subst_cp (SyntaxVCT.V_var arg) SyntaxVCT.VIndex
                 (Contexts.c_of t),
               t),
            None)));;

let rec check_funcl
  t p g fdef (SyntaxPED.FCLp_funcl (loc, f, pexp)) =
    Monad.check_bind (Monad.convert_fun (SyntaxVCT.VNamed f, (fdef, Some pexp)))
      (fun (_, (SyntaxVCT.A_function (x, b, c, ta),
                 Some (SyntaxPED.PEXPp_exp (pa, e))))
        -> Monad.check_bind (Monad.return (Contexts.add_to_scope g [x]))
             (fun g1 ->
               Monad.check_bind
                 (Monad.return
                   (Contexts.add_var g1 (x, Contexts.GEPair (b, c))))
                 (fun g1a ->
                   Monad.check_bind
                     (check_pat true t p g1a pa
                       (SyntaxVCT.T_refined_type
                         (SyntaxVCT.VIndex, b,
                           SyntaxVCT.C_eq
                             (SyntaxVCT.CE_val
                                (SyntaxVCT.V_var SyntaxVCT.VIndex),
                               SyntaxVCT.CE_val (SyntaxVCT.V_var x)))))
                     (fun (_, (bs, vars)) ->
                       Monad.check_bind (check_varsM g1a loc vars)
                         (fun _ ->
                           Monad.check_bind
                             (Monad.return (Contexts.add_to_scope g1a vars))
                             (fun g1b ->
                               Monad.check_bind
                                 (Monad.return (Contexts.add_vars_ge g1b bs))
                                 (fun g1c ->
                                   Monad.check_bind
                                     (check_s t
                                       (ContextsPiDelta.add_fun p
 (return_fun ta))
                                       g1c ContextsPiDelta.emptyDEnv e ta)
                                     (fun _ ->
                                       Monad.return
 (t, (ContextsPiDelta.add_fun p (SyntaxVCT.VNamed f, (fdef, Some pexp)),
       g))))))))));;

let rec check_scattered
  t p g x3 = match t, p, g, x3 with
    t, p, g,
      SyntaxPED.SDp_function (loc, SyntaxPED.Typ_annot_opt_pnone uu, name)
      -> Monad.return (t, (p, g))
    | t, p, g,
        SyntaxPED.SDp_function
          (uv, SyntaxPED.Typ_annot_opt_psome_fn (uw, fdef), name)
        -> Monad.return
             (t, (ContextsPiDelta.add_fun p
                    (SyntaxVCT.VNamed name, (fdef, None)),
                   g))
    | t, p, g, SyntaxPED.SDp_funclp (ux, SyntaxPED.FCLp_funcl (loc, f, pexp)) ->
        (match Monad.lookup_fun t p (SyntaxVCT.VNamed f)
          with None ->
            Monad.fail (Monad.TypeError (loc, "No valspec for function"))
          | Some [] ->
            Monad.fail (Monad.TypeError (loc, "No valspec for function"))
          | Some [(_, (fdef, _))] ->
            check_funcl t p g fdef (SyntaxPED.FCLp_funcl (loc, f, pexp))
          | Some ((_, (_, _)) :: _ :: _) ->
            Monad.fail (Monad.TypeError (loc, "No valspec for function")))
    | t, p, g, SyntaxPED.SDp_variant (loc, x, kids) ->
        (match
          Contexts.lookup SyntaxVCT.equal_xp (ContextsPiDelta.theta_T t)
            (SyntaxVCT.VNamed x)
          with None ->
            (let tau =
               SyntaxVCT.T_refined_type
                 (SyntaxVCT.VIndex, SyntaxVCT.B_union (x, []), SyntaxVCT.C_true)
               in
              Monad.return
                (ContextsPiDelta.theta_T_update
                   (fun _ ->
                     (SyntaxVCT.VNamed x, tau) :: ContextsPiDelta.theta_T t)
                   t,
                  (p, g)))
          | Some _ ->
            Monad.fail
              (Monad.TypeError (loc, ("Type " ^ x) ^ " already defined")))
    | t, p, g, SyntaxPED.SDp_unioncl (loc, union_name, variant_name, t1) ->
        (match
          Contexts.lookup SyntaxVCT.equal_xp (ContextsPiDelta.theta_T t)
            (SyntaxVCT.VNamed union_name)
          with None -> Monad.return (t, (p, g))
          | Some (SyntaxVCT.T_refined_type
                   (zvar, SyntaxVCT.B_union (nme, bs), c))
            -> Monad.return
                 (ContextsPiDelta.update_type t (SyntaxVCT.VNamed union_name)
                    (SyntaxVCT.T_refined_type
                      (zvar, SyntaxVCT.B_union (nme, bs @ [(variant_name, t1)]),
                        c)),
                   (p, g)))
    | t, p, g, SyntaxPED.SDp_end (uy, name) -> Monad.return (t, (p, g));;

let rec check_def_funcl
  t p g fdef x4 = match t, p, g, fdef, x4 with
    t, p, g, fdef, [] -> Monad.return (t, (p, g))
    | t, p, g, fdef, funclps :: pes ->
        Monad.check_bind (check_funcl t p g fdef funclps)
          (fun (ta, (pa, ga)) -> check_def_funcl ta pa ga fdef pes);;

let rec check_def
  t p g x3 = match t, p, g, x3 with
    t, p, g, SyntaxPED.DEFp_typedef (loc, x, xbc, tau) ->
      (match
        Contexts.lookup SyntaxVCT.equal_xp (ContextsPiDelta.theta_T t)
          (SyntaxVCT.VNamed x)
        with None ->
          Monad.return
            (ContextsPiDelta.add_type t (SyntaxVCT.VNamed x) tau, (p, g))
        | Some _ ->
          Monad.fail
            (Monad.TypeError (loc, ("Type " ^ x) ^ " already defined")))
    | t, p, g, SyntaxPED.DEFp_fundef (loc, SyntaxVCT.A_monotype uu, e) ->
        Monad.fail (Monad.NotImplemented (loc, "fundef"))
    | t, p, g,
        SyntaxPED.DEFp_fundef (loc, SyntaxVCT.A_function (v, va, vb, vc), pexps)
        -> check_def_funcl t p g (SyntaxVCT.A_function (v, va, vb, vc)) pexps
    | ta, p, g,
        SyntaxPED.DEFp_spec
          (loc, f, SyntaxVCT.A_function (SyntaxVCT.VNamed x, b, c, t))
        -> Monad.return
             (ta, (ContextsPiDelta.add_fun p
                     (SyntaxVCT.VNamed f,
                       (SyntaxVCT.A_function (SyntaxVCT.VNamed x, b, c, t),
                         None)),
                    g))
    | t, p, g, SyntaxPED.DEFp_spec (loc, f, SyntaxVCT.A_monotype uv) ->
        Monad.fail (Monad.NotImplemented (loc, "spec"))
    | t, pa, g, SyntaxPED.DEFp_val (loc, SyntaxPED.LBp_val (uw, p, e)) ->
        Monad.check_bind
          (infer_e_lbind loc t pa g ContextsPiDelta.emptyDEnv p e)
          (fun (z, (bs, (ta, vars))) ->
            Monad.check_bind (check_varsM g loc vars)
              (fun _ ->
                Monad.check_bind
                  (Monad.mk_fresh
                    [Stringa.Chara
                       (false, false, true, false, false, true, true, false);
                      Stringa.Chara
                        (false, false, false, false, true, true, true, false);
                      Stringa.Chara
                        (true, false, false, false, false, true, true, false);
                      Stringa.Chara
                        (false, false, true, false, true, true, true, false)])
                  (fun za ->
                    Monad.check_bind (Monad.freshen_t ta)
                      (fun taa ->
                        Monad.return
                          (t, (pa, Contexts.add_vars_ge
                                     (Contexts.add_to_scope g vars)
                                     ((za,
(Contexts.b_of taa,
  SyntaxVCT.C_conj
    (mk_c_eq z za,
      Contexts.subst_c_v0 (Contexts.c_of taa) (Monad.mk_var z)))) ::
                                       bs @ kvars_of taa)))))))
    | t, p, g, SyntaxPED.DEFp_overload (loc, idd, idlist) ->
        Monad.return
          (t, (ContextsPiDelta.phi_o_update
                 (fun _ ->
                   Finite_Map.fmupd SyntaxVCT.equal_xp (SyntaxVCT.VNamed idd)
                     (Lista.map (fun a -> SyntaxVCT.VNamed a) idlist)
                     (ContextsPiDelta.phi_o p))
                 p,
                g))
    | t, p, g, SyntaxPED.DEFp_default (loc, order) ->
        Monad.return
          (ContextsPiDelta.theta_d_update (fun _ -> Some order) t, (p, g))
    | t, p, g, SyntaxPED.DEFp_scattered (ux, sd) -> check_scattered t p g sd;;

let rec check_defs
  t p g x3 = match t, p, g, x3 with t, p, g, [] -> Monad.return g
    | t, p, g, def :: defs ->
        Monad.check_bind (check_def t p g def)
          (fun (ta, (pa, ga)) -> check_defs ta pa ga defs);;

let rec fix_defs_p (SyntaxPED.Pp_prog defs) = SyntaxPED.Pp_prog defs;;

let rec check_p_emptyEnv
  (SyntaxPED.Pp_prog defs) =
    check_defs ContextsPiDelta.emptyThetaEnv ContextsPiDelta.emptyPiEnv
      Contexts.emptyEnv defs;;

end;; (*struct TypingMonadFunction*)
