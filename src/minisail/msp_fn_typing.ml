open Msp_ast
module Satis : sig
  val upto : Arith.nat -> Arith.nat list
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
      SyntaxVCT.bp -> (string * SyntaxVCT.bp) list
  val convert_b :
    unit ContextsPiDelta.theta_ext ->
      SyntaxVCT.vp -> SyntaxVCT.bp -> Z3.z3_type * Z3.z3_bool_expr
  val convert_blist :
    unit ContextsPiDelta.theta_ext ->
      SyntaxVCT.vp ->
        SyntaxVCT.bp list -> Z3.z3_type list * Z3.z3_bool_expr list
  val convert_xbc :
    unit ContextsPiDelta.theta_ext ->
      SyntaxVCT.xp ->
        SyntaxVCT.bp -> SyntaxVCT.cp -> Z3.z3_decl list * Z3.z3_bool_expr
  val subst_c_z : SyntaxVCT.xp -> SyntaxVCT.cp -> SyntaxVCT.cp
  val convert_g_aux :
    unit ContextsPiDelta.theta_ext ->
      (SyntaxVCT.xp * Contexts.g_entry) list ->
        Z3.z3_decl list * Z3.z3_bool_expr list
  val convert_smt_problem_valid :
    unit ContextsPiDelta.theta_ext ->
      ('a, unit) Contexts.gamma_ext ->
        (SyntaxVCT.xp * Contexts.g_entry) list ->
          SyntaxVCT.cp ->
            (SyntaxVCT.xp * Contexts.g_entry) list *
              (Z3.z3_decl list * (Z3.z3_decl list * Z3.z3_bool_expr))
  val pp_z3_expr : Z3.z3_expr -> string
  val pp_z3_bool_expr : Z3.z3_bool_expr -> string
  val lin_ze :
    Arith.nat ->
      Z3.z3_expr -> Arith.nat * (Z3.z3_expr * (Z3.z3_expr * Z3.z3_expr) list)
  val lin_ze_pair :
    Arith.nat ->
      Z3.z3_expr ->
        Z3.z3_expr ->
          (Z3.z3_expr -> Z3.z3_expr -> Z3.z3_expr) ->
            Arith.nat * (Z3.z3_expr * (Z3.z3_expr * Z3.z3_expr) list)
  val lin_zb :
    Arith.nat ->
      Z3.z3_bool_expr ->
        Arith.nat * (Z3.z3_bool_expr * (Z3.z3_expr * Z3.z3_expr) list)
  val rewrite_passes :
    'a -> 'b -> Z3.z3_decl list ->
                  Z3.z3_bool_expr -> Z3.z3_decl list * Z3.z3_bool_expr
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
  val z3_vector_lookup : string
  val convert_bitvec : SyntaxVCT.lit list -> string
  val pp_bitvec : SyntaxVCT.lit -> string list
  val pp_bv_consts :
    ('a, unit) Contexts.gamma_ext ->
      (SyntaxVCT.xp * Contexts.g_entry) list -> SyntaxVCT.cp -> string list
  val pp_z3_vector_funs : string
  val pp_z3_exp_pred : Arith.nat -> string
  val pp_z3_type : Z3.z3_type -> string
  val pp_z3_type_var : Z3.z3_type_var -> string
  val pp_z3_fields : (string * Z3.z3_type_var) list -> string
  val pp_z3_ty_constr : Z3.z3_constr -> string
  val pp_z3_decl : Z3.z3_decl -> string
  val z3_declare_tuple : Arith.int -> Z3.z3_decl
  val pp_tuples : Arith.int -> string list
  val pp_builtins : Arith.int -> string list
  val freshen_type : Z3.z3_type -> Z3.z3_type
  val freshen_type_var : Z3.z3_type_var -> Z3.z3_type_var
  val freshen_constr : Z3.z3_constr -> Z3.z3_constr
  val freshen_decl : Z3.z3_decl -> Z3.z3_decl
  val convert_t :
    unit ContextsPiDelta.theta_ext ->
      SyntaxVCT.vp -> SyntaxVCT.tau -> Z3.z3_type * Z3.z3_bool_expr
  val convert_typedef :
    unit ContextsPiDelta.theta_ext ->
      SyntaxVCT.xp * SyntaxVCT.tau -> Z3.z3_decl option
  val pp_typedef :
    unit ContextsPiDelta.theta_ext -> SyntaxVCT.xp * SyntaxVCT.tau -> string
  val max_tuples : Arith.int
  val convert_smt_problem_final :
    unit ContextsPiDelta.theta_ext ->
      ('a, unit) Contexts.gamma_ext ->
        (SyntaxVCT.xp * Contexts.g_entry) list ->
          SyntaxVCT.cp ->
            (SyntaxVCT.xp * Contexts.g_entry) list ->
              Z3.z3_decl list -> 'b list -> Z3.z3_bool_expr -> string list
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

let rec upto
  i = (if Arith.equal_nat i Arith.zero_nat then [Arith.zero_nat]
        else Arith.suc (Arith.minus_nat i Arith.one_nat) ::
               upto (Arith.minus_nat i Arith.one_nat));;

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
    | Z3.Z3E_exp v, e2 -> Z3.Z3BE_eq (Z3.Z3E_exp v, e2)
    | Z3.Z3E_abs v, e2 -> Z3.Z3BE_eq (Z3.Z3E_abs v, e2)
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
    | e1, Z3.Z3E_exp v -> Z3.Z3BE_eq (e1, Z3.Z3E_exp v)
    | e1, Z3.Z3E_abs v -> Z3.Z3BE_eq (e1, Z3.Z3E_abs v)
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
    | SyntaxVCT.L_bitvec va ->
        Z3.Z3E_bitvec
          (Stringa.implode
            (Lista.maps
              (fun b ->
                (if SyntaxVCT.equal_lita b SyntaxVCT.L_zero
                  then [Stringa.Chara
                          (false, false, false, false, true, true, false,
                            false)]
                  else [Stringa.Chara
                          (true, false, false, false, true, true, false,
                            false)]))
              va))
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
    | SyntaxVCT.CE_uop (SyntaxVCT.Nott, e) -> Z3.Z3E_not (convert_ce e)
    | SyntaxVCT.CE_uop (SyntaxVCT.Abs, e) -> Z3.Z3E_abs (convert_ce e)
    | SyntaxVCT.CE_many_plus v -> failwith "undefined"
    | SyntaxVCT.CE_uop (SyntaxVCT.Exp, va) -> Z3.Z3E_exp (convert_ce va)
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
    | SyntaxVCT.B_vec (v, va), SyntaxVCT.B_reg vb -> []
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
    | SyntaxVCT.B_tuple v, SyntaxVCT.B_reg va -> []
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
    | SyntaxVCT.B_union (v, va), SyntaxVCT.B_reg vb -> []
    | SyntaxVCT.B_union (v, va), SyntaxVCT.B_string -> []
    | SyntaxVCT.B_union (v, va), SyntaxVCT.B_exception -> []
    | SyntaxVCT.B_union (v, va), SyntaxVCT.B_finite_set vb -> []
    | SyntaxVCT.B_record v, uz -> []
    | SyntaxVCT.B_undef, uz -> []
    | SyntaxVCT.B_reg v, uz -> []
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
  pi (SyntaxVCT.B_union (s, cs)) =
    (match
      Contexts.lookup SyntaxVCT.equal_xp (ContextsPiDelta.theta_T pi)
        (SyntaxVCT.VNamed s)
      with None -> []
      | Some tdef ->
        type_app (Contexts.b_of tdef) (SyntaxVCT.B_union (s, cs)));;

let rec convert_b
  uu uv x2 = match uu, uv, x2 with
    uu, uv, SyntaxVCT.B_int -> (Z3.Z3T_int, Z3.Z3BE_true)
    | uw, ux, SyntaxVCT.B_bool -> (Z3.Z3T_bool, Z3.Z3BE_true)
    | p, v, SyntaxVCT.B_tuple blist ->
        (let (blist2, clist) = convert_blist p v blist in
          (Z3.Z3T_dt
             ("Tuple" ^ Utils.string_lit_of_nat (Lista.size_list blist),
               blist2),
            z3and clist))
    | p, uy, SyntaxVCT.B_record ((fid, uz) :: xs) ->
        (match ContextsPiDelta.lookup_record_name p fid
          with None -> (Z3.Z3T_dt ("unknownrecord", []), Z3.Z3BE_true)
          | Some s -> (Z3.Z3T_dt (s, []), Z3.Z3BE_true))
    | p, va, SyntaxVCT.B_record [] ->
        (Z3.Z3T_dt ("unknownrecord", []), Z3.Z3BE_true)
    | vb, vc, SyntaxVCT.B_bit -> (Z3.Z3T_bool, Z3.Z3BE_true)
    | p, v, SyntaxVCT.B_vec (vd, b) ->
        (let (t, _) = convert_b p v b in
          (Z3.Z3T_array (Z3.Z3T_int, t), Z3.Z3BE_true))
    | p, ve, SyntaxVCT.B_string -> (Z3.Z3T_string, Z3.Z3BE_true)
    | p, vf, SyntaxVCT.B_unit -> (Z3.Z3T_dt ("Unit", []), Z3.Z3BE_true)
    | p, v, SyntaxVCT.B_union (s, cs) ->
        (Z3.Z3T_dt
           (s, Lista.map (fun b -> Product_Type.fst (convert_b p v b))
                 (Lista.map Product_Type.snd
                   (type_app_t p (SyntaxVCT.B_union (s, cs))))),
          Z3.Z3BE_true)
    | vg, vh, SyntaxVCT.B_reg vi -> (Z3.Z3T_dt ("reg", []), Z3.Z3BE_true)
    | vj, vk, SyntaxVCT.B_var v -> (Z3.Z3T_sort v, Z3.Z3BE_true)
    | vl, vm, SyntaxVCT.B_tid v -> (Z3.Z3T_dt (v, []), Z3.Z3BE_true)
    | p, v, SyntaxVCT.B_list b ->
        (Z3.Z3T_dt ("List", [Product_Type.fst (convert_b p v b)]), Z3.Z3BE_true)
    | vn, b, SyntaxVCT.B_real -> (Z3.Z3T_string, Z3.Z3BE_true)
and convert_blist p v blist = Contexts.unzip (Lista.map (convert_b p v) blist);;

let rec convert_xbc
  p x b c =
    (let (t1, c1) = convert_b p (SyntaxVCT.V_var x) b in
      ([Z3.Z3D_decl_const (convert_x x, t1)], z3and [c1; convert_c c]));;

let rec subst_c_z
  x c = SyntaxPED.subst_cp (SyntaxVCT.V_var x) SyntaxVCT.VIndex c;;

let rec convert_g_aux
  p x1 = match p, x1 with p, [] -> ([], [])
    | p, (x, Contexts.GEPair (b, c)) :: gamma ->
        (let (ds, es) = convert_g_aux p gamma in
         let (d, e) = convert_xbc p x b c in
          (d @ ds, e :: es))
    | p, (x, Contexts.GETyp t) :: gamma ->
        (let (ds, es) = convert_g_aux p gamma in
         let (d, e) =
           convert_xbc p x (Contexts.b_of t) (subst_c_z x (Contexts.c_of t)) in
          (d @ ds, e :: es));;

let rec convert_smt_problem_valid
  p g ev c =
    (let ga = Contexts.gamma_x g @ Contexts.gamma_u g in
     let (d1, e1) = convert_g_aux p ga in
     let (d2, e2) = convert_g_aux p ev in
     let ca = convert_c c in
      (ga, (d1, (d2, z3and (e1 @ [Z3.Z3BE_not (z3and (ca :: e2))])))));;

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
    | Z3.Z3E_exp e -> ("(^ 2 " ^ pp_z3_expr e) ^ " )"
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
        ((("( => " ^ pp_z3_bool_expr c1) ^ " ") ^ pp_z3_bool_expr c2) ^ ")"
    | Z3.Z3BE_pred (s, elist) ->
        ((("( " ^ s) ^ " ") ^
          Lista.foldr (fun t -> (fun a -> (pp_z3_expr t ^ " ") ^ a)) elist
            " ") ^
          ")";;

let rec lin_ze
  i x1 = match i, x1 with
    i, Z3.Z3E_exp e ->
      (let new_var = "exp_" ^ Stringa.implode (Utils.string_of_nat i) in
        (Arith.plus_nat i Arith.one_nat,
          (Z3.Z3E_var new_var, [(Z3.Z3E_var new_var, e)])))
    | i, Z3.Z3E_var s -> (i, (Z3.Z3E_var s, []))
    | i, Z3.Z3E_len e ->
        (let (ia, (ea, b)) = lin_ze i e in (ia, (Z3.Z3E_len ea, b)))
    | i, Z3.Z3E_num n -> (i, (Z3.Z3E_num n, []))
    | i, Z3.Z3E_true -> (i, (Z3.Z3E_true, []))
    | i, Z3.Z3E_false -> (i, (Z3.Z3E_false, []))
    | i, Z3.Z3E_bitone -> (i, (Z3.Z3E_bitone, []))
    | i, Z3.Z3E_bitzero -> (i, (Z3.Z3E_bitzero, []))
    | i, Z3.Z3E_unit -> (i, (Z3.Z3E_unit, []))
    | i, Z3.Z3E_plus (e1, e2) ->
        lin_ze_pair i e1 e2 (fun a b -> Z3.Z3E_plus (a, b))
    | i, Z3.Z3E_leq (e1, e2) ->
        lin_ze_pair i e1 e2 (fun a b -> Z3.Z3E_leq (a, b))
    | i, Z3.Z3E_geq (e1, e2) ->
        lin_ze_pair i e1 e2 (fun a b -> Z3.Z3E_geq (a, b))
    | i, Z3.Z3E_times (e1, e2) ->
        lin_ze_pair i e1 e2 (fun a b -> Z3.Z3E_times (a, b))
    | i, Z3.Z3E_div (e1, e2) ->
        lin_ze_pair i e1 e2 (fun a b -> Z3.Z3E_div (a, b))
    | i, Z3.Z3E_mod (e1, e2) ->
        lin_ze_pair i e1 e2 (fun a b -> Z3.Z3E_mod (a, b))
    | i, Z3.Z3E_minus (e1, e2) ->
        lin_ze_pair i e1 e2 (fun a b -> Z3.Z3E_minus (a, b))
    | i, Z3.Z3E_eq (e1, e2) -> lin_ze_pair i e1 e2 (fun a b -> Z3.Z3E_eq (a, b))
    | i, Z3.Z3E_bitvec s -> (i, (Z3.Z3E_bitvec s, []))
    | i, Z3.Z3E_proj (s, e) ->
        (let (ia, (ea, b)) = lin_ze i e in (ia, (Z3.Z3E_proj (s, ea), b)))
    | i, Z3.Z3E_not e ->
        (let (ia, (ea, b)) = lin_ze i e in (ia, (Z3.Z3E_not ea, b)))
    | i, Z3.Z3E_and (e1, e2) ->
        lin_ze_pair i e1 e2 (fun a b -> Z3.Z3E_and (a, b))
    | i, Z3.Z3E_or (e1, e2) -> lin_ze_pair i e1 e2 (fun a b -> Z3.Z3E_or (a, b))
    | i, Z3.Z3E_constr (s, elist) ->
        (let (ia, (elista, bs)) =
           Lista.foldr
             (fun sa (ia, (es, bs)) ->
               (let (ib, (e, b)) = lin_ze ia sa in (ib, (e :: es, b @ bs))))
             elist (i, ([], []))
           in
          (ia, (Z3.Z3E_constr (s, elista), bs)))
    | i, Z3.Z3E_neq (e1, e2) ->
        lin_ze_pair i e1 e2 (fun a b -> Z3.Z3E_neq (a, b))
    | i, Z3.Z3E_abs e ->
        (let (ia, (ea, b)) = lin_ze i e in (ia, (Z3.Z3E_abs ea, b)))
    | i, Z3.Z3E_concat elist ->
        (let (ia, (elista, bs)) =
           Lista.foldr
             (fun s (ia, (es, bs)) ->
               (let (ib, (e, b)) = lin_ze ia s in (ib, (e :: es, b @ bs))))
             elist (i, ([], []))
           in
          (ia, (Z3.Z3E_concat elista, bs)))
    | i, Z3.Z3E_string v -> (i, (Z3.Z3E_string v, []))
and lin_ze_pair
  i e1 e2 ctor =
    (let (i1, (e1a, bs1)) = lin_ze i e1 in
     let (i2, (e2a, bs2)) = lin_ze i1 e2 in
      (i2, (ctor e1a e2a, bs1 @ bs2)));;

let rec lin_zb
  i x1 = match i, x1 with
    i, Z3.Z3BE_eq (e1, e2) ->
      (let (i1, (e1a, bs1)) = lin_ze i e1 in
       let (i2, (e2a, bs2)) = lin_ze i1 e2 in
        (i2, (Z3.Z3BE_eq (e1a, e2a), bs1 @ bs2)))
    | i, Z3.Z3BE_leq (e1, e2) ->
        (let (i1, (e1a, bs1)) = lin_ze i e1 in
         let (i2, (e2a, bs2)) = lin_ze i1 e2 in
          (i2, (Z3.Z3BE_leq (e1a, e2a), bs1 @ bs2)))
    | i, Z3.Z3BE_true -> (i, (Z3.Z3BE_true, []))
    | i, Z3.Z3BE_false -> (i, (Z3.Z3BE_false, []))
    | i, Z3.Z3BE_and elist ->
        (let (ia, (elista, bs)) =
           Lista.foldr
             (fun s (ia, (es, bs)) ->
               (let (ib, (e, b)) = lin_zb ia s in (ib, (e :: es, b @ bs))))
             elist (i, ([], []))
           in
          (ia, (Z3.Z3BE_and elista, bs)))
    | i, Z3.Z3BE_or elist ->
        (let (ia, (elista, bs)) =
           Lista.foldr
             (fun s (ia, (es, bs)) ->
               (let (ib, (e, b)) = lin_zb ia s in (ib, (e :: es, b @ bs))))
             elist (i, ([], []))
           in
          (ia, (Z3.Z3BE_or elista, bs)))
    | i, Z3.Z3BE_implies (e1, e2) ->
        (let (i1, (e1a, bs1)) = lin_zb i e1 in
         let (i2, (e2a, bs2)) = lin_zb i1 e2 in
          (i2, (Z3.Z3BE_implies (e1a, e2a), bs1 @ bs2)))
    | i, Z3.Z3BE_not e1 ->
        (let (i1, (e1a, bs1)) = lin_zb i e1 in (i1, (Z3.Z3BE_not e1a, bs1)))
    | i, Z3.Z3BE_pred (s, elist) ->
        (let (ia, (elista, bs)) =
           Lista.foldr
             (fun sa (ia, (es, bs)) ->
               (let (ib, (e, b)) = lin_ze ia sa in (ib, (e :: es, b @ bs))))
             elist (i, ([], []))
           in
          (ia, (Z3.Z3BE_pred (s, elista), bs)));;

let rec rewrite_passes
  p g d1 e1 =
    (let x = lin_zb Arith.zero_nat e1 in
     let (i, (e1a, bs)) = (let (xa, a) = x in (Arith.int_of_nat xa, a)) in
     let var_decls =
       Lista.map
         (fun ia ->
           Z3.Z3D_decl_const
             ("exp_" ^ Stringa.implode (Utils.string_of_int ia), Z3.Z3T_int))
         (Lista.upto Arith.zero_int i)
       in
     let exp_eqs =
       Lista.map (fun (e1b, e2) -> Z3.Z3BE_pred ("exp_constraint", [e1b; e2]))
         bs
       in
      (d1 @ var_decls, Z3.Z3BE_and (e1a :: exp_eqs)));;

let z3_vector_sort : string = "(Array Int Bool)";;

let rec pp_bv_concats
  n = Lista.maps
        (fun i ->
          [((((("(declare-fun concat" ^ Utils.string_lit_of_int i) ^ " (") ^
               Utils.string_lit_map " " (fun _ -> z3_vector_sort)
                 (Lista.upto Arith.one_inta i)) ^
              ") ") ^
             z3_vector_sort) ^
             ")"])
        (Lista.upto Arith.one_inta n);;

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
    | SyntaxVCT.B_reg v -> []
    | SyntaxVCT.B_string -> []
    | SyntaxVCT.B_exception -> []
    | SyntaxVCT.B_finite_set v -> [];;

let rec pp_sort_decl
  p g = Lista.remdups Stringa.equal_literal
          (Lista.maps
            (fun (_, t) ->
              Lista.map
                (fun s -> ("(declare-sort " ^ Contexts.remove_tick s) ^ ")")
                (Lista.remdups Stringa.equal_literal (t_t_vars t)))
            (ContextsPiDelta.theta_T p));;

let rec bv_consts_v
  = function SyntaxVCT.V_lit (SyntaxVCT.L_bitvec l) -> [SyntaxVCT.L_bitvec l]
    | SyntaxVCT.V_tuple vs -> Lista.maps bv_consts_v vs
    | SyntaxVCT.V_lit SyntaxVCT.L_unit -> []
    | SyntaxVCT.V_lit SyntaxVCT.L_zero -> []
    | SyntaxVCT.V_lit SyntaxVCT.L_one -> []
    | SyntaxVCT.V_lit SyntaxVCT.L_true -> []
    | SyntaxVCT.V_lit SyntaxVCT.L_false -> []
    | SyntaxVCT.V_lit (SyntaxVCT.L_num va) -> []
    | SyntaxVCT.V_lit (SyntaxVCT.L_string va) -> []
    | SyntaxVCT.V_lit SyntaxVCT.L_undef -> []
    | SyntaxVCT.V_lit (SyntaxVCT.L_real va) -> []
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

let z3_vector_lookup : string = " select ";;

let rec convert_bitvec = function [] -> ""
                         | SyntaxVCT.L_one :: bv -> "1" ^ convert_bitvec bv
                         | SyntaxVCT.L_zero :: bv -> "0" ^ convert_bitvec bv;;

let rec pp_bitvec
  = function
    SyntaxVCT.L_bitvec s ->
      [((("(declare-const bitvec" ^ convert_bitvec s) ^ " ") ^ z3_vector_sort) ^
         " )";
        (((((("(assert (and " ^ "( = (llen bitvec") ^ convert_bitvec s) ^
             ") ") ^
            Utils.string_lit_of_nat (Lista.size_list s)) ^
           " ) ") ^
          Utils.string_lit_concat
            (Lista.map
              (fun (i, x) ->
                ((((((("( = ( " ^ z3_vector_lookup) ^ "  bitvec") ^
                      convert_bitvec s) ^
                     " ") ^
                    Utils.string_lit_of_nat i) ^
                   ") ") ^
                  (match x with SyntaxVCT.L_zero -> " false "
                    | SyntaxVCT.L_one -> " true ")) ^
                  " ) ")
              (Lista.enumerate Arith.zero_nat s))) ^
          " )) "]
    | SyntaxVCT.L_unit -> []
    | SyntaxVCT.L_zero -> []
    | SyntaxVCT.L_one -> []
    | SyntaxVCT.L_true -> []
    | SyntaxVCT.L_false -> []
    | SyntaxVCT.L_num v -> []
    | SyntaxVCT.L_string v -> []
    | SyntaxVCT.L_undef -> []
    | SyntaxVCT.L_real v -> [];;

let rec pp_bv_consts
  g ev c =
    (let bvs =
       bv_consts_aux (Contexts.gamma_x g) @ bv_consts_aux ev @ bv_consts_c c in
      Lista.maps pp_bitvec (Lista.remdups SyntaxVCT.equal_lit bvs));;

let pp_z3_vector_funs : string = "";;

let rec pp_z3_exp_pred
  maxx =
    ("(define-fun exp_constraint ((x Int ) (y Int )) Bool (or " ^
      Utils.string_lit_map " "
        (fun i ->
          ((((("( and " ^ " ( = x ") ^
               Stringa.implode
                 (Utils.string_of_int
                   (Arith.power Arith.power_int
                     (Arith.Int_of_integer (Z.of_int 2)) i))) ^
              " ) ") ^
             "( = y ") ^
            Stringa.implode (Utils.string_of_int (Arith.int_of_nat i))) ^
            " ))")
        (upto maxx)) ^
      ")) ";;

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
            (Lista.upto Arith.one_inta n),
          [Z3.Z3C_ty_constr
             ("mk-tuple" ^ Utils.string_lit_of_int n,
               Lista.map
                 (fun i ->
                   ((("proj" ^ Utils.string_lit_of_int n) ^ "X") ^
                      Utils.string_lit_of_int i,
                     Z3.Z3TV_tv_var (Arith.integer_of_int i)))
                 (Lista.upto Arith.one_inta n))]);;

let rec pp_tuples
  n = Lista.map (fun i -> pp_z3_decl (z3_declare_tuple i))
        (Lista.upto Arith.one_inta n);;

let rec pp_builtins
  n = pp_z3_exp_pred (Arith.nat_of_integer (Z.of_int 16)) ::
        pp_z3_vector_funs ::
          (("(declare-fun llen (" ^ z3_vector_sort) ^ ") Int)") ::
            pp_z3_decl
              (Z3.Z3D_decl_datatype
                ("Unit", [], [Z3.Z3C_ty_constr ("unit", [])])) ::
              pp_tuples n;;

let rec freshen_type
  = function Z3.Z3T_int -> Z3.Z3T_int
    | Z3.Z3T_bool -> Z3.Z3T_bool
    | Z3.Z3T_unit -> Z3.Z3T_unit
    | Z3.Z3T_array (t1, t2) -> Z3.Z3T_array (freshen_type t1, freshen_type t2)
    | Z3.Z3T_dt (s, zts) -> Z3.Z3T_dt (s, Lista.map freshen_type zts)
    | Z3.Z3T_sort s -> Z3.Z3T_sort (s ^ "T")
    | Z3.Z3T_string -> Z3.Z3T_string;;

let rec freshen_type_var
  = function Z3.Z3TV_tv_type t -> Z3.Z3TV_tv_type (freshen_type t)
    | Z3.Z3TV_tv_var i -> Z3.Z3TV_tv_var i;;

let rec freshen_constr
  (Z3.Z3C_ty_constr (s, stvs)) =
    Z3.Z3C_ty_constr
      (s, Lista.map (fun (sa, t) -> (sa, freshen_type_var t)) stvs);;

let rec freshen_decl
  = function Z3.Z3D_decl_fun -> Z3.Z3D_decl_fun
    | Z3.Z3D_decl_const (s, t) -> Z3.Z3D_decl_const (s, freshen_type t)
    | Z3.Z3D_decl_datatype (s, vs, cs) ->
        Z3.Z3D_decl_datatype
          (s, Lista.map freshen_type_var vs, Lista.map freshen_constr cs);;

let rec convert_t
  p v (SyntaxVCT.T_refined_type (vIndex0, b, c)) =
    (let (t, e) = convert_b p v b in
      (t, z3and [e; convert_c (SyntaxPED.subst_cp v SyntaxVCT.VIndex c)]));;

let rec convert_typedef
  p x1 = match p, x1 with
    p, (SyntaxVCT.VNamed x,
         SyntaxVCT.T_refined_type (uu, SyntaxVCT.B_union (s, clist), uv))
      -> (let decl =
            Z3.Z3D_decl_datatype
              (x, Lista.map (fun v -> Z3.Z3TV_tv_type (Z3.Z3T_sort v))
                    (Lista.maps (fun (_, a) -> t_t_vars a) clist),
                Lista.map
                  (fun (sa, t) ->
                    (let (zt, _) =
                       convert_t p (SyntaxVCT.V_var SyntaxVCT.VIndex) t in
                      Z3.Z3C_ty_constr
                        (sa, [((("proj" ^ x) ^ "x") ^ sa,
                                Z3.Z3TV_tv_type zt)])))
                  clist)
            in
           Some (freshen_decl decl))
    | p, (SyntaxVCT.VNamed x,
           SyntaxVCT.T_refined_type (uw, SyntaxVCT.B_record clist, ux))
        -> (let decl =
              Z3.Z3D_decl_datatype
                (x, Lista.map (fun v -> Z3.Z3TV_tv_type (Z3.Z3T_sort v))
                      (Lista.maps (fun (_, a) -> b_t_vars a) clist),
                  [Z3.Z3C_ty_constr
                     ("mk-" ^ x,
                       Lista.map
                         (fun (s, t) ->
                           (let (zt, _) =
                              convert_b p (SyntaxVCT.V_var SyntaxVCT.VIndex) t
                              in
                             ("proj" ^ s, Z3.Z3TV_tv_type zt)))
                         clist)])
              in
             Some (freshen_decl decl))
    | uy, (SyntaxVCT.VIndex, va) -> None
    | uy, (v, SyntaxVCT.T_refined_type (vb, SyntaxVCT.B_var ve, vd)) -> None
    | uy, (v, SyntaxVCT.T_refined_type (vb, SyntaxVCT.B_tid ve, vd)) -> None
    | uy, (v, SyntaxVCT.T_refined_type (vb, SyntaxVCT.B_int, vd)) -> None
    | uy, (v, SyntaxVCT.T_refined_type (vb, SyntaxVCT.B_bool, vd)) -> None
    | uy, (v, SyntaxVCT.T_refined_type (vb, SyntaxVCT.B_bit, vd)) -> None
    | uy, (v, SyntaxVCT.T_refined_type (vb, SyntaxVCT.B_unit, vd)) -> None
    | uy, (v, SyntaxVCT.T_refined_type (vb, SyntaxVCT.B_real, vd)) -> None
    | uy, (v, SyntaxVCT.T_refined_type (vb, SyntaxVCT.B_vec (ve, vf), vd)) ->
        None
    | uy, (v, SyntaxVCT.T_refined_type (vb, SyntaxVCT.B_list ve, vd)) -> None
    | uy, (v, SyntaxVCT.T_refined_type (vb, SyntaxVCT.B_tuple ve, vd)) -> None
    | uy, (v, SyntaxVCT.T_refined_type (vb, SyntaxVCT.B_undef, vd)) -> None
    | uy, (v, SyntaxVCT.T_refined_type (vb, SyntaxVCT.B_reg ve, vd)) -> None
    | uy, (v, SyntaxVCT.T_refined_type (vb, SyntaxVCT.B_string, vd)) -> None
    | uy, (v, SyntaxVCT.T_refined_type (vb, SyntaxVCT.B_exception, vd)) -> None
    | uy, (v, SyntaxVCT.T_refined_type (vb, SyntaxVCT.B_finite_set ve, vd)) ->
        None;;

let rec pp_typedef
  p td = (match convert_typedef p td with None -> "" | Some a -> pp_z3_decl a);;

let max_tuples : Arith.int = Arith.Int_of_integer (Z.of_int 10);;

let rec convert_smt_problem_final
  p ga ev c g d1 d2 e1 =
    (let (d1a, e1a) = rewrite_passes p ga d1 e1 in
      pp_bv_concats (Arith.Int_of_integer (Z.of_int 3)) @
        pp_builtins max_tuples @
          pp_bv_consts ga ev c @
            pp_sort_decl p ga @
              Lista.map (pp_typedef p) (ContextsPiDelta.minimise_td p g) @
                Lista.map pp_z3_decl d1a @
                  [("(define-fun constraint () Bool " ^ pp_z3_bool_expr e1a) ^
                     (if Arith.equal_nat (Lista.size_list d2) Arith.zero_nat
                       then ")" else "))")] @
                    ["(assert constraint)"; "(check-sat)"]);;

let rec pp_smt_problem_valid
  p g ev c =
    (let a = convert_smt_problem_valid p g ev c in
     let (ga, aa) = a in
     let (d1, ab) = aa in
     let (ac, b) = ab in
      convert_smt_problem_final p g ev c ga d1 ac b);;

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
    | SyntaxVCT.B_reg v -> true
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
  val tsubst_t_many :
    SyntaxVCT.tau -> (string * SyntaxVCT.bp) list -> SyntaxVCT.tau
  val kvars_of :
    SyntaxVCT.tau -> (SyntaxVCT.xp * (SyntaxVCT.bp * SyntaxVCT.cp)) list
  val tsubst_bp_many :
    SyntaxVCT.bp -> (string * SyntaxVCT.bp) list -> SyntaxVCT.bp
  val subtype :
    Location.loc ->
      unit ContextsPiDelta.theta_ext ->
        (SyntaxPED.pexpp, unit) Contexts.gamma_ext ->
          SyntaxVCT.tau -> SyntaxVCT.tau -> bool Monad.checkM
  val infer_l :
    unit ContextsPiDelta.theta_ext ->
      SyntaxVCT.lit ->
        (SyntaxVCT.xp *
          ((SyntaxVCT.xp * (SyntaxVCT.bp * SyntaxVCT.cp)) list * SyntaxVCT.tau))
          Monad.checkM
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
  val single_base : SyntaxVCT.tau list -> SyntaxVCT.bp option
  val check_varM :
    (SyntaxPED.pexpp, unit) Contexts.gamma_ext ->
      Location.loc -> SyntaxVCT.xp -> bool Monad.checkM
  val check_varsM :
    (SyntaxPED.pexpp, unit) Contexts.gamma_ext ->
      Location.loc -> SyntaxVCT.xp list -> bool Monad.checkM
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
  val check_pexp :
    unit ContextsPiDelta.theta_ext ->
      (SyntaxPED.pexpp, unit) ContextsPiDelta.phi_ext ->
        (SyntaxPED.pexpp, unit) Contexts.gamma_ext ->
          unit ContextsPiDelta.delta_ext ->
            SyntaxPED.pexpp ->
              SyntaxVCT.tau ->
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
               | SyntaxVCT.B_reg v -> "(unknown)"
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
    | g, loc, SyntaxPED.Pp_lit (v, va) ->
        Monad.return (SyntaxVCT.VNamed "_", ([], (None, [])))
    | g, loc, SyntaxPED.Pp_wild v ->
        Monad.return (SyntaxVCT.VNamed "_", ([], (None, [])))
    | g, loc, SyntaxPED.Pp_as_var (v, va, vb) ->
        Monad.return (SyntaxVCT.VNamed "_", ([], (None, [])))
    | g, loc, SyntaxPED.Pp_typ (v, va, SyntaxPED.Pp_lit (vc, vd)) ->
        Monad.return (SyntaxVCT.VNamed "_", ([], (None, [])))
    | g, loc, SyntaxPED.Pp_typ (v, va, SyntaxPED.Pp_as_var (vc, vd, ve)) ->
        Monad.return (SyntaxVCT.VNamed "_", ([], (None, [])))
    | g, loc, SyntaxPED.Pp_typ (v, va, SyntaxPED.Pp_typ (vc, vd, ve)) ->
        Monad.return (SyntaxVCT.VNamed "_", ([], (None, [])))
    | g, loc, SyntaxPED.Pp_typ (v, va, SyntaxPED.Pp_as_typ (vc, vd, ve)) ->
        Monad.return (SyntaxVCT.VNamed "_", ([], (None, [])))
    | g, loc, SyntaxPED.Pp_typ (v, va, SyntaxPED.Pp_app (vc, vd, ve)) ->
        Monad.return (SyntaxVCT.VNamed "_", ([], (None, [])))
    | g, loc, SyntaxPED.Pp_typ (v, va, SyntaxPED.Pp_vector (vc, vd)) ->
        Monad.return (SyntaxVCT.VNamed "_", ([], (None, [])))
    | g, loc, SyntaxPED.Pp_typ (v, va, SyntaxPED.Pp_vector_concat (vc, vd)) ->
        Monad.return (SyntaxVCT.VNamed "_", ([], (None, [])))
    | g, loc, SyntaxPED.Pp_typ (v, va, SyntaxPED.Pp_tup (vc, vd)) ->
        Monad.return (SyntaxVCT.VNamed "_", ([], (None, [])))
    | g, loc, SyntaxPED.Pp_typ (v, va, SyntaxPED.Pp_list (vc, vd)) ->
        Monad.return (SyntaxVCT.VNamed "_", ([], (None, [])))
    | g, loc, SyntaxPED.Pp_typ (v, va, SyntaxPED.Pp_cons (vc, vd, ve)) ->
        Monad.return (SyntaxVCT.VNamed "_", ([], (None, [])))
    | g, loc, SyntaxPED.Pp_typ (v, va, SyntaxPED.Pp_string_append (vc, vd)) ->
        Monad.return (SyntaxVCT.VNamed "_", ([], (None, [])))
    | g, loc, SyntaxPED.Pp_id (v, va) ->
        Monad.return (SyntaxVCT.VNamed "_", ([], (None, [])))
    | g, loc, SyntaxPED.Pp_as_typ (v, va, vb) ->
        Monad.return (SyntaxVCT.VNamed "_", ([], (None, [])))
    | g, loc, SyntaxPED.Pp_app (v, va, vb) ->
        Monad.return (SyntaxVCT.VNamed "_", ([], (None, [])))
    | g, loc, SyntaxPED.Pp_vector (v, va) ->
        Monad.return (SyntaxVCT.VNamed "_", ([], (None, [])))
    | g, loc, SyntaxPED.Pp_vector_concat (v, va) ->
        Monad.return (SyntaxVCT.VNamed "_", ([], (None, [])))
    | g, loc, SyntaxPED.Pp_tup (v, va) ->
        Monad.return (SyntaxVCT.VNamed "_", ([], (None, [])))
    | g, loc, SyntaxPED.Pp_list (v, va) ->
        Monad.return (SyntaxVCT.VNamed "_", ([], (None, [])))
    | g, loc, SyntaxPED.Pp_cons (v, va, vb) ->
        Monad.return (SyntaxVCT.VNamed "_", ([], (None, [])))
    | g, loc, SyntaxPED.Pp_string_append (v, va) ->
        Monad.return (SyntaxVCT.VNamed "_", ([], (None, [])));;

let rec tsubst_t_many
  b x1 = match b, x1 with b, [] -> b
    | ba, (bv, b) :: bsub -> SyntaxPED.tsubst_tp b bv (tsubst_t_many ba bsub);;

let rec kvars_of uu = [];;

let rec tsubst_bp_many
  b x1 = match b, x1 with b, [] -> b
    | ba, (bv, b) :: bsub -> SyntaxPED.tsubst_bp b bv (tsubst_bp_many ba bsub);;

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
                              [(z, (tsubst_bp_many (Contexts.b_of t1) bp,
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
                              [(z, (tsubst_bp_many (Contexts.b_of t1) bp,
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
                              [(z, (tsubst_bp_many (Contexts.b_of t1) bp,
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
                              [(z, (tsubst_bp_many (Contexts.b_of t1) bp,
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
                              [(z, (tsubst_bp_many (Contexts.b_of t1) bp,
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
                              [(z, (tsubst_bp_many (Contexts.b_of t1) bp,
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
                              [(z, (tsubst_bp_many (Contexts.b_of t1) bp,
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
                                 [(z, (tsubst_bp_many (Contexts.b_of t1) bp,
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
                              [(z, (tsubst_bp_many (Contexts.b_of t1) bp,
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
                              [(z, (tsubst_bp_many (Contexts.b_of t1) bp,
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
                                 [(z, (tsubst_bp_many (Contexts.b_of t1) bp,
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
                              [(z, (tsubst_bp_many (Contexts.b_of t1) bp,
                                     Contexts.subst_c_v0 (Contexts.c_of t1)
                                       (Monad.mk_var z)))])
                            (Contexts.convert_ge [])
                            (Contexts.subst_c_v0 (Contexts.c_of t2a)
                              (Monad.mk_var z)))))))
    | loc, p, g, SyntaxVCT.T_refined_type (v, SyntaxVCT.B_reg vc, vb), t2 ->
        Monad.check_bind
          (Monad.freshen_t
            (SyntaxVCT.T_refined_type (v, SyntaxVCT.B_reg vc, vb)))
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
                              [(z, (tsubst_bp_many (Contexts.b_of t1) bp,
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
                              [(z, (tsubst_bp_many (Contexts.b_of t1) bp,
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
                              [(z, (tsubst_bp_many (Contexts.b_of t1) bp,
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
                                 [(z, (tsubst_bp_many (Contexts.b_of t1) bp,
Contexts.subst_c_v0 (Contexts.c_of t1) (Monad.mk_var z)))])
                               (Contexts.convert_ge [])
                               (Contexts.subst_c_v0 (Contexts.c_of t2a)
                                 (Monad.mk_var z)))))));;

let rec infer_l
  t x1 = match t, x1 with
    t, SyntaxVCT.L_bitvec bs ->
      (match ContextsPiDelta.theta_d t
        with None ->
          Monad.fail
            (Monad.TypeError (Location.Loc_unknown, "Default order not set"))
        | Some dord ->
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
                    (x, ([(x, (SyntaxVCT.B_vec (dord, SyntaxVCT.B_bit),
                                Contexts.mk_l_eq_c x (SyntaxVCT.L_bitvec bs)))],
                          SyntaxVCT.T_refined_type
                            (SyntaxVCT.VIndex,
                              SyntaxVCT.B_vec (dord, SyntaxVCT.B_bit),
                              Contexts.mk_l_eq_c SyntaxVCT.VIndex
                                (SyntaxVCT.L_bitvec bs)))))))
    | t, SyntaxVCT.L_undef ->
        Monad.fail
          (Monad.TypeError
            (Location.Loc_unknown, "Cannot infer type of undefined"))
    | t, SyntaxVCT.L_unit ->
        Monad.check_bind
          (Monad.mk_fresh
            [Stringa.Chara (false, false, true, true, false, true, true, false);
              Stringa.Chara
                (true, false, false, true, false, true, true, false);
              Stringa.Chara
                (false, false, true, false, true, true, true, false)])
          (fun x ->
            Monad.return
              (x, ([(x, (Contexts.b_of_lit SyntaxVCT.L_unit,
                          Contexts.mk_l_eq_c x SyntaxVCT.L_unit))],
                    Contexts.mk_l_eq_t SyntaxVCT.L_unit)))
    | t, SyntaxVCT.L_zero ->
        Monad.check_bind
          (Monad.mk_fresh
            [Stringa.Chara (false, false, true, true, false, true, true, false);
              Stringa.Chara
                (true, false, false, true, false, true, true, false);
              Stringa.Chara
                (false, false, true, false, true, true, true, false)])
          (fun x ->
            Monad.return
              (x, ([(x, (Contexts.b_of_lit SyntaxVCT.L_zero,
                          Contexts.mk_l_eq_c x SyntaxVCT.L_zero))],
                    Contexts.mk_l_eq_t SyntaxVCT.L_zero)))
    | t, SyntaxVCT.L_one ->
        Monad.check_bind
          (Monad.mk_fresh
            [Stringa.Chara (false, false, true, true, false, true, true, false);
              Stringa.Chara
                (true, false, false, true, false, true, true, false);
              Stringa.Chara
                (false, false, true, false, true, true, true, false)])
          (fun x ->
            Monad.return
              (x, ([(x, (Contexts.b_of_lit SyntaxVCT.L_one,
                          Contexts.mk_l_eq_c x SyntaxVCT.L_one))],
                    Contexts.mk_l_eq_t SyntaxVCT.L_one)))
    | t, SyntaxVCT.L_true ->
        Monad.check_bind
          (Monad.mk_fresh
            [Stringa.Chara (false, false, true, true, false, true, true, false);
              Stringa.Chara
                (true, false, false, true, false, true, true, false);
              Stringa.Chara
                (false, false, true, false, true, true, true, false)])
          (fun x ->
            Monad.return
              (x, ([(x, (Contexts.b_of_lit SyntaxVCT.L_true,
                          Contexts.mk_l_eq_c x SyntaxVCT.L_true))],
                    Contexts.mk_l_eq_t SyntaxVCT.L_true)))
    | t, SyntaxVCT.L_false ->
        Monad.check_bind
          (Monad.mk_fresh
            [Stringa.Chara (false, false, true, true, false, true, true, false);
              Stringa.Chara
                (true, false, false, true, false, true, true, false);
              Stringa.Chara
                (false, false, true, false, true, true, true, false)])
          (fun x ->
            Monad.return
              (x, ([(x, (Contexts.b_of_lit SyntaxVCT.L_false,
                          Contexts.mk_l_eq_c x SyntaxVCT.L_false))],
                    Contexts.mk_l_eq_t SyntaxVCT.L_false)))
    | t, SyntaxVCT.L_num v ->
        Monad.check_bind
          (Monad.mk_fresh
            [Stringa.Chara (false, false, true, true, false, true, true, false);
              Stringa.Chara
                (true, false, false, true, false, true, true, false);
              Stringa.Chara
                (false, false, true, false, true, true, true, false)])
          (fun x ->
            Monad.return
              (x, ([(x, (Contexts.b_of_lit (SyntaxVCT.L_num v),
                          Contexts.mk_l_eq_c x (SyntaxVCT.L_num v)))],
                    Contexts.mk_l_eq_t (SyntaxVCT.L_num v))))
    | t, SyntaxVCT.L_string v ->
        Monad.check_bind
          (Monad.mk_fresh
            [Stringa.Chara (false, false, true, true, false, true, true, false);
              Stringa.Chara
                (true, false, false, true, false, true, true, false);
              Stringa.Chara
                (false, false, true, false, true, true, true, false)])
          (fun x ->
            Monad.return
              (x, ([(x, (Contexts.b_of_lit (SyntaxVCT.L_string v),
                          Contexts.mk_l_eq_c x (SyntaxVCT.L_string v)))],
                    Contexts.mk_l_eq_t (SyntaxVCT.L_string v))))
    | t, SyntaxVCT.L_real v ->
        Monad.check_bind
          (Monad.mk_fresh
            [Stringa.Chara (false, false, true, true, false, true, true, false);
              Stringa.Chara
                (true, false, false, true, false, true, true, false);
              Stringa.Chara
                (false, false, true, false, true, true, true, false)])
          (fun x ->
            Monad.return
              (x, ([(x, (Contexts.b_of_lit (SyntaxVCT.L_real v),
                          Contexts.mk_l_eq_c x (SyntaxVCT.L_real v)))],
                    Contexts.mk_l_eq_t (SyntaxVCT.L_real v))));;

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
                                   (Contexts.add_vars_ge
                                     (Contexts.add_var gamma
                                       (z,
 Contexts.GEPair
   (SyntaxVCT.B_tuple bs, Contexts.subst_c_v0 c (SyntaxVCT.V_var z))))
                                     gs)
                                   (SyntaxVCT.T_refined_type
                                     (SyntaxVCT.VIndex, SyntaxVCT.B_tuple bs,
                                       tup_c2))
                                   (SyntaxVCT.T_refined_type
                                     (zvarin, SyntaxVCT.B_tuple bs, c)))
                                 (fun b ->
                                   (if b then Monad.return
        (z, (gs @ [(z, (SyntaxVCT.B_tuple bs, tup_c))], vars))
                                     else Monad.fail
    (Monad.CheckFail
      (loc, gamma, "check_pat Tuple",
        SyntaxVCT.T_refined_type
          (SyntaxVCT.VIndex, SyntaxVCT.B_tuple bs, tup_c2),
        SyntaxVCT.T_refined_type (zvarin, SyntaxVCT.B_tuple bs, c))))))))))
    | ux, uy, uz, gamma, SyntaxPED.Pp_tup (loc, va),
        SyntaxVCT.T_refined_type (v, SyntaxVCT.B_var vd, vc)
        -> Monad.fail
             (Monad.CheckFail
               (loc, gamma, "check_pat Pp_tup. type unexpected",
                 SyntaxVCT.T_refined_type (v, SyntaxVCT.B_var vd, vc),
                 SyntaxVCT.T_refined_type (v, SyntaxVCT.B_var vd, vc)))
    | ux, uy, uz, gamma, SyntaxPED.Pp_tup (loc, va),
        SyntaxVCT.T_refined_type (v, SyntaxVCT.B_tid vd, vc)
        -> Monad.fail
             (Monad.CheckFail
               (loc, gamma, "check_pat Pp_tup. type unexpected",
                 SyntaxVCT.T_refined_type (v, SyntaxVCT.B_tid vd, vc),
                 SyntaxVCT.T_refined_type (v, SyntaxVCT.B_tid vd, vc)))
    | ux, uy, uz, gamma, SyntaxPED.Pp_tup (loc, va),
        SyntaxVCT.T_refined_type (v, SyntaxVCT.B_int, vc)
        -> Monad.fail
             (Monad.CheckFail
               (loc, gamma, "check_pat Pp_tup. type unexpected",
                 SyntaxVCT.T_refined_type (v, SyntaxVCT.B_int, vc),
                 SyntaxVCT.T_refined_type (v, SyntaxVCT.B_int, vc)))
    | ux, uy, uz, gamma, SyntaxPED.Pp_tup (loc, va),
        SyntaxVCT.T_refined_type (v, SyntaxVCT.B_bool, vc)
        -> Monad.fail
             (Monad.CheckFail
               (loc, gamma, "check_pat Pp_tup. type unexpected",
                 SyntaxVCT.T_refined_type (v, SyntaxVCT.B_bool, vc),
                 SyntaxVCT.T_refined_type (v, SyntaxVCT.B_bool, vc)))
    | ux, uy, uz, gamma, SyntaxPED.Pp_tup (loc, va),
        SyntaxVCT.T_refined_type (v, SyntaxVCT.B_bit, vc)
        -> Monad.fail
             (Monad.CheckFail
               (loc, gamma, "check_pat Pp_tup. type unexpected",
                 SyntaxVCT.T_refined_type (v, SyntaxVCT.B_bit, vc),
                 SyntaxVCT.T_refined_type (v, SyntaxVCT.B_bit, vc)))
    | ux, uy, uz, gamma, SyntaxPED.Pp_tup (loc, va),
        SyntaxVCT.T_refined_type (v, SyntaxVCT.B_unit, vc)
        -> Monad.fail
             (Monad.CheckFail
               (loc, gamma, "check_pat Pp_tup. type unexpected",
                 SyntaxVCT.T_refined_type (v, SyntaxVCT.B_unit, vc),
                 SyntaxVCT.T_refined_type (v, SyntaxVCT.B_unit, vc)))
    | ux, uy, uz, gamma, SyntaxPED.Pp_tup (loc, va),
        SyntaxVCT.T_refined_type (v, SyntaxVCT.B_real, vc)
        -> Monad.fail
             (Monad.CheckFail
               (loc, gamma, "check_pat Pp_tup. type unexpected",
                 SyntaxVCT.T_refined_type (v, SyntaxVCT.B_real, vc),
                 SyntaxVCT.T_refined_type (v, SyntaxVCT.B_real, vc)))
    | ux, uy, uz, gamma, SyntaxPED.Pp_tup (loc, va),
        SyntaxVCT.T_refined_type (v, SyntaxVCT.B_vec (vd, ve), vc)
        -> Monad.fail
             (Monad.CheckFail
               (loc, gamma, "check_pat Pp_tup. type unexpected",
                 SyntaxVCT.T_refined_type (v, SyntaxVCT.B_vec (vd, ve), vc),
                 SyntaxVCT.T_refined_type (v, SyntaxVCT.B_vec (vd, ve), vc)))
    | ux, uy, uz, gamma, SyntaxPED.Pp_tup (loc, va),
        SyntaxVCT.T_refined_type (v, SyntaxVCT.B_list vd, vc)
        -> Monad.fail
             (Monad.CheckFail
               (loc, gamma, "check_pat Pp_tup. type unexpected",
                 SyntaxVCT.T_refined_type (v, SyntaxVCT.B_list vd, vc),
                 SyntaxVCT.T_refined_type (v, SyntaxVCT.B_list vd, vc)))
    | ux, uy, uz, gamma, SyntaxPED.Pp_tup (loc, va),
        SyntaxVCT.T_refined_type (v, SyntaxVCT.B_union (vd, ve), vc)
        -> Monad.fail
             (Monad.CheckFail
               (loc, gamma, "check_pat Pp_tup. type unexpected",
                 SyntaxVCT.T_refined_type (v, SyntaxVCT.B_union (vd, ve), vc),
                 SyntaxVCT.T_refined_type (v, SyntaxVCT.B_union (vd, ve), vc)))
    | ux, uy, uz, gamma, SyntaxPED.Pp_tup (loc, va),
        SyntaxVCT.T_refined_type (v, SyntaxVCT.B_record vd, vc)
        -> Monad.fail
             (Monad.CheckFail
               (loc, gamma, "check_pat Pp_tup. type unexpected",
                 SyntaxVCT.T_refined_type (v, SyntaxVCT.B_record vd, vc),
                 SyntaxVCT.T_refined_type (v, SyntaxVCT.B_record vd, vc)))
    | ux, uy, uz, gamma, SyntaxPED.Pp_tup (loc, va),
        SyntaxVCT.T_refined_type (v, SyntaxVCT.B_undef, vc)
        -> Monad.fail
             (Monad.CheckFail
               (loc, gamma, "check_pat Pp_tup. type unexpected",
                 SyntaxVCT.T_refined_type (v, SyntaxVCT.B_undef, vc),
                 SyntaxVCT.T_refined_type (v, SyntaxVCT.B_undef, vc)))
    | ux, uy, uz, gamma, SyntaxPED.Pp_tup (loc, va),
        SyntaxVCT.T_refined_type (v, SyntaxVCT.B_reg vd, vc)
        -> Monad.fail
             (Monad.CheckFail
               (loc, gamma, "check_pat Pp_tup. type unexpected",
                 SyntaxVCT.T_refined_type (v, SyntaxVCT.B_reg vd, vc),
                 SyntaxVCT.T_refined_type (v, SyntaxVCT.B_reg vd, vc)))
    | ux, uy, uz, gamma, SyntaxPED.Pp_tup (loc, va),
        SyntaxVCT.T_refined_type (v, SyntaxVCT.B_string, vc)
        -> Monad.fail
             (Monad.CheckFail
               (loc, gamma, "check_pat Pp_tup. type unexpected",
                 SyntaxVCT.T_refined_type (v, SyntaxVCT.B_string, vc),
                 SyntaxVCT.T_refined_type (v, SyntaxVCT.B_string, vc)))
    | ux, uy, uz, gamma, SyntaxPED.Pp_tup (loc, va),
        SyntaxVCT.T_refined_type (v, SyntaxVCT.B_exception, vc)
        -> Monad.fail
             (Monad.CheckFail
               (loc, gamma, "check_pat Pp_tup. type unexpected",
                 SyntaxVCT.T_refined_type (v, SyntaxVCT.B_exception, vc),
                 SyntaxVCT.T_refined_type (v, SyntaxVCT.B_exception, vc)))
    | ux, uy, uz, gamma, SyntaxPED.Pp_tup (loc, va),
        SyntaxVCT.T_refined_type (v, SyntaxVCT.B_finite_set vd, vc)
        -> Monad.fail
             (Monad.CheckFail
               (loc, gamma, "check_pat Pp_tup. type unexpected",
                 SyntaxVCT.T_refined_type (v, SyntaxVCT.B_finite_set vd, vc),
                 SyntaxVCT.T_refined_type (v, SyntaxVCT.B_finite_set vd, vc)))
    | litok, ta, p, gamma, SyntaxPED.Pp_lit (loc, l), t ->
        Monad.check_bind (infer_l ta l)
          (fun (_, (_, taa)) ->
            (if SyntaxVCT.equal_bpa (Contexts.b_of t) (Contexts.b_of taa)
              then Monad.check_bind
                     (Monad.mk_fresh
                       [Stringa.Chara
                          (false, false, false, false, true, true, true, false);
                         Stringa.Chara
                           (true, false, false, false, false, true, true,
                             false);
                         Stringa.Chara
                           (false, false, true, false, true, true, true, false);
                         Stringa.Chara
                           (false, false, true, true, false, true, true,
                             false)])
                     (fun z ->
                       Monad.return
                         (z, ([(z, (Contexts.b_of t,
                                     SyntaxVCT.C_conj
                                       (Contexts.subst_c_x (Contexts.c_of t) z,
 Contexts.mk_l_eq_c z l)))],
                               [])))
              else Monad.fail
                     (Monad.TypeError
                       (loc, (("Literal base type mismatched. Expected " ^
                                pp_b (Contexts.b_of t)) ^
                               " Found: ") ^
                               pp_b (Contexts.b_of_lit l)))))
    | litok, t, p, gamma, SyntaxPED.Pp_vector_concat (loc, vs),
        SyntaxVCT.T_refined_type (vb, SyntaxVCT.B_vec (odr, b), c)
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
    | vc, t, p, gamma, SyntaxPED.Pp_vector_concat (loc, vs),
        SyntaxVCT.T_refined_type (vd, SyntaxVCT.B_var v, c)
        -> Monad.fail (Monad.TypeError (loc, "Pp_vec_concat"))
    | vc, t, p, gamma, SyntaxPED.Pp_vector_concat (loc, vs),
        SyntaxVCT.T_refined_type (vd, SyntaxVCT.B_tid v, c)
        -> Monad.fail (Monad.TypeError (loc, "Pp_vec_concat"))
    | vc, t, p, gamma, SyntaxPED.Pp_vector_concat (loc, vs),
        SyntaxVCT.T_refined_type (vd, SyntaxVCT.B_int, c)
        -> Monad.fail (Monad.TypeError (loc, "Pp_vec_concat"))
    | vc, t, p, gamma, SyntaxPED.Pp_vector_concat (loc, vs),
        SyntaxVCT.T_refined_type (vd, SyntaxVCT.B_bool, c)
        -> Monad.fail (Monad.TypeError (loc, "Pp_vec_concat"))
    | vc, t, p, gamma, SyntaxPED.Pp_vector_concat (loc, vs),
        SyntaxVCT.T_refined_type (vd, SyntaxVCT.B_bit, c)
        -> Monad.fail (Monad.TypeError (loc, "Pp_vec_concat"))
    | vc, t, p, gamma, SyntaxPED.Pp_vector_concat (loc, vs),
        SyntaxVCT.T_refined_type (vd, SyntaxVCT.B_unit, c)
        -> Monad.fail (Monad.TypeError (loc, "Pp_vec_concat"))
    | vc, t, p, gamma, SyntaxPED.Pp_vector_concat (loc, vs),
        SyntaxVCT.T_refined_type (vd, SyntaxVCT.B_real, c)
        -> Monad.fail (Monad.TypeError (loc, "Pp_vec_concat"))
    | vc, t, p, gamma, SyntaxPED.Pp_vector_concat (loc, vs),
        SyntaxVCT.T_refined_type (vd, SyntaxVCT.B_list v, c)
        -> Monad.fail (Monad.TypeError (loc, "Pp_vec_concat"))
    | vc, t, p, gamma, SyntaxPED.Pp_vector_concat (loc, vs),
        SyntaxVCT.T_refined_type (vd, SyntaxVCT.B_tuple v, c)
        -> Monad.fail (Monad.TypeError (loc, "Pp_vec_concat"))
    | vc, t, p, gamma, SyntaxPED.Pp_vector_concat (loc, vs),
        SyntaxVCT.T_refined_type (vd, SyntaxVCT.B_union (v, va), c)
        -> Monad.fail (Monad.TypeError (loc, "Pp_vec_concat"))
    | vc, t, p, gamma, SyntaxPED.Pp_vector_concat (loc, vs),
        SyntaxVCT.T_refined_type (vd, SyntaxVCT.B_record v, c)
        -> Monad.fail (Monad.TypeError (loc, "Pp_vec_concat"))
    | vc, t, p, gamma, SyntaxPED.Pp_vector_concat (loc, vs),
        SyntaxVCT.T_refined_type (vd, SyntaxVCT.B_undef, c)
        -> Monad.fail (Monad.TypeError (loc, "Pp_vec_concat"))
    | vc, t, p, gamma, SyntaxPED.Pp_vector_concat (loc, vs),
        SyntaxVCT.T_refined_type (vd, SyntaxVCT.B_reg v, c)
        -> Monad.fail (Monad.TypeError (loc, "Pp_vec_concat"))
    | vc, t, p, gamma, SyntaxPED.Pp_vector_concat (loc, vs),
        SyntaxVCT.T_refined_type (vd, SyntaxVCT.B_string, c)
        -> Monad.fail (Monad.TypeError (loc, "Pp_vec_concat"))
    | vc, t, p, gamma, SyntaxPED.Pp_vector_concat (loc, vs),
        SyntaxVCT.T_refined_type (vd, SyntaxVCT.B_exception, c)
        -> Monad.fail (Monad.TypeError (loc, "Pp_vec_concat"))
    | vc, t, p, gamma, SyntaxPED.Pp_vector_concat (loc, vs),
        SyntaxVCT.T_refined_type (vd, SyntaxVCT.B_finite_set v, c)
        -> Monad.fail (Monad.TypeError (loc, "Pp_vec_concat"))
    | litok, tb, pa, gamma, SyntaxPED.Pp_typ (loc, ta, p), t ->
        Monad.check_bind (check_pat litok tb pa gamma p ta)
          (fun (_, (_, _)) -> check_pat litok tb pa gamma p t)
    | litok, ta, pa, gamma, SyntaxPED.Pp_app (loc, ctor, [p]), t ->
        (match ContextsPiDelta.lookup_constr_union_type ta ctor
          with None -> Monad.fail (Monad.TypeError (loc, "Pp_constr"))
          | Some (t1, t2) ->
            (match Contexts.unify_b (Contexts.b_of t) (Contexts.b_of t1)
              with None ->
                Monad.fail
                  (Monad.CheckFail
                    (loc, gamma, "Pp_constr (outside types; not unifying)", t1,
                      t))
              | Some bsub ->
                Monad.check_bind
                  (check_pat litok ta pa gamma p (tsubst_t_many t2 bsub))
                  (fun (x, (g, vars)) ->
                    Monad.check_bind
                      (Monad.mk_fresh
                        [Stringa.Chara
                           (false, false, false, false, true, true, true,
                             false);
                          Stringa.Chara
                            (true, false, false, false, false, true, true,
                              false);
                          Stringa.Chara
                            (false, false, true, false, true, true, true,
                              false)])
                      (fun z ->
                        Monad.check_bind (subtype loc ta gamma t1 t)
                          (fun st ->
                            (if st
                              then Monad.return
                                     (z, ((z,
    (Contexts.b_of t,
      Contexts.mk_v_eq_c z (SyntaxVCT.V_constr (ctor, SyntaxVCT.V_var x)))) ::
    g,
   vars))
                              else Monad.fail
                                     (Monad.CheckFail
                                       (loc, gamma, "Pp_constr (outside types)",
 t1, t))))))))
    | vf, ta, p, gamma, SyntaxPED.Pp_as_var (loc, vg, vh), t ->
        Monad.fail (Monad.TypeError (loc, "Pp_as_var"))
    | vi, ta, p, gamma, SyntaxPED.Pp_as_typ (loc, vj, vk), t ->
        Monad.fail (Monad.TypeError (loc, "Pp_as_var"))
    | vl, ta, p, gamma, SyntaxPED.Pp_vector (loc, vs), t ->
        Monad.fail (Monad.TypeError (loc, "Pp_vector"))
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
          | SyntaxVCT.T_refined_type (_, SyntaxVCT.B_reg _, _) ->
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
          | SyntaxVCT.T_refined_type (_, SyntaxVCT.B_reg _, _) ->
            Monad.fail (Monad.TypeError (loc, "Pp_list"))
          | SyntaxVCT.T_refined_type (_, SyntaxVCT.B_string, _) ->
            Monad.fail (Monad.TypeError (loc, "Pp_list"))
          | SyntaxVCT.T_refined_type (_, SyntaxVCT.B_exception, _) ->
            Monad.fail (Monad.TypeError (loc, "Pp_list"))
          | SyntaxVCT.T_refined_type (_, SyntaxVCT.B_finite_set _, _) ->
            Monad.fail (Monad.TypeError (loc, "Pp_list")))
and check_pat_list
  vn t p g loc x5 x6 = match vn, t, p, g, loc, x5, x6 with
    vn, t, p, g, loc, [], [] -> Monad.return ([], ([], []))
    | litok, ta, pa, g, loc, p :: ps, t :: ts ->
        Monad.check_bind (check_pat litok ta pa g p t)
          (fun (x, (ga, vars1)) ->
            Monad.check_bind (check_pat_list litok ta pa g loc ps ts)
              (fun (xs, (gs, vars2)) ->
                Monad.return (x :: xs, (ga @ gs, vars1 @ vars2))))
    | vo, vp, vq, g, loc, v :: va, [] ->
        Monad.fail (Monad.TypeError (loc, "pat list"))
    | vo, vp, vq, g, loc, [], v :: va ->
        Monad.fail (Monad.TypeError (loc, "pat list"))
and check_pat_vec_list
  vm t p g loc x5 odr b = match vm, t, p, g, loc, x5, odr, b with
    vm, t, p, g, loc, [], odr, b -> Monad.return ([], ([], []))
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

let rec single_base
  ts = (match Lista.remdups SyntaxVCT.equal_bp (Lista.map Contexts.b_of ts)
         with [] -> None | [b] -> Some b | _ :: _ :: _ -> None);;

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
        SyntaxVCT.T_refined_type (vb, SyntaxVCT.B_reg ve, vd)
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
    t, p, g, d, SyntaxVCT.V_lit l -> infer_l t l
    | t, p, g, d, SyntaxVCT.V_var x ->
        (if Contexts.lookup_scope g x
          then (match Contexts.lookup_ivar g x
                 with None ->
                   (match ContextsPiDelta.lookup_mvar d (id_of x)
                     with None ->
                       (match ContextsPiDelta.lookup_constr_union_x t x
                         with None ->
                           (match ContextsPiDelta.lookup_register t x
                             with None ->
                               Monad.fail
                                 (Monad.VarUnknown (Location.Loc_unknown, x))
                             | Some ta -> Monad.return (x, ([], ta)))
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
    | t, p, g, d, SyntaxVCT.V_vec vs ->
        (match ContextsPiDelta.theta_d t
          with None ->
            Monad.fail
              (Monad.TypeError (Location.Loc_unknown, "Default order not set"))
          | Some dord ->
            Monad.check_bind (Monad.mapM (infer_v t p g d) vs)
              (fun xx ->
                Monad.check_bind (Monad.return (unzip3 xx))
                  (fun (_, (ga, ts)) ->
                    Monad.check_bind (Monad.return (Lista.concat ga))
                      (fun _ ->
                        Monad.check_bind
                          (Monad.mk_fresh
                            [Stringa.Chara
                               (false, true, true, false, true, true, true,
                                 false);
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
                              (if Arith.equal_nat (Lista.size_list bs)
                                    Arith.one_nat
                                then Monad.return
                                       (x,
 ([(x, (SyntaxVCT.B_vec (dord, Lista.hd bs), Contexts.mk_vec_len_eq_c x vs))],
   SyntaxVCT.T_refined_type
     (SyntaxVCT.VIndex, SyntaxVCT.B_vec (dord, Lista.hd bs),
       Contexts.mk_vec_len_eq_c SyntaxVCT.VIndex vs)))
                                else Monad.fail
                                       Monad.VectorElementsDiffType)))))))
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
                 | SyntaxVCT.T_refined_type (_, SyntaxVCT.B_reg _, _) ->
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
        Monad.check_bind (infer_e ta p g d e2)
          (fun (_, (g1, t2)) ->
            Monad.check_bind
              (check_lexp ta p (Contexts.add_vars_ge g g1) d e1 t2)
              (fun (_, (ga, _)) ->
                Monad.check_bind
                  (check_s ta p (Contexts.add_vars_ge g ga) d e3 t)
                  (fun _ -> Monad.return g)))
    | t, p, g, d, SyntaxPED.Ep_record (loc, fes), t1 ->
        Monad.check_bind
          (Monad.mapM
            (fun (f, e) ->
              (match ContextsPiDelta.lookup_field_in_type t1 f
                with None ->
                  Monad.fail (Monad.CheckFail (loc, g, "missing field", t1, t1))
                | Some b ->
                  Monad.check_bind
                    (Monad.return
                      (SyntaxVCT.T_refined_type
                        (SyntaxVCT.VIndex, b, SyntaxVCT.C_true)))
                    (check_s t p g d e)))
            fes)
          (fun _ -> Monad.return g)
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
                            | SyntaxVCT.B_reg _ ->
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
              (Monad.mapM (fun pat -> check_pexp ta p g d pat t1 t) pes)
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
                             "general check expr", t2, t1)))))
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
                             "general check expr", t2, t1)))))
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
                             "general check expr", t2, t1)))))
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
                             "general check expr", t2, t1)))))
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
                             "general check expr", t2, t1)))))
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
                             g, "general check expr", t2, t1)))))
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
                             "general check expr", t2, t1)))))
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
                             "general check expr", t2, t1)))))
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
                             g, "general check expr", t2, t1)))))
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
                             g, "general check expr", t2, t1)))))
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
                             "general check expr", t2, t1)))))
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
                             "general check expr", t2, t1)))))
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
                             g, "general check expr", t2, t1)))))
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
                             "general check expr", t2, t1)))))
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
                             "general check expr", t2, t1)))))
    | t, p, g, d, SyntaxPED.Ep_ref (v, va), t1 ->
        Monad.check_bind (infer_e t p g d (SyntaxPED.Ep_ref (v, va)))
          (fun (_, (ga, t2)) ->
            Monad.check_bind
              (subtype (SyntaxPED.loc_e (SyntaxPED.Ep_ref (v, va))) t
                (Contexts.add_vars_ge g ga) t2 t1)
              (fun st ->
                (if st then Monad.return g
                  else Monad.fail
                         (Monad.CheckFail
                           (SyntaxPED.loc_e (SyntaxPED.Ep_ref (v, va)), g,
                             "general check expr", t2, t1)))))
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
                             "general check expr", t2, t1)))))
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
                             "general check expr", t2, t1)))))
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
                             g, "general check expr", t2, t1)))))
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
                             g, "general check expr", t2, t1)))))
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
                             "general check expr", t2, t1)))))
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
                             "general check expr", t2, t1)))))
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
                             "general check expr", t2, t1)))))
and check_pexp
  ta pa g d x4 t1 t = match ta, pa, g, d, x4, t1, t with
    ta, pa, g, d, SyntaxPED.PEXPp_exp (p, s), t1, t ->
      Monad.check_bind (check_pat true ta pa g p t1)
        (fun (z, (bs, vars)) ->
          Monad.check_bind (check_varsM g Location.Loc_unknown vars)
            (fun _ ->
              Monad.check_bind (Monad.freshen_t t1)
                (fun t1a ->
                  Monad.check_bind
                    (Monad.mk_fresh
                      [Stringa.Chara
                         (false, false, false, false, true, true, true, false);
                        Stringa.Chara
                          (true, false, false, false, false, true, true, false);
                        Stringa.Chara
                          (false, false, true, false, true, true, true, false)])
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
                            (check_s ta pa (Contexts.add_to_scope ga vars) d s
                              t)
                            (fun _ -> Monad.return g))))))
    | ta, pa, g, d, SyntaxPED.PEXPp_when (p, s_guard, s), t1, t ->
        Monad.check_bind (check_pat true ta pa g p t1)
          (fun (z, (bs, vars)) ->
            Monad.check_bind (check_varsM g Location.Loc_unknown vars)
              (fun _ ->
                Monad.check_bind (Monad.freshen_t t1)
                  (fun t1a ->
                    Monad.check_bind
                      (Monad.mk_fresh
                        [Stringa.Chara
                           (false, false, false, false, true, true, true,
                             false);
                          Stringa.Chara
                            (true, false, false, false, false, true, true,
                              false);
                          Stringa.Chara
                            (false, false, true, false, true, true, true,
                              false)])
                      (fun za ->
                        Monad.check_bind
                          (Monad.return
                            (Contexts.add_to_scope
                              (Contexts.add_vars_ge g
                                ((za, (Contexts.b_of t1a,
SyntaxVCT.C_conj
  (mk_c_eq z za, Contexts.subst_c_v0 (Contexts.c_of t1a) (Monad.mk_var z)))) ::
                                  bs))
                              vars))
                          (fun ga ->
                            Monad.check_bind
                              (check_s ta pa ga d s_guard
                                (SyntaxVCT.T_refined_type
                                  (SyntaxVCT.VIndex, SyntaxVCT.B_bool,
                                    SyntaxVCT.C_true)))
                              (fun _ -> Monad.return g))))))
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
              | SyntaxVCT.B_reg _ -> Monad.fail (Monad.UnknownErrorLoc loc)
              | SyntaxVCT.B_string -> Monad.fail (Monad.UnknownErrorLoc loc)
              | SyntaxVCT.B_exception -> Monad.fail (Monad.UnknownErrorLoc loc)
              | SyntaxVCT.B_finite_set _ ->
                Monad.fail (Monad.UnknownErrorLoc loc)))
    | ux, uy, uz, vg, SyntaxPED.Ep_bop (loc, vh, vi, vj) ->
        Monad.fail (Monad.NotImplemented (loc, "bop"))
    | vk, vl, vm, vn, SyntaxPED.Ep_uop (loc, vo, vp) ->
        Monad.fail (Monad.NotImplemented (loc, "uop"))
    | t, p, g, d, SyntaxPED.Ep_ref (loc, idd) ->
        (match ContextsPiDelta.lookup_register t (SyntaxVCT.VNamed idd)
          with None -> Monad.fail (Monad.UnknownErrorLoc loc)
          | Some ta ->
            Monad.check_bind
              (Monad.mk_fresh
                [Stringa.Chara
                   (false, true, false, false, true, true, true, false);
                  Stringa.Chara
                    (true, false, true, false, false, true, true, false);
                  Stringa.Chara
                    (false, true, true, false, false, true, true, false)])
              (fun z ->
                Monad.return
                  (z, ([(z, (SyntaxVCT.B_reg ta, SyntaxVCT.C_true))],
                        SyntaxVCT.T_refined_type
                          (SyntaxVCT.VIndex, SyntaxVCT.B_reg ta,
                            SyntaxVCT.C_true)))))
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
                        (match single_base ts
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
  (SyntaxVCT.VIndex, SyntaxVCT.B_vec (ord, b),
    Contexts.mk_vec_len_eq_c SyntaxVCT.VIndex es)))))))))
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
              | SyntaxVCT.T_refined_type (_, SyntaxVCT.B_reg _, _) ->
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
    | t, p, g, d, SyntaxPED.Ep_record_update (loc, va, fes) ->
        Monad.check_bind (infer_e t p g d va)
          (fun (z2, (g2, t2)) ->
            Monad.check_bind
              (Monad.mapM
                (fun (f, e) ->
                  (match ContextsPiDelta.lookup_field_in_type t2 f
                    with None ->
                      Monad.fail
                        (Monad.CheckFail
                          (SyntaxPED.loc_e e, g, "record update invalid field",
                            t2, t2))
                    | Some b ->
                      check_s t p g d e
                        (SyntaxVCT.T_refined_type
                          (SyntaxVCT.VIndex, b, SyntaxVCT.C_true))))
                fes)
              (fun _ -> Monad.return (z2, (g2, t2))))
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
               Monad.check_bind (Monad.freshen_t tau)
                 (fun taua ->
                   Monad.check_bind
                     (subtype (SyntaxPED.loc_e e) t (Contexts.add_vars_ge g ga)
                       ta (SyntaxVCT.T_refined_type
                            (SyntaxVCT.VIndex, b2,
                              SyntaxPED.subst_cp
                                (SyntaxVCT.V_var SyntaxVCT.VIndex) z2 c2)))
                     (fun st ->
                       (if st
                         then Monad.check_bind
                                (Monad.return
                                  (Satis.type_app b2 (Contexts.b_of ta)))
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
    (SyntaxVCT.VIndex, tsubst_bp_many (Contexts.b_of taua) sub,
      Contexts.c_of taua)))
(fun taub ->
  (let kv =
     (z, (Contexts.b_of taub,
           SyntaxVCT.C_conj_many
             [Contexts.subst_c_v0 (Contexts.c_of ta) (Monad.mk_var z2);
               Contexts.subst_c_v0 (Contexts.c_of taub) (Monad.mk_var z)]))
     in
    Monad.check_bind (Monad.trace (Monad.AppI Monad.VarI))
      (fun _ ->
        Monad.return
          (z, (kv :: [] @ ga @ [] @ [(z2, (tsubst_bp_many b2 sub, c2))],
                taub)))))))
                         else (if Arith.less_nat Arith.zero_nat
                                    (Lista.size_list asa)
                                then infer_app t p g d asa e
                                else Monad.fail
                                       (Monad.FunctionArgWrongType
 (SyntaxPED.loc_e e, ta,
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
            (ContextsPiDelta.add_type t (SyntaxVCT.VNamed x) tau,
              (p, Contexts.add_type_to_scope g tau))
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
    | t, p, g, SyntaxPED.DEFp_scattered (ux, sd) -> check_scattered t p g sd
    | ta, p, g, SyntaxPED.DEFp_reg (uy, t, x) ->
        Monad.return
          (ContextsPiDelta.add_register ta x t,
            (p, Contexts.add_to_scope g [x]));;

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
