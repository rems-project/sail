module A = Ast
module I = Minisail_isa.SailAST
module E = Minisail_isa.Env
open Type_check
open Ast_util
   
let convert_loop = function
  | A.While -> I.While
  | A.Until -> I.Until

let rec convert_effect = function
  | A.Effect_aux (ea, _) ->  (convert_effect_aux ea)
and convert_effect_aux = function
  | A.Effect_set _ -> I.Effect_set []
             
let rec convert_kid = function
  | A.Kid_aux (k,_) -> (convert_kid_aux k)
and convert_kid_aux = function
  | A.Var x -> I.Var x

let rec convert_kind = function
  | A.K_aux (k,_) -> (convert_kind_aux k)
and convert_kind_aux = function
  | A.K_type -> I.K_type 
  | A.K_int  -> I.K_int 
  | A.K_order  -> I.K_order
  | A.K_bool  -> I.K_bool 

                             
let convert_kinded_id = function
  | A.KOpt_aux (A.KOpt_kind (k,kid),_) -> (I.KOpt_kind (convert_kind k, convert_kid kid))

             
let rec convert_order = function
  | A.Ord_aux (o,_) ->  (convert_order_aux o)
and convert_order_aux = function
  | A.Ord_var k -> I.Ord_var (convert_kid k)
  | A.Ord_inc -> I.Ord_inc
  | A.Ord_dec -> I.Ord_dec
             
let rec convert_lit = function
  | A.L_aux (l,_) -> (convert_lit_aux l)
and convert_lit_aux = function
  | A.L_unit -> I.L_unit
  | A.L_zero -> I.L_zero
  | A.L_one -> I.L_one
  | A.L_true -> I.L_true
  | A.L_false -> I.L_false
  | A.L_num(num) -> I.L_num num
  | A.L_hex(hex) -> I.L_hex hex
  | A.L_bin(bin) -> I.L_bin bin
  | A.L_string(string1) -> I.L_string string1
  | A.L_undef -> I.L_undef
  | A.L_real(real) -> I.L_real real

                   
let convert_id = function
  | A.Id_aux (A.Id x , _ ) ->  (I.Id x)
  | A.Id_aux (A.Operator x , _ ) -> (I.Operator x)


                            
let rec convert_nexp = function
  | A.Nexp_aux (nexp,_) -> ( convert_nexp_aux nexp)
and convert_nexp_aux = function
  | A.Nexp_id id -> I.Nexp_id (convert_id id)
  | A.Nexp_var kid -> I.Nexp_var (convert_kid kid)
  | A.Nexp_constant n -> I.Nexp_constant n
  | A.Nexp_app(id,n0) -> I.Nexp_app(convert_id id, List.map convert_nexp n0)
  | A.Nexp_times(n1,n2) -> I.Nexp_times (convert_nexp n1, convert_nexp n2)
  | A.Nexp_sum(n1,n2) -> I.Nexp_sum (convert_nexp n1, convert_nexp n2)
  | A.Nexp_minus(n1, n2) -> I.Nexp_minus (convert_nexp n1, convert_nexp n2)
  | A.Nexp_exp nexp -> I.Nexp_exp (convert_nexp nexp)
  | A.Nexp_neg nexp -> I.Nexp_neg (convert_nexp nexp)

let rec convert_nc = function
  | A.NC_aux (nc, _) ->  (convert_nc_aux nc)
and convert_nc_aux = function
  | A.NC_equal(n1,n2) -> I.NC_equal(convert_nexp n1, convert_nexp n2)
  | A.NC_bounded_ge(n1,n2) -> I.NC_bounded_ge(convert_nexp n1, convert_nexp n2)
  | A.NC_bounded_gt(n1,n2) -> I.NC_bounded_gt(convert_nexp n1, convert_nexp n2)
  | A.NC_bounded_le(n1,n2) -> I.NC_bounded_le(convert_nexp n1, convert_nexp n2)
  | A.NC_bounded_lt(n1,n2) -> I.NC_bounded_lt(convert_nexp n1, convert_nexp n2)
  | A.NC_not_equal(n1,n2) -> I.NC_not_equal(convert_nexp n1, convert_nexp n2)
  | A.NC_set(kid, nums) -> I.NC_set(convert_kid kid, nums)
  | A.NC_or(nc1,nc2) -> I.NC_and(convert_nc nc1, convert_nc nc2)
  | A.NC_and(nc1, nc2) -> I.NC_and(convert_nc nc1, convert_nc nc2)
  | A.NC_app (id, args) -> I.NC_app(convert_id id, List.map convert_typ_arg args)
  | A.NC_var kid -> I.NC_var (convert_kid kid)
  | A.NC_true -> I.NC_true
  | A.NC_false -> I.NC_false

and convert_typ_arg = function
  | A.A_aux (ta,_) ->  (convert_typ_arg_aux ta)
and convert_typ_arg_aux = function
 | A.A_nexp n -> I.A_nexp (convert_nexp n)
 | A.A_typ t -> I.A_typ (convert_typ t)
 | A.A_order o -> I.A_order (convert_order o)
 | A.A_bool nc -> I.A_bool (convert_nc nc)

    
and convert_typ = function
  | A.Typ_aux (ta,_) ->  (convert_typ_aux ta)
and convert_typ_aux = function
  | A.Typ_internal_unknown -> I.Typ_internal_unknown
  | A.Typ_id id -> I.Typ_id (convert_id id)
  | A.Typ_var kid -> I.Typ_var (convert_kid kid)
  | A.Typ_fn (typs, typ, effect ) -> I.Typ_fn (List.map convert_typ typs, convert_typ typ, convert_effect effect)
  | A.Typ_bidir(t1,t2,effect) -> I.Typ_bidir(convert_typ t1, convert_typ t2, convert_effect effect)
  | A.Typ_tup typs -> I.Typ_tup (List.map convert_typ typs)
  | A.Typ_app(id,tas) -> I.Typ_app(convert_id id, List.map convert_typ_arg tas)
  | A.Typ_exist(ks, nc, typ) -> I.Typ_exist(List.map convert_kinded_id ks, convert_nc nc, convert_typ typ)

let convert_typ_expanded (_,tan) typ =
  match destruct_tannot tan with
    None -> Printf.eprintf "no env\n";
            convert_typ typ
  | Some (env,_,_) -> Printf.eprintf "expand syn\n";
                      let typ' = Env.expand_synonyms env typ
                      in convert_typ typ'
                              
let rec convert_quant_item = function
  | A.QI_aux (qi,_) ->  (convert_quant_item_aux qi)
and convert_quant_item_aux = function
 | A.QI_id kid -> I.QI_id (convert_kinded_id kid)
 | A.QI_constraint nc -> I.QI_constraint (convert_nc nc)
 | A.QI_constant ks -> I.QI_constant (List.map convert_kinded_id ks)

    
let rec convert_typquant = function
  |  A.TypQ_aux (tq, _) -> (convert_typquant_aux tq)
and convert_typquant_aux = function
  | A.TypQ_tq qis -> I.TypQ_tq( List.map convert_quant_item qis)
  | A.TypQ_no_forall -> I.TypQ_no_forall

       

let rec convert_typ_pat = function
  | A.TP_aux (tpa,_) ->  (convert_typ_pat_aux tpa)
and convert_typ_pat_aux = function
  | A.TP_wild -> I.TP_wild
  | A.TP_var kid -> I.TP_var (convert_kid kid)
  | A.TP_app (id, tps) -> I.TP_app(convert_id id, List.map convert_typ_pat tps)

let convert_kbindings f b = List.map (fun (x,y) -> (convert_kid x, f y)) (KBindings.bindings b)
let convert_bindings f b = List.map (fun (x,y) -> (convert_id x, f y)) (Bindings.bindings b)

let convert_typ_expanded_e e t = let typ' = Env.expand_synonyms e t
                                 in convert_typ typ'

                         
let rec convert_type_union tan = function
  | A.Tu_aux (tu, _) ->  (convert_type_union_aux tan tu)
and convert_type_union_aux tan = function
  | A.Tu_ty_id (t,i) -> I.Tu_ty_id( convert_typ_expanded tan t, convert_id i)

let rec convert_type_union_e e = function
  | A.Tu_aux (tu, _) ->  (convert_type_union_e_aux e tu)
and convert_type_union_e_aux e = function
  | A.Tu_ty_id (t,i) -> I.Tu_ty_id( convert_typ_expanded_e e t, convert_id i)
                      

let convert_mut = function
    Immutable -> E.Immutable
  | Mutable -> E.Mutable
                                  
let convert_env e = E.Env_ext (
                        convert_bindings (fun (x,y) -> (convert_typquant x, convert_typ_expanded_e e y)) (Env.get_val_specs e),
                        convert_kbindings (fun x ->  (convert_kind_aux x)) (Env.get_typ_vars e),
                        convert_bindings (fun (x,y) -> (convert_mut x, convert_typ_expanded_e e y)) (Env.get_locals e), (* FIXME. Conv mut flag *)
                        convert_bindings (fun (tq,fs) ->
                            (convert_typquant tq, List.map (fun (t,i) -> (convert_id i, convert_typ_expanded_e e t)) fs)) (Env.get_records e),
                        convert_bindings (fun (tq,fs) -> (convert_typquant tq,
                                                          List.map (convert_type_union_e e) fs)) (Env.get_variants e),
                        [],
                        Util.option_map convert_order (Env.get_default_order_option e),
                        Util.option_map (convert_typ_expanded_e e) (Env.get_ret_typ e),
                        convert_bindings (fun (_,_,t) -> convert_typ_expanded_e e t) (Env.get_registers e),
                        convert_bindings (fun (tq,ta) -> (convert_typquant tq, convert_typ_arg ta)) (Env.get_typ_synonyms e),
                        convert_bindings (fun ids -> List.map convert_id (IdSet.elements ids)) (Env.get_enums e),
                        Some Tcsmt.prove,
                        ())


                        
let rec convert_tannot (( _ , tan ) as tan1) : unit E.tannot_ext option = match destruct_tannot tan with
  | None -> None
  | Some (env,typ,ef) ->
     let inst =  get_instantiations tan in 
     Some (Tannot_ext (convert_env env , convert_typ_expanded tan1 typ, convert_effect ef,  None,
                       Util.option_map (convert_kbindings convert_typ_arg) inst,
                                     () ))
(*                     
    I.effect = convert_effect t.effect;
    I.exepected = option_map convert_typ t.expected
    I.instantiation = option_map (convert_kbindings convert_typ_arg) t.instantiation 
 *)


                        
let rec convert_pat_aux tan = function
  | A.P_lit(lit) -> I.P_lit (convert_tannot tan, convert_lit lit)
  | A.P_wild -> I.P_wild(convert_tannot tan)
  | A.P_or(pat1,pat2) -> I.P_or (convert_tannot tan,convert_pat pat1, convert_pat pat2)
  | A.P_not(pat) -> I.P_not (convert_tannot tan,convert_pat pat)
  | A.P_as(pat,id) -> I.P_as(convert_tannot tan,convert_pat pat, convert_id id)
  | A.P_typ(typ,pat) -> I.P_typ (convert_tannot tan,convert_typ_expanded tan typ, convert_pat pat)
  | A.P_id(id) -> I.P_id (convert_tannot tan,convert_id id)
  | A.P_var(pat,typ_pat) -> I.P_var (convert_tannot tan,convert_pat pat, convert_typ_pat typ_pat)
  | A.P_app(id,pat0) -> I.P_app (convert_tannot tan,convert_id id, List.map convert_pat pat0)
  | A.P_vector(pat0) -> I.P_vector (convert_tannot tan,List.map convert_pat pat0)
  | A.P_vector_concat(pat0) -> I.P_vector_concat (convert_tannot tan,List.map convert_pat pat0)
  | A.P_tup(pat0) -> I.P_tup (convert_tannot tan,List.map convert_pat pat0)
  | A.P_list(pat0) -> I.P_list (convert_tannot tan,List.map convert_pat pat0)
  | A.P_cons(pat1,pat2) -> I.P_cons(convert_tannot tan, convert_pat pat1, convert_pat pat2)
  | A.P_string_append(pat0) -> I.P_string_append (convert_tannot tan,List.map convert_pat pat0)
                     
and  convert_pat = function
  | A.P_aux (pat,tan) -> convert_pat_aux tan pat

let rec convert_mpat_aux tan = function
  | A.MP_lit(lit) -> I.MP_lit (convert_tannot tan,convert_lit lit)
  | A.MP_as(pat,id) -> I.MP_as(convert_tannot tan,convert_mpat pat, convert_id id)
  | A.MP_typ(pat,typ) -> I.MP_typ (convert_tannot tan,convert_mpat pat,convert_typ_expanded tan typ)
  | A.MP_id(id) -> I.MP_id (convert_tannot tan,convert_id id)
  | A.MP_app(id,pat0) -> I.MP_app (convert_tannot tan,convert_id id, List.map convert_mpat pat0)
  | A.MP_vector(pat0) -> I.MP_vector (convert_tannot tan,List.map convert_mpat pat0)
  | A.MP_vector_concat(pat0) -> I.MP_vector_concat (convert_tannot tan,List.map convert_mpat pat0)
  | A.MP_tup(pat0) -> I.MP_tup (convert_tannot tan,List.map convert_mpat pat0)
  | A.MP_list(pat0) -> I.MP_list (convert_tannot tan,List.map convert_mpat pat0)
  | A.MP_cons(pat1,pat2) -> I.MP_cons(convert_tannot tan, convert_mpat pat1, convert_mpat pat2)
  | A.MP_string_append(pat0) -> I.MP_string_append (convert_tannot tan,List.map convert_mpat pat0)
                     
and  convert_mpat = function
  | A.MP_aux (pat,tan) -> convert_mpat_aux tan pat

                       
let rec convert_pexp_aux tan = function
  | A.Pat_exp (pat,exp) -> I.Pat_exp (convert_tannot tan,convert_pat pat, convert_exp exp)
  | A.Pat_when (pat,exp1,exp2) -> I.Pat_when (convert_tannot tan,convert_pat pat, convert_exp exp1, convert_exp exp2)
                                
and convert_pexp = function
  | A.Pat_aux (x,tan) -> convert_pexp_aux tan x

and convert_letbind_aux tan = function
  | A.LB_val (pat, exp) -> I.LB_val (convert_tannot tan,convert_pat pat, convert_exp exp)
                       
and convert_letbind = function
  | A.LB_aux (lb,tan) -> convert_letbind_aux tan lb

and convert_exp_aux tan = function
    | A.E_block(exp0) -> I.E_block (convert_tannot tan,List.map convert_exp exp0)
    | A.E_id(id) -> I.E_id (convert_tannot tan,convert_id id)
    | A.E_lit(lit) -> I.E_lit (convert_tannot tan,convert_lit lit)
    | A.E_cast(typ,exp) -> I.E_cast (convert_tannot tan,convert_typ_expanded tan typ, convert_exp exp)
    | A.E_app(id,exp0) -> I.E_app(convert_tannot tan,convert_id id, List.map convert_exp exp0)
    | A.E_app_infix(exp1,id,exp2) -> I.E_app_infix(convert_tannot tan,convert_exp exp1, convert_id id, convert_exp exp2)
    | A.E_tuple(exp0) -> I.E_tuple(convert_tannot tan,List.map convert_exp exp0)
    | A.E_if(exp1,exp2,exp3) -> I.E_if(convert_tannot tan,convert_exp exp1, convert_exp exp2, convert_exp exp3)
    | A.E_loop(loop,internal_loop_measure,exp1,exp2) -> I.E_loop(convert_tannot tan,convert_loop loop, convert_internal_loop_measure internal_loop_measure, convert_exp exp1, convert_exp exp2)
    | A.E_for(id,exp1,exp2,exp3,order,exp4) -> I.E_for(convert_tannot tan,convert_id id, convert_exp exp1,convert_exp exp2,convert_exp exp3,
                                                       convert_order order, convert_exp exp4)
    | A.E_vector(exp0) -> I.E_vector(convert_tannot tan,List.map convert_exp exp0)
    | A.E_vector_access(exp,exp_prime) -> I.E_vector_access(convert_tannot tan,convert_exp exp, convert_exp exp_prime)
    | A.E_vector_subrange(exp,exp1,exp2) -> I.E_vector_subrange(convert_tannot tan,convert_exp exp, convert_exp exp1, convert_exp exp2)
    | A.E_vector_update(exp,exp1,exp2) -> I.E_vector_update(convert_tannot tan,convert_exp exp, convert_exp exp1, convert_exp exp2)
    | A.E_vector_update_subrange(exp,exp1,exp2,exp3) -> I.E_vector_update_subrange(convert_tannot tan,convert_exp exp, convert_exp exp1, convert_exp exp2, convert_exp exp3)
    | A.E_vector_append(exp1,exp2) -> I.E_vector_append(convert_tannot tan,convert_exp exp1, convert_exp exp2)
    | A.E_list(exp0) -> I.E_list(convert_tannot tan,List.map convert_exp exp0)
    | A.E_cons(exp1,exp2) -> I.E_cons(convert_tannot tan,convert_exp exp1, convert_exp exp2)
    | A.E_record(fexp0) -> I.E_record(convert_tannot tan,List.map convert_fexp fexp0)
    | A.E_record_update(exp,fexp0) -> I.E_record_update(convert_tannot tan,convert_exp exp, List.map convert_fexp fexp0)
    | A.E_field(exp,id) -> I.E_field(convert_tannot tan,convert_exp exp, convert_id id)
    | A.E_case(exp,pexp0) -> I.E_case(convert_tannot tan,convert_exp exp, List.map convert_pexp pexp0)
    | A.E_let(letbind,exp) -> I.E_let(convert_tannot tan,convert_letbind letbind, convert_exp exp)
    | A.E_assign(lexp,exp) -> I.E_assign(convert_tannot tan,convert_lexp lexp, convert_exp exp)
    | A.E_sizeof(nexp) -> I.E_sizeof(convert_tannot tan,convert_nexp nexp)
    | A.E_return(exp) -> I.E_return(convert_tannot tan,convert_exp exp)
    | A.E_exit(exp) -> I.E_exit(convert_tannot tan,convert_exp exp)
    | A.E_ref(id) -> I.E_ref(convert_tannot tan,convert_id id)
    | A.E_throw(exp) -> I.E_throw(convert_tannot tan,convert_exp exp)
    | A.E_try(exp,pexp0) -> I.E_try(convert_tannot tan,convert_exp exp, List.map convert_pexp pexp0)
    | A.E_assert(exp,exp_prime) -> I.E_assert(convert_tannot tan,convert_exp exp, convert_exp exp_prime)
    | A.E_var(lexp,exp,exp_prime) -> I.E_var(convert_tannot tan,convert_lexp lexp, convert_exp exp, convert_exp exp_prime)
    | A.E_internal_plet(pat,exp,exp_prime) -> I.E_internal_plet(convert_tannot tan,convert_pat pat, convert_exp exp, convert_exp exp_prime)
    | A.E_internal_return(exp) -> I.E_internal_return(convert_tannot tan,convert_exp exp)
    (*    | A.E_internal_value(value) -> I.E_internal_value(convert_tannot tan,string "E_internal_value" ^^ string "(" ^^ pp_raw_value value ^^ string ")"*)
    | A.E_constraint(n_constraint) -> I.E_constraint(convert_tannot tan,convert_nc n_constraint)
                                    
                     
and convert_exp = function
  | A.E_aux (exp,tan) -> convert_exp_aux tan exp

and convert_fexp = function
  | A.FE_aux (fe,tan) -> convert_fexp_aux tan fe

and convert_fexp_aux tan = function
  | A.FE_Fexp (id,exp) -> I.FE_Fexp (convert_tannot tan,convert_id id, convert_exp exp)
                       
and convert_internal_loop_measure = function
  | A.Measure_aux (m,_) -> convert_internal_loop_measure_aux m

and convert_internal_loop_measure_aux = function
  | A.Measure_none -> I.Measure_none
  | A.Measure_some e -> I.Measure_some (convert_exp e)
                         
                       
and convert_lexp = function
  | A.LEXP_aux (lb,tan) -> convert_lexp_aux tan lb

and convert_lexp_aux tan = function
  | A.LEXP_id id -> I.LEXP_id (convert_tannot tan,convert_id id)
  | A.LEXP_deref e -> I.LEXP_deref (convert_tannot tan,convert_exp e)
  | A.LEXP_memory (id, exps) -> I.LEXP_memory(convert_tannot tan, convert_id id, List.map convert_exp exps)
  | A.LEXP_cast (typ,id) -> I.LEXP_cast (convert_tannot tan,convert_typ_expanded tan typ, convert_id id)
  | A.LEXP_tup ls -> I.LEXP_tup (convert_tannot tan,List.map convert_lexp ls)
  | A.LEXP_vector_concat ls -> I.LEXP_vector_concat (convert_tannot tan,List.map convert_lexp ls)
  | A.LEXP_vector (l,e) -> I.LEXP_vector (convert_tannot tan,convert_lexp l, convert_exp e)
  | A.LEXP_vector_range (l, e1,e2)-> I.LEXP_vector_range (convert_tannot tan,convert_lexp l, convert_exp e1, convert_exp e2)
  | A.LEXP_field(lexp,id) -> I.LEXP_field (convert_tannot tan,convert_lexp lexp, convert_id id)
                       
let convert_funcl_aux tan = function
  | A.FCL_Funcl (fid, pexp) -> I.FCL_Funcl (convert_tannot tan,convert_id fid, PEXP_funcl (convert_pexp pexp))
                     
let convert_funcl = function
  | A.FCL_aux (f,tan) -> convert_funcl_aux tan f 

let rec convert_rec_opt = function
  | A.Rec_aux (ra,_) -> convert_rec_opt_aux ra
and convert_rec_opt_aux = function
  | A.Rec_nonrec -> I.Rec_nonrec
  | A.Rec_rec -> I.Rec_rec
  | A.Rec_measure (pat,exp) -> I.Rec_measure (convert_pat pat, convert_exp exp)

                             


let rec convert_tannot_opt tan = function
  | A.Typ_annot_opt_aux (t,_) -> convert_tannot_opt_aux tan t
and convert_tannot_opt_aux tan = function
  | A.Typ_annot_opt_none ->  I.Typ_annot_opt_none 
  | A.Typ_annot_opt_some (tq,typ) -> I.Typ_annot_opt_some(convert_typquant tq, convert_typ_expanded tan typ)


(* Not handling effects *)                         
let convert_effect_opt = function
  | _ ->  I.Effect_opt_none
                     
let convert_fundef = function
  | A.FD_aux (A.FD_function (a,b,c,d),(tan)) -> (I.FD_function (convert_tannot tan, convert_rec_opt a,
                                                                         convert_tannot_opt tan b, convert_effect_opt c,
                                                                         List.map convert_funcl d))

let convert_order = function
  | A.Ord_aux (o,_) ->  I.Ord_inc
                                                
let convert_default_spec = function
  | A.DT_aux ( DT_order o, _) ->  ( I.DT_order (convert_order o))

let rec convert_dec_spec = function
  | A.DEC_aux (da,tan) ->  convert_dec_spec_aux tan da
and convert_dec_spec_aux tan = function
  | A.DEC_reg(e1,e2,t,id) -> I.DEC_reg(convert_tannot tan,convert_effect e1, convert_effect e2, convert_typ t, convert_id id)
(* | A.DEC_config of id * typ * ( 'a exp)
 | A.DEC_alias of id * ( 'a alias_spec)
 | A.DEC_typ_alias of typ * id * ( 'a alias_spec)*)


let rec convert_type_def env = function
  | A.TD_aux (tda, tan) -> I.TD_aux (convert_type_def_aux env tda)
and convert_type_def_aux env = function
  | A.TD_abbrev(id,tq,ta) -> I.TD_abbrev(convert_id id, convert_typquant tq, convert_typ_arg ta)
  | A.TD_record(id , tq, fields, b) -> I.TD_record(convert_id id, convert_typquant tq,
                      List.map (fun (t,id) -> (convert_typ t, convert_id id)) fields, b)
  | A.TD_variant(id,tq, tu,b) -> I.TD_variant(convert_id id, convert_typquant tq, List.map (convert_type_union_e env) tu, b)
  | A.TD_enum(id, ids, b) -> I.TD_enum(convert_id id, List.map convert_id ids, b)
(*  | A.TD_bitfield(id, typ, xs) -. A.TD_bitfield(convert_tannot tan,convert_id id, convert_typ typ, [])  FIXME *)

let rec convert_typschm tan = function
  | A.TypSchm_aux (tsa, _) -> convert_typschm_aux tan tsa
and convert_typschm_aux tan = function
  | A.TypSchm_ts (tq,t) -> I.TypSchm_ts (convert_typquant tq, convert_typ_expanded tan t)


                         
let rec convert_mpexp = function
  | A.MPat_aux (mp,tan) ->  convert_mpexp_aux tan mp
and convert_mpexp_aux tan = function
  | A.MPat_pat mp -> I.MPat_pat (convert_tannot tan,convert_mpat mp)
  | A.MPat_when(mp,ep) -> I.MPat_when(convert_tannot tan, convert_mpat mp, convert_exp ep)

let rec convert_val_spec = function
  | A.VS_aux (vsa,tan) -> I.VS_aux (convert_val_spec_aux tan vsa )
and convert_val_spec_aux tan = function
  | A.VS_val_spec (ts,id, ss, b ) -> (convert_typschm tan ts, (convert_id id, ((fun _ -> None), b)))

let rec convert_mapcl = function
  | A.MCL_aux (mcl,tan) -> convert_mapcl_aux tan mcl
and convert_mapcl_aux tan = function
  | A.MCL_bidir (mp1, mp2) -> I.MCL_bidir (convert_tannot tan, convert_mpexp mp1, convert_mpexp mp2)
  | A.MCL_forwards(mp,ep) -> I.MCL_forwards(convert_tannot tan, convert_mpexp mp, convert_exp ep)
  | A.MCL_backwards(mp,ep) -> I.MCL_backwards(convert_tannot tan, convert_mpexp mp, convert_exp ep)

                                   
let rec convert_mapdef = function
  | A.MD_aux (mda, tan) -> convert_mapdef_aux tan mda
and convert_mapdef_aux tan = function
  | A.MD_mapping (id, o, mapcls ) -> I.MD_mapping (convert_tannot tan, convert_id id, convert_tannot_opt tan o, []) (* FIXME *)

let convert_prec = function
 | A.Infix -> I.Infix
 | A.InfixL -> I.InfixL 
 | A.InfixR -> I.InfixR

let rec convert_scattered_def = function
  | A.SD_aux (sda, tan) -> convert_scattered_def_aux tan sda
and convert_scattered_def_aux tan = function
 | A.SD_function (ro, t, e, id) -> I.SD_function (convert_tannot tan, convert_rec_opt ro, convert_tannot_opt tan t, convert_effect_opt e, convert_id id)
 | A.SD_funcl fcl -> I.SD_funcl (convert_tannot tan,convert_funcl fcl)
 | A.SD_variant (id, tq ) -> I.SD_variant (convert_tannot tan,convert_id id, convert_typquant tq)
 | A.SD_unioncl (id,tu) -> I.SD_unioncl(convert_tannot tan,convert_id id, convert_type_union tan  tu)
 | A.SD_mapping (id, top) -> I.SD_mapping(convert_tannot tan,convert_id id, convert_tannot_opt tan top)
 | A.SD_mapcl(id, mapcl) -> I.SD_mapcl(convert_tannot tan,convert_id id, convert_mapcl mapcl)
 | A.SD_end id  -> I.SD_end (convert_tannot tan,convert_id id)    



let convert_loop_measure = function
  | A.Loop (l,exp) -> I.Loop (convert_loop l, convert_exp exp)
                               
let convert_def env = function
  | A.DEF_fundef x -> I.DEF_fundef (convert_fundef x)
  | A.DEF_overload (oid , idlist ) -> I.DEF_overload (convert_id oid, List.map convert_id idlist)
  | A.DEF_val lb -> I.DEF_val (convert_letbind lb)
  | A.DEF_default ds -> I.DEF_default (convert_default_spec ds)
  | A.DEF_type td -> I.DEF_type (convert_type_def env td)
  | A.DEF_spec vs -> I.DEF_spec (convert_val_spec vs)
  | A.DEF_mapdef md  -> I.DEF_mapdef (convert_mapdef md)
  | A.DEF_fixity (prec, num, id) -> I.DEF_fixity (convert_prec prec, num, convert_id id)
  | A.DEF_scattered ds -> I.DEF_scattered (convert_scattered_def ds)
  | A.DEF_measure (id, pat, exp) -> I.DEF_measure (convert_id id, convert_pat pat, convert_exp exp)
  | A.DEF_loop_measures (id, lms) -> I.DEF_loop_measures (convert_id id, List.map convert_loop_measure lms)
  | A.DEF_reg_dec ds -> I.DEF_reg_dec (convert_dec_spec ds)
  | A.DEF_internal_mutrec fds -> I.DEF_internal_mutrec (List.map convert_fundef fds)
  | A.DEF_pragma (s1,s2,_) -> I.DEF_pragma (s1,s2)


