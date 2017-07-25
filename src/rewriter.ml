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
(*    Thomas Bauereiss                                                    *)
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

open Big_int
open Ast
open Ast_util
open Type_check
open Spec_analysis

type 'a rewriters = {
    rewrite_exp  : 'a rewriters -> 'a exp -> 'a exp;
    rewrite_lexp : 'a rewriters -> 'a lexp -> 'a lexp;
    rewrite_pat  : 'a rewriters -> 'a pat -> 'a pat;
    rewrite_let  : 'a rewriters -> 'a letbind -> 'a letbind;
    rewrite_fun  : 'a rewriters -> 'a fundef -> 'a fundef;
    rewrite_def  : 'a rewriters -> 'a def -> 'a def;
    rewrite_defs : 'a rewriters -> 'a defs -> 'a defs;
  }


let (>>) f g = fun x -> g(f(x))

let effect_of_fpat (FP_aux (_,(_,a))) = effect_of_annot a
let effect_of_lexp (LEXP_aux (_,(_,a))) = effect_of_annot a
let effect_of_fexp (FE_aux (_,(_,a))) = effect_of_annot a
let effect_of_fexps (FES_aux (FES_Fexps (fexps,_),_)) =
  List.fold_left union_effects no_effect (List.map effect_of_fexp fexps)
let effect_of_opt_default (Def_val_aux (_,(_,a))) = effect_of_annot a
let effect_of_pexp (Pat_aux (_,(_,a))) = effect_of_annot a
let effect_of_lb (LB_aux (_,(_,a))) = effect_of_annot a

let get_loc_exp (E_aux (_,(l,_))) = l

let simple_annot l typ = (Parse_ast.Generated l, Some (Env.empty, typ, no_effect))
let simple_num l n = E_aux (
  E_lit (L_aux (L_num n, Parse_ast.Generated l)),
  simple_annot (Parse_ast.Generated l)
    (atom_typ (Nexp_aux (Nexp_constant n, Parse_ast.Generated l))))

let fresh_name_counter = ref 0

let fresh_name () =
  let current = !fresh_name_counter in
  let () = fresh_name_counter := (current + 1) in
  current
let reset_fresh_name_counter () =
  fresh_name_counter := 0

let fresh_id pre l =
  let current = fresh_name () in
  Id_aux (Id (pre ^ string_of_int current), Parse_ast.Generated l)

let fresh_id_exp pre ((l,annot)) =
  let id = fresh_id pre l in
  E_aux (E_id id, (Parse_ast.Generated l, annot))

let fresh_id_pat pre ((l,annot)) =
  let id = fresh_id pre l in
  P_aux (P_id id, (Parse_ast.Generated l, annot))

let union_eff_exps es =
  List.fold_left union_effects no_effect (List.map effect_of es)

let fix_eff_exp (E_aux (e,((l,_) as annot))) = match snd annot with
| Some (env, typ, eff) ->
  let effsum = union_effects eff (match e with
    | E_block es -> union_eff_exps es
    | E_nondet es -> union_eff_exps es
    | E_id _
    | E_lit _ -> no_effect
    | E_cast (_,e) -> effect_of e
    | E_app (_,es)
    | E_tuple es -> union_eff_exps es
    | E_app_infix (e1,_,e2) -> union_eff_exps [e1;e2]
    | E_if (e1,e2,e3) -> union_eff_exps [e1;e2;e3]
    | E_for (_,e1,e2,e3,_,e4) -> union_eff_exps [e1;e2;e3;e4]
    | E_vector es -> union_eff_exps es
    | E_vector_indexed (ies,opt_default) ->
       let (_,es) = List.split ies in
       union_effects (effect_of_opt_default opt_default) (union_eff_exps es)
    | E_vector_access (e1,e2) -> union_eff_exps [e1;e2]
    | E_vector_subrange (e1,e2,e3) -> union_eff_exps [e1;e2;e3]
    | E_vector_update (e1,e2,e3) -> union_eff_exps [e1;e2;e3]
    | E_vector_update_subrange (e1,e2,e3,e4) -> union_eff_exps [e1;e2;e3;e4]
    | E_vector_append (e1,e2) -> union_eff_exps [e1;e2]
    | E_list es -> union_eff_exps es
    | E_cons (e1,e2) -> union_eff_exps [e1;e2]
    | E_record fexps -> effect_of_fexps fexps
    | E_record_update(e,fexps) ->
      union_effects (effect_of e) (effect_of_fexps fexps)
    | E_field (e,_) -> effect_of e
    | E_case (e,pexps) ->
      List.fold_left union_effects (effect_of e) (List.map effect_of_pexp pexps)
    | E_let (lb,e) -> union_effects (effect_of_lb lb) (effect_of e)
    | E_assign (lexp,e) -> union_effects (effect_of_lexp lexp) (effect_of e)
    | E_exit e -> effect_of e
    | E_return e -> effect_of e
    | E_sizeof _ | E_sizeof_internal _ -> no_effect
    | E_assert (c,m) -> no_effect
    | E_comment _ | E_comment_struc _ -> no_effect
    | E_internal_cast (_,e) -> effect_of e
    | E_internal_exp _ -> no_effect
    | E_internal_exp_user _ -> no_effect
    | E_internal_let (lexp,e1,e2) ->
      union_effects (effect_of_lexp lexp)
        (union_effects (effect_of e1) (effect_of e2))
    | E_internal_plet (_,e1,e2) -> union_effects (effect_of e1) (effect_of e2)
    | E_internal_return e1 -> effect_of e1)
  in
  E_aux (e, (l, Some (env, typ, effsum)))
| None ->
  E_aux (e, (l, None))

let fix_eff_lexp (LEXP_aux (lexp,((l,_) as annot))) = match snd annot with
| Some (env, typ, eff) ->
  let effsum = union_effects eff (match lexp with
    | LEXP_id _ -> no_effect
    | LEXP_cast _ -> no_effect
    | LEXP_memory (_,es) -> union_eff_exps es
    | LEXP_vector (lexp,e) -> union_effects (effect_of_lexp lexp) (effect_of e)
    | LEXP_vector_range (lexp,e1,e2) ->
      union_effects (effect_of_lexp lexp)
        (union_effects (effect_of e1) (effect_of e2))
    | LEXP_field (lexp,_) -> effect_of_lexp lexp) in
  LEXP_aux (lexp, (l, Some (env, typ, effsum)))
| None ->
  LEXP_aux (lexp, (l, None))

let fix_eff_fexp (FE_aux (fexp,((l,_) as annot))) = match snd annot with
| Some (env, typ, eff) ->
  let effsum = union_effects eff (match fexp with
    | FE_Fexp (_,e) -> effect_of e) in
  FE_aux (fexp, (l, Some (env, typ, effsum)))
| None ->
  FE_aux (fexp, (l, None))

let fix_eff_fexps fexps = fexps (* FES_aux have no effect information *)

let fix_eff_opt_default (Def_val_aux (opt_default,((l,_) as annot))) = match snd annot with
| Some (env, typ, eff) ->
  let effsum = union_effects eff (match opt_default with
    | Def_val_empty -> no_effect
    | Def_val_dec e -> effect_of e) in
  Def_val_aux (opt_default, (l, Some (env, typ, effsum)))
| None ->
  Def_val_aux (opt_default, (l, None))

let fix_eff_pexp (Pat_aux (pexp,((l,_) as annot))) = match snd annot with
| Some (env, typ, eff) ->
  let effsum = union_effects eff (match pexp with
    | Pat_exp (_,e) -> effect_of e) in
  Pat_aux (pexp, (l, Some (env, typ, effsum)))
| None ->
  Pat_aux (pexp, (l, None))

let fix_eff_lb (LB_aux (lb,((l,_) as annot))) = match snd annot with
| Some (env, typ, eff) ->
  let effsum = union_effects eff (match lb with
    | LB_val_explicit (_,_,e) -> effect_of e
    | LB_val_implicit (_,e) -> effect_of e) in
  LB_aux (lb, (l, Some (env, typ, effsum)))
| None ->
  LB_aux (lb, (l, None))

let effectful_effs = function
  | Effect_aux (Effect_set effs, _) ->
    List.exists
      (fun (BE_aux (be,_)) ->
       match be with
       | BE_nondet | BE_unspec | BE_undef | BE_lset -> false
       | _ -> true
      ) effs
  | _ -> true

let effectful eaux = effectful_effs (effect_of eaux)

let updates_vars_effs = function
  | Effect_aux (Effect_set effs, _) ->
    List.exists
      (fun (BE_aux (be,_)) ->
       match be with
       | BE_lset -> true
       | _ -> false
      ) effs
  | _ -> true

let updates_vars eaux = updates_vars_effs (effect_of eaux)

let id_to_string (Id_aux(id,l)) =
  match id with
    | Id(s) -> s
    | DeIid(s) -> s


(*let rec partial_assoc (eq: 'a -> 'a -> bool) (v: 'a) (ls : ('a *'b) list ) : 'b option  = match ls with
  | [] -> None
  | (v1,v2)::ls -> if (eq v1 v) then Some v2 else partial_assoc eq v ls

let mk_atom_typ i = {t=Tapp("atom",[TA_nexp i])}

let simple_num l n : tannot exp =
  let typ = simple_annot (mk_atom_typ (mk_c (big_int_of_int n))) in
  E_aux (E_lit (L_aux (L_num n,l)), (l,typ))

let rec rewrite_nexp_to_exp program_vars l nexp = 
  let rewrite n = rewrite_nexp_to_exp program_vars l n in
  let typ = mk_atom_typ nexp in
  let actual_rewrite_n nexp = 
    match nexp.nexp with
      | Nconst i -> E_aux (E_lit (L_aux (L_num (int_of_big_int i),l)), (l,simple_annot typ))
      | Nadd (n1,n2) -> E_aux (E_app_infix (rewrite n1,(Id_aux (Id "+",l)),rewrite n2),
                               (l, (tag_annot typ (External (Some "add")))))
      | Nmult (n1,n2) -> E_aux (E_app_infix (rewrite n1,(Id_aux (Id "*",l)),rewrite n2),
                                (l, tag_annot typ (External (Some "multiply"))))
      | Nsub (n1,n2) -> E_aux (E_app_infix (rewrite n1,(Id_aux (Id "-",l)),rewrite n2),
                               (l, tag_annot typ (External (Some "minus"))))
      | N2n (n, _) -> E_aux (E_app_infix (E_aux (E_lit (L_aux (L_num 2,l)), (l, simple_annot (mk_atom_typ n_two))),
                                          (Id_aux (Id "**",l)),
                                          rewrite n), (l, tag_annot typ (External (Some "power"))))
      | Npow(n,i) -> E_aux (E_app_infix 
                              (rewrite n, (Id_aux (Id "**",l)),
                               E_aux (E_lit (L_aux (L_num i,l)),
                                      (l, simple_annot (mk_atom_typ (mk_c_int i))))),
                            (l, tag_annot typ (External (Some "power"))))
      | Nneg(n) -> E_aux (E_app_infix (E_aux (E_lit (L_aux (L_num 0,l)), (l, simple_annot (mk_atom_typ n_zero))),
                                       (Id_aux (Id "-",l)),
                                       rewrite n),
                          (l, tag_annot typ (External (Some "minus"))))
      | Nvar v -> (*TODO these need to generate an error as it's a place where there's insufficient specification. 
                    But, for now I need to permit this to make power.sail compile, and most errors are in trap 
                    or vectors *)
              (*let _ = Printf.eprintf "unbound variable here %s\n" v in*) 
        E_aux (E_id (Id_aux (Id v,l)),(l,simple_annot typ))
      | _ -> raise (Reporting_basic.err_unreachable l ("rewrite_nexp given n that can't be rewritten: " ^ (n_to_string nexp))) in
  match program_vars with
    | None -> actual_rewrite_n nexp
    | Some program_vars ->
      (match partial_assoc nexp_eq_check nexp program_vars with
        | None -> actual_rewrite_n nexp
        | Some(None,ev) ->
          (*let _ = Printf.eprintf "var case of rewrite, %s\n" ev in*)
          E_aux (E_id (Id_aux (Id ev,l)), (l, simple_annot typ))
        | Some(Some f,ev) -> 
          E_aux (E_app ((Id_aux (Id f,l)), [ (E_aux (E_id (Id_aux (Id ev,l)), (l,simple_annot typ)))]),
                 (l, tag_annot typ (External (Some f)))))

let rec match_to_program_vars ns bounds =
  match ns with
    | [] -> []
    | n::ns -> match find_var_from_nexp n bounds with
        | None -> match_to_program_vars ns bounds
        | Some(augment,ev) -> 
          (*let _ = Printf.eprintf "adding n %s to program var %s\n" (n_to_string n) ev in*)
          (n,(augment,ev))::(match_to_program_vars ns bounds)*)

let explode s =
  let rec exp i l = if i < 0 then l else exp (i - 1) (s.[i] :: l) in
  exp (String.length s - 1) []


let vector_string_to_bit_list l lit = 

  let hexchar_to_binlist = function
    | '0' -> ['0';'0';'0';'0']
    | '1' -> ['0';'0';'0';'1']
    | '2' -> ['0';'0';'1';'0']
    | '3' -> ['0';'0';'1';'1']
    | '4' -> ['0';'1';'0';'0']
    | '5' -> ['0';'1';'0';'1']
    | '6' -> ['0';'1';'1';'0']
    | '7' -> ['0';'1';'1';'1']
    | '8' -> ['1';'0';'0';'0']
    | '9' -> ['1';'0';'0';'1']
    | 'A' -> ['1';'0';'1';'0']
    | 'B' -> ['1';'0';'1';'1']
    | 'C' -> ['1';'1';'0';'0']
    | 'D' -> ['1';'1';'0';'1']
    | 'E' -> ['1';'1';'1';'0']
    | 'F' -> ['1';'1';'1';'1']
    | _ -> raise (Reporting_basic.err_unreachable l "hexchar_to_binlist given unrecognized character") in
  
  let s_bin = match lit with
    | L_hex s_hex -> List.flatten (List.map hexchar_to_binlist (explode (String.uppercase s_hex)))
    | L_bin s_bin -> explode s_bin
    | _ -> raise (Reporting_basic.err_unreachable l "s_bin given non vector literal") in

  List.map (function '0' -> L_aux (L_zero, Parse_ast.Generated l)
                   | '1' -> L_aux (L_one,Parse_ast.Generated l)
                   | _ -> raise (Reporting_basic.err_unreachable (Parse_ast.Generated l) "binary had non-zero or one")) s_bin

let rewrite_pat rewriters (P_aux (pat,(l,annot))) =
  let rewrap p = P_aux (p,(l,annot)) in
  let rewrite = rewriters.rewrite_pat rewriters in
  match pat with
  | P_lit (L_aux ((L_hex _ | L_bin _) as lit,_)) ->
    let ps =  List.map (fun p -> P_aux (P_lit p, simple_annot l bit_typ))
        (vector_string_to_bit_list l lit) in
    rewrap (P_vector ps)
  | P_lit _ | P_wild | P_id _ -> rewrap pat
  | P_as(pat,id) -> rewrap (P_as( rewrite pat, id))
  | P_typ(typ,pat) -> rewrite pat
  | P_app(id ,pats) -> rewrap (P_app(id, List.map rewrite pats))
  | P_record(fpats,_) ->
    rewrap (P_record(List.map (fun (FP_aux(FP_Fpat(id,pat),pannot)) -> FP_aux(FP_Fpat(id, rewrite pat), pannot)) fpats,
                     false))
  | P_vector pats -> rewrap (P_vector(List.map rewrite pats))
  | P_vector_indexed ipats -> rewrap (P_vector_indexed(List.map (fun (i,pat) -> (i, rewrite pat)) ipats))
  | P_vector_concat pats -> rewrap (P_vector_concat (List.map rewrite pats))
  | P_tup pats -> rewrap (P_tup (List.map rewrite pats))
  | P_list pats -> rewrap (P_list (List.map rewrite pats))
  | P_cons (pat1, pat2) -> rewrap (P_cons (rewrite pat1, rewrite pat2))

let rewrite_exp rewriters (E_aux (exp,(l,annot))) = 
  let rewrap e = E_aux (e,(l,annot)) in
  let rewrite = rewriters.rewrite_exp rewriters in
  match exp with
  | E_comment _ | E_comment_struc _ -> rewrap exp
  | E_block exps -> rewrap (E_block (List.map rewrite exps))
  | E_nondet exps -> rewrap (E_nondet (List.map rewrite exps))
  | E_lit (L_aux ((L_hex _ | L_bin _) as lit,_)) ->
    let es = List.map (fun p -> E_aux (E_lit p, simple_annot l bit_typ))
        (vector_string_to_bit_list l lit) in
    rewrap (E_vector es)
  | E_id _ | E_lit _  -> rewrap exp
  | E_cast (typ, exp) -> rewrap (E_cast (typ, rewrite exp))
  | E_app (id,exps) -> rewrap (E_app (id,List.map rewrite exps))
  | E_app_infix(el,id,er) -> rewrap (E_app_infix(rewrite el,id,rewrite er))
  | E_tuple exps -> rewrap (E_tuple (List.map rewrite exps))
  | E_if (c,t,e) -> rewrap (E_if (rewrite c,rewrite t, rewrite e))
  | E_for (id, e1, e2, e3, o, body) ->
    rewrap (E_for (id, rewrite e1, rewrite e2, rewrite e3, o, rewrite body))
  | E_vector exps -> rewrap (E_vector (List.map rewrite exps))
  | E_vector_indexed (exps,(Def_val_aux(default,dannot))) ->
    let def = match default with
      | Def_val_empty -> default
      | Def_val_dec e -> Def_val_dec (rewrite e) in
    rewrap (E_vector_indexed (List.map (fun (i,e) -> (i, rewrite e)) exps, Def_val_aux(def,dannot)))
  | E_vector_access (vec,index) -> rewrap (E_vector_access (rewrite vec,rewrite index))
  | E_vector_subrange (vec,i1,i2) ->
    rewrap (E_vector_subrange (rewrite vec,rewrite i1,rewrite i2))
  | E_vector_update (vec,index,new_v) -> 
    rewrap (E_vector_update (rewrite vec,rewrite index,rewrite new_v))
  | E_vector_update_subrange (vec,i1,i2,new_v) ->
    rewrap (E_vector_update_subrange (rewrite vec,rewrite i1,rewrite i2,rewrite new_v))
  | E_vector_append (v1,v2) -> rewrap (E_vector_append (rewrite v1,rewrite v2))
  | E_list exps -> rewrap (E_list (List.map rewrite exps)) 
  | E_cons(h,t) -> rewrap (E_cons (rewrite h,rewrite t))
  | E_record (FES_aux (FES_Fexps(fexps, bool),fannot)) -> 
    rewrap (E_record 
              (FES_aux (FES_Fexps 
                          (List.map (fun (FE_aux(FE_Fexp(id,e),fannot)) -> 
                               FE_aux(FE_Fexp(id,rewrite e),fannot)) fexps, bool), fannot)))
  | E_record_update (re,(FES_aux (FES_Fexps(fexps, bool),fannot))) ->
    rewrap (E_record_update ((rewrite re),
                             (FES_aux (FES_Fexps 
                                         (List.map (fun (FE_aux(FE_Fexp(id,e),fannot)) -> 
                                              FE_aux(FE_Fexp(id,rewrite e),fannot)) fexps, bool), fannot))))
  | E_field(exp,id) -> rewrap (E_field(rewrite exp,id))
  | E_case (exp ,pexps) -> 
    rewrap (E_case (rewrite exp,
                    (List.map 
                       (fun (Pat_aux (Pat_exp(p,e),pannot)) -> 
                          Pat_aux (Pat_exp(rewriters.rewrite_pat rewriters p,rewrite e),pannot)) pexps)))
  | E_let (letbind,body) -> rewrap (E_let(rewriters.rewrite_let rewriters letbind,rewrite body))
  | E_assign (lexp,exp) -> rewrap (E_assign(rewriters.rewrite_lexp rewriters lexp,rewrite exp))
  | E_sizeof n -> rewrap (E_sizeof n)
  | E_exit e -> rewrap (E_exit (rewrite e))
  | E_return e -> rewrap (E_return (rewrite e))
  | E_assert(e1,e2) -> rewrap (E_assert(rewrite e1,rewrite e2))
  | E_internal_cast (casted_annot,exp) ->
    rewrap (E_internal_cast (casted_annot, rewrite exp))
    (* check_exp (env_of exp) (strip_exp exp) (typ_of_annot casted_annot) *)
    (*let new_exp = rewrite exp in
    (*let _ = Printf.eprintf "Removing an internal_cast with %s\n" (tannot_to_string casted_annot) in*)
    (match casted_annot,exp with
     | Base((_,t),_,_,_,_,_),E_aux(ec,(ecl,Base((_,exp_t),_,_,_,_,_))) ->
       (*let _ = Printf.eprintf "Considering removing an internal cast where the two types are %s and %s\n" 
         (t_to_string t) (t_to_string exp_t) in*)
       (match t.t,exp_t.t with
        (*TODO should pass d_env into here so that I can look at the abbreviations if there are any here*)
        | Tapp("vector",[TA_nexp n1;TA_nexp nw1;TA_ord o1;_]),
          Tapp("vector",[TA_nexp n2;TA_nexp nw2;TA_ord o2;_]) 
        | Tapp("vector",[TA_nexp n1;TA_nexp nw1;TA_ord o1;_]),
          Tapp("reg",[TA_typ {t=(Tapp("vector",[TA_nexp n2; TA_nexp nw2; TA_ord o2;_]))}]) ->
          (match n1.nexp with
           | Nconst i1 -> if nexp_eq n1 n2 then new_exp else rewrap (E_cast (t_to_typ t,new_exp))
           | _ -> (match o1.order with
               | Odec -> 
                 (*let _ = Printf.eprintf "Considering removing a cast or not: %s %s, %b\n" 
                     (n_to_string nw1) (n_to_string n1) (nexp_one_more_than nw1 n1) in*)
                 rewrap (E_cast (Typ_aux (Typ_var (Kid_aux((Var "length"),Parse_ast.Generated l)),
                                          Parse_ast.Generated l),new_exp))
               | _ -> new_exp))
        | _ -> new_exp
     | Base((_,t),_,_,_,_,_),_ ->
       (*let _ = Printf.eprintf "Considering removing an internal cast where the remaining type is %s\n%!"
            (t_to_string t) in*)
       (match t.t with
        | Tapp("vector",[TA_nexp n1;TA_nexp nw1;TA_ord o1;_]) ->
          (match o1.order with
           | Odec -> 
             let _ = Printf.eprintf "Considering removing a cast or not: %s %s, %b\n" 
                 (n_to_string nw1) (n_to_string n1) (nexp_one_more_than nw1 n1) in
             rewrap (E_cast (Typ_aux (Typ_var (Kid_aux((Var "length"), Parse_ast.Generated l)),
                                      Parse_ast.Generated l), new_exp))
           | _ -> new_exp)
        | _ -> new_exp)
     | _ -> (*let _ = Printf.eprintf "Not a base match?\n" in*) new_exp*)
  (*| E_internal_exp (l,impl) ->
    match impl with
     | Base((_,t),_,_,_,_,bounds) ->
       (*let _ = Printf.eprintf "Rewriting internal expression, with type %s, and bounds %s\n" 
         (t_to_string t) (bounds_to_string bounds) in*)
       let bounds = match nmap with | None -> bounds | Some (nm,_) -> add_map_to_bounds nm bounds in
       (*let _ = Printf.eprintf "Bounds after looking at nmap %s\n" (bounds_to_string bounds) in*)
       (match t.t with
        (*Old case; should possibly be removed*)
        | Tapp("register",[TA_typ {t= Tapp("vector",[ _; TA_nexp r;_;_])}])
        | Tapp("vector", [_;TA_nexp r;_;_])
        | Tabbrev(_, {t=Tapp("vector",[_;TA_nexp r;_;_])}) ->
          (*let _ = Printf.eprintf "vector case with %s, bounds are %s\n" 
                (n_to_string r) (bounds_to_string bounds) in*)
          let nexps = expand_nexp r in
          (match (match_to_program_vars nexps bounds) with
           | [] -> rewrite_nexp_to_exp None l r
           | map -> rewrite_nexp_to_exp (Some map) l r)
        | Tapp("implicit", [TA_nexp i]) ->
          (*let _ = Printf.eprintf "Implicit case with %s\n" (n_to_string i) in*)
          let nexps = expand_nexp i in
          (match (match_to_program_vars nexps bounds) with
           | [] -> rewrite_nexp_to_exp None l i
           | map -> rewrite_nexp_to_exp (Some map) l i)
        | _ -> 
          raise (Reporting_basic.err_unreachable l 
                   ("Internal_exp given unexpected types " ^ (t_to_string t))))
     | _ -> raise (Reporting_basic.err_unreachable l ("Internal_exp given none Base annot"))*)
  (*| E_sizeof_internal (l,impl) ->
    (match impl with
     | Base((_,t),_,_,_,_,bounds) ->
       let bounds = match nmap with | None -> bounds | Some (nm,_) -> add_map_to_bounds nm bounds in
       (match t.t with
        | Tapp("atom",[TA_nexp n]) ->
          let nexps = expand_nexp n in
          (*let _ = Printf.eprintf "Removing sizeof_internal with type %s\n" (t_to_string t) in*)
          (match (match_to_program_vars nexps bounds) with
           | [] -> rewrite_nexp_to_exp None l n
           | map -> rewrite_nexp_to_exp (Some map) l n)
        | _ -> raise (Reporting_basic.err_unreachable l ("Sizeof internal had non-atom type " ^ (t_to_string t))))
     | _ -> raise (Reporting_basic.err_unreachable l ("Sizeof internal had none base annot"))*)
  (*| E_internal_exp_user ((l,user_spec),(_,impl)) -> 
    (match (user_spec,impl) with
     | (Base((_,tu),_,_,_,_,_), Base((_,ti),_,_,_,_,bounds)) ->
       (*let _ = Printf.eprintf "E_interal_user getting rewritten two types are %s and %s\n"
            (t_to_string tu) (t_to_string ti) in*)
       let bounds =  match nmap with | None -> bounds | Some (nm,_) -> add_map_to_bounds nm bounds in
       (match (tu.t,ti.t) with
        | (Tapp("implicit", [TA_nexp u]),Tapp("implicit",[TA_nexp i])) ->
          (*let _ = Printf.eprintf "Implicit case with %s\n" (n_to_string i) in*)
          let nexps = expand_nexp i in
          (match (match_to_program_vars nexps bounds) with
           | [] -> rewrite_nexp_to_exp None l i
           (*add u to program_vars env; for now it will work out properly by accident*)
           | map -> rewrite_nexp_to_exp (Some map) l i)
        | _ -> 
          raise (Reporting_basic.err_unreachable l 
                   ("Internal_exp_user given unexpected types " ^ (t_to_string tu) ^ ", " ^ (t_to_string ti))))
     | _ -> raise (Reporting_basic.err_unreachable l ("Internal_exp_user given none Base annot")))*)
  | E_internal_let _ -> raise (Reporting_basic.err_unreachable l "Internal let found before it should have been introduced")
  | E_internal_return _ -> raise (Reporting_basic.err_unreachable l "Internal return found before it should have been introduced")
  | E_internal_plet _ -> raise (Reporting_basic.err_unreachable l " Internal plet found before it should have been introduced")
  | _ -> rewrap exp
                           
let rewrite_let rewriters (LB_aux(letbind,(l,annot))) =
  (*let local_map = get_map_tannot annot in
  let map =
    match map,local_map with
    | None,None -> None
    | None,Some m -> Some(m, Envmap.empty)
    | Some(m,s), None -> Some(m,s)
    | Some(m,s), Some m' -> match merge_option_maps (Some m) local_map with
      | None -> Some(m,s) (*Shouldn't happen*)
      | Some new_m -> Some(new_m,s) in*)
  match letbind with
  | LB_val_explicit (typschm, pat,exp) ->
    LB_aux(LB_val_explicit (typschm,rewriters.rewrite_pat rewriters pat,
                            rewriters.rewrite_exp rewriters exp),(l,annot))
  | LB_val_implicit ( pat, exp) ->
    LB_aux(LB_val_implicit (rewriters.rewrite_pat rewriters pat,
                            rewriters.rewrite_exp rewriters exp),(l,annot))

let rewrite_lexp rewriters (LEXP_aux(lexp,(l,annot))) =
  let rewrap le = LEXP_aux(le,(l,annot)) in
  match lexp with
  | LEXP_id _ | LEXP_cast _ -> rewrap lexp
  | LEXP_tup tupls -> rewrap (LEXP_tup (List.map (rewriters.rewrite_lexp rewriters) tupls))
  | LEXP_memory (id,exps) -> rewrap (LEXP_memory(id,List.map (rewriters.rewrite_exp rewriters) exps))
  | LEXP_vector (lexp,exp) ->
    rewrap (LEXP_vector (rewriters.rewrite_lexp rewriters lexp,rewriters.rewrite_exp rewriters exp))
  | LEXP_vector_range (lexp,exp1,exp2) -> 
    rewrap (LEXP_vector_range (rewriters.rewrite_lexp rewriters lexp,
                               rewriters.rewrite_exp rewriters exp1,
                               rewriters.rewrite_exp rewriters exp2))
  | LEXP_field (lexp,id) -> rewrap (LEXP_field (rewriters.rewrite_lexp rewriters lexp,id))

let rewrite_fun rewriters (FD_aux (FD_function(recopt,tannotopt,effectopt,funcls),(l,fdannot))) = 
  let rewrite_funcl (FCL_aux (FCL_Funcl(id,pat,exp),(l,annot))) =
    let _ = reset_fresh_name_counter () in
    (*let _ = Printf.eprintf "Rewriting function %s, pattern %s\n" 
      (match id with (Id_aux (Id i,_)) -> i) (Pretty_print.pat_to_string pat) in*)
  (*let map = get_map_tannot fdannot in
  let map =
    match map with
    | None -> None
    | Some m -> Some(m, Envmap.empty) in*)
  (FCL_aux (FCL_Funcl (id,rewriters.rewrite_pat rewriters pat,
                         rewriters.rewrite_exp rewriters exp),(l,annot))) 
  in FD_aux (FD_function(recopt,tannotopt,effectopt,List.map rewrite_funcl funcls),(l,fdannot))

let rewrite_def rewriters d = match d with
  | DEF_type _ | DEF_kind _ | DEF_spec _ | DEF_default _ | DEF_reg_dec _ | DEF_comm _ | DEF_overload _ -> d
  | DEF_fundef fdef -> DEF_fundef (rewriters.rewrite_fun rewriters fdef)
  | DEF_val letbind -> DEF_val (rewriters.rewrite_let rewriters letbind)
  | DEF_scattered _ -> raise (Reporting_basic.err_unreachable Parse_ast.Unknown "DEF_scattered survived to rewritter")

let rewrite_defs_base rewriters (Defs defs) = 
  let rec rewrite ds = match ds with
    | [] -> []
    | d::ds -> (rewriters.rewrite_def rewriters d)::(rewrite ds) in
  Defs (rewrite defs)

let rewriters_base =
  {rewrite_exp = rewrite_exp;
   rewrite_pat = rewrite_pat;
   rewrite_let = rewrite_let;
   rewrite_lexp = rewrite_lexp;
   rewrite_fun = rewrite_fun;
   rewrite_def = rewrite_def;
   rewrite_defs = rewrite_defs_base}
    
let rewrite_defs (Defs defs) = rewrite_defs_base rewriters_base (Defs defs)

module Envmap = Finite_map.Fmap_map(String)

(* TODO: This seems to only consider a single assignment (or possibly two, in
   separate branches of an if-expression). Hence, it seems the result is always
   at most one variable. Is this intended?
   It is only used below when pulling out local variables inside if-expressions
   into the outer scope, which seems dubious. I comment it out for now. *)
(*let rec introduced_variables (E_aux (exp,(l,annot))) =
  match exp with
  | E_cast (typ, exp) -> introduced_variables exp
  | E_if (c,t,e) -> Envmap.intersect (introduced_variables t) (introduced_variables e)
  | E_assign (lexp,exp) -> introduced_vars_le lexp exp
  | _ -> Envmap.empty

and introduced_vars_le (LEXP_aux(lexp,annot)) exp =
  match lexp with
  | LEXP_id (Id_aux (Id id,_))  | LEXP_cast(_,(Id_aux (Id id,_))) ->
    (match annot with
     | Base((_,t),Emp_intro,_,_,_,_) ->
       Envmap.insert Envmap.empty (id,(t,exp))
     | _ -> Envmap.empty)
  | _ -> Envmap.empty*)

type ('a,'pat,'pat_aux,'fpat,'fpat_aux) pat_alg =
  { p_lit            : lit -> 'pat_aux
  ; p_wild           : 'pat_aux
  ; p_as             : 'pat * id -> 'pat_aux
  ; p_typ            : Ast.typ * 'pat -> 'pat_aux
  ; p_id             : id -> 'pat_aux
  ; p_app            : id * 'pat list -> 'pat_aux
  ; p_record         : 'fpat list * bool -> 'pat_aux
  ; p_vector         : 'pat list -> 'pat_aux
  ; p_vector_indexed : (int * 'pat) list -> 'pat_aux
  ; p_vector_concat  : 'pat list -> 'pat_aux
  ; p_tup            : 'pat list -> 'pat_aux
  ; p_list           : 'pat list -> 'pat_aux
  ; p_aux            : 'pat_aux * 'a annot -> 'pat
  ; fP_aux           : 'fpat_aux * 'a annot -> 'fpat
  ; fP_Fpat          : id * 'pat -> 'fpat_aux
  }

let rec fold_pat_aux (alg : ('a,'pat,'pat_aux,'fpat,'fpat_aux) pat_alg) : 'a pat_aux -> 'pat_aux =
  function
  | P_lit lit           -> alg.p_lit lit
  | P_wild              -> alg.p_wild
  | P_id id             -> alg.p_id id
  | P_as (p,id)         -> alg.p_as (fold_pat alg p,id)
  | P_typ (typ,p)       -> alg.p_typ (typ,fold_pat alg p)
  | P_app (id,ps)       -> alg.p_app (id,List.map (fold_pat alg) ps)
  | P_record (ps,b)     -> alg.p_record (List.map (fold_fpat alg) ps, b)
  | P_vector ps         -> alg.p_vector (List.map (fold_pat alg) ps)
  | P_vector_indexed ps -> alg.p_vector_indexed (List.map (fun (i,p) -> (i, fold_pat alg p)) ps)
  | P_vector_concat ps  -> alg.p_vector_concat (List.map (fold_pat alg) ps)
  | P_tup ps            -> alg.p_tup (List.map (fold_pat alg) ps)
  | P_list ps           -> alg.p_list (List.map (fold_pat alg) ps)


and fold_pat (alg : ('a,'pat,'pat_aux,'fpat,'fpat_aux) pat_alg) : 'a pat -> 'pat =
  function
  | P_aux (pat,annot)   -> alg.p_aux (fold_pat_aux alg pat,annot)
and fold_fpat_aux (alg : ('a,'pat,'pat_aux,'fpat,'fpat_aux) pat_alg) : 'a fpat_aux -> 'fpat_aux =
  function
  | FP_Fpat (id,pat)    -> alg.fP_Fpat (id,fold_pat alg pat)
and fold_fpat (alg : ('a,'pat,'pat_aux,'fpat,'fpat_aux) pat_alg) : 'a fpat -> 'fpat =
  function
  | FP_aux (fpat,annot) -> alg.fP_aux (fold_fpat_aux alg fpat,annot)
                                      
(* identity fold from term alg to term alg *)
let id_pat_alg : ('a,'a pat, 'a pat_aux, 'a fpat, 'a fpat_aux) pat_alg = 
  { p_lit            = (fun lit -> P_lit lit)
  ; p_wild           = P_wild
  ; p_as             = (fun (pat,id) -> P_as (pat,id))
  ; p_typ            = (fun (typ,pat) -> P_typ (typ,pat))
  ; p_id             = (fun id -> P_id id)
  ; p_app            = (fun (id,ps) -> P_app (id,ps))
  ; p_record         = (fun (ps,b) -> P_record (ps,b))
  ; p_vector         = (fun ps -> P_vector ps)
  ; p_vector_indexed = (fun ps -> P_vector_indexed ps)
  ; p_vector_concat  = (fun ps -> P_vector_concat ps)
  ; p_tup            = (fun ps -> P_tup ps)
  ; p_list           = (fun ps -> P_list ps)
  ; p_aux            = (fun (pat,annot) -> P_aux (pat,annot))
  ; fP_aux           = (fun (fpat,annot) -> FP_aux (fpat,annot))
  ; fP_Fpat          = (fun (id,pat) -> FP_Fpat (id,pat))
  }
  
type ('a,'exp,'exp_aux,'lexp,'lexp_aux,'fexp,'fexp_aux,'fexps,'fexps_aux,
      'opt_default_aux,'opt_default,'pexp,'pexp_aux,'letbind_aux,'letbind,
      'pat,'pat_aux,'fpat,'fpat_aux) exp_alg = 
  { e_block                  : 'exp list -> 'exp_aux
  ; e_nondet                 : 'exp list -> 'exp_aux
  ; e_id                     : id -> 'exp_aux
  ; e_lit                    : lit -> 'exp_aux
  ; e_cast                   : Ast.typ * 'exp -> 'exp_aux
  ; e_app                    : id * 'exp list -> 'exp_aux
  ; e_app_infix              : 'exp * id * 'exp -> 'exp_aux
  ; e_tuple                  : 'exp list -> 'exp_aux
  ; e_if                     : 'exp * 'exp * 'exp -> 'exp_aux
  ; e_for                    : id * 'exp * 'exp * 'exp * Ast.order * 'exp -> 'exp_aux
  ; e_vector                 : 'exp list -> 'exp_aux
  ; e_vector_indexed         : (int * 'exp) list * 'opt_default -> 'exp_aux
  ; e_vector_access          : 'exp * 'exp -> 'exp_aux
  ; e_vector_subrange        : 'exp * 'exp * 'exp -> 'exp_aux
  ; e_vector_update          : 'exp * 'exp * 'exp -> 'exp_aux
  ; e_vector_update_subrange : 'exp * 'exp * 'exp * 'exp -> 'exp_aux
  ; e_vector_append          : 'exp * 'exp -> 'exp_aux
  ; e_list                   : 'exp list -> 'exp_aux
  ; e_cons                   : 'exp * 'exp -> 'exp_aux
  ; e_record                 : 'fexps -> 'exp_aux
  ; e_record_update          : 'exp * 'fexps -> 'exp_aux
  ; e_field                  : 'exp * id -> 'exp_aux
  ; e_case                   : 'exp * 'pexp list -> 'exp_aux
  ; e_let                    : 'letbind * 'exp -> 'exp_aux
  ; e_assign                 : 'lexp * 'exp -> 'exp_aux
  ; e_sizeof                 : nexp -> 'exp_aux
  ; e_exit                   : 'exp -> 'exp_aux
  ; e_return                 : 'exp -> 'exp_aux
  ; e_assert                 : 'exp * 'exp -> 'exp_aux
  ; e_internal_cast          : 'a annot * 'exp -> 'exp_aux
  ; e_internal_exp           : 'a annot -> 'exp_aux
  ; e_internal_exp_user      : 'a annot * 'a annot -> 'exp_aux
  ; e_internal_let           : 'lexp * 'exp * 'exp -> 'exp_aux
  ; e_internal_plet          : 'pat * 'exp * 'exp -> 'exp_aux
  ; e_internal_return        : 'exp -> 'exp_aux
  ; e_aux                    : 'exp_aux * 'a annot -> 'exp
  ; lEXP_id                  : id -> 'lexp_aux
  ; lEXP_memory              : id * 'exp list -> 'lexp_aux
  ; lEXP_cast                : Ast.typ * id -> 'lexp_aux
  ; lEXP_tup                 : 'lexp list -> 'lexp_aux
  ; lEXP_vector              : 'lexp * 'exp -> 'lexp_aux
  ; lEXP_vector_range        : 'lexp * 'exp * 'exp -> 'lexp_aux
  ; lEXP_field               : 'lexp * id -> 'lexp_aux
  ; lEXP_aux                 : 'lexp_aux * 'a annot -> 'lexp
  ; fE_Fexp                  : id * 'exp -> 'fexp_aux
  ; fE_aux                   : 'fexp_aux * 'a annot -> 'fexp
  ; fES_Fexps                : 'fexp list * bool -> 'fexps_aux
  ; fES_aux                  : 'fexps_aux * 'a annot -> 'fexps
  ; def_val_empty            : 'opt_default_aux
  ; def_val_dec              : 'exp -> 'opt_default_aux
  ; def_val_aux              : 'opt_default_aux * 'a annot -> 'opt_default
  ; pat_exp                  : 'pat * 'exp -> 'pexp_aux
  ; pat_aux                  : 'pexp_aux * 'a annot -> 'pexp
  ; lB_val_explicit          : typschm * 'pat * 'exp -> 'letbind_aux
  ; lB_val_implicit          : 'pat * 'exp -> 'letbind_aux
  ; lB_aux                   : 'letbind_aux * 'a annot -> 'letbind
  ; pat_alg                  : ('a,'pat,'pat_aux,'fpat,'fpat_aux) pat_alg
  }
    
let rec fold_exp_aux alg = function
  | E_block es -> alg.e_block (List.map (fold_exp alg) es)
  | E_nondet es -> alg.e_nondet (List.map (fold_exp alg) es)
  | E_id id -> alg.e_id id
  | E_lit lit -> alg.e_lit lit
  | E_cast (typ,e) -> alg.e_cast (typ, fold_exp alg e)
  | E_app (id,es) -> alg.e_app (id, List.map (fold_exp alg) es)
  | E_app_infix (e1,id,e2) -> alg.e_app_infix (fold_exp alg e1, id, fold_exp alg e2)
  | E_tuple es -> alg.e_tuple (List.map (fold_exp alg) es)
  | E_if (e1,e2,e3) -> alg.e_if (fold_exp alg e1, fold_exp alg e2, fold_exp alg e3)
  | E_for (id,e1,e2,e3,order,e4) ->
     alg.e_for (id,fold_exp alg e1, fold_exp alg e2, fold_exp alg e3, order, fold_exp alg e4)
  | E_vector es -> alg.e_vector (List.map (fold_exp alg) es)
  | E_vector_indexed (es,opt) ->
     alg.e_vector_indexed (List.map (fun (id,e) -> (id,fold_exp alg e)) es, fold_opt_default alg opt)
  | E_vector_access (e1,e2) -> alg.e_vector_access (fold_exp alg e1, fold_exp alg e2)
  | E_vector_subrange (e1,e2,e3) ->
     alg.e_vector_subrange (fold_exp alg e1, fold_exp alg e2, fold_exp alg e3)
  | E_vector_update (e1,e2,e3) ->
     alg.e_vector_update (fold_exp alg e1, fold_exp alg e2, fold_exp alg e3)
  | E_vector_update_subrange (e1,e2,e3,e4) ->
     alg.e_vector_update_subrange (fold_exp alg e1,fold_exp alg e2, fold_exp alg e3, fold_exp alg e4)
  | E_vector_append (e1,e2) -> alg.e_vector_append (fold_exp alg e1, fold_exp alg e2)
  | E_list es -> alg.e_list (List.map (fold_exp alg) es)
  | E_cons (e1,e2) -> alg.e_cons (fold_exp alg e1, fold_exp alg e2)
  | E_record fexps -> alg.e_record (fold_fexps alg fexps)
  | E_record_update (e,fexps) -> alg.e_record_update (fold_exp alg e, fold_fexps alg fexps)
  | E_field (e,id) -> alg.e_field (fold_exp alg e, id)
  | E_case (e,pexps) -> alg.e_case (fold_exp alg e, List.map (fold_pexp alg) pexps)
  | E_let (letbind,e) -> alg.e_let (fold_letbind alg letbind, fold_exp alg e)
  | E_assign (lexp,e) -> alg.e_assign (fold_lexp alg lexp, fold_exp alg e)
  | E_sizeof nexp -> alg.e_sizeof nexp
  | E_exit e -> alg.e_exit (fold_exp alg e)
  | E_return e -> alg.e_return (fold_exp alg e)
  | E_assert(e1,e2) -> alg.e_assert (fold_exp alg e1, fold_exp alg e2)
  | E_internal_cast (annot,e) -> alg.e_internal_cast (annot, fold_exp alg e)
  | E_internal_exp annot -> alg.e_internal_exp annot
  | E_internal_exp_user (annot1,annot2) -> alg.e_internal_exp_user (annot1,annot2)
  | E_internal_let (lexp,e1,e2) ->
     alg.e_internal_let (fold_lexp alg lexp, fold_exp alg e1, fold_exp alg e2)
  | E_internal_plet (pat,e1,e2) ->
     alg.e_internal_plet (fold_pat alg.pat_alg pat, fold_exp alg e1, fold_exp alg e2)
  | E_internal_return e -> alg.e_internal_return (fold_exp alg e)
and fold_exp alg (E_aux (exp_aux,annot)) = alg.e_aux (fold_exp_aux alg exp_aux, annot)
and fold_lexp_aux alg = function
  | LEXP_id id -> alg.lEXP_id id
  | LEXP_memory (id,es) -> alg.lEXP_memory (id, List.map (fold_exp alg) es)
  | LEXP_cast (typ,id) -> alg.lEXP_cast (typ,id)
  | LEXP_vector (lexp,e) -> alg.lEXP_vector (fold_lexp alg lexp, fold_exp alg e)
  | LEXP_vector_range (lexp,e1,e2) ->
     alg.lEXP_vector_range (fold_lexp alg lexp, fold_exp alg e1, fold_exp alg e2)
 | LEXP_field (lexp,id) -> alg.lEXP_field (fold_lexp alg lexp, id)
and fold_lexp alg (LEXP_aux (lexp_aux,annot)) =
  alg.lEXP_aux (fold_lexp_aux alg lexp_aux, annot)
and fold_fexp_aux alg (FE_Fexp (id,e)) = alg.fE_Fexp (id, fold_exp alg e)
and fold_fexp alg (FE_aux (fexp_aux,annot)) = alg.fE_aux (fold_fexp_aux alg fexp_aux,annot)
and fold_fexps_aux alg (FES_Fexps (fexps,b)) = alg.fES_Fexps (List.map (fold_fexp alg) fexps, b)
and fold_fexps alg (FES_aux (fexps_aux,annot)) = alg.fES_aux (fold_fexps_aux alg fexps_aux, annot)
and fold_opt_default_aux alg = function
  | Def_val_empty -> alg.def_val_empty
  | Def_val_dec e -> alg.def_val_dec (fold_exp alg e)
and fold_opt_default alg (Def_val_aux (opt_default_aux,annot)) =
  alg.def_val_aux (fold_opt_default_aux alg opt_default_aux, annot)
and fold_pexp_aux alg (Pat_exp (pat,e)) = alg.pat_exp (fold_pat alg.pat_alg pat, fold_exp alg e)
and fold_pexp alg (Pat_aux (pexp_aux,annot)) = alg.pat_aux (fold_pexp_aux alg pexp_aux, annot)
and fold_letbind_aux alg = function
  | LB_val_explicit (t,pat,e) -> alg.lB_val_explicit (t,fold_pat alg.pat_alg pat, fold_exp alg e)
  | LB_val_implicit (pat,e) -> alg.lB_val_implicit (fold_pat alg.pat_alg pat, fold_exp alg e)
and fold_letbind alg (LB_aux (letbind_aux,annot)) = alg.lB_aux (fold_letbind_aux alg letbind_aux, annot)

let id_exp_alg =
  { e_block = (fun es -> E_block es)
  ; e_nondet = (fun es -> E_nondet es)
  ; e_id = (fun id -> E_id id)
  ; e_lit = (fun lit -> (E_lit lit))
  ; e_cast = (fun (typ,e) -> E_cast (typ,e))
  ; e_app = (fun (id,es) -> E_app (id,es))
  ; e_app_infix = (fun (e1,id,e2) -> E_app_infix (e1,id,e2))
  ; e_tuple = (fun es -> E_tuple es)
  ; e_if = (fun (e1,e2,e3) -> E_if (e1,e2,e3))
  ; e_for = (fun (id,e1,e2,e3,order,e4) -> E_for (id,e1,e2,e3,order,e4))
  ; e_vector = (fun es -> E_vector es)
  ; e_vector_indexed = (fun (es,opt2) -> E_vector_indexed (es,opt2))
  ; e_vector_access = (fun (e1,e2) -> E_vector_access (e1,e2))
  ; e_vector_subrange =  (fun (e1,e2,e3) -> E_vector_subrange (e1,e2,e3))
  ; e_vector_update = (fun (e1,e2,e3) -> E_vector_update (e1,e2,e3))
  ; e_vector_update_subrange =  (fun (e1,e2,e3,e4) -> E_vector_update_subrange (e1,e2,e3,e4))
  ; e_vector_append = (fun (e1,e2) -> E_vector_append (e1,e2))
  ; e_list = (fun es -> E_list es)
  ; e_cons = (fun (e1,e2) -> E_cons (e1,e2))
  ; e_record = (fun fexps -> E_record fexps)
  ; e_record_update = (fun (e1,fexp) -> E_record_update (e1,fexp))
  ; e_field = (fun (e1,id) -> (E_field (e1,id)))
  ; e_case = (fun (e1,pexps) -> E_case (e1,pexps))
  ; e_let = (fun (lb,e2) -> E_let (lb,e2))
  ; e_assign = (fun (lexp,e2) -> E_assign (lexp,e2))
  ; e_sizeof = (fun nexp -> E_sizeof nexp)
  ; e_exit = (fun e1 -> E_exit (e1))
  ; e_return = (fun e1 -> E_return e1)
  ; e_assert = (fun (e1,e2) -> E_assert(e1,e2)) 
  ; e_internal_cast = (fun (a,e1) -> E_internal_cast (a,e1))
  ; e_internal_exp = (fun a -> E_internal_exp a)
  ; e_internal_exp_user = (fun (a1,a2) -> E_internal_exp_user (a1,a2))
  ; e_internal_let = (fun (lexp, e2, e3) -> E_internal_let (lexp,e2,e3))
  ; e_internal_plet = (fun (pat, e1, e2) -> E_internal_plet (pat,e1,e2))
  ; e_internal_return = (fun e -> E_internal_return e)
  ; e_aux = (fun (e,annot) -> E_aux (e,annot))
  ; lEXP_id = (fun id -> LEXP_id id)
  ; lEXP_memory = (fun (id,es) -> LEXP_memory (id,es))
  ; lEXP_cast = (fun (typ,id) -> LEXP_cast (typ,id))
  ; lEXP_tup = (fun tups -> LEXP_tup tups)
  ; lEXP_vector = (fun (lexp,e2) -> LEXP_vector (lexp,e2))
  ; lEXP_vector_range = (fun (lexp,e2,e3) -> LEXP_vector_range (lexp,e2,e3))
  ; lEXP_field = (fun (lexp,id) -> LEXP_field (lexp,id))
  ; lEXP_aux = (fun (lexp,annot) -> LEXP_aux (lexp,annot))
  ; fE_Fexp = (fun (id,e) -> FE_Fexp (id,e))
  ; fE_aux = (fun (fexp,annot) -> FE_aux (fexp,annot))
  ; fES_Fexps = (fun (fexps,b) -> FES_Fexps (fexps,b))
  ; fES_aux = (fun (fexp,annot) -> FES_aux (fexp,annot))
  ; def_val_empty = Def_val_empty
  ; def_val_dec = (fun e -> Def_val_dec e)
  ; def_val_aux = (fun (defval,aux) -> Def_val_aux (defval,aux))
  ; pat_exp = (fun (pat,e) -> (Pat_exp (pat,e)))
  ; pat_aux = (fun (pexp,a) -> (Pat_aux (pexp,a)))
  ; lB_val_explicit = (fun (typ,pat,e) -> LB_val_explicit (typ,pat,e))
  ; lB_val_implicit = (fun (pat,e) -> LB_val_implicit (pat,e))
  ; lB_aux = (fun (lb,annot) -> LB_aux (lb,annot))
  ; pat_alg = id_pat_alg
  }

(* Folding algorithms for not only rewriting patterns/expressions, but also
   computing some additional value. Usage: Pass default value (bot) and a
   binary join operator as arguments, and specify the non-default cases of
   rewriting/computation by overwriting fields of the record.
   See rewrite_sizeof for examples. *)
let compute_pat_alg bot join =
  let join_list vs = List.fold_left join bot vs in
  let split_join f ps = let (vs,ps) = List.split ps in (join_list vs, f ps) in
  { p_lit            = (fun lit -> (bot, P_lit lit))
  ; p_wild           = (bot, P_wild)
  ; p_as             = (fun ((v,pat),id) -> (v, P_as (pat,id)))
  ; p_typ            = (fun (typ,(v,pat)) -> (v, P_typ (typ,pat)))
  ; p_id             = (fun id -> (bot, P_id id))
  ; p_app            = (fun (id,ps) -> split_join (fun ps -> P_app (id,ps)) ps)
  ; p_record         = (fun (ps,b) -> split_join (fun ps -> P_record (ps,b)) ps)
  ; p_vector         = split_join (fun ps -> P_vector ps)
  ; p_vector_indexed = (fun ps ->
                          let (is,ps) = List.split ps in
                          let (vs,ps) = List.split ps in
                          (join_list vs, P_vector_indexed (List.combine is ps)))
  ; p_vector_concat  = split_join (fun ps -> P_vector_concat ps)
  ; p_tup            = split_join (fun ps -> P_tup ps)
  ; p_list           = split_join (fun ps -> P_list ps)
  ; p_aux            = (fun ((v,pat),annot) -> (v, P_aux (pat,annot)))
  ; fP_aux           = (fun ((v,fpat),annot) -> (v, FP_aux (fpat,annot)))
  ; fP_Fpat          = (fun (id,(v,pat)) -> (v, FP_Fpat (id,pat)))
  }

let compute_exp_alg bot join =
  let join_list vs = List.fold_left join bot vs in
  let split_join f es = let (vs,es) = List.split es in (join_list vs, f es) in
  { e_block = split_join (fun es -> E_block es)
  ; e_nondet = split_join (fun es -> E_nondet es)
  ; e_id = (fun id -> (bot, E_id id))
  ; e_lit = (fun lit -> (bot, E_lit lit))
  ; e_cast = (fun (typ,(v,e)) -> (v, E_cast (typ,e)))
  ; e_app = (fun (id,es) -> split_join (fun es -> E_app (id,es)) es)
  ; e_app_infix = (fun ((v1,e1),id,(v2,e2)) -> (join v1 v2, E_app_infix (e1,id,e2)))
  ; e_tuple = split_join (fun es -> E_tuple es)
  ; e_if = (fun ((v1,e1),(v2,e2),(v3,e3)) -> (join_list [v1;v2;v3], E_if (e1,e2,e3)))
  ; e_for = (fun (id,(v1,e1),(v2,e2),(v3,e3),order,(v4,e4)) ->
      (join_list [v1;v2;v3;v4], E_for (id,e1,e2,e3,order,e4)))
  ; e_vector = split_join (fun es -> E_vector es)
  ; e_vector_indexed = (fun (es,(v2,opt2)) ->
      let (is,es) = List.split es in
      let (vs,es) = List.split es in
      (join_list (vs @ [v2]), E_vector_indexed (List.combine is es,opt2)))
  ; e_vector_access = (fun ((v1,e1),(v2,e2)) -> (join v1 v2, E_vector_access (e1,e2)))
  ; e_vector_subrange =  (fun ((v1,e1),(v2,e2),(v3,e3)) -> (join_list [v1;v2;v3], E_vector_subrange (e1,e2,e3)))
  ; e_vector_update = (fun ((v1,e1),(v2,e2),(v3,e3)) -> (join_list [v1;v2;v3], E_vector_update (e1,e2,e3)))
  ; e_vector_update_subrange =  (fun ((v1,e1),(v2,e2),(v3,e3),(v4,e4)) -> (join_list [v1;v2;v3;v4], E_vector_update_subrange (e1,e2,e3,e4)))
  ; e_vector_append = (fun ((v1,e1),(v2,e2)) -> (join v1 v2, E_vector_append (e1,e2)))
  ; e_list = split_join (fun es -> E_list es)
  ; e_cons = (fun ((v1,e1),(v2,e2)) -> (join v1 v2, E_cons (e1,e2)))
  ; e_record = (fun (vs,fexps) -> (vs, E_record fexps))
  ; e_record_update = (fun ((v1,e1),(vf,fexp)) -> (join v1 vf, E_record_update (e1,fexp)))
  ; e_field = (fun ((v1,e1),id) -> (v1, E_field (e1,id)))
  ; e_case = (fun ((v1,e1),pexps) ->
      let (vps,pexps) = List.split pexps in
      (join_list (v1::vps), E_case (e1,pexps)))
  ; e_let = (fun ((vl,lb),(v2,e2)) -> (join vl v2, E_let (lb,e2)))
  ; e_assign = (fun ((vl,lexp),(v2,e2)) -> (join vl v2, E_assign (lexp,e2)))
  ; e_sizeof = (fun nexp -> (bot, E_sizeof nexp))
  ; e_exit = (fun (v1,e1) -> (v1, E_exit (e1)))
  ; e_return = (fun (v1,e1) -> (v1, E_return e1))
  ; e_assert = (fun ((v1,e1),(v2,e2)) -> (join v1 v2, E_assert(e1,e2)) )
  ; e_internal_cast = (fun (a,(v1,e1)) -> (v1, E_internal_cast (a,e1)))
  ; e_internal_exp = (fun a -> (bot, E_internal_exp a))
  ; e_internal_exp_user = (fun (a1,a2) -> (bot, E_internal_exp_user (a1,a2)))
  ; e_internal_let = (fun ((vl, lexp), (v2,e2), (v3,e3)) ->
      (join_list [vl;v2;v3], E_internal_let (lexp,e2,e3)))
  ; e_internal_plet = (fun ((vp,pat), (v1,e1), (v2,e2)) ->
      (join_list [vp;v1;v2], E_internal_plet (pat,e1,e2)))
  ; e_internal_return = (fun (v,e) -> (v, E_internal_return e))
  ; e_aux = (fun ((v,e),annot) -> (v, E_aux (e,annot)))
  ; lEXP_id = (fun id -> (bot, LEXP_id id))
  ; lEXP_memory = (fun (id,es) -> split_join (fun es -> LEXP_memory (id,es)) es)
  ; lEXP_cast = (fun (typ,id) -> (bot, LEXP_cast (typ,id)))
  ; lEXP_tup = split_join (fun tups -> LEXP_tup tups)
  ; lEXP_vector = (fun ((vl,lexp),(v2,e2)) -> (join vl v2, LEXP_vector (lexp,e2)))
  ; lEXP_vector_range = (fun ((vl,lexp),(v2,e2),(v3,e3)) ->
      (join_list [vl;v2;v3], LEXP_vector_range (lexp,e2,e3)))
  ; lEXP_field = (fun ((vl,lexp),id) -> (vl, LEXP_field (lexp,id)))
  ; lEXP_aux = (fun ((vl,lexp),annot) -> (vl, LEXP_aux (lexp,annot)))
  ; fE_Fexp = (fun (id,(v,e)) -> (v, FE_Fexp (id,e)))
  ; fE_aux = (fun ((vf,fexp),annot) -> (vf, FE_aux (fexp,annot)))
  ; fES_Fexps = (fun (fexps,b) ->
      let (vs,fexps) = List.split fexps in
      (join_list vs, FES_Fexps (fexps,b)))
  ; fES_aux = (fun ((vf,fexp),annot) -> (vf, FES_aux (fexp,annot)))
  ; def_val_empty = (bot, Def_val_empty)
  ; def_val_dec = (fun (v,e) -> (v, Def_val_dec e))
  ; def_val_aux = (fun ((v,defval),aux) -> (v, Def_val_aux (defval,aux)))
  ; pat_exp = (fun ((vp,pat),(v,e)) -> (join vp v, Pat_exp (pat,e)))
  ; pat_aux = (fun ((v,pexp),a) -> (v, Pat_aux (pexp,a)))
  ; lB_val_explicit = (fun (typ,(vp,pat),(v,e)) -> (join vp v, LB_val_explicit (typ,pat,e)))
  ; lB_val_implicit = (fun ((vp,pat),(v,e)) -> (join vp v, LB_val_implicit (pat,e)))
  ; lB_aux = (fun ((vl,lb),annot) -> (vl,LB_aux (lb,annot)))
  ; pat_alg = compute_pat_alg bot join
  }

let rewrite_sizeof defs =
  let sizeof_frees exp =
    fst (fold_exp
      { (compute_exp_alg KidSet.empty KidSet.union) with
        e_sizeof = (fun nexp -> (nexp_frees nexp, E_sizeof nexp)) }
      exp) in

  let nexps_from_params pat =
    fst (fold_pat
      { (compute_pat_alg [] (@)) with
        p_aux = (fun ((v,pat),((l,_) as annot)) ->
          let v' = match pat with
          | P_id id | P_as (_, id) ->
            let (Typ_aux (typ,_) as typ_aux) = typ_of_annot annot in
            (match typ with
              | Typ_app (atom, [Typ_arg_aux (Typ_arg_nexp nexp, _)])
                when string_of_id atom = "atom" ->
                [nexp, E_id id]
              | Typ_app (vector, _) when string_of_id vector = "vector" ->
                let (_,len,_,_) = vector_typ_args_of typ_aux in
                let exp = E_app
                  (Id_aux (Id "length", Parse_ast.Generated l),
                  [E_aux (E_id id, annot)]) in
                [len, exp]
              | _ -> [])
          | _ -> [] in
          (v @ v', P_aux (pat,annot)))} pat) in

  let rec e_sizeof nmap (Nexp_aux (nexp, l) as nexp_aux) =
    try snd (List.find (fun (nexp,_) -> nexp_identical nexp nexp_aux) nmap)
    with
    | Not_found ->
      let binop nexp1 op nexp2 = E_app_infix (
        E_aux (e_sizeof nmap nexp1, simple_annot l (atom_typ nexp1)),
        Id_aux (Id op, Unknown),
        E_aux (e_sizeof nmap nexp2, simple_annot l (atom_typ nexp2))
        ) in
      (match nexp with
      | Nexp_constant i -> E_lit (L_aux (L_num i, l))
      | Nexp_times (nexp1, nexp2) -> binop nexp1 "*" nexp2
      | Nexp_sum (nexp1, nexp2) -> binop nexp1 "+" nexp2
      | Nexp_minus (nexp1, nexp2) -> binop nexp1 "-" nexp2
      | _ -> E_sizeof nexp_aux) in

  let rewrite_sizeof_exp nmap rewriters exp =
    let exp = rewriters_base.rewrite_exp rewriters exp in
    fold_exp { id_exp_alg with e_sizeof = e_sizeof nmap } exp in

  let rewrite_sizeof_fun rewriters
    (FD_aux (FD_function (rec_opt,tannot,eff,funcls),annot)) =
    let rewrite_funcl_body (FCL_aux (FCL_Funcl (id,pat,exp), annot)) =
      let body_env = env_of exp in
      let body_typ = typ_of exp in
      let nmap = nexps_from_params pat in
      let exp =
        try check_exp body_env
          (strip_exp (fold_exp { id_exp_alg with e_sizeof = e_sizeof nmap } exp))
          body_typ
        with
          | Type_error _ -> exp in
      FCL_aux (FCL_Funcl (id,pat,exp), annot) in
    let funcls = List.map rewrite_funcl_body funcls in
    FD_aux (FD_function (rec_opt,tannot,eff,funcls),annot) in

  rewrite_defs_base
    { rewriters_base with
      rewrite_exp = rewrite_sizeof_exp [];
      rewrite_fun = rewrite_sizeof_fun }
    defs

let remove_vector_concat_pat pat =

  (* ivc: bool that indicates whether the exp is in a vector_concat pattern *)
  let remove_typed_patterns =
    fold_pat { id_pat_alg with
               p_aux = (function
                        | (P_typ (_,P_aux (p,_)),annot)
                        | (p,annot) -> 
                           P_aux (p,annot)
                       )
             } in
  
  let pat = remove_typed_patterns pat in

  let fresh_id_v = fresh_id "v__" in

  (* expects that P_typ elements have been removed from AST,
     that the length of all vectors involved is known,
     that we don't have indexed vectors *)

  (* introduce names for all patterns of form P_vector_concat *)
  let name_vector_concat_roots =
    { p_lit = (fun lit -> P_lit lit)
    ; p_typ = (fun (typ,p) -> P_typ (typ,p false)) (* cannot happen *)
    ; p_wild = P_wild
    ; p_as = (fun (pat,id) -> P_as (pat true,id))
    ; p_id  = (fun id -> P_id id)
    ; p_app = (fun (id,ps) -> P_app (id, List.map (fun p -> p false) ps))
    ; p_record = (fun (fpats,b) -> P_record (fpats, b))
    ; p_vector = (fun ps -> P_vector (List.map (fun p -> p false) ps))
    ; p_vector_indexed = (fun ps -> P_vector_indexed (List.map (fun (i,p) -> (i,p false)) ps))
    ; p_vector_concat  = (fun ps -> P_vector_concat (List.map (fun p -> p false) ps))
    ; p_tup            = (fun ps -> P_tup (List.map (fun p -> p false) ps))
    ; p_list           = (fun ps -> P_list (List.map (fun p -> p false) ps))
    ; p_aux =
        (fun (pat,((l,_) as annot)) contained_in_p_as ->
          match pat with
          | P_vector_concat pats ->
             (if contained_in_p_as
              then P_aux (pat,annot)
              else P_aux (P_as (P_aux (pat,annot),fresh_id_v l),annot))
          | _ -> P_aux (pat,annot)
        )
    ; fP_aux = (fun (fpat,annot) -> FP_aux (fpat,annot))
    ; fP_Fpat = (fun (id,p) -> FP_Fpat (id,p false))
    } in

  let pat = (fold_pat name_vector_concat_roots pat) false in

  (* introduce names for all unnamed child nodes of P_vector_concat *)
  let name_vector_concat_elements =
    let p_vector_concat pats =
      let aux ((P_aux (p,((l,_) as a))) as pat) = match p with
        | P_vector _ -> P_aux (P_as (pat,fresh_id_v l),a)
        | P_id id -> P_aux (P_id id,a)
        | P_as (p,id) -> P_aux (P_as (p,id),a)
        | P_wild -> P_aux (P_wild,a)
        | _ ->
           raise
             (Reporting_basic.err_unreachable
                l "name_vector_concat_elements: Non-vector in vector-concat pattern") in
      P_vector_concat (List.map aux pats) in
    {id_pat_alg with p_vector_concat = p_vector_concat} in

  let pat = fold_pat name_vector_concat_elements pat in



  let rec tag_last = function
    | x :: xs -> let is_last = xs = [] in (x,is_last) :: tag_last xs
    | _ -> [] in

  (* remove names from vectors in vector_concat patterns and collect them as declarations for the
     function body or expression *)
  let unname_vector_concat_elements = (* :
        ('a,
         'a pat *      ((tannot exp -> tannot exp) list),
         'a pat_aux *  ((tannot exp -> tannot exp) list),
         'a fpat *     ((tannot exp -> tannot exp) list),
         'a fpat_aux * ((tannot exp -> tannot exp) list))
          pat_alg = *)

    (* build a let-expression of the form "let child = root[i..j] in body" *)
    let letbind_vec (rootid,rannot) (child,cannot) (i,j) =
      let (l,_) = cannot in
      let (Id_aux (Id rootname,_)) = rootid in
      let (Id_aux (Id childname,_)) = child in
      
      let root = E_aux (E_id rootid, rannot) in
      let index_i = simple_num l i in
      let index_j = simple_num l j in
      
      let subv = fix_eff_exp (E_aux (E_vector_subrange (root, index_i, index_j), cannot)) in

      let letbind = fix_eff_lb (LB_aux (LB_val_implicit (P_aux (P_id child,cannot),subv),cannot)) in
      (letbind,
       (fun body -> fix_eff_exp (E_aux (E_let (letbind,body), simple_annot l (typ_of body)))),
       (rootname,childname)) in

    let p_aux = function
      | ((P_as (P_aux (P_vector_concat pats,rannot'),rootid),decls),rannot) ->
         let rtyp = Env.base_typ_of (env_of_annot rannot') (typ_of_annot rannot') in
         let (start,last_idx) = (match vector_typ_args_of rtyp with
          | (Nexp_aux (Nexp_constant start,_), Nexp_aux (Nexp_constant length,_), ord, _) ->
            (start, if is_order_inc ord then start + length - 1 else start - length + 1)
          | _ ->
            raise (Reporting_basic.err_unreachable (fst rannot')
              ("unname_vector_concat_elements: vector of unspecified length in vector-concat pattern"))) in
         let aux (pos,pat_acc,decl_acc) (P_aux (p,cannot),is_last) =
           let ctyp = Env.base_typ_of (env_of_annot cannot) (typ_of_annot cannot) in
           let (_,length,ord,_) = vector_typ_args_of ctyp in
            (*)| (_,length,ord,_) ->*)
               let (pos',index_j) = match length with
                 | Nexp_aux (Nexp_constant i,_) ->
                   if is_order_inc ord then (pos+i, pos+i-1)
                   else (pos-i, pos-i+1)
                 | Nexp_aux (_,l) ->
                     if is_last then (pos,last_idx)
                     else
                     raise
                       (Reporting_basic.err_unreachable
                          l ("unname_vector_concat_elements: vector of unspecified length in vector-concat pattern")) in
               (match p with 
                (* if we see a named vector pattern, remove the name and remember to 
                  declare it later *)
                | P_as (P_aux (p,cannot),cname) ->
                   let (lb,decl,info) = letbind_vec (rootid,rannot) (cname,cannot) (pos,index_j) in
                   (pos', pat_acc @ [P_aux (p,cannot)], decl_acc @ [((lb,decl),info)])
                (* if we see a P_id variable, remember to declare it later *)
                | P_id cname ->
                   let (lb,decl,info) = letbind_vec (rootid,rannot) (cname,cannot) (pos,index_j) in
                   (pos', pat_acc @ [P_aux (P_id cname,cannot)], decl_acc @ [((lb,decl),info)])
                (* normal vector patterns are fine *)
                | _ -> (pos', pat_acc @ [P_aux (p,cannot)],decl_acc) )
            (* non-vector patterns aren't *)
            (*)| _ ->
               raise
                 (Reporting_basic.err_unreachable
                    (fst cannot)
                    ("unname_vector_concat_elements: Non-vector in vector-concat pattern:" ^
                       string_of_typ (typ_of_annot cannot))
                 )*) in
          let pats_tagged = tag_last pats in
          let (_,pats',decls') = List.fold_left aux (start,[],[]) pats_tagged in

          (* abuse P_vector_concat as a P_vector_const pattern: it has the of
          patterns as an argument but they're meant to be consed together *)
          (P_aux (P_as (P_aux (P_vector_concat pats',rannot'),rootid),rannot), decls @ decls')
      | ((p,decls),annot) -> (P_aux (p,annot),decls) in

    { p_lit            = (fun lit -> (P_lit lit,[]))
    ; p_wild           = (P_wild,[])
    ; p_as             = (fun ((pat,decls),id) -> (P_as (pat,id),decls))
    ; p_typ            = (fun (typ,(pat,decls)) -> (P_typ (typ,pat),decls))
    ; p_id             = (fun id -> (P_id id,[]))
    ; p_app            = (fun (id,ps) -> let (ps,decls) = List.split ps in
                                         (P_app (id,ps),List.flatten decls))
    ; p_record         = (fun (ps,b) -> let (ps,decls) = List.split ps in
                                        (P_record (ps,b),List.flatten decls))
    ; p_vector         = (fun ps -> let (ps,decls) = List.split ps in
                                    (P_vector ps,List.flatten decls))
    ; p_vector_indexed = (fun ps -> let (is,ps) = List.split ps in
                                    let (ps,decls) = List.split ps in
                                    let ps = List.combine is ps in
                                    (P_vector_indexed ps,List.flatten decls))
    ; p_vector_concat  = (fun ps -> let (ps,decls) = List.split ps in
                                    (P_vector_concat ps,List.flatten decls))
    ; p_tup            = (fun ps -> let (ps,decls) = List.split ps in
                                    (P_tup ps,List.flatten decls))
    ; p_list           = (fun ps -> let (ps,decls) = List.split ps in
                                    (P_list ps,List.flatten decls))
    ; p_aux            = (fun ((pat,decls),annot) -> p_aux ((pat,decls),annot))
    ; fP_aux           = (fun ((fpat,decls),annot) -> (FP_aux (fpat,annot),decls))
    ; fP_Fpat          = (fun (id,(pat,decls)) -> (FP_Fpat (id,pat),decls))
    } in

  let (pat,decls) = fold_pat unname_vector_concat_elements pat in

  let decls =
    let module S = Set.Make(String) in

    let roots_needed =
      List.fold_right
        (fun (_,(rootid,childid)) roots_needed ->
         if S.mem childid roots_needed then
           (* let _ = print_endline rootid in *)
           S.add rootid roots_needed
         else if String.length childid >= 3 && String.sub childid 0 2 = String.sub "v__" 0 2 then
           roots_needed
         else
           S.add rootid roots_needed
        ) decls S.empty in
    List.filter
      (fun (_,(_,childid)) ->  
       S.mem childid roots_needed ||
         String.length childid < 3 ||
           not (String.sub childid 0 2 = String.sub "v__" 0 2))
      decls in

  let (letbinds,decls) =
    let (decls,_) = List.split decls in
    List.split decls in

  let decls = List.fold_left (fun f g x -> f (g x)) (fun b -> b) decls in


  (* at this point shouldn't have P_as patterns in P_vector_concat patterns any more,
     all P_as and P_id vectors should have their declarations in decls.
     Now flatten all vector_concat patterns *)
  
  let flatten =
    let p_vector_concat ps =
      let aux p acc = match p with
        | (P_aux (P_vector_concat pats,_)) -> pats @ acc
        | pat -> pat :: acc in
      P_vector_concat (List.fold_right aux ps []) in
    {id_pat_alg with p_vector_concat = p_vector_concat} in
  
  let pat = fold_pat flatten pat in

  (* at this point pat should be a flat pattern: no vector_concat patterns
     with vector_concats patterns as direct child-nodes anymore *)

  let range a b =
    let rec aux a b = if a > b then [] else a :: aux (a+1) b in
    if a > b then List.rev (aux b a) else aux a b in

  let remove_vector_concats =
    let p_vector_concat ps =
      let aux acc (P_aux (p,annot),is_last) =
        let env = env_of_annot annot in
        let typ = Env.base_typ_of env (typ_of_annot annot) in
        let eff = effect_of_annot (snd annot) in
        let (l,_) = annot in
        let wild _ = P_aux (P_wild,(Parse_ast.Generated l, Some (env, bit_typ, eff))) in
        if is_vector_typ typ then
          match p, vector_typ_args_of typ with
          | P_vector ps,_ -> acc @ ps
          | _, (_,Nexp_aux (Nexp_constant length,_),_,_) ->
             acc @ (List.map wild (range 0 (length - 1)))
          | _, _ ->
            (*if is_last then*) acc @ [wild 0]
        else raise
          (Reporting_basic.err_unreachable l
            ("remove_vector_concats: Non-vector in vector-concat pattern " ^
              string_of_typ (typ_of_annot annot))) in

      let has_length (P_aux (p,annot)) =
        let typ = Env.base_typ_of (env_of_annot annot) (typ_of_annot annot) in
        match vector_typ_args_of typ with
        | (_,Nexp_aux (Nexp_constant length,_),_,_) -> true
        | _ -> false in

      let ps_tagged = tag_last ps in
      let ps' = List.fold_left aux [] ps_tagged in
      let last_has_length ps = List.exists (fun (p,b) -> b && has_length p) ps_tagged in

      if last_has_length ps then
        P_vector ps'
      else
        (* If the last vector pattern in the vector_concat pattern has unknown
        length we misuse the P_vector_concat constructor's argument to place in
        the following way: P_vector_concat [x;y; ... ;z] should be mapped to the
        pattern-match x :: y :: .. z, i.e. if x : 'a, then z : vector 'a. *)
        P_vector_concat ps' in

    {id_pat_alg with p_vector_concat = p_vector_concat} in
  
  let pat = fold_pat remove_vector_concats pat in
  
  (pat,letbinds,decls)

(* assumes there are no more E_internal expressions *)
let rewrite_exp_remove_vector_concat_pat rewriters (E_aux (exp,(l,annot)) as full_exp) =
  let rewrap e = E_aux (e,(l,annot)) in
  let rewrite_rec = rewriters.rewrite_exp rewriters in
  let rewrite_base = rewrite_exp rewriters in
  match exp with
  | E_case (e,ps) ->
     let aux (Pat_aux (Pat_exp (pat,body),annot')) =
       let (pat,_,decls) = remove_vector_concat_pat pat in
       Pat_aux (Pat_exp (pat, decls (rewrite_rec body)),annot') in
     rewrap (E_case (rewrite_rec e, List.map aux ps))
  | E_let (LB_aux (LB_val_explicit (typ,pat,v),annot'),body) ->
     let (pat,_,decls) = remove_vector_concat_pat pat in
     rewrap (E_let (LB_aux (LB_val_explicit (typ,pat,rewrite_rec v),annot'),
                    decls (rewrite_rec body)))
  | E_let (LB_aux (LB_val_implicit (pat,v),annot'),body) ->
     let (pat,_,decls) = remove_vector_concat_pat pat in
     rewrap (E_let (LB_aux (LB_val_implicit (pat,rewrite_rec v),annot'),
                    decls (rewrite_rec body)))
  | exp -> rewrite_base full_exp

let rewrite_fun_remove_vector_concat_pat
      rewriters (FD_aux (FD_function(recopt,tannotopt,effectopt,funcls),(l,fdannot))) = 
  let rewrite_funcl (FCL_aux (FCL_Funcl(id,pat,exp),(l,annot))) =
    let (pat',_,decls) = remove_vector_concat_pat pat in
    let exp' = decls (rewriters.rewrite_exp rewriters exp) in
    (FCL_aux (FCL_Funcl (id,pat',exp'),(l,annot))) 
  in FD_aux (FD_function(recopt,tannotopt,effectopt,List.map rewrite_funcl funcls),(l,fdannot))

let rewrite_defs_remove_vector_concat (Defs defs) =
  let rewriters =
    {rewrite_exp = rewrite_exp_remove_vector_concat_pat;
     rewrite_pat = rewrite_pat;
     rewrite_let = rewrite_let;
     rewrite_lexp = rewrite_lexp;
     rewrite_fun = rewrite_fun_remove_vector_concat_pat;
     rewrite_def = rewrite_def;
     rewrite_defs = rewrite_defs_base} in
  let rewrite_def d =
    let d = rewriters.rewrite_def rewriters d in
    match d with
    | DEF_val (LB_aux (LB_val_explicit (t,pat,exp),a)) ->
       let (pat,letbinds,_) = remove_vector_concat_pat pat in
       let defvals = List.map (fun lb -> DEF_val lb) letbinds in
       [DEF_val (LB_aux (LB_val_explicit (t,pat,exp),a))] @ defvals
    | DEF_val (LB_aux (LB_val_implicit (pat,exp),a)) -> 
       let (pat,letbinds,_) = remove_vector_concat_pat pat in
       let defvals = List.map (fun lb -> DEF_val lb) letbinds in
       [DEF_val (LB_aux (LB_val_implicit (pat,exp),a))] @ defvals
    | d -> [d] in
  Defs (List.flatten (List.map rewrite_def defs))

let rec contains_bitvector_pat (P_aux (pat,annot)) = match pat with
| P_lit _ | P_wild | P_id _ -> false
| P_as (pat,_) | P_typ (_,pat) -> contains_bitvector_pat pat
| P_vector _ | P_vector_concat _ | P_vector_indexed _ ->
    let typ = Env.base_typ_of (env_of_annot annot) (typ_of_annot annot) in
    is_bitvector_typ typ
| P_app (_,pats) | P_tup pats | P_list pats ->
    List.exists contains_bitvector_pat pats
| P_record (fpats,_) ->
    List.exists (fun (FP_aux (FP_Fpat (_,pat),_)) -> contains_bitvector_pat pat) fpats

let remove_bitvector_pat pat =

  (* first introduce names for bitvector patterns *)
  let name_bitvector_roots =
    { p_lit = (fun lit -> P_lit lit)
    ; p_typ = (fun (typ,p) -> P_typ (typ,p false))
    ; p_wild = P_wild
    ; p_as = (fun (pat,id) -> P_as (pat true,id))
    ; p_id  = (fun id -> P_id id)
    ; p_app = (fun (id,ps) -> P_app (id, List.map (fun p -> p false) ps))
    ; p_record = (fun (fpats,b) -> P_record (fpats, b))
    ; p_vector = (fun ps -> P_vector (List.map (fun p -> p false) ps))
    ; p_vector_indexed = (fun ps -> P_vector_indexed (List.map (fun (i,p) -> (i,p false)) ps))
    ; p_vector_concat  = (fun ps -> P_vector_concat (List.map (fun p -> p false) ps))
    ; p_tup            = (fun ps -> P_tup (List.map (fun p -> p false) ps))
    ; p_list           = (fun ps -> P_list (List.map (fun p -> p false) ps))
    ; p_aux =
        (fun (pat,annot) contained_in_p_as ->
          let env = env_of_annot annot in
          let t = Env.base_typ_of env (typ_of_annot annot) in
          let (l,_) = annot in
          match pat, is_bitvector_typ t, contained_in_p_as with
          | P_vector _, true, false
          | P_vector_indexed _, true, false ->
            P_aux (P_as (P_aux (pat,annot),fresh_id "b__" l), annot)
          | _ -> P_aux (pat,annot)
        )
    ; fP_aux = (fun (fpat,annot) -> FP_aux (fpat,annot))
    ; fP_Fpat = (fun (id,p) -> FP_Fpat (id,p false))
    } in
  let pat = (fold_pat name_bitvector_roots pat) false in

  (* Then collect guard expressions testing whether the literal bits of a
     bitvector pattern match those of a given bitvector, and collect let
     bindings for the bits bound by P_id or P_as patterns *)

  (* Helper functions for generating guard expressions *)
  let access_bit_exp (rootid,rannot) l idx =
    let root : tannot exp = E_aux (E_id rootid,rannot) in
    E_aux (E_vector_access (root,simple_num l idx), simple_annot l bit_typ) in

  let test_bit_exp rootid l t idx exp =
    let rannot = simple_annot l t in
    let elem = access_bit_exp (rootid,rannot) l idx in
    let eqid = Id_aux (Id "eq", Parse_ast.Generated l) in
    let eqannot = simple_annot l bool_typ in
    let eqexp : tannot exp = E_aux (E_app(eqid,[elem;exp]), eqannot) in
    Some (eqexp) in

  let test_subvec_exp rootid l typ i j lits =
    let (start, length, ord, _) = vector_typ_args_of typ in
    let length' = nconstant (List.length lits) in
    let start' =
      if is_order_inc ord then nconstant 0
      else nminus length' (nconstant 1) in
    let typ' = vector_typ start' length' ord bit_typ in
    let subvec_exp =
      match start, length with
      | Nexp_aux (Nexp_constant s, _), Nexp_aux (Nexp_constant l, _)
        when s = i && l = List.length lits ->
        E_id rootid
      | _ ->
      (*if vec_start t = i && vec_length t = List.length lits
      then E_id rootid
      else*) E_vector_subrange (
             E_aux (E_id rootid, simple_annot l typ),
             simple_num l i,
             simple_num l j) in
    E_aux (E_app(
      Id_aux (Id "eq_vec", Parse_ast.Generated l),
      [E_aux (subvec_exp, simple_annot l typ');
      E_aux (E_vector lits, simple_annot l typ')]),
      simple_annot l bool_typ) in

  let letbind_bit_exp rootid l typ idx id =
    let rannot = simple_annot l typ in
    let elem = access_bit_exp (rootid,rannot) l idx in
    let e = P_aux (P_id id, simple_annot l bit_typ) in
    let letbind = LB_aux (LB_val_implicit (e,elem), simple_annot l bit_typ) in
    let letexp = (fun body ->
      let (E_aux (_,(_,bannot))) = body in
      E_aux (E_let (letbind,body), (Parse_ast.Generated l, bannot))) in
    (letexp, letbind) in

  (* Helper functions for composing guards *)
  let bitwise_and exp1 exp2 =
    let (E_aux (_,(l,_))) = exp1 in
    let andid = Id_aux (Id "bool_and", Parse_ast.Generated l) in
    E_aux (E_app(andid,[exp1;exp2]), simple_annot l bool_typ) in

  let compose_guards guards =
    List.fold_right (Util.option_binop bitwise_and) guards None in

  let flatten_guards_decls gd =
    let (guards,decls,letbinds) = Util.split3 gd in
    (compose_guards guards, (List.fold_right (@@) decls), List.flatten letbinds) in

  (* Collect guards and let bindings *)
  let guard_bitvector_pat =
    let collect_guards_decls ps rootid t =
      let (start,_,ord,_) = vector_typ_args_of t in
      let rec collect current (guards,dls) idx ps =
        let idx' = if is_order_inc ord then idx + 1 else idx - 1 in
        (match ps with
          | pat :: ps' ->
            (match pat with
              | P_aux (P_lit lit, (l,annot)) ->
                let e = E_aux (E_lit lit, (Parse_ast.Generated l, annot)) in
                let current' = (match current with
                  | Some (l,i,j,lits) -> Some (l,i,idx,lits @ [e])
                  | None -> Some (l,idx,idx,[e])) in
                collect current' (guards, dls) idx' ps'
              | P_aux (P_as (pat',id), (l,annot)) ->
                let dl = letbind_bit_exp rootid l t idx id in
                collect current (guards, dls @ [dl]) idx (pat' :: ps')
              | _ ->
                let dls' = (match pat with
                  | P_aux (P_id id, (l,annot)) ->
                    dls @ [letbind_bit_exp rootid l t idx id]
                  | _ -> dls) in
                let guards' = (match current with
                  | Some (l,i,j,lits) ->
                    guards @ [Some (test_subvec_exp rootid l t i j lits)]
                  | None -> guards) in
                collect None (guards', dls') idx' ps')
          | [] ->
            let guards' = (match current with
              | Some (l,i,j,lits) ->
                guards @ [Some (test_subvec_exp rootid l t i j lits)]
              | None -> guards) in
            (guards',dls)) in
      let (guards,dls) = match start with
      | Nexp_aux (Nexp_constant s, _) ->
        collect None ([],[]) s ps
      | _ ->
        let (P_aux (_, (l,_))) = pat in
        raise (Reporting_basic.err_unreachable l
          "guard_bitvector_pat called on pattern with non-constant start index") in
      let (decls,letbinds) = List.split dls in
      (compose_guards guards, List.fold_right (@@) decls, letbinds) in

    let collect_guards_decls_indexed ips rootid t =
      let rec guard_decl (idx,pat) = (match pat with
        | P_aux (P_lit lit, (l,annot)) ->
          let exp = E_aux (E_lit lit, (l,annot)) in
          (test_bit_exp rootid l t idx exp, (fun b -> b), [])
        | P_aux (P_as (pat',id), (l,annot)) ->
          let (guard,decls,letbinds) = guard_decl (idx,pat') in
          let (letexp,letbind) = letbind_bit_exp rootid l t idx id in
          (guard, decls >> letexp, letbind :: letbinds)
        | P_aux (P_id id, (l,annot)) ->
          let (letexp,letbind) = letbind_bit_exp rootid l t idx id in
          (None, letexp, [letbind])
        | _ -> (None, (fun b -> b), [])) in
      let (guards,decls,letbinds) = Util.split3 (List.map guard_decl ips) in
      (compose_guards guards, List.fold_right (@@) decls, List.flatten letbinds) in

    { p_lit            = (fun lit -> (P_lit lit, (None, (fun b -> b), [])))
    ; p_wild           = (P_wild, (None, (fun b -> b), []))
    ; p_as             = (fun ((pat,gdls),id) -> (P_as (pat,id), gdls))
    ; p_typ            = (fun (typ,(pat,gdls)) -> (P_typ (typ,pat), gdls))
    ; p_id             = (fun id -> (P_id id, (None, (fun b -> b), [])))
    ; p_app            = (fun (id,ps) -> let (ps,gdls) = List.split ps in
                                         (P_app (id,ps), flatten_guards_decls gdls))
    ; p_record         = (fun (ps,b) -> let (ps,gdls) = List.split ps in
                                        (P_record (ps,b), flatten_guards_decls gdls))
    ; p_vector         = (fun ps -> let (ps,gdls) = List.split ps in
                                    (P_vector ps, flatten_guards_decls gdls))
    ; p_vector_indexed = (fun p -> let (is,p) = List.split p in
                                   let (ps,gdls) = List.split p in
                                   let ps = List.combine is ps in
                                   (P_vector_indexed ps, flatten_guards_decls gdls))
    ; p_vector_concat  = (fun ps -> let (ps,gdls) = List.split ps in
                                    (P_vector_concat ps, flatten_guards_decls gdls))
    ; p_tup            = (fun ps -> let (ps,gdls) = List.split ps in
                                    (P_tup ps, flatten_guards_decls gdls))
    ; p_list           = (fun ps -> let (ps,gdls) = List.split ps in
                                    (P_list ps, flatten_guards_decls gdls))
    ; p_aux            = (fun ((pat,gdls),annot) ->
                           let env = env_of_annot annot in
                           let t = Env.base_typ_of env (typ_of_annot annot) in
                           (match pat, is_bitvector_typ t with
                           | P_as (P_aux (P_vector ps, _), id), true ->
                             (P_aux (P_id id, annot), collect_guards_decls ps id t)
                           | P_as (P_aux (P_vector_indexed ips, _), id), true ->
                             (P_aux (P_id id, annot), collect_guards_decls_indexed ips id t)
                           | _, _ -> (P_aux (pat,annot), gdls)))
    ; fP_aux           = (fun ((fpat,gdls),annot) -> (FP_aux (fpat,annot), gdls))
    ; fP_Fpat          = (fun (id,(pat,gdls)) -> (FP_Fpat (id,pat), gdls))
    } in
  fold_pat guard_bitvector_pat pat

let remove_wildcards pre (P_aux (_,(l,_)) as pat) =
  fold_pat
    {id_pat_alg with
      p_aux = function
        | (P_wild,(l,annot)) -> P_aux (P_id (fresh_id pre l),(l,annot))
        | (p,annot) -> P_aux (p,annot) }
    pat

(* Check if one pattern subsumes the other, and if so, calculate a
   substitution of variables that are used in the same position.
   TODO: Check somewhere that there are no variable clashes (the same variable
   name used in different positions of the patterns)
 *)
let rec subsumes_pat (P_aux (p1,annot1) as pat1) (P_aux (p2,annot2) as pat2) =
  let rewrap p = P_aux (p,annot1) in
  let subsumes_list s pats1 pats2 =
    if List.length pats1 = List.length pats2
    then
      let subs = List.map2 s pats1 pats2 in
      List.fold_right
        (fun p acc -> match p, acc with
          | Some subst, Some substs -> Some (subst @ substs)
          | _ -> None)
        subs (Some [])
    else None in
  match p1, p2 with
  | P_lit (L_aux (lit1,_)), P_lit (L_aux (lit2,_)) ->
      if lit1 = lit2 then Some [] else None
  | P_as (pat1,_), _ -> subsumes_pat pat1 pat2
  | _, P_as (pat2,_) -> subsumes_pat pat1 pat2
  | P_typ (_,pat1), _ -> subsumes_pat pat1 pat2
  | _, P_typ (_,pat2) -> subsumes_pat pat1 pat2
  | P_id (Id_aux (id1,_) as aid1), P_id (Id_aux (id2,_) as aid2) ->
    if id1 = id2 then Some []
    else if Env.lookup_id aid1 (env_of_annot annot1) = Unbound &&
            Env.lookup_id aid2 (env_of_annot annot2) = Unbound
           then Some [(id2,id1)] else None
  | P_id id1, _ ->
    if Env.lookup_id id1 (env_of_annot annot1) = Unbound then Some [] else None
  | P_wild, _ -> Some []
  | P_app (Id_aux (id1,l1),args1), P_app (Id_aux (id2,_),args2) ->
    if id1 = id2 then subsumes_list subsumes_pat args1 args2 else None
  | P_record (fps1,b1), P_record (fps2,b2) ->
    if b1 = b2 then subsumes_list subsumes_fpat fps1 fps2 else None
  | P_vector pats1, P_vector pats2
  | P_vector_concat pats1, P_vector_concat pats2
  | P_tup pats1, P_tup pats2
  | P_list pats1, P_list pats2 ->
    subsumes_list subsumes_pat pats1 pats2
  | P_vector_indexed ips1, P_vector_indexed ips2 ->
    let (is1,ps1) = List.split ips1 in
    let (is2,ps2) = List.split ips2 in
    if is1 = is2 then subsumes_list subsumes_pat ps1 ps2 else None
  | _ -> None
and subsumes_fpat (FP_aux (FP_Fpat (id1,pat1),_)) (FP_aux (FP_Fpat (id2,pat2),_)) =
  if id1 = id2 then subsumes_pat pat1 pat2 else None

let equiv_pats pat1 pat2 =
  match subsumes_pat pat1 pat2, subsumes_pat pat2 pat1 with
  | Some _, Some _ -> true
  | _, _ -> false

let subst_id_pat pat (id1,id2) =
  let p_id (Id_aux (id,l)) = (if id = id1 then P_id (Id_aux (id2,l)) else P_id (Id_aux (id,l))) in
  fold_pat {id_pat_alg with p_id = p_id} pat

let subst_id_exp exp (id1,id2) =
  (* TODO Don't substitute bound occurrences inside let expressions etc *)
  let e_id (Id_aux (id,l)) = (if id = id1 then E_id (Id_aux (id2,l)) else E_id (Id_aux (id,l))) in
  fold_exp {id_exp_alg with e_id = e_id} exp

let rec pat_to_exp (P_aux (pat,(l,annot))) =
  let rewrap e = E_aux (e,(l,annot)) in
  match pat with
  | P_lit lit -> rewrap (E_lit lit)
  | P_wild -> raise (Reporting_basic.err_unreachable l
      "pat_to_exp given wildcard pattern")
  | P_as (pat,id) -> rewrap (E_id id)
  | P_typ (_,pat) -> pat_to_exp pat
  | P_id id -> rewrap (E_id id)
  | P_app (id,pats) -> rewrap (E_app (id, List.map pat_to_exp pats))
  | P_record (fpats,b) ->
      rewrap (E_record (FES_aux (FES_Fexps (List.map fpat_to_fexp fpats,b),(l,annot))))
  | P_vector pats -> rewrap (E_vector (List.map pat_to_exp pats))
  | P_vector_concat pats -> raise (Reporting_basic.err_unreachable l
      "pat_to_exp not implemented for P_vector_concat")
      (* We assume that vector concatenation patterns have been transformed
         away already *)
  | P_tup pats -> rewrap (E_tuple (List.map pat_to_exp pats))
  | P_list pats -> rewrap (E_list (List.map pat_to_exp pats))
  | P_vector_indexed ipats -> raise (Reporting_basic.err_unreachable l
      "pat_to_exp not implemented for P_vector_indexed") (* TODO *)
and fpat_to_fexp (FP_aux (FP_Fpat (id,pat),(l,annot))) =
  FE_aux (FE_Fexp (id, pat_to_exp pat),(l,annot))

let case_exp e t cs =
  let pexp (pat,body,annot) = Pat_aux (Pat_exp (pat,body),annot) in
  let ps = List.map pexp cs in
  (* let efr = union_effs (List.map effect_of_pexp ps) in *)
  fix_eff_exp (E_aux (E_case (e,ps), (get_loc_exp e, Some (env_of e, t, no_effect))))

let rewrite_guarded_clauses l cs =
  let rec group clauses =
    let add_clause (pat,cls,annot) c = (pat,cls @ [c],annot) in
    let rec group_aux current acc = (function
      | ((pat,guard,body,annot) as c) :: cs ->
          let (current_pat,_,_) = current in
          (match subsumes_pat current_pat pat with
            | Some substs ->
                let pat' = List.fold_left subst_id_pat pat substs in
                let guard' = (match guard with
                  | Some exp -> Some (List.fold_left subst_id_exp exp substs)
                  | None -> None) in
                let body' = List.fold_left subst_id_exp body substs in
                let c' = (pat',guard',body',annot) in
                group_aux (add_clause current c') acc cs
            | None ->
                let pat = remove_wildcards "g__" pat in
                group_aux (pat,[c],annot) (acc @ [current]) cs)
      | [] -> acc @ [current]) in
    let groups = match clauses with
      | ((pat,guard,body,annot) as c) :: cs ->
          group_aux (remove_wildcards "g__" pat, [c], annot) [] cs
      | _ ->
          raise (Reporting_basic.err_unreachable l
            "group given empty list in rewrite_guarded_clauses") in
    List.map (fun cs -> if_pexp cs) groups
  and if_pexp (pat,cs,annot) = (match cs with
    | c :: _ ->
        (* fix_eff_pexp (pexp *)
        let body = if_exp pat cs in
        let pexp = fix_eff_pexp (Pat_aux (Pat_exp (pat,body),annot)) in
        let (Pat_aux (Pat_exp (_,_),annot)) = pexp in
        (pat, body, annot)
    | [] ->
        raise (Reporting_basic.err_unreachable l
            "if_pexp given empty list in rewrite_guarded_clauses"))
  and if_exp current_pat = (function
    | (pat,guard,body,annot) :: ((pat',guard',body',annot') as c') :: cs ->
        (match guard with
          | Some exp ->
              let else_exp =
                if equiv_pats current_pat pat'
                then if_exp current_pat (c' :: cs)
                else case_exp (pat_to_exp current_pat) (typ_of body') (group (c' :: cs)) in
              fix_eff_exp (E_aux (E_if (exp,body,else_exp), simple_annot (fst annot) (typ_of body)))
          | None -> body)
    | [(pat,guard,body,annot)] -> body
    | [] ->
        raise (Reporting_basic.err_unreachable l
            "if_exp given empty list in rewrite_guarded_clauses")) in
  group cs

let rewrite_exp_remove_bitvector_pat rewriters (E_aux (exp,(l,annot)) as full_exp) =
  let rewrap e = E_aux (e,(l,annot)) in
  let rewrite_rec = rewriters.rewrite_exp rewriters in
  let rewrite_base = rewrite_exp rewriters in
  match exp with
  | E_case (e,ps)
    when List.exists (fun (Pat_aux (Pat_exp (pat,_),_)) -> contains_bitvector_pat pat) ps ->
     let clause (Pat_aux (Pat_exp (pat,body),annot')) =
       let (pat',(guard,decls,_)) = remove_bitvector_pat pat in
       let body' = decls (rewrite_rec body) in
       (pat',guard,body',annot') in
     let clauses = rewrite_guarded_clauses l (List.map clause ps) in
     if (effectful e) then
       let e = rewrite_rec e in
       let (E_aux (_,(el,eannot))) = e in
       let pat_e' = fresh_id_pat "p__" (el,eannot) in
       let exp_e' = pat_to_exp pat_e' in
       (* let fresh = fresh_id "p__" el in
       let exp_e' = E_aux (E_id fresh, gen_annot l (get_type e) pure_e) in
       let pat_e' = P_aux (P_id fresh, gen_annot l (get_type e) pure_e) in *)
       let letbind_e = LB_aux (LB_val_implicit (pat_e',e), (el,eannot)) in
       let exp' = case_exp exp_e' (typ_of full_exp) clauses in
       rewrap (E_let (letbind_e, exp'))
     else case_exp e (typ_of full_exp) clauses
  | E_let (LB_aux (LB_val_explicit (typ,pat,v),annot'),body) ->
     let (pat,(_,decls,_)) = remove_bitvector_pat pat in
     rewrap (E_let (LB_aux (LB_val_explicit (typ,pat,rewrite_rec v),annot'),
                    decls (rewrite_rec body)))
  | E_let (LB_aux (LB_val_implicit (pat,v),annot'),body) ->
     let (pat,(_,decls,_)) = remove_bitvector_pat pat in
     rewrap (E_let (LB_aux (LB_val_implicit (pat,rewrite_rec v),annot'),
                    decls (rewrite_rec body)))
  | _ -> rewrite_base full_exp

let rewrite_fun_remove_bitvector_pat
      rewriters (FD_aux (FD_function(recopt,tannotopt,effectopt,funcls),(l,fdannot))) =
  let _ = reset_fresh_name_counter () in
  (* TODO Can there be clauses with different id's in one FD_function? *)
  let funcls = match funcls with
    | (FCL_aux (FCL_Funcl(id,_,_),_) :: _) ->
        let clause (FCL_aux (FCL_Funcl(_,pat,exp),annot)) =
          let (pat,(guard,decls,_)) = remove_bitvector_pat pat in
          let exp = decls (rewriters.rewrite_exp rewriters exp) in
          (pat,guard,exp,annot) in
        let cs = rewrite_guarded_clauses l (List.map clause funcls) in
        List.map (fun (pat,exp,annot) -> FCL_aux (FCL_Funcl(id,pat,exp),annot)) cs
    | _ -> funcls (* TODO is the empty list possible here? *) in
  FD_aux (FD_function(recopt,tannotopt,effectopt,funcls),(l,fdannot))

let rewrite_defs_remove_bitvector_pats (Defs defs) =
  let rewriters =
    {rewrite_exp = rewrite_exp_remove_bitvector_pat;
     rewrite_pat = rewrite_pat;
     rewrite_let = rewrite_let;
     rewrite_lexp = rewrite_lexp;
     rewrite_fun = rewrite_fun_remove_bitvector_pat;
     rewrite_def = rewrite_def;
     rewrite_defs = rewrite_defs_base } in
  let rewrite_def d =
    let d = rewriters.rewrite_def rewriters d in
    match d with
    | DEF_val (LB_aux (LB_val_explicit (t,pat,exp),a)) ->
       let (pat',(_,_,letbinds)) = remove_bitvector_pat pat in
       let defvals = List.map (fun lb -> DEF_val lb) letbinds in
       [DEF_val (LB_aux (LB_val_explicit (t,pat',exp),a))] @ defvals
    | DEF_val (LB_aux (LB_val_implicit (pat,exp),a)) ->
       let (pat',(_,_,letbinds)) = remove_bitvector_pat pat in
       let defvals = List.map (fun lb -> DEF_val lb) letbinds in
       [DEF_val (LB_aux (LB_val_implicit (pat',exp),a))] @ defvals
    | d -> [d] in
  Defs (List.flatten (List.map rewrite_def defs))


(*Expects to be called after rewrite_defs; thus the following should not appear:
  internal_exp of any form
  lit vectors in patterns or expressions
 *)
let rewrite_exp_lift_assign_intro rewriters ((E_aux (exp,((l,_) as annot))) as full_exp) =
  let rewrap e = E_aux (e,annot) in
  let rewrap_effects e eff =
    E_aux (e, (l,Some (env_of_annot annot, typ_of_annot annot, eff))) in
  let rewrite_rec = rewriters.rewrite_exp rewriters in
  let rewrite_base = rewrite_exp rewriters in
  match exp with
  | E_block exps ->
    let rec walker exps = match exps with
      | [] -> []
      | (E_aux(E_assign((LEXP_aux ((LEXP_id id | LEXP_cast (_,id)),_)) as le,e),
               ((l, Some (env,typ,eff)) as annot)) as exp)::exps ->
        (match Env.lookup_id id env with
         | Unbound ->
            let le' = rewriters.rewrite_lexp rewriters le in
            let e' = rewrite_base e in
            let exps' = walker exps in
            let effects = union_eff_exps exps' in
            let block = E_aux (E_block exps', (l, Some (env, unit_typ, effects))) in
            [fix_eff_exp (E_aux (E_internal_let(le', e', block), annot))]
         | _ -> (rewrite_rec exp)::(walker exps))
      (*| ((E_aux(E_if(c,t,e),(l,annot))) as exp)::exps ->
        let vars_t = introduced_variables t in
        let vars_e = introduced_variables e in
        let new_vars = Envmap.intersect vars_t vars_e in
        if Envmap.is_empty new_vars
         then (rewrite_base exp)::walker exps
         else
           let new_nmap = match nmap with
             | None -> Some(Nexpmap.empty,new_vars)
             | Some(nm,s) -> Some(nm, Envmap.union new_vars s) in
           let c' = rewrite_base c in
           let t' = rewriters.rewrite_exp rewriters new_nmap t in
           let e' = rewriters.rewrite_exp rewriters new_nmap e in
           let exps' = walker exps in
           fst ((Envmap.fold 
                  (fun (res,effects) i (t,e) ->
                let bitlit =  E_aux (E_lit (L_aux(L_zero, Parse_ast.Generated l)),
                                     (Parse_ast.Generated l, simple_annot bit_t)) in
                let rangelit = E_aux (E_lit (L_aux (L_num 0, Parse_ast.Generated l)),
                                      (Parse_ast.Generated l, simple_annot nat_t)) in
                let set_exp =
                  match t.t with
                  | Tid "bit" | Tabbrev(_,{t=Tid "bit"}) -> bitlit
                  | Tapp("range", _) | Tapp("atom", _) -> rangelit
                  | Tapp("vector", [_;_;_;TA_typ ( {t=Tid "bit"} | {t=Tabbrev(_,{t=Tid "bit"})})])
                  | Tapp(("reg"|"register"),[TA_typ ({t = Tapp("vector",
                                                               [_;_;_;TA_typ ( {t=Tid "bit"}
                                                                             | {t=Tabbrev(_,{t=Tid "bit"})})])})])
                  | Tabbrev(_,{t = Tapp("vector",
                                        [_;_;_;TA_typ ( {t=Tid "bit"}
                                                      | {t=Tabbrev(_,{t=Tid "bit"})})])}) ->
                    E_aux (E_vector_indexed([], Def_val_aux(Def_val_dec bitlit,
                                                            (Parse_ast.Generated l,simple_annot bit_t))),
                           (Parse_ast.Generated l, simple_annot t))
                  | _ -> e in
                let unioneffs = union_effects effects (get_effsum_exp set_exp) in
                ([E_aux (E_internal_let (LEXP_aux (LEXP_id (Id_aux (Id i, Parse_ast.Generated l)),
                                                  (Parse_ast.Generated l, (tag_annot t Emp_intro))),
                                        set_exp,
                                        E_aux (E_block res, (Parse_ast.Generated l, (simple_annot_efr unit_t effects)))),
                        (Parse_ast.Generated l, simple_annot_efr unit_t unioneffs))],unioneffs)))
             (E_aux(E_if(c',t',e'),(Parse_ast.Generated l, annot))::exps',eff_union_exps (c'::t'::e'::exps')) new_vars)*)
      | e::exps -> (rewrite_rec e)::(walker exps)
    in
    rewrap (E_block (walker exps))
  | E_assign(((LEXP_aux ((LEXP_id id | LEXP_cast (_,id)),lannot)) as le),e) ->
    let le' = rewriters.rewrite_lexp rewriters le in
    let e' = rewrite_base e in
    let effects = effect_of e' in
    (match Env.lookup_id id (env_of_annot annot) with
     | Unbound ->
       rewrap_effects
         (E_internal_let(le', e', E_aux(E_block [], simple_annot l unit_typ)))
         effects
     | Local _ ->
       let effects' = union_effects effects (effect_of_annot (snd lannot)) in
       let annot' = Some (env_of_annot annot, unit_typ, effects') in
       E_aux((E_assign(le', e')),(l, annot'))
     | _ -> rewrite_base full_exp)
  | _ -> rewrite_base full_exp

let rewrite_lexp_lift_assign_intro rewriters ((LEXP_aux(lexp,annot)) as le) =
  let rewrap le = LEXP_aux(le,annot) in
  let rewrite_base = rewrite_lexp rewriters in
  match lexp, annot with
  | (LEXP_id id | LEXP_cast (_,id)), (l, Some (env, typ, eff)) ->
    (match Env.lookup_id id env with
    | Unbound | Local _ ->
      LEXP_aux (lexp, (l, Some (env, typ, union_effects eff (mk_effect [BE_lset]))))
    | _ -> rewrap lexp)
  | _ -> rewrite_base le


let rewrite_defs_exp_lift_assign defs = rewrite_defs_base
    {rewrite_exp = rewrite_exp_lift_assign_intro;
     rewrite_pat = rewrite_pat;
     rewrite_let = rewrite_let;
     rewrite_lexp = rewrite_lexp_lift_assign_intro;
     rewrite_fun = rewrite_fun;
     rewrite_def = rewrite_def;
     rewrite_defs = rewrite_defs_base} defs

(*let rewrite_exp_separate_ints rewriters ((E_aux (exp,((l,_) as annot))) as full_exp) =
  (*let tparms,t,tag,nexps,eff,cum_eff,bounds = match annot with
    | Base((tparms,t),tag,nexps,eff,cum_eff,bounds) -> tparms,t,tag,nexps,eff,cum_eff,bounds
    | _ -> [],unit_t,Emp_local,[],pure_e,pure_e,nob in*)
  let rewrap e = E_aux (e,annot) in
  (*let rewrap_effects e effsum =
    E_aux (e,(l,Base ((tparms,t),tag,nexps,eff,effsum,bounds))) in*)
  let rewrite_rec = rewriters.rewrite_exp rewriters in
  let rewrite_base = rewrite_exp rewriters in
  match exp with
  | E_lit (L_aux (((L_num _) as lit),_)) ->
    (match (is_within_machine64 t nexps) with
     | Yes -> let _ = Printf.eprintf "Rewriter of num_const, within 64bit int yes\n" in rewrite_base full_exp
     | Maybe -> let _ = Printf.eprintf "Rewriter of num_const, within 64bit int maybe\n" in rewrite_base full_exp
     | No -> let _ = Printf.eprintf "Rewriter of num_const, within 64bit int no\n" in E_aux(E_app(Id_aux (Id "integer_of_int",l),[rewrite_base full_exp]),
                   (l, Base((tparms,t),External(None),nexps,eff,cum_eff,bounds))))
  | E_cast (typ, exp) -> rewrap (E_cast (typ, rewrite_rec exp))
  | E_app (id,exps) -> rewrap (E_app (id,List.map rewrite_rec exps))
  | E_app_infix(el,id,er) -> rewrap (E_app_infix(rewrite_rec el,id,rewrite_rec er))
  | E_for (id, e1, e2, e3, o, body) ->
      rewrap (E_for (id, rewrite_rec e1, rewrite_rec e2, rewrite_rec e3, o, rewrite_rec body))
  | E_vector_access (vec,index) -> rewrap (E_vector_access (rewrite_rec vec,rewrite_rec index))
  | E_vector_subrange (vec,i1,i2) ->
    rewrap (E_vector_subrange (rewrite_rec vec,rewrite_rec i1,rewrite_rec i2))
  | E_vector_update (vec,index,new_v) -> 
    rewrap (E_vector_update (rewrite_rec vec,rewrite_rec index,rewrite_rec new_v))
  | E_vector_update_subrange (vec,i1,i2,new_v) ->
    rewrap (E_vector_update_subrange (rewrite_rec vec,rewrite_rec i1,rewrite_rec i2,rewrite_rec new_v))
  | E_case (exp ,pexps) -> 
    rewrap (E_case (rewrite_rec exp,
                    (List.map 
                       (fun (Pat_aux (Pat_exp(p,e),pannot)) -> 
                          Pat_aux (Pat_exp(rewriters.rewrite_pat rewriters nmap p,rewrite_rec e),pannot)) pexps)))
  | E_let (letbind,body) -> rewrap (E_let(rewriters.rewrite_let rewriters nmap letbind,rewrite_rec body))
  | E_internal_let (lexp,exp,body) ->
    rewrap (E_internal_let (rewriters.rewrite_lexp rewriters nmap lexp, rewrite_rec exp, rewrite_rec body))
  | _ -> rewrite_base full_exp

let rewrite_defs_separate_numbs defs = rewrite_defs_base
    {rewrite_exp = rewrite_exp_separate_ints;
     rewrite_pat = rewrite_pat;
     rewrite_let = rewrite_let; (*will likely need a new one?*)
     rewrite_lexp = rewrite_lexp; (*will likely need a new one?*)
     rewrite_fun = rewrite_fun;
     rewrite_def = rewrite_def;
     rewrite_defs = rewrite_defs_base} defs*)

let rewrite_defs_ocaml defs =
  let defs_sorted = top_sort_defs defs in
  let defs_vec_concat_removed = rewrite_defs_remove_vector_concat defs_sorted in
  let defs_lifted_assign = rewrite_defs_exp_lift_assign defs_vec_concat_removed in
(*  let defs_separate_nums = rewrite_defs_separate_numbs defs_lifted_assign in *)
  defs_lifted_assign

let rewrite_defs_remove_blocks =
  let letbind_wild v body =
    let (E_aux (_,(l,tannot))) = v in
    let annot_pat = (simple_annot l (typ_of v)) in
    let annot_lb = (Parse_ast.Generated l, tannot) in
    let annot_let = (Parse_ast.Generated l, Some (env_of body, typ_of body, union_eff_exps [v;body])) in
    E_aux (E_let (LB_aux (LB_val_implicit (P_aux (P_wild,annot_pat),v),annot_lb),body),annot_let) in

  let rec f l = function
    | [] -> E_aux (E_lit (L_aux (L_unit,Parse_ast.Generated l)), (simple_annot l unit_typ))
    | [e] -> e  (* check with Kathy if that annotation is fine *)
    | e :: es -> letbind_wild e (f l es) in

  let e_aux = function
    | (E_block es,(l,_)) -> f l es
    | (e,annot) -> E_aux (e,annot) in
    
  let alg = { id_exp_alg with e_aux = e_aux } in

  rewrite_defs_base
    {rewrite_exp = (fun _ -> fold_exp alg)
    ; rewrite_pat = rewrite_pat
    ; rewrite_let = rewrite_let
    ; rewrite_lexp = rewrite_lexp
    ; rewrite_fun = rewrite_fun
    ; rewrite_def = rewrite_def
    ; rewrite_defs = rewrite_defs_base
    }



let letbind (v : 'a exp) (body : 'a exp -> 'a exp) : 'a exp =
  (* body is a function : E_id variable -> actual body *)
  let (E_aux (_,(l,annot))) = v in
  match annot with
  | Some (env, Typ_aux (Typ_id tid, _), eff) when string_of_id tid = "unit" ->
     let e = E_aux (E_lit (L_aux (L_unit,Parse_ast.Generated l)),(simple_annot l unit_typ))  in
     let body = body e in
     let annot_pat = simple_annot l unit_typ in
     let annot_lb = annot_pat in
     let annot_let = (Parse_ast.Generated l, Some (env, typ_of body, union_eff_exps [v;body])) in
     let pat = P_aux (P_wild,annot_pat) in
     
     E_aux (E_let (LB_aux (LB_val_implicit (pat,v),annot_lb),body),annot_let)
  | Some (env, typ, eff) ->
     let id = fresh_id "w__" l in
     let annot_pat = simple_annot l (typ_of v) in
     let e_id = E_aux (E_id id, (Parse_ast.Generated l, Some (env, typ, no_effect))) in
     let body = body e_id in

     let annot_lb = annot_pat in
     let annot_let = (Parse_ast.Generated l, Some (env, typ_of body, union_eff_exps [v;body])) in
     let pat = P_aux (P_id id,annot_pat) in
     
     E_aux (E_let (LB_aux (LB_val_implicit (pat,v),annot_lb),body),annot_let)
  | None ->
     raise (Reporting_basic.err_unreachable l "no type information")


let rec mapCont (f : 'b -> ('b -> 'a exp) -> 'a exp) (l : 'b list) (k : 'b list -> 'a exp) : 'a exp = 
  match l with
  | [] -> k []
  | exp :: exps -> f exp (fun exp -> mapCont f exps (fun exps -> k (exp :: exps)))
                
let rewrite_defs_letbind_effects  =  

  let rec value ((E_aux (exp_aux,_)) as exp) =
    not (effectful exp || updates_vars exp)
  and value_optdefault (Def_val_aux (o,_)) = match o with
    | Def_val_empty -> true
    | Def_val_dec e -> value e
  and value_fexps (FES_aux (FES_Fexps (fexps,_),_)) =
    List.fold_left (fun b (FE_aux (FE_Fexp (_,e),_)) -> b && value e) true fexps in


  let rec n_exp_name (exp : 'a exp) (k : 'a exp -> 'a exp) : 'a exp =
    n_exp exp (fun exp -> if value exp then k exp else letbind exp k)

  and n_exp_pure (exp : 'a exp) (k : 'a exp -> 'a exp) : 'a exp =
    n_exp exp (fun exp -> if value exp then k exp else letbind exp k)

  and n_exp_nameL (exps : 'a exp list) (k : 'a exp list -> 'a exp) : 'a exp =
    mapCont n_exp_name exps k

  and n_fexp (fexp : 'a fexp) (k : 'a fexp -> 'a exp) : 'a exp =
    let (FE_aux (FE_Fexp (id,exp),annot)) = fexp in
    n_exp_name exp (fun exp -> 
    k (fix_eff_fexp (FE_aux (FE_Fexp (id,exp),annot))))

  and n_fexpL (fexps : 'a fexp list) (k : 'a fexp list -> 'a exp) : 'a exp =
    mapCont n_fexp fexps k

  and n_pexp (newreturn : bool) (pexp : 'a pexp) (k : 'a pexp -> 'a exp) : 'a exp =
    let (Pat_aux (Pat_exp (pat,exp),annot)) = pexp in
    k (fix_eff_pexp (Pat_aux (Pat_exp (pat,n_exp_term newreturn exp), annot)))

  and n_pexpL (newreturn : bool) (pexps : 'a pexp list) (k : 'a pexp list -> 'a exp) : 'a exp =
    mapCont (n_pexp newreturn) pexps k

  and n_fexps (fexps : 'a fexps) (k : 'a fexps -> 'a exp) : 'a exp = 
    let (FES_aux (FES_Fexps (fexps_aux,b),annot)) = fexps in
    n_fexpL fexps_aux (fun fexps_aux -> 
    k (fix_eff_fexps (FES_aux (FES_Fexps (fexps_aux,b),annot))))

  and n_opt_default (opt_default : 'a opt_default) (k : 'a opt_default -> 'a exp) : 'a exp = 
    let (Def_val_aux (opt_default,annot)) = opt_default in
    match opt_default with
    | Def_val_empty -> k (Def_val_aux (Def_val_empty,annot))
    | Def_val_dec exp ->
       n_exp_name exp (fun exp -> 
       k (fix_eff_opt_default (Def_val_aux (Def_val_dec exp,annot))))

  and n_lb (lb : 'a letbind) (k : 'a letbind -> 'a exp) : 'a exp =
    let (LB_aux (lb,annot)) = lb in
    match lb with
    | LB_val_explicit (typ,pat,exp1) ->
       n_exp exp1 (fun exp1 -> 
       k (fix_eff_lb (LB_aux (LB_val_explicit (typ,pat,exp1),annot))))
    | LB_val_implicit (pat,exp1) ->
       n_exp exp1 (fun exp1 -> 
       k (fix_eff_lb (LB_aux (LB_val_implicit (pat,exp1),annot))))

  and n_lexp (lexp : 'a lexp) (k : 'a lexp -> 'a exp) : 'a exp =
    let (LEXP_aux (lexp_aux,annot)) = lexp in
    match lexp_aux with
    | LEXP_id _ -> k lexp
    | LEXP_memory (id,es) ->
       n_exp_nameL es (fun es -> 
       k (fix_eff_lexp (LEXP_aux (LEXP_memory (id,es),annot))))
    | LEXP_cast (typ,id) -> 
       k (fix_eff_lexp (LEXP_aux (LEXP_cast (typ,id),annot)))
    | LEXP_vector (lexp,e) ->
       n_lexp lexp (fun lexp -> 
       n_exp_name e (fun e -> 
       k (fix_eff_lexp (LEXP_aux (LEXP_vector (lexp,e),annot)))))
    | LEXP_vector_range (lexp,e1,e2) ->
       n_lexp lexp (fun lexp ->
       n_exp_name e1 (fun e1 ->
       n_exp_name e2 (fun e2 ->
       k (fix_eff_lexp (LEXP_aux (LEXP_vector_range (lexp,e1,e2),annot))))))
    | LEXP_field (lexp,id) ->
       n_lexp lexp (fun lexp ->
       k (fix_eff_lexp (LEXP_aux (LEXP_field (lexp,id),annot))))

  and n_exp_term (newreturn : bool) (exp : 'a exp) : 'a exp =
    let (E_aux (_,(l,tannot))) = exp in
    let exp =
      if newreturn then
        let typ = typ_of exp in
        E_aux (E_internal_return exp, simple_annot l typ)
      else
        exp in
    (* n_exp_term forces an expression to be translated into a form 
       "let .. let .. let .. in EXP" where EXP has no effect and does not update
       variables *)
    n_exp_pure exp (fun exp -> exp)

  and n_exp (E_aux (exp_aux,annot) as exp : 'a exp) (k : 'a exp -> 'a exp) : 'a exp = 

    let rewrap e = fix_eff_exp (E_aux (e,annot)) in

    match exp_aux with
    | E_block es -> failwith "E_block should have been removed till now"
    | E_nondet _ -> failwith "E_nondet not supported"
    | E_id id -> k exp
    | E_lit _ -> k exp
    | E_cast (typ,exp') ->
       n_exp_name exp' (fun exp' ->
       k (rewrap (E_cast (typ,exp'))))
    | E_app (id,exps) ->
       n_exp_nameL exps (fun exps ->
       k (rewrap (E_app (id,exps))))
    | E_app_infix (exp1,id,exp2) ->
       n_exp_name exp1 (fun exp1 ->
       n_exp_name exp2 (fun exp2 ->
       k (rewrap (E_app_infix (exp1,id,exp2)))))
    | E_tuple exps ->
       n_exp_nameL exps (fun exps ->
       k (rewrap (E_tuple exps)))
    | E_if (exp1,exp2,exp3) ->
       n_exp_name exp1 (fun exp1 ->
       let (E_aux (_,annot2)) = exp2 in
       let (E_aux (_,annot3)) = exp3 in
       let newreturn = effectful exp2 || effectful exp3 in
       let exp2 = n_exp_term newreturn exp2 in
       let exp3 = n_exp_term newreturn exp3 in
       k (rewrap (E_if (exp1,exp2,exp3))))
    | E_for (id,start,stop,by,dir,body) ->
       n_exp_name start (fun start -> 
       n_exp_name stop (fun stop ->
       n_exp_name by (fun by ->
       let body = n_exp_term (effectful body) body in
       k (rewrap (E_for (id,start,stop,by,dir,body))))))
    | E_vector exps ->
       n_exp_nameL exps (fun exps ->
       k (rewrap (E_vector exps)))
    | E_vector_indexed (exps,opt_default)  ->
       let (is,exps) = List.split exps in
       n_exp_nameL exps (fun exps -> 
       n_opt_default opt_default (fun opt_default ->
       let exps = List.combine is exps in
       k (rewrap (E_vector_indexed (exps,opt_default)))))
    | E_vector_access (exp1,exp2) ->
       n_exp_name exp1 (fun exp1 ->
       n_exp_name exp2 (fun exp2 ->
       k (rewrap (E_vector_access (exp1,exp2)))))
    | E_vector_subrange (exp1,exp2,exp3) ->
       n_exp_name exp1 (fun exp1 -> 
       n_exp_name exp2 (fun exp2 -> 
       n_exp_name exp3 (fun exp3 ->
       k (rewrap (E_vector_subrange (exp1,exp2,exp3))))))
    | E_vector_update (exp1,exp2,exp3) ->
       n_exp_name exp1 (fun exp1 -> 
       n_exp_name exp2 (fun exp2 -> 
       n_exp_name exp3 (fun exp3 ->
       k (rewrap (E_vector_update (exp1,exp2,exp3))))))
    | E_vector_update_subrange (exp1,exp2,exp3,exp4) ->
       n_exp_name exp1 (fun exp1 -> 
       n_exp_name exp2 (fun exp2 -> 
       n_exp_name exp3 (fun exp3 -> 
       n_exp_name exp4 (fun exp4 ->
       k (rewrap (E_vector_update_subrange (exp1,exp2,exp3,exp4)))))))
    | E_vector_append (exp1,exp2) ->
       n_exp_name exp1 (fun exp1 ->
       n_exp_name exp2 (fun exp2 ->
       k (rewrap (E_vector_append (exp1,exp2)))))
    | E_list exps ->
       n_exp_nameL exps (fun exps ->
       k (rewrap (E_list exps)))
    | E_cons (exp1,exp2) -> 
       n_exp_name exp1 (fun exp1 ->
       n_exp_name exp2 (fun exp2 ->
       k (rewrap (E_cons (exp1,exp2)))))
    | E_record fexps ->
       n_fexps fexps (fun fexps ->
       k (rewrap (E_record fexps)))
    | E_record_update (exp1,fexps) -> 
       n_exp_name exp1 (fun exp1 ->
       n_fexps fexps (fun fexps ->
       k (rewrap (E_record_update (exp1,fexps)))))
    | E_field (exp1,id) ->
       n_exp_name exp1 (fun exp1 ->
       k (rewrap (E_field (exp1,id))))
    | E_case (exp1,pexps) ->
       let newreturn =
         List.fold_left
           (fun b (Pat_aux (_,(_,annot))) -> b || effectful_effs (effect_of_annot annot))
           false pexps in
       n_exp_name exp1 (fun exp1 -> 
       n_pexpL newreturn pexps (fun pexps ->
       k (rewrap (E_case (exp1,pexps)))))
    | E_let (lb,body) ->
       n_lb lb (fun lb -> 
       rewrap (E_let (lb,n_exp body k)))
    | E_sizeof nexp ->
       k (rewrap (E_sizeof nexp))
    | E_sizeof_internal annot ->
       k (rewrap (E_sizeof_internal annot))
    | E_assign (lexp,exp1) ->
       n_lexp lexp (fun lexp ->
       n_exp_name exp1 (fun exp1 ->
       k (rewrap (E_assign (lexp,exp1)))))
    | E_exit exp' -> k (E_aux (E_exit (n_exp_term (effectful exp') exp'),annot))
    | E_assert (exp1,exp2) ->
       n_exp exp1 (fun exp1 ->
       n_exp exp2 (fun exp2 ->
       k (rewrap (E_assert (exp1,exp2)))))
    | E_internal_cast (annot',exp') ->
       n_exp_name exp' (fun exp' ->
       k (rewrap (E_internal_cast (annot',exp'))))
    | E_internal_exp _ -> k exp
    | E_internal_exp_user _ -> k exp
    | E_internal_let (lexp,exp1,exp2) ->
       n_lexp lexp (fun lexp ->
       n_exp exp1 (fun exp1 ->
       rewrap (E_internal_let (lexp,exp1,n_exp exp2 k))))
    | E_internal_return exp1 ->
       n_exp_name exp1 (fun exp1 ->
       k (rewrap (E_internal_return exp1)))
    | E_comment str ->
      k (rewrap (E_comment str))
    | E_comment_struc exp' ->
       n_exp exp' (fun exp' ->
               k (rewrap (E_comment_struc exp')))
    | E_return exp' ->
       n_exp_name exp' (fun exp' ->
       k (rewrap (E_return exp')))
    | E_internal_plet _ -> failwith "E_internal_plet should not be here yet" in

  let rewrite_fun _ (FD_aux (FD_function(recopt,tannotopt,effectopt,funcls),fdannot)) = 
    let newreturn =
      List.fold_left
        (fun b (FCL_aux (FCL_Funcl(id,pat,exp),(_,annot))) ->
         b || effectful_effs (effect_of_annot annot)) false funcls in
    let rewrite_funcl (FCL_aux (FCL_Funcl(id,pat,exp),annot)) =
      let _ = reset_fresh_name_counter () in
      FCL_aux (FCL_Funcl (id,pat,n_exp_term newreturn exp),annot)
    in FD_aux (FD_function(recopt,tannotopt,effectopt,List.map rewrite_funcl funcls),fdannot) in
  rewrite_defs_base
    {rewrite_exp = rewrite_exp
    ; rewrite_pat = rewrite_pat
    ; rewrite_let = rewrite_let
    ; rewrite_lexp = rewrite_lexp
    ; rewrite_fun = rewrite_fun
    ; rewrite_def = rewrite_def
    ; rewrite_defs = rewrite_defs_base
    }

let rewrite_defs_effectful_let_expressions =

  let e_let (lb,body) = 
    match lb with
    | LB_aux (LB_val_explicit (_,pat,exp'),annot')
    | LB_aux (LB_val_implicit (pat,exp'),annot') ->
       if effectful exp'
       then E_internal_plet (pat,exp',body)
       else E_let (lb,body) in
                             
  let e_internal_let = fun (lexp,exp1,exp2) ->
    if effectful exp1 then
      match lexp with
      | LEXP_aux (LEXP_id id,annot)
      | LEXP_aux (LEXP_cast (_,id),annot) ->
         E_internal_plet (P_aux (P_id id,annot),exp1,exp2)
      | _ -> failwith "E_internal_plet with unexpected lexp"
    else E_internal_let (lexp,exp1,exp2) in

  let alg = { id_exp_alg with e_let = e_let; e_internal_let = e_internal_let } in
  rewrite_defs_base
    {rewrite_exp = (fun _ -> fold_exp alg)
    ; rewrite_pat = rewrite_pat
    ; rewrite_let = rewrite_let
    ; rewrite_lexp = rewrite_lexp
    ; rewrite_fun = rewrite_fun
    ; rewrite_def = rewrite_def
    ; rewrite_defs = rewrite_defs_base
    }

             
(* Now all expressions have no blocks anymore, any term is a sequence of let-expressions,
 * internal let-expressions, or internal plet-expressions ended by a term that does not
 * access memory or registers and does not update variables *)

let dedup eq =
  List.fold_left (fun acc e -> if List.exists (eq e) acc then acc else e :: acc) []

let eqidtyp (id1,_) (id2,_) =
  let name1 = match id1 with Id_aux ((Id name | DeIid name),_) -> name in
  let name2 = match id2 with Id_aux ((Id name | DeIid name),_) -> name in
  name1 = name2

let find_updated_vars exp = 
  let ( @@ ) (a,b) (a',b') = (a @ a',b @ b') in
  let lapp2 (l : (('a list * 'b list) list)) : ('a list * 'b list) =
    List.fold_left
      (fun ((intros_acc : 'a list),(updates_acc : 'b list)) (intros,updates) ->
       (intros_acc @ intros, updates_acc @ updates)) ([],[]) l in
  
  let (intros,updates) =
    fold_exp
      { e_aux = (fun (e,_) -> e)
      ; e_id = (fun _ -> ([],[]))
      ; e_lit = (fun _ -> ([],[]))
      ; e_cast = (fun (_,e) -> e)
      ; e_block = (fun es -> lapp2 es)
      ; e_nondet = (fun es -> lapp2 es)
      ; e_app = (fun (_,es) -> lapp2 es)
      ; e_app_infix = (fun (e1,_,e2) -> e1 @@ e2)
      ; e_tuple = (fun es -> lapp2 es)
      ; e_if = (fun (e1,e2,e3) -> e1 @@ e2 @@ e3)
      ; e_for = (fun (_,e1,e2,e3,_,e4) -> e1 @@ e2 @@ e3 @@ e4)
      ; e_vector = (fun es -> lapp2 es)
      ; e_vector_indexed = (fun (es,opt) -> opt @@ lapp2 (List.map snd es))
      ; e_vector_access = (fun (e1,e2) -> e1 @@ e2)
      ; e_vector_subrange =  (fun (e1,e2,e3) -> e1 @@ e2 @@ e3)
      ; e_vector_update = (fun (e1,e2,e3) -> e1 @@ e2 @@ e3)
      ; e_vector_update_subrange =  (fun (e1,e2,e3,e4) -> e1 @@ e2 @@ e3 @@ e4)
      ; e_vector_append = (fun (e1,e2) -> e1 @@ e2)
      ; e_list = (fun es -> lapp2 es)
      ; e_cons = (fun (e1,e2) -> e1 @@ e2)
      ; e_record = (fun fexps -> fexps)
      ; e_record_update = (fun (e1,fexp) -> e1 @@ fexp)
      ; e_field = (fun (e1,id) -> e1)
      ; e_case = (fun (e1,pexps) -> e1 @@ lapp2 pexps)
      ; e_let = (fun (lb,e2) -> lb @@ e2)
      ; e_assign = (fun ((ids,acc),e2) -> ([],ids) @@ acc @@ e2)
      ; e_sizeof = (fun nexp -> ([],[]))
      ; e_exit = (fun e1 -> ([],[]))
      ; e_return = (fun e1 -> e1)
      ; e_assert = (fun (e1,e2) -> ([],[]))
      ; e_internal_cast = (fun (_,e1) -> e1)
      ; e_internal_exp = (fun _ -> ([],[]))
      ; e_internal_exp_user = (fun _ -> ([],[]))
      ; e_internal_let =
          (fun (([id],acc),e2,e3) ->
           let (xs,ys) = ([id],[]) @@ acc @@ e2 @@ e3 in
           let ys = List.filter (fun id2 -> not (eqidtyp id id2)) ys in
           (xs,ys))
      ; e_internal_plet = (fun (_, e1, e2) -> e1 @@ e2)
      ; e_internal_return = (fun e -> e)
      ; lEXP_id = (fun id -> (Some id,[],([],[])))
      ; lEXP_memory = (fun (_,es) -> (None,[],lapp2 es))
      ; lEXP_cast = (fun (_,id) -> (Some id,[],([],[])))
      ; lEXP_tup = (fun tups -> failwith "FORCHRISTOPHER:: this needs implementing, not sure what you want to do")
      ; lEXP_vector = (fun ((ids,acc),e1) -> (None,ids,acc @@ e1))
      ; lEXP_vector_range = (fun ((ids,acc),e1,e2) -> (None,ids,acc @@ e1 @@ e2))
      ; lEXP_field = (fun ((ids,acc),_) -> (None,ids,acc))
      ; lEXP_aux =
          (function
            | ((Some id,ids,acc),(annot)) ->
               (match Env.lookup_id id (env_of_annot annot) with
               | Unbound | Local _ -> ((id,annot) :: ids,acc)
               | _ -> (ids,acc))
            | ((_,ids,acc),_) -> (ids,acc)
          )
      ; fE_Fexp = (fun (_,e) -> e)
      ; fE_aux = (fun (fexp,_) -> fexp)
      ; fES_Fexps = (fun (fexps,_) -> lapp2 fexps)
      ; fES_aux = (fun (fexp,_) -> fexp)
      ; def_val_empty = ([],[])
      ; def_val_dec = (fun e -> e)
      ; def_val_aux = (fun (defval,_) -> defval)
      ; pat_exp = (fun (_,e) -> e)
      ; pat_aux = (fun (pexp,_) -> pexp)
      ; lB_val_explicit = (fun (_,_,e) -> e)
      ; lB_val_implicit = (fun (_,e) -> e)
      ; lB_aux = (fun (lb,_) -> lb)
      ; pat_alg = id_pat_alg
      } exp in
  dedup eqidtyp updates

let swaptyp typ (l,tannot) = match tannot with
  | Some (env, typ', eff) -> (l, Some (env, typ, eff))
  | _ -> raise (Reporting_basic.err_unreachable l "swaptyp called with empty type annotation")

let mktup l es =
  match es with
  | [] -> E_aux (E_lit (L_aux (L_unit,Parse_ast.Generated l)),(simple_annot l unit_typ))
  | [e] -> e
  | e :: _ -> 
     let effs =
       List.fold_left (fun acc e -> union_effects acc (effect_of e)) no_effect es in
     let typ = mk_typ (Typ_tup (List.map typ_of es)) in
     E_aux (E_tuple es,(Parse_ast.Generated l, Some (env_of e, typ, effs)))

let mktup_pat l es =
  match es with
  | [] -> P_aux (P_wild,(simple_annot l unit_typ))
  | [E_aux (E_id id,_) as exp] ->
     P_aux (P_id id,(simple_annot l (typ_of exp)))
  | _ ->
     let typ = mk_typ (Typ_tup (List.map typ_of es)) in
     let pats = List.map (function
       | (E_aux (E_id id,_) as exp) ->
         P_aux (P_id id,(simple_annot l (typ_of exp)))
       | exp ->
         P_aux (P_wild,(simple_annot l (typ_of exp)))) es in
     P_aux (P_tup pats,(simple_annot l typ))


type 'a updated_term =
  | Added_vars of 'a exp * 'a pat
  | Same_vars of 'a exp

let rec rewrite_var_updates ((E_aux (expaux,((l,_) as annot))) as exp) =

  let rec add_vars overwrite ((E_aux (expaux,annot)) as exp) vars =
    match expaux with
    | E_let (lb,exp) ->
       let exp = add_vars overwrite exp vars in
       E_aux (E_let (lb,exp),swaptyp (typ_of exp) annot)
    | E_internal_let (lexp,exp1,exp2) ->
       let exp2 = add_vars overwrite exp2 vars in
       E_aux (E_internal_let (lexp,exp1,exp2), swaptyp (typ_of exp2) annot)
    | E_internal_plet (pat,exp1,exp2) ->
       let exp2 = add_vars overwrite exp2 vars in
       E_aux (E_internal_plet (pat,exp1,exp2), swaptyp (typ_of exp2) annot)
    | E_internal_return exp2 ->
       let exp2 = add_vars overwrite exp2 vars in
       E_aux (E_internal_return exp2,swaptyp (typ_of exp2) annot)
    | _ ->
       (* after rewrite_defs_letbind_effects there cannot be terms that have
          effects/update local variables in "tail-position": check n_exp_term
          and where it is used. *)
       if overwrite then
         match typ_of exp with
         | Typ_aux (Typ_id (Id_aux (Id "unit", _)), _) -> vars
         | _ -> raise (Reporting_basic.err_unreachable l
             "add_vars: trying to overwrite a non-unit expression in tail-position")
       else
         let typ' = Typ_aux (Typ_tup [typ_of exp;typ_of vars], Parse_ast.Generated l) in
         E_aux (E_tuple [exp;vars],swaptyp typ' annot) in
  
  let rewrite (E_aux (expaux,((el,_) as annot))) (P_aux (_,(pl,pannot)) as pat) =
    let overwrite = match typ_of_annot annot with
      | Typ_aux (Typ_id (Id_aux (Id "unit", _)), _) -> true
      | _ -> false in
    match expaux with
    | E_for(id,exp1,exp2,exp3,order,exp4) ->
       (* Translate for loops into calls to one of the foreach combinators.
          The loop body becomes a function of the loop variable and any
          mutable local variables that are updated inside the loop.
          Since the foreach* combinators are higher-order functions,
          they cannot be represented faithfully in the AST. The following
          code abuses the parameters of an E_app node, embedding the loop body
          function as an expression followed by the list of variables it
          expects. In (Lem) pretty-printing, this turned into an anonymous
          function and passed to foreach*. *)
       let vars = List.map (fun (var,(l,t)) -> E_aux (E_id var,(l,t))) (find_updated_vars exp4) in
       let vartuple = mktup el vars in
       let exp4 = rewrite_var_updates (add_vars overwrite exp4 vartuple) in
       let (E_aux (_,(_,annot4))) = exp4 in
       let fname = match effectful exp4,order with
         | false, Ord_aux (Ord_inc,_) -> "foreach_inc"
         | false, Ord_aux (Ord_dec,_) -> "foreach_dec"
         | true,  Ord_aux (Ord_inc,_) -> "foreachM_inc"
         | true,  Ord_aux (Ord_dec,_) -> "foreachM_dec" in
       let funcl = Id_aux (Id fname,Parse_ast.Generated el) in
       let loopvar =
         (* Don't bother with creating a range type annotation, since the
         Lem pretty-printing does not use it. *)
         (* let (bf,tf) = match typ_of exp1 with
           | {t = Tapp ("atom",[TA_nexp f])} -> (TA_nexp f,TA_nexp f)
           | {t = Tapp ("reg", [TA_typ {t = Tapp ("atom",[TA_nexp f])}])} -> (TA_nexp f,TA_nexp f)
           | {t = Tapp ("range",[TA_nexp bf;TA_nexp tf])} -> (TA_nexp bf,TA_nexp tf)
           | {t = Tapp ("reg", [TA_typ {t = Tapp ("range",[TA_nexp bf;TA_nexp tf])}])} -> (TA_nexp bf,TA_nexp tf)
           | {t = Tapp (name,_)} -> failwith (name ^ " shouldn't be here") in
         let (bt,tt) = match typ_of exp2 with
           | {t = Tapp ("atom",[TA_nexp t])} -> (TA_nexp t,TA_nexp t)
           | {t = Tapp ("atom",[TA_typ {t = Tapp ("atom", [TA_nexp t])}])} -> (TA_nexp t,TA_nexp t)
           | {t = Tapp ("range",[TA_nexp bt;TA_nexp tt])} -> (TA_nexp bt,TA_nexp tt)
           | {t = Tapp ("atom",[TA_typ {t = Tapp ("range",[TA_nexp bt;TA_nexp tt])}])} -> (TA_nexp bt,TA_nexp tt)
           | {t = Tapp (name,_)} -> failwith (name ^ " shouldn't be here") in
         let t = {t = Tapp ("range",match order with
                                    | Ord_aux (Ord_inc,_) -> [bf;tt]
                                    | Ord_aux (Ord_dec,_) -> [tf;bt])} in *)
         E_aux (E_id id, simple_annot l int_typ) in
       let v = E_aux (E_app (funcl,[loopvar;mktup el [exp1;exp2;exp3];exp4;vartuple]),
                      (Parse_ast.Generated el, annot4)) in
       let pat =
         if overwrite then mktup_pat el vars
         else P_aux (P_tup [pat; mktup_pat pl vars],
                     simple_annot pl (typ_of v)) in
       Added_vars (v,pat)
    | E_if (c,e1,e2) ->
       let vars = List.map (fun (var,(l,t)) -> E_aux (E_id var,(l,t)))
                           (dedup eqidtyp (find_updated_vars e1 @ find_updated_vars e2)) in
       if vars = [] then
         (Same_vars (E_aux (E_if (c,rewrite_var_updates e1,rewrite_var_updates e2),annot)))
       else
         let vartuple = mktup el vars in
         let e1 = rewrite_var_updates (add_vars overwrite e1 vartuple) in
         let e2 = rewrite_var_updates (add_vars overwrite e2 vartuple) in
         (* after rewrite_defs_letbind_effects c has no variable updates *)
         let env = env_of_annot annot in
         let typ = typ_of e1 in
         let eff = union_eff_exps [e1;e2] in
         let v = E_aux (E_if (c,e1,e2), (Parse_ast.Generated el, Some (env, typ, eff))) in
         let pat =
           if overwrite then mktup_pat el vars
           else P_aux (P_tup [pat; mktup_pat pl vars],
                       (simple_annot pl (typ_of v))) in
         Added_vars (v,pat)
    | E_case (e1,ps) ->
       (* after rewrite_defs_letbind_effects e1 needs no rewriting *)
       let vars =
                 let f acc (Pat_aux (Pat_exp (_,e),_)) = acc @ find_updated_vars e in
         List.map (fun (var,(l,t)) -> E_aux (E_id var,(l,t)))
                  (dedup eqidtyp (List.fold_left f [] ps)) in
       if vars = [] then
         let ps = List.map (fun (Pat_aux (Pat_exp (p,e),a)) -> Pat_aux (Pat_exp (p,rewrite_var_updates e),a)) ps in
         Same_vars (E_aux (E_case (e1,ps),annot))
       else
         let vartuple = mktup el vars in
         let typ = 
           let (Pat_aux (Pat_exp (_,first),_)) = List.hd ps in
           typ_of first in
         let (ps,typ,effs) =
           let f (acc,typ,effs) (Pat_aux (Pat_exp (p,e),pannot)) =
             let etyp = typ_of e in
             let () = assert (string_of_typ etyp = string_of_typ typ) in
             let e = rewrite_var_updates (add_vars overwrite e vartuple) in
             let pannot = simple_annot pl (typ_of e) in
             let effs = union_effects effs (effect_of e) in
             let pat' = Pat_aux (Pat_exp (p,e),pannot) in
             (acc @ [pat'],typ,effs) in
           List.fold_left f ([],typ,no_effect) ps in
         let v = E_aux (E_case (e1,ps), (Parse_ast.Generated pl, Some (env_of_annot annot, typ, effs))) in
         let pat =
           if overwrite then mktup_pat el vars
           else P_aux (P_tup [pat; mktup_pat pl vars],
                       (simple_annot pl (typ_of v))) in
         Added_vars (v,pat)
    | E_assign (lexp,vexp) ->
       let effs = match effect_of_annot (snd annot) with
         | Effect_aux (Effect_set effs, _) -> effs
         | _ ->
           raise (Reporting_basic.err_unreachable l
             "assignment without effects annotation") in
       if not (List.exists (function BE_aux (BE_lset,_) -> true | _ -> false) effs) then
         Same_vars (E_aux (E_assign (lexp,vexp),annot))
       else 
         (match lexp with
          | LEXP_aux (LEXP_id id,annot) ->
             let pat = P_aux (P_id id, simple_annot pl (typ_of vexp)) in
             Added_vars (vexp,pat)
          | LEXP_aux (LEXP_cast (_,id),annot) ->
             let pat = P_aux (P_id id, simple_annot pl (typ_of vexp)) in
             Added_vars (vexp,pat)
          | LEXP_aux (LEXP_vector (LEXP_aux (LEXP_id id,((l2,_) as annot2)),i),((l1,_) as annot)) ->
             let eid = E_aux (E_id id, simple_annot l2 (typ_of_annot annot2)) in
             let vexp = E_aux (E_vector_update (eid,i,vexp),
                               simple_annot l1 (typ_of_annot annot)) in
             let pat = P_aux (P_id id, simple_annot pl (typ_of vexp)) in
             Added_vars (vexp,pat)
          | LEXP_aux (LEXP_vector_range (LEXP_aux (LEXP_id id,((l2,_) as annot2)),i,j),
                      ((l,_) as annot)) -> 
             let eid = E_aux (E_id id, simple_annot l2 (typ_of_annot annot2)) in
             let vexp = E_aux (E_vector_update_subrange (eid,i,j,vexp),
                               simple_annot l (typ_of_annot annot)) in
             let pat = P_aux (P_id id, simple_annot pl (typ_of vexp)) in
             Added_vars (vexp,pat)
          | _ -> Same_vars (E_aux (E_assign (lexp,vexp),annot)))
    | _ ->
       (* after rewrite_defs_letbind_effects this expression is pure and updates
       no variables: check n_exp_term and where it's used. *)
       Same_vars (E_aux (expaux,annot))  in

  match expaux with
  | E_let (lb,body) ->
     let body = rewrite_var_updates body in
     let (eff,lb) = match lb with
       | LB_aux (LB_val_implicit (pat,v),lbannot) ->
          (match rewrite v pat with
           | Added_vars (v,pat) ->
              let (E_aux (_,(l,_))) = v in
              let lbannot = (simple_annot l (typ_of v)) in
              (effect_of v,LB_aux (LB_val_implicit (pat,v),lbannot))
           | Same_vars v -> (effect_of v,LB_aux (LB_val_implicit (pat,v),lbannot)))
       | LB_aux (LB_val_explicit (typ,pat,v),lbannot) ->
          (match rewrite v pat with 
           | Added_vars (v,pat) ->
              let (E_aux (_,(l,_))) = v in
              let lbannot = (simple_annot l (typ_of v)) in
              (effect_of v,LB_aux (LB_val_implicit (pat,v),lbannot))
           | Same_vars v -> (effect_of v,LB_aux (LB_val_explicit (typ,pat,v),lbannot))) in
     let tannot = Some (env_of_annot annot, typ_of body, union_effects eff (effect_of body)) in
     E_aux (E_let (lb,body),(Parse_ast.Generated l,tannot))
  | E_internal_let (lexp,v,body) ->
     (* Rewrite E_internal_let into E_let and call recursively *)
     let id = match lexp with
       | LEXP_aux (LEXP_id id,_) -> id
       | LEXP_aux (LEXP_cast (_,id),_) -> id in
     let env = env_of_annot annot in
     let vtyp = typ_of v in
     let veff = effect_of v in
     let bodyenv = env_of body in
     let bodytyp = typ_of body in
     let bodyeff = effect_of body in
     let pat = P_aux (P_id id, (simple_annot l vtyp)) in
     let lbannot = (Parse_ast.Generated l, Some (env, vtyp, veff)) in
     let lb = LB_aux (LB_val_implicit (pat,v),lbannot) in
     let exp = E_aux (E_let (lb,body),(Parse_ast.Generated l, Some (bodyenv, bodytyp, union_effects veff bodyeff))) in
     rewrite_var_updates exp
  | E_internal_plet (pat,v,body) ->
     failwith "rewrite_var_updates: E_internal_plet shouldn't be introduced yet"
  (* There are no expressions that have effects or variable updates in
     "tail-position": check the definition nexp_term and where it is used. *)
  | _ -> exp

let replace_memwrite_e_assign exp = 
  let e_aux = fun (expaux,annot) ->
    match expaux with
    | E_assign (LEXP_aux (LEXP_memory (id,args),_),v) -> E_aux (E_app (id,args @ [v]),annot)
    | _ -> E_aux (expaux,annot) in
  fold_exp { id_exp_alg with e_aux = e_aux } exp



let remove_reference_types exp =

  let rec rewrite_t (Typ_aux (t_aux,a)) = (Typ_aux (rewrite_t_aux t_aux,a))
  and rewrite_t_aux t_aux = match t_aux with
    | Typ_app (Id_aux (Id "reg",_), [Typ_arg_aux (Typ_arg_typ (Typ_aux (t_aux2, _)), _)]) ->
      rewrite_t_aux t_aux2
    | Typ_app (name,t_args) -> Typ_app (name,List.map rewrite_t_arg t_args)
    | Typ_fn (t1,t2,eff) -> Typ_fn (rewrite_t t1,rewrite_t t2,eff)
    | Typ_tup ts -> Typ_tup (List.map rewrite_t ts)
    | _ -> t_aux
  and rewrite_t_arg t_arg = match t_arg with
    | Typ_arg_aux (Typ_arg_typ t, a) -> Typ_arg_aux (Typ_arg_typ (rewrite_t t), a)
    | _ -> t_arg in

  let rec rewrite_annot = function
    | (l, None) -> (l, None)
    | (l, Some (env, typ, eff)) -> (l, Some (env, rewrite_t typ, eff)) in

  map_exp_annot rewrite_annot exp



let rewrite_defs_remove_superfluous_letbinds =

  let rec small (E_aux (exp,_)) = match exp with
    | E_id _
    | E_lit _ -> true
    | E_cast (_,e) -> small e
    | E_list es -> List.for_all small es
    | E_cons (e1,e2) -> small e1 && small e2
    | E_sizeof _ -> true
    | _ -> false in

  let e_aux (exp,annot) = match exp with
    | E_let (lb,exp2) ->
       begin match lb,exp2 with
       (* 'let x = EXP1 in x' can be replaced with 'EXP1' *)
       | LB_aux (LB_val_explicit (_,P_aux (P_id (Id_aux (id,_)),_),exp1),_),
         E_aux (E_id (Id_aux (id',_)),_)
       | LB_aux (LB_val_explicit (_,P_aux (P_id (Id_aux (id,_)),_),exp1),_),
         E_aux (E_cast (_,E_aux (E_id (Id_aux (id',_)),_)),_)
       | LB_aux (LB_val_implicit (P_aux (P_id (Id_aux (id,_)),_),exp1),_),
         E_aux (E_id (Id_aux (id',_)),_)
       | LB_aux (LB_val_implicit (P_aux (P_id (Id_aux (id,_)),_),exp1),_),
         E_aux (E_cast (_,E_aux (E_id (Id_aux (id',_)),_)),_)
            when id = id' ->
          exp1
       (* "let x = EXP1 in return x" can be replaced with 'return (EXP1)', at
          least when EXP1 is 'small' enough *)
       | LB_aux (LB_val_explicit (_,P_aux (P_id (Id_aux (id,_)),_),exp1),_),
         E_aux (E_internal_return (E_aux (E_id (Id_aux (id',_)),_)),_)
       | LB_aux (LB_val_implicit (P_aux (P_id (Id_aux (id,_)),_),exp1),_),
         E_aux (E_internal_return (E_aux (E_id (Id_aux (id',_)),_)),_)
            when id = id' && small exp1 ->
          let (E_aux (_,e1annot)) = exp1 in
          E_aux (E_internal_return (exp1),e1annot)
       | _ -> E_aux (exp,annot) 
       end
    | _ -> E_aux (exp,annot) in

  let alg = { id_exp_alg with e_aux = e_aux } in
  rewrite_defs_base
    { rewrite_exp = (fun _ -> fold_exp alg)
    ; rewrite_pat = rewrite_pat
    ; rewrite_let = rewrite_let
    ; rewrite_lexp = rewrite_lexp
    ; rewrite_fun = rewrite_fun
    ; rewrite_def = rewrite_def
    ; rewrite_defs = rewrite_defs_base
    }
  

let rewrite_defs_remove_superfluous_returns =

  let has_unittype e = match typ_of e with
    | Typ_aux (Typ_id (Id_aux (Id "unit", _)), _) -> true
    | _ -> false in

  let e_aux (exp,annot) = match exp with
    | E_internal_plet (pat,exp1,exp2) ->
       begin match pat,exp2 with
       | P_aux (P_lit (L_aux (lit,_)),_),
         E_aux (E_internal_return (E_aux (E_lit (L_aux (lit',_)),_)),_)
            when lit = lit' ->
          exp1
       | P_aux (P_wild,pannot),
         E_aux (E_internal_return (E_aux (E_lit (L_aux (L_unit,_)),_)),_)
            when has_unittype exp1 ->
          exp1
       | P_aux (P_id (Id_aux (id,_)),_),
         E_aux (E_internal_return (E_aux (E_id (Id_aux (id',_)),_)),_)
            when id = id' ->
          exp1
       | _ -> E_aux (exp,annot)
       end
    | _ -> E_aux (exp,annot) in

  let alg = { id_exp_alg with e_aux = e_aux } in
  rewrite_defs_base
    {rewrite_exp = (fun _ -> fold_exp alg)
    ; rewrite_pat = rewrite_pat
    ; rewrite_let = rewrite_let
    ; rewrite_lexp = rewrite_lexp
    ; rewrite_fun = rewrite_fun
    ; rewrite_def = rewrite_def
    ; rewrite_defs = rewrite_defs_base
    }


let rewrite_defs_remove_e_assign =
  let rewrite_exp _ e =
    replace_memwrite_e_assign (remove_reference_types (rewrite_var_updates e)) in
  rewrite_defs_base
    { rewrite_exp = rewrite_exp
    ; rewrite_pat = rewrite_pat
    ; rewrite_let = rewrite_let
    ; rewrite_lexp = rewrite_lexp
    ; rewrite_fun = rewrite_fun
    ; rewrite_def = rewrite_def
    ; rewrite_defs = rewrite_defs_base
    }


let rewrite_defs_lem =
  top_sort_defs >>
  rewrite_sizeof >>
  rewrite_defs_remove_vector_concat >>
  rewrite_defs_remove_bitvector_pats >>
  rewrite_defs_exp_lift_assign >> 
  rewrite_defs_remove_blocks >> 
  rewrite_defs_letbind_effects >> 
  rewrite_defs_remove_e_assign >> 
  rewrite_defs_effectful_let_expressions >> 
  rewrite_defs_remove_superfluous_letbinds >>
  rewrite_defs_remove_superfluous_returns
  
