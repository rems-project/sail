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
(*  SPDX-License-Identifier: BSD-2-Clause                                   *)
(****************************************************************************)

open Parse_ast
open Parse_ast.Attribute_data

module Big_int = Nat_big_num

let ( &&& ) (lhs : l option) (rhs : l option Lazy.t) : l option =
  match lhs with
  | Some l -> Some l
  | None -> (
      match rhs with (lazy (Some l)) -> Some l | (lazy None) -> None
    )

let diff_list ~at:l f (xs : 'a list) (ys : 'a list) : l option =
  let rec go xs ys = match (xs, ys) with x :: xs, y :: ys -> f x y &&& lazy (go xs ys) | _ -> None in
  if List.compare_lengths xs ys = 0 then go xs ys else Some l

let diff_kind (K_aux (k1, l)) (K_aux (k2, _)) = if k1 = k2 then None else Some l

let diff_kid (Kid_aux (Var v1, l)) (Kid_aux (Var v2, _)) = if v1 = v2 then None else Some l

let diff_id (Id_aux (id1, l)) (Id_aux (id2, l)) = if id1 = id2 then None else Some l

let diff_lit (L_aux (lit1, l)) (L_aux (lit2, _)) = if lit1 = lit2 then None else Some l

let diff_infix_token ~at:l f lhs rhs =
  match (lhs, rhs) with IT_primary x1, IT_primary x2 -> f x1 x2 | _ -> if lhs = rhs then None else Some l

let rec strip_atyp_parens = function ATyp_aux (ATyp_parens atyp, _) -> strip_atyp_parens atyp | atyp -> atyp

let diff_eq ~at:l x y = if x = y then None else Some l

let diff_eq_pred ~at:l pred x y = if pred x y then None else Some l

let diff_option ~at:l f x y = match (x, y) with Some x, Some y -> f x y | None, None -> None | _ -> Some l

let diff_kinded_id (KOpt_aux (lhs, l)) (KOpt_aux (rhs, _)) =
  (* Final field is for kind-inference *)
  let (KOpt_kind (kw1, vars1, opt_kind1, _)) = lhs in
  let (KOpt_kind (kw2, vars2, opt_kind2, _)) = rhs in
  diff_eq ~at:l kw1 kw2
  &&& lazy (diff_list ~at:l diff_kid vars1 vars2)
  &&& lazy (diff_option ~at:l diff_kind opt_kind1 opt_kind2)

(* Note that rather than using [match (lhs, rhs) with] this is written
   in this style so OCaml will warn us for any missing cases,
   particularly in the future if the parse AST changes. *)
let rec diff_atyp lhs rhs =
  let (ATyp_aux (lhs, l)) = strip_atyp_parens lhs in
  let (ATyp_aux (rhs, _)) = strip_atyp_parens rhs in
  match lhs with
  | ATyp_parens _ -> assert false
  | ATyp_id id1 -> (
      match rhs with ATyp_id id2 -> diff_id id1 id2 | _ -> Some l
    )
  | ATyp_var kid1 -> (
      match rhs with ATyp_var kid2 -> diff_kid kid1 kid2 | _ -> Some l
    )
  | ATyp_lit lit1 -> (
      match rhs with ATyp_lit lit2 -> diff_lit lit1 lit2 | _ -> Some l
    )
  | ATyp_nset nums1 -> (
      match rhs with ATyp_nset nums2 -> diff_eq_pred ~at:l (Util.equal_list Big_int.equal) nums1 nums2 | _ -> Some l
    )
  | ATyp_in (n1, set1) -> (
      match rhs with ATyp_in (n2, set2) -> diff_atyp n1 n2 &&& lazy (diff_atyp set1 set2) | _ -> Some l
    )
  | ATyp_times (x1, y1) -> (
      match rhs with ATyp_times (x2, y2) -> diff_atyp x1 x2 &&& lazy (diff_atyp y1 y2) | _ -> Some l
    )
  | ATyp_sum (x1, y1) -> (
      match rhs with ATyp_sum (x2, y2) -> diff_atyp x1 x2 &&& lazy (diff_atyp y1 y2) | _ -> Some l
    )
  | ATyp_minus (x1, y1) -> (
      match rhs with ATyp_minus (x2, y2) -> diff_atyp x1 x2 &&& lazy (diff_atyp y1 y2) | _ -> Some l
    )
  | ATyp_exp atyp1 -> (
      match rhs with ATyp_exp atyp2 -> diff_atyp atyp1 atyp2 | _ -> Some l
    )
  | ATyp_neg atyp1 -> (
      match rhs with ATyp_neg atyp2 -> diff_atyp atyp1 atyp2 | _ -> Some l
    )
  | ATyp_infix tokens1 -> (
      match rhs with
      | ATyp_infix tokens2 ->
          diff_list ~at:l
            (fun (tok1, s1, e1) (tok2, _, _) -> diff_infix_token ~at:(Range (s1, e1)) diff_atyp tok1 tok2)
            tokens1 tokens2
      | _ -> Some l
    )
  | ATyp_inc -> if rhs = ATyp_inc then None else Some l
  | ATyp_dec -> if rhs = ATyp_dec then None else Some l
  | ATyp_set ids1 -> (
      match rhs with ATyp_set ids2 -> diff_list ~at:l diff_id ids1 ids2 | _ -> Some l
    )
  (* We ignore the effect argument on functions and bidirectional types *)
  | ATyp_fn (dom1, codom1, _) -> (
      match rhs with ATyp_fn (dom2, codom2, _) -> diff_atyp dom1 dom2 &&& lazy (diff_atyp codom1 codom2) | _ -> Some l
    )
  | ATyp_bidir (left1, right1, _) -> (
      match rhs with
      | ATyp_bidir (left2, right2, _) -> diff_atyp left1 left2 &&& lazy (diff_atyp right1 right2)
      | _ -> Some l
    )
  | ATyp_wild -> if rhs = ATyp_wild then None else Some l
  | ATyp_tuple atyps1 -> (
      match rhs with ATyp_tuple atyps2 -> diff_list ~at:l diff_atyp atyps1 atyps2 | _ -> Some l
    )
  | ATyp_app (id1, atyps1) -> (
      match rhs with
      | ATyp_app (id2, atyps2) -> diff_id id1 id2 &&& lazy (diff_list ~at:l diff_atyp atyps1 atyps2)
      | _ -> Some l
    )
  | ATyp_if (i1, t1, e1) -> (
      match rhs with
      | ATyp_if (i2, t2, e2) -> diff_atyp i1 i2 &&& lazy (diff_atyp t1 t2) &&& lazy (diff_atyp e1 e2)
      | _ -> Some l
    )
  | ATyp_exist (vars1, c1, t1) -> (
      match rhs with
      | ATyp_exist (vars2, c2, t2) ->
          diff_list ~at:l diff_kinded_id vars1 vars2 &&& lazy (diff_atyp c1 c2) &&& lazy (diff_atyp t1 t2)
      | _ -> Some l
    )

let diff_quant_item (QI_aux (lhs, l)) (QI_aux (rhs, _)) =
  match lhs with
  | QI_id kopt1 -> (
      match rhs with QI_id kopt2 -> diff_kinded_id kopt1 kopt2 | _ -> Some l
    )
  | QI_constraint c1 -> (
      match rhs with QI_constraint c2 -> diff_atyp c1 c2 | _ -> Some l
    )

let diff_typquant (TypQ_aux (lhs, l)) (TypQ_aux (rhs, _)) =
  match lhs with
  | TypQ_tq items1 -> (
      match rhs with TypQ_tq items2 -> diff_list ~at:l diff_quant_item items1 items2 | _ -> Some l
    )
  | TypQ_no_forall -> diff_eq ~at:l lhs rhs

let diff_typschm (TypSchm_aux (lhs, l)) (TypSchm_aux (rhs, _)) =
  let (TypSchm_ts (quant1, atyp1)) = lhs in
  let (TypSchm_ts (quant2, atyp2)) = rhs in
  diff_typquant quant1 quant2 &&& lazy (diff_atyp atyp1 atyp2)

let rec diff_index_range (BF_aux (lhs, l)) (BF_aux (rhs, _)) =
  match lhs with
  | BF_single n1 -> (
      match rhs with BF_single n2 -> diff_atyp n1 n2 | _ -> Some l
    )
  | BF_range (n1, m1) -> (
      match rhs with BF_range (n2, m2) -> diff_atyp n1 n2 &&& lazy (diff_atyp m1 m2) | _ -> Some l
    )
  | BF_concat (left1, right1) -> (
      match rhs with
      | BF_concat (left2, right2) -> diff_index_range left1 left2 &&& lazy (diff_index_range right1 right2)
      | _ -> Some l
    )

let rec diff_attribute_data (AD_aux (lhs, l)) (AD_aux (rhs, _)) =
  match lhs with
  | AD_object obj1 -> (
      match rhs with
      | AD_object obj2 ->
          diff_list ~at:l (fun (k1, v1) (k2, v2) -> diff_eq ~at:l k1 k2 &&& lazy (diff_attribute_data v1 v2)) obj1 obj2
      | _ -> Some l
    )
  | AD_list ads1 -> (
      match rhs with AD_list ads2 -> diff_list ~at:l diff_attribute_data ads1 ads2 | _ -> Some l
    )
  | AD_num n -> (
      match rhs with AD_num m -> diff_eq_pred ~at:l Big_int.equal n m | _ -> Some l
    )
  | AD_string _ -> diff_eq ~at:l lhs rhs
  | AD_bool _ -> diff_eq ~at:l lhs rhs

let rec diff_pat (P_aux (lhs, l)) (P_aux (rhs, _)) =
  match lhs with
  | P_lit lit1 -> (
      match rhs with P_lit lit2 -> diff_lit lit1 lit2 | _ -> Some l
    )
  | P_wild -> diff_eq ~at:l lhs rhs
  | P_typ (atyp1, p1) -> (
      match rhs with P_typ (atyp2, p2) -> diff_pat p1 p2 &&& lazy (diff_atyp atyp1 atyp2) | _ -> Some l
    )
  | P_id id1 -> (
      match rhs with P_id id2 -> diff_id id1 id2 | _ -> Some l
    )
  | P_var (p1, atyp1) -> (
      match rhs with P_var (p2, atyp2) -> diff_pat p1 p2 &&& lazy (diff_atyp atyp1 atyp2) | _ -> Some l
    )
  | P_app (id1, ps1) -> (
      match rhs with P_app (id2, ps2) -> diff_id id1 id2 &&& lazy (diff_list ~at:l diff_pat ps1 ps2) | _ -> Some l
    )
  | P_vector ps1 -> (
      match rhs with P_vector ps2 -> diff_list ~at:l diff_pat ps1 ps2 | _ -> Some l
    )
  | P_vector_concat ps1 -> (
      match rhs with P_vector_concat ps2 -> diff_list ~at:l diff_pat ps1 ps2 | _ -> Some l
    )
  | P_vector_subrange (id1, n1, m1) -> (
      match rhs with
      | P_vector_subrange (id2, n2, m2) -> diff_id id1 id2 &&& lazy (diff_eq ~at:l n1 n2) &&& lazy (diff_eq ~at:l m1 m2)
      | _ -> Some l
    )
  | P_tuple ps1 -> (
      match rhs with P_tuple ps2 -> diff_list ~at:l diff_pat ps1 ps2 | _ -> Some l
    )
  | P_list ps1 -> (
      match rhs with P_list ps2 -> diff_list ~at:l diff_pat ps1 ps2 | _ -> Some l
    )
  | P_cons (hd1, tl1) -> (
      match rhs with P_cons (hd2, tl2) -> diff_pat hd1 hd2 &&& lazy (diff_pat tl1 tl2) | _ -> Some l
    )
  | P_string_append ps1 -> (
      match rhs with P_string_append ps2 -> diff_list ~at:l diff_pat ps1 ps2 | _ -> Some l
    )
  | P_struct (id_opt1, fps1) -> (
      match rhs with
      | P_struct (id_opt2, fps2) ->
          diff_option ~at:l diff_id id_opt1 id_opt2 &&& lazy (diff_list ~at:l diff_fpat fps1 fps2)
      | _ -> Some l
    )
  | P_attribute (attr1, arg1, p1) -> (
      match rhs with
      | P_attribute (attr2, arg2, p2) ->
          diff_eq ~at:l attr1 attr2 &&& lazy (diff_option ~at:l diff_attribute_data arg1 arg2) &&& lazy (diff_pat p1 p2)
      | _ -> Some l
    )

and diff_fpat (FP_aux (lhs, l)) (FP_aux (rhs, _)) =
  match lhs with
  | FP_field (id1, pat1) -> (
      match rhs with FP_field (id2, pat2) -> diff_id id1 id2 &&& lazy (diff_pat pat1 pat2) | _ -> Some l
    )
  | FP_wild -> diff_eq ~at:l lhs rhs

(* Consider [{x}] and [x] the same as we allow the formatter to insert
   blocks around if-then-else in certain cases. *)
let rec strip_singleton_block = function E_aux (E_block [exp], _) -> strip_singleton_block exp | exp -> exp

let rec diff_exp lhs rhs =
  let (E_aux (lhs, l)) = strip_singleton_block lhs in
  let (E_aux (rhs, _)) = strip_singleton_block rhs in
  match lhs with
  | E_block exps1 -> (
      match rhs with E_block exps2 -> diff_list ~at:l diff_exp exps1 exps2 | _ -> Some l
    )
  | E_id id1 -> (
      match rhs with E_id id2 -> diff_id id1 id2 | _ -> Some l
    )
  | E_ref reg1 -> (
      match rhs with E_ref reg2 -> diff_id reg1 reg2 | _ -> Some l
    )
  | E_deref exp1 -> (
      match rhs with E_deref exp2 -> diff_exp exp1 exp2 | _ -> Some l
    )
  | E_lit lit1 -> (
      match rhs with E_lit lit2 -> diff_lit lit1 lit2 | _ -> Some l
    )
  | E_typ (atyp1, exp1) -> (
      match rhs with E_typ (atyp2, exp2) -> diff_exp exp1 exp2 &&& lazy (diff_atyp atyp1 atyp2) | _ -> Some l
    )
  | E_app (f1, args1) -> (
      match rhs with E_app (f2, args2) -> diff_id f1 f2 &&& lazy (diff_list ~at:l diff_exp args1 args2) | _ -> Some l
    )
  | E_app_infix (left1, op1, right1) -> (
      match rhs with
      | E_app_infix (left2, op2, right2) ->
          diff_id op1 op2 &&& lazy (diff_exp left1 left2) &&& lazy (diff_exp right1 right2)
      | _ -> Some l
    )
  | E_infix tokens1 -> (
      match rhs with
      | E_infix tokens2 ->
          diff_list ~at:l
            (fun (tok1, s1, e1) (tok2, _, _) -> diff_infix_token ~at:(Range (s1, e1)) diff_exp tok1 tok2)
            tokens1 tokens2
      | _ -> Some l
    )
  | E_tuple exps1 -> (
      match rhs with E_tuple exps2 -> diff_list ~at:l diff_exp exps1 exps2 | _ -> Some l
    )
  | E_if (i1, t1, e1, _) -> (
      match rhs with E_if (i2, t2, e2, _) -> diff_list ~at:l diff_exp [i1; t1; e1] [i2; t2; e2] | _ -> Some l
    )
  | E_loop (loop_type1, measure1, cond1, body1) -> (
      match rhs with
      | E_loop (loop_type2, measure2, cond2, body2) ->
          diff_eq ~at:l loop_type1 loop_type2
          &&& lazy (diff_measure measure1 measure2)
          &&& lazy (diff_exp cond1 cond2)
          &&& lazy (diff_exp body1 body2)
      | _ -> Some l
    )
  | E_for (v1, f1, t1, s1, ord1, body1) -> (
      match rhs with
      | E_for (v2, f2, t2, s2, ord2, body2) ->
          diff_id v1 v2
          &&& lazy (diff_list ~at:l diff_exp [f1; t1; s1; body1] [f2; t2; s2; body2])
          &&& lazy (diff_atyp ord1 ord2)
      | _ -> Some l
    )
  | E_vector exps1 -> (
      match rhs with E_vector exps2 -> diff_list ~at:l diff_exp exps1 exps2 | _ -> Some l
    )
  | E_vector_access (v1, n1) -> (
      match rhs with E_vector_access (v2, n2) -> diff_exp v1 v2 &&& lazy (diff_exp n1 n2) | _ -> Some l
    )
  | E_vector_subrange (v1, n1, m1) -> (
      match rhs with
      | E_vector_subrange (v2, n2, m2) -> diff_exp v1 v2 &&& lazy (diff_exp n1 n2) &&& lazy (diff_exp m1 m2)
      | _ -> Some l
    )
  | E_vector_update (v1, n1, x1) -> (
      match rhs with
      | E_vector_update (v2, n2, x2) -> diff_exp v1 v2 &&& lazy (diff_exp n1 n2) &&& lazy (diff_exp x1 x2)
      | _ -> Some l
    )
  | E_vector_update_subrange (v1, n1, m1, x1) -> (
      match rhs with
      | E_vector_update_subrange (v2, n2, m2, x2) ->
          diff_exp v1 v2 &&& lazy (diff_exp n1 n2) &&& lazy (diff_exp m1 m2) &&& lazy (diff_exp x1 x2)
      | _ -> Some l
    )
  | E_vector_append (x1, y1) -> (
      match rhs with E_vector_append (x2, y2) -> diff_exp x1 x2 &&& lazy (diff_exp x1 x2) | _ -> Some l
    )
  | E_list exps1 -> (
      match rhs with E_list exps2 -> diff_list ~at:l diff_exp exps1 exps2 | _ -> Some l
    )
  | E_cons (hd1, tl1) -> (
      match rhs with E_cons (hd2, tl2) -> diff_exp hd1 hd2 &&& lazy (diff_exp tl1 tl2) | _ -> Some l
    )
  | E_struct (id_opt1, exps1) -> (
      match rhs with
      | E_struct (id_opt2, exps2) ->
          diff_option ~at:l diff_id id_opt1 id_opt2 &&& lazy (diff_list ~at:l diff_exp exps1 exps2)
      | _ -> Some l
    )
  | E_struct_update (s1, updates1) -> (
      match rhs with
      | E_struct_update (s2, updates2) -> diff_exp s1 s2 &&& lazy (diff_list ~at:l diff_exp updates1 updates2)
      | _ -> Some l
    )
  | E_field (exp1, field1) -> (
      match rhs with E_field (exp2, field2) -> diff_exp exp1 exp2 &&& lazy (diff_id field1 field2) | _ -> Some l
    )
  | E_match (head_exp1, arms1) -> (
      match rhs with
      | E_match (head_exp2, arms2) -> diff_exp head_exp1 head_exp2 &&& lazy (diff_list ~at:l diff_pexp arms1 arms2)
      | _ -> Some l
    )
  | E_let (lb1, body1) -> (
      match rhs with E_let (lb2, body2) -> diff_letbind lb1 lb2 &&& lazy (diff_exp body1 body2) | _ -> Some l
    )
  | E_assign (lexp1, exp1) -> (
      match rhs with E_assign (lexp2, exp2) -> diff_exp lexp1 lexp2 &&& lazy (diff_exp exp1 exp2) | _ -> Some l
    )
  | E_sizeof atyp1 -> (
      match rhs with E_sizeof atyp2 -> diff_atyp atyp1 atyp2 | _ -> Some l
    )
  | E_constraint atyp1 -> (
      match rhs with E_constraint atyp2 -> diff_atyp atyp1 atyp2 | _ -> Some l
    )
  | E_exit exp1 -> (
      match rhs with E_exit exp2 -> diff_exp exp1 exp2 | _ -> Some l
    )
  | E_config s1 -> (
      match rhs with E_config s2 -> diff_eq ~at:l s1 s2 | _ -> Some l
    )
  | E_throw exp1 -> (
      match rhs with E_throw exp2 -> diff_exp exp1 exp2 | _ -> Some l
    )
  | E_try (head_exp1, arms1) -> (
      match rhs with
      | E_try (head_exp2, arms2) -> diff_exp head_exp1 head_exp2 &&& lazy (diff_list ~at:l diff_pexp arms1 arms2)
      | _ -> Some l
    )
  | E_return exp1 -> (
      match rhs with E_return exp2 -> diff_exp exp1 exp2 | _ -> Some l
    )
  | E_assert (cond1, msg1) -> (
      match rhs with E_assert (cond2, msg2) -> diff_exp cond1 cond2 &&& lazy (diff_exp msg1 msg2) | _ -> Some l
    )
  | E_var (lexp1, v1, body1) -> (
      match rhs with
      | E_var (lexp2, v2, body2) -> diff_exp lexp1 lexp2 &&& lazy (diff_exp v1 v2) &&& lazy (diff_exp body1 body2)
      | _ -> Some l
    )
  | E_attribute (attr1, arg1, exp1) -> (
      match rhs with
      | E_attribute (attr2, arg2, exp2) ->
          diff_eq ~at:l attr1 attr2
          &&& lazy (diff_option ~at:l diff_attribute_data arg1 arg2)
          &&& lazy (diff_exp exp1 exp2)
      | _ -> Some l
    )
  | E_internal_plet (pat1, v1, body1) -> (
      match rhs with
      | E_internal_plet (pat2, v2, body2) -> diff_pat pat1 pat2 &&& lazy (diff_exp v1 v2) &&& lazy (diff_exp body1 body2)
      | _ -> Some l
    )
  | E_internal_return exp1 -> (
      match rhs with E_internal_return exp2 -> diff_exp exp1 exp2 | _ -> Some l
    )
  | E_internal_assume (atyp1, exp1) -> (
      match rhs with
      | E_internal_assume (atyp2, exp2) -> diff_atyp atyp1 atyp2 &&& lazy (diff_exp exp1 exp2)
      | _ -> Some l
    )

and diff_measure (Measure_aux (lhs, l)) (Measure_aux (rhs, _)) =
  match lhs with
  | Measure_none -> diff_eq ~at:l lhs rhs
  | Measure_some exp1 -> (
      match rhs with Measure_some exp2 -> diff_exp exp1 exp2 | Measure_none -> Some l
    )

and diff_pexp (Pat_aux (lhs, l)) (Pat_aux (rhs, _)) =
  match lhs with
  | Pat_exp (pat1, exp1) -> (
      match rhs with Pat_exp (pat2, exp2) -> diff_pat pat1 pat2 &&& lazy (diff_exp exp1 exp2) | _ -> Some l
    )
  | Pat_when (pat1, guard1, exp1) -> (
      match rhs with
      | Pat_when (pat2, guard2, exp2) ->
          diff_pat pat1 pat2 &&& lazy (diff_exp guard1 guard2) &&& lazy (diff_exp exp1 exp2)
      | _ -> Some l
    )
  | Pat_attribute (attr1, arg1, pexp1) -> (
      match rhs with
      | Pat_attribute (attr2, arg2, pexp2) ->
          diff_eq ~at:l attr1 attr2
          &&& lazy (diff_option ~at:l diff_attribute_data arg1 arg2)
          &&& lazy (diff_pexp pexp1 pexp2)
      | _ -> Some l
    )

and diff_letbind (LB_aux (lhs, _)) (LB_aux (rhs, _)) =
  let (LB_val (pat1, exp1)) = lhs in
  let (LB_val (pat2, exp2)) = rhs in
  diff_pat pat1 pat2 &&& lazy (diff_exp exp1 exp2)

let rec diff_mpat (MP_aux (lhs, l)) (MP_aux (rhs, _)) =
  match lhs with
  | MP_lit lit1 -> (
      match rhs with MP_lit lit2 -> diff_lit lit1 lit2 | _ -> Some l
    )
  | MP_typ (p1, atyp1) -> (
      match rhs with MP_typ (p2, atyp2) -> diff_mpat p1 p2 &&& lazy (diff_atyp atyp1 atyp2) | _ -> Some l
    )
  | MP_id id1 -> (
      match rhs with MP_id id2 -> diff_id id1 id2 | _ -> Some l
    )
  | MP_app (id1, ps1) -> (
      match rhs with MP_app (id2, ps2) -> diff_id id1 id2 &&& lazy (diff_list ~at:l diff_mpat ps1 ps2) | _ -> Some l
    )
  | MP_vector ps1 -> (
      match rhs with MP_vector ps2 -> diff_list ~at:l diff_mpat ps1 ps2 | _ -> Some l
    )
  | MP_vector_concat ps1 -> (
      match rhs with MP_vector_concat ps2 -> diff_list ~at:l diff_mpat ps1 ps2 | _ -> Some l
    )
  | MP_vector_subrange (id1, n1, m1) -> (
      match rhs with
      | MP_vector_subrange (id2, n2, m2) -> diff_id id1 id2 &&& lazy (diff_eq ~at:l n1 n2) &&& lazy (diff_eq ~at:l m1 m2)
      | _ -> Some l
    )
  | MP_tuple ps1 -> (
      match rhs with MP_tuple ps2 -> diff_list ~at:l diff_mpat ps1 ps2 | _ -> Some l
    )
  | MP_list ps1 -> (
      match rhs with MP_list ps2 -> diff_list ~at:l diff_mpat ps1 ps2 | _ -> Some l
    )
  | MP_cons (hd1, tl1) -> (
      match rhs with MP_cons (hd2, tl2) -> diff_mpat hd1 hd2 &&& lazy (diff_mpat tl1 tl2) | _ -> Some l
    )
  | MP_string_append ps1 -> (
      match rhs with MP_string_append ps2 -> diff_list ~at:l diff_mpat ps1 ps2 | _ -> Some l
    )
  | MP_struct (id_opt1, fps1) -> (
      match rhs with
      | MP_struct (id_opt2, fps2) ->
          diff_option ~at:l diff_id id_opt1 id_opt2
          &&& lazy (diff_list ~at:l (fun (f1, p1) (f2, p2) -> diff_id f1 f2 &&& lazy (diff_mpat p1 p2)) fps1 fps2)
      | _ -> Some l
    )
  | MP_as (p1, id1) -> (
      match rhs with MP_as (p2, id2) -> diff_mpat p1 p2 &&& lazy (diff_id id1 id2) | _ -> Some l
    )

let diff_mpexp (MPat_aux (lhs, l)) (MPat_aux (rhs, _)) =
  match lhs with
  | MPat_pat p1 -> (
      match rhs with MPat_pat p2 -> diff_mpat p1 p2 | _ -> Some l
    )
  | MPat_when (p1, exp1) -> (
      match rhs with MPat_when (p2, exp2) -> diff_mpat p1 p2 &&& lazy (diff_exp exp1 exp2) | _ -> Some l
    )

let rec diff_mapcl (MCL_aux (lhs, l)) (MCL_aux (rhs, _)) =
  match lhs with
  | MCL_attribute (attr1, arg1, mcl1) -> (
      match rhs with
      | MCL_attribute (attr2, arg2, mcl2) ->
          diff_eq ~at:l attr1 attr2
          &&& lazy (diff_option ~at:l diff_attribute_data arg1 arg2)
          &&& lazy (diff_mapcl mcl1 mcl2)
      | _ -> Some l
    )
  | MCL_doc (comment1, mcl1) -> (
      match rhs with
      | MCL_doc (comment2, mcl2) -> diff_eq ~at:l comment1 comment2 &&& lazy (diff_mapcl mcl1 mcl2)
      | _ -> Some l
    )
  | MCL_bidir (left_mpexp1, right_mpexp1) -> (
      match rhs with
      | MCL_bidir (left_mpexp2, right_mpexp2) ->
          diff_mpexp left_mpexp1 left_mpexp2 &&& lazy (diff_mpexp right_mpexp1 right_mpexp2)
      | _ -> Some l
    )
  | MCL_forwards_deprecated _ ->
      Reporting.warn "Deprecated" l "Cannot check AST equivalence here, as a deprecated construct was found.";
      None
  | MCL_forwards pexp1 -> (
      match rhs with
      | MCL_forwards pexp2 -> diff_pexp pexp1 pexp2
      | MCL_forwards_deprecated _ ->
          Reporting.warn "Deprecated" l "Cannot check AST equivalence here, as a deprecated construct was found.";
          None
      | _ -> Some l
    )
  | MCL_backwards pexp1 -> (
      match rhs with MCL_backwards pexp2 -> diff_pexp pexp1 pexp2 | _ -> Some l
    )
  | MCL_when (mcl1, exp1) -> (
      match rhs with MCL_when (mcl2, exp2) -> diff_mapcl mcl1 mcl2 &&& lazy (diff_exp exp1 exp2) | _ -> Some l
    )

let diff_mapdef (MD_aux (lhs, l)) (MD_aux (rhs, _)) =
  let (MD_mapping (id1, opt_typschm1, mcls1)) = lhs in
  let (MD_mapping (id2, opt_typschm2, mcls2)) = rhs in
  diff_id id1 id2
  &&& lazy (diff_option ~at:l diff_typschm opt_typschm1 opt_typschm2)
  &&& lazy (diff_list ~at:l diff_mapcl mcls1 mcls2)

let diff_val_spec (VS_aux (lhs, l)) (VS_aux (rhs, _)) =
  let (VS_val_spec (typschm1, id1, extern1)) = lhs in
  let (VS_val_spec (typschm2, id2, extern2)) = rhs in
  diff_id id1 id2 &&& lazy (diff_typschm typschm1 typschm2) &&& lazy (diff_option ~at:l (diff_eq ~at:l) extern1 extern2)

let rec diff_field_annot ~at:outer_l f lhs rhs =
  match lhs with
  | Ann_attribute (attr1, arg1, x1, l) -> (
      match rhs with
      | Ann_attribute (attr2, arg2, x2, _) ->
          diff_eq ~at:l attr1 attr2
          &&& lazy (diff_option ~at:l diff_attribute_data arg1 arg2)
          &&& lazy (diff_field_annot ~at:outer_l f x1 x2)
      | _ -> Some l
    )
  | Ann_doc (comment1, x1, l) -> (
      match rhs with
      | Ann_doc (comment2, x2, _) -> diff_eq ~at:l comment1 comment2 &&& lazy (diff_field_annot ~at:outer_l f x1 x2)
      | _ -> Some l
    )
  | Ann_item x1 -> (
      match rhs with Ann_item x2 -> f x1 x2 | _ -> Some outer_l
    )

let diff_tannot_opt (Typ_annot_opt_aux (lhs, l)) (Typ_annot_opt_aux (rhs, _)) =
  match lhs with
  | Typ_annot_opt_none -> diff_eq ~at:l lhs rhs
  | Typ_annot_opt_some (typq1, atyp1) -> (
      match rhs with
      | Typ_annot_opt_some (typq2, atyp2) -> diff_typquant typq1 typq2 &&& lazy (diff_atyp atyp1 atyp2)
      | Typ_annot_opt_none -> Some l
    )

let diff_rec_opt (Rec_aux (lhs, l)) (Rec_aux (rhs, _)) =
  match lhs with
  | Rec_none -> diff_eq ~at:l lhs rhs
  | Rec_measure (pat1, exp1) -> (
      match rhs with Rec_measure (pat2, exp2) -> diff_pat pat1 pat2 &&& lazy (diff_exp exp1 exp2) | Rec_none -> Some l
    )

let rec diff_funcl (FCL_aux (lhs, l)) (FCL_aux (rhs, _)) =
  match lhs with
  | FCL_private fcl1 -> (
      match rhs with FCL_private fcl2 -> diff_funcl fcl1 fcl2 | _ -> Some l
    )
  | FCL_attribute (attr1, arg1, fcl1) -> (
      match rhs with
      | FCL_attribute (attr2, arg2, fcl2) ->
          diff_eq ~at:l attr1 attr2
          &&& lazy (diff_option ~at:l diff_attribute_data arg1 arg2)
          &&& lazy (diff_funcl fcl1 fcl2)
      | _ -> Some l
    )
  | FCL_doc (comment1, fcl1) -> (
      match rhs with
      | FCL_doc (comment2, fcl2) -> diff_eq ~at:l comment1 comment2 &&& lazy (diff_funcl fcl1 fcl2)
      | _ -> Some l
    )
  | FCL_funcl (id1, pexp1) -> (
      match rhs with FCL_funcl (id2, pexp2) -> diff_id id1 id2 &&& lazy (diff_pexp pexp1 pexp2) | _ -> Some l
    )

let rec diff_type_union (Tu_aux (lhs, l)) (Tu_aux (rhs, _)) =
  match lhs with
  | Tu_private tu1 -> (
      match rhs with Tu_private tu2 -> diff_type_union tu1 tu2 | _ -> Some l
    )
  | Tu_attribute (attr1, arg1, tu1) -> (
      match rhs with
      | Tu_attribute (attr2, arg2, tu2) ->
          diff_eq ~at:l attr1 attr2
          &&& lazy (diff_option ~at:l diff_attribute_data arg1 arg2)
          &&& lazy (diff_type_union tu1 tu2)
      | _ -> Some l
    )
  | Tu_doc (comment1, tu1) -> (
      match rhs with
      | Tu_doc (comment2, tu2) -> diff_eq ~at:l comment1 comment2 &&& lazy (diff_type_union tu1 tu2)
      | _ -> Some l
    )
  | Tu_ty_id (atyp1, id1) -> (
      match rhs with Tu_ty_id (atyp2, id2) -> diff_id id1 id2 &&& lazy (diff_atyp atyp1 atyp2) | _ -> Some l
    )
  | Tu_ty_anon_rec (fields1, id1) -> (
      match rhs with
      | Tu_ty_anon_rec (fields2, id2) ->
          diff_id id1 id2
          &&& lazy
                (diff_list ~at:l
                   (diff_field_annot ~at:l (fun (field1, atyp1) (field2, atyp2) ->
                        diff_id field1 field2 &&& lazy (diff_atyp atyp1 atyp2)
                    )
                   )
                   fields1 fields2
                )
      | _ -> Some l
    )

let diff_fundef (FD_aux (lhs, l)) (FD_aux (rhs, _)) =
  let (FD_function (rec_opt1, tannot_opt1, funcls1)) = lhs in
  let (FD_function (rec_opt2, tannot_opt2, funcls2)) = rhs in
  diff_rec_opt rec_opt1 rec_opt2
  &&& lazy (diff_tannot_opt tannot_opt1 tannot_opt2)
  &&& lazy (diff_list ~at:l diff_funcl funcls1 funcls2)

let diff_type_def (TD_aux (lhs, l)) (TD_aux (rhs, _)) =
  match lhs with
  | TD_abbrev (id1, tq1, k1, atyp1) -> (
      match rhs with
      | TD_abbrev (id2, tq2, k2, atyp2) ->
          diff_id id1 id2
          &&& lazy (diff_typquant tq1 tq2)
          &&& lazy (diff_option ~at:l diff_kind k1 k2)
          &&& lazy (diff_atyp atyp1 atyp2)
      | _ -> Some l
    )
  | TD_record (id1, tq1, fields1) -> (
      match rhs with
      | TD_record (id2, tq2, fields2) ->
          diff_id id1 id2
          &&& lazy (diff_typquant tq1 tq2)
          &&& lazy
                (diff_list ~at:l
                   (diff_field_annot ~at:l (fun (field1, atyp1) (field2, atyp2) ->
                        diff_id field1 field2 &&& lazy (diff_atyp atyp1 atyp2)
                    )
                   )
                   fields1 fields2
                )
      | _ -> Some l
    )
  | TD_variant (id1, tq1, tus1, nt1) -> (
      match rhs with
      | TD_variant (id2, tq2, tus2, nt2) ->
          diff_id id1 id2
          &&& lazy (diff_typquant tq1 tq2)
          &&& lazy (diff_list ~at:l diff_type_union tus1 tus2)
          &&& lazy (diff_eq ~at:l nt1 nt2)
      | _ -> Some l
    )
  | TD_enum (id1, with1, members1) -> (
      match rhs with
      | TD_enum (id2, with2, members2) ->
          diff_id id1 id2
          &&& lazy
                (diff_list ~at:l
                   (fun (f1, atyp1) (f2, atyp2) -> diff_id f1 f2 &&& lazy (diff_atyp atyp1 atyp2))
                   with1 with2
                )
          &&& lazy
                (diff_list ~at:l
                   (fun (member1, exp_opt1) (member2, exp_opt2) ->
                     diff_field_annot ~at:l diff_id member1 member2
                     &&& lazy (diff_option ~at:l diff_exp exp_opt1 exp_opt2)
                   )
                   members1 members2
                )
      | _ -> Some l
    )
  | TD_abstract (id1, k1, conf1) -> (
      match rhs with
      | TD_abstract (id2, k2, conf2) -> diff_id id1 id2 &&& lazy (diff_kind k1 k2) &&& lazy (diff_eq ~at:l conf1 conf2)
      | _ -> Some l
    )
  | TD_bitfield (id1, atyp1, fields1) -> (
      match rhs with
      | TD_bitfield (id2, atyp2, fields2) ->
          diff_id id1 id2
          &&& lazy (diff_atyp atyp1 atyp2)
          &&& lazy
                (diff_list ~at:l
                   (diff_field_annot ~at:l (fun (field1, range1) (field2, range2) ->
                        diff_id field1 field2 &&& lazy (diff_index_range range1 range2)
                    )
                   )
                   fields1 fields2
                )
      | _ -> Some l
    )

let diff_pragma ~at:l lhs rhs =
  match lhs with
  | Pragma_line (str1, _) -> (
      match rhs with Pragma_line (str2, _) -> diff_eq ~at:l str1 str2 | _ -> Some l
    )
  | Pragma_structured obj1 -> (
      match rhs with
      | Pragma_structured obj2 ->
          diff_list ~at:l
            (fun (name1, adata1) (name2, adata2) ->
              diff_eq ~at:l name1 name2 &&& lazy (diff_attribute_data adata1 adata2)
            )
            obj1 obj2
      | _ -> Some l
    )

let diff_scattered_def (SD_aux (lhs, l)) (SD_aux (rhs, _)) =
  match lhs with
  | SD_function (id1, tannot_opt1) -> (
      match rhs with
      | SD_function (id2, tannot_opt2) -> diff_id id1 id2 &&& lazy (diff_tannot_opt tannot_opt1 tannot_opt2)
      | _ -> Some l
    )
  | SD_funcl funcl1 -> (
      match rhs with SD_funcl funcl2 -> diff_funcl funcl1 funcl2 | _ -> Some l
    )
  | SD_enum id1 -> (
      match rhs with SD_enum id2 -> diff_id id1 id2 | _ -> Some l
    )
  | SD_enumcl (id1, m1) -> (
      match rhs with SD_enumcl (id2, m2) -> diff_id id1 id2 &&& lazy (diff_id m1 m2) | _ -> Some l
    )
  | SD_variant (id1, typq1) -> (
      match rhs with SD_variant (id2, typq2) -> diff_id id1 id2 &&& lazy (diff_typquant typq1 typq2) | _ -> Some l
    )
  | SD_unioncl (id1, tu1) -> (
      match rhs with SD_unioncl (id2, tu2) -> diff_id id1 id2 &&& lazy (diff_type_union tu1 tu2) | _ -> Some l
    )
  | SD_mapping (id1, tannot_opt1) -> (
      match rhs with
      | SD_mapping (id2, tannot_opt2) -> diff_id id1 id2 &&& lazy (diff_tannot_opt tannot_opt1 tannot_opt2)
      | _ -> Some l
    )
  | SD_mapcl (id1, mcl1) -> (
      match rhs with SD_mapcl (id2, mcl2) -> diff_id id1 id2 &&& lazy (diff_mapcl mcl1 mcl2) | _ -> Some l
    )
  | SD_end id1 -> (
      match rhs with SD_end id2 -> diff_id id1 id2 | _ -> Some l
    )

let diff_subst (IS_aux (lhs, l)) (IS_aux (rhs, _)) =
  match lhs with
  | IS_id (l_id1, r_id1) -> (
      match rhs with IS_id (l_id2, r_id2) -> diff_id l_id1 l_id2 &&& lazy (diff_id r_id1 r_id2) | _ -> Some l
    )
  | IS_typ (v1, atyp1) -> (
      match rhs with IS_typ (v2, atyp2) -> diff_kid v1 v2 &&& lazy (diff_atyp atyp1 atyp2) | _ -> Some l
    )

let diff_dec_spec (DEC_aux (lhs, l)) (DEC_aux (rhs, _)) =
  let (DEC_reg (atyp1, id1, opt_exp1)) = lhs in
  let (DEC_reg (atyp2, id2, opt_exp2)) = rhs in
  diff_id id1 id2 &&& lazy (diff_atyp atyp1 atyp2) &&& lazy (diff_option ~at:l diff_exp opt_exp1 opt_exp2)

let diff_outcome (OV_aux (lhs, l)) (OV_aux (rhs, _)) =
  let (OV_outcome (id1, typschm1, typq1)) = lhs in
  let (OV_outcome (id2, typschm2, typq2)) = rhs in
  diff_id id1 id2 &&& lazy (diff_typschm typschm1 typschm2) &&& lazy (diff_typquant typq1 typq2)

let diff_default_typing_spec (DT_aux (lhs, l)) (DT_aux (rhs, _)) =
  let (DT_order (k1, atyp1)) = lhs in
  let (DT_order (k2, atyp2)) = rhs in
  diff_kind k1 k2 &&& lazy (diff_atyp atyp1 atyp2)

let rec diff_def (DEF_aux (lhs, l)) (DEF_aux (rhs, _)) =
  match lhs with
  | DEF_type td1 -> (
      match rhs with DEF_type td2 -> diff_type_def td1 td2 | _ -> Some l
    )
  | DEF_constraint atyp1 -> (
      match rhs with DEF_constraint atyp2 -> diff_atyp atyp1 atyp2 | _ -> Some l
    )
  | DEF_fundef fdef1 -> (
      match rhs with DEF_fundef fdef2 -> diff_fundef fdef1 fdef2 | _ -> Some l
    )
  | DEF_mapdef mdef1 -> (
      match rhs with DEF_mapdef mdef2 -> diff_mapdef mdef1 mdef2 | _ -> Some l
    )
  | DEF_impl funcl1 -> (
      match rhs with DEF_impl funcl2 -> diff_funcl funcl1 funcl2 | _ -> Some l
    )
  | DEF_let lb1 -> (
      match rhs with DEF_let lb2 -> diff_letbind lb1 lb2 | _ -> Some l
    )
  | DEF_overload (id1, ids1) -> (
      match rhs with
      | DEF_overload (id2, ids2) -> diff_id id1 id2 &&& lazy (diff_list ~at:l diff_id ids1 ids2)
      | _ -> Some l
    )
  | DEF_fixity (prec1, n1, tok1) -> (
      match rhs with
      | DEF_fixity (prec2, n2, tok2) ->
          diff_eq ~at:l prec1 prec2 &&& lazy (diff_eq_pred ~at:l Big_int.equal n1 n2) &&& lazy (diff_eq ~at:l tok1 tok2)
      | _ -> Some l
    )
  | DEF_val vs1 -> (
      match rhs with DEF_val vs2 -> diff_val_spec vs1 vs2 | _ -> Some l
    )
  | DEF_outcome (o1, defs1) -> (
      match rhs with
      | DEF_outcome (o2, defs2) -> diff_outcome o1 o2 &&& lazy (diff_list ~at:l diff_def defs1 defs2)
      | _ -> Some l
    )
  | DEF_instantiation (id1, substs1) -> (
      match rhs with
      | DEF_instantiation (id2, substs2) -> diff_id id1 id2 &&& lazy (diff_list ~at:l diff_subst substs1 substs2)
      | _ -> Some l
    )
  | DEF_default dtspec1 -> (
      match rhs with DEF_default dtspec2 -> diff_default_typing_spec dtspec1 dtspec2 | _ -> Some l
    )
  | DEF_scattered sdef1 -> (
      match rhs with DEF_scattered sdef2 -> diff_scattered_def sdef1 sdef2 | _ -> Some l
    )
  | DEF_measure (id1, pat1, exp1) -> (
      match rhs with
      | DEF_measure (id2, pat2, exp2) -> diff_id id1 id2 &&& lazy (diff_pat pat1 pat2) &&& lazy (diff_exp exp1 exp2)
      | _ -> Some l
    )
  | DEF_loop_measures (id1, measures1) -> (
      match rhs with
      | DEF_loop_measures (id2, measures2) ->
          diff_id id1 id2
          &&& lazy
                (diff_list ~at:l
                   (fun (Loop (l1, exp1)) (Loop (l2, exp2)) -> diff_eq ~at:l l1 l2 &&& lazy (diff_exp exp1 exp2))
                   measures1 measures2
                )
      | _ -> Some l
    )
  | DEF_register dec_spec1 -> (
      match rhs with DEF_register dec_spec2 -> diff_dec_spec dec_spec1 dec_spec2 | _ -> Some l
    )
  | DEF_pragma (cmd1, arg1) -> (
      match rhs with
      | DEF_pragma (cmd2, arg2) -> diff_eq ~at:l cmd1 cmd2 &&& lazy (diff_pragma ~at:l arg1 arg2)
      | _ -> Some l
    )
  | DEF_private def1 -> (
      match rhs with DEF_private def2 -> diff_def def1 def2 | _ -> Some l
    )
  | DEF_attribute (attr1, arg1, def1) -> (
      match rhs with
      | DEF_attribute (attr2, arg2, def2) ->
          diff_eq ~at:l attr1 attr2
          &&& lazy (diff_option ~at:l diff_attribute_data arg1 arg2)
          &&& lazy (diff_def def1 def2)
      | _ -> Some l
    )
  | DEF_doc (comment1, def1) -> (
      match rhs with
      | DEF_doc (comment2, def2) -> diff_eq ~at:l comment1 comment2 &&& lazy (diff_def def1 def2)
      | _ -> Some l
    )
  | DEF_internal_mutrec fundefs1 -> (
      match rhs with DEF_internal_mutrec fundefs2 -> diff_list ~at:l diff_fundef fundefs1 fundefs2 | _ -> Some l
    )
