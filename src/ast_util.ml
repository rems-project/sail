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
(*    Alasdair Armstrong                                                  *)
(*    Brian Campbell                                                      *)
(*    Thomas Bauereiss                                                    *)
(*    Anthony Fox                                                         *)
(*    Jon French                                                          *)
(*    Dominic Mulligan                                                    *)
(*    Stephen Kell                                                        *)
(*    Mark Wassell                                                        *)
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

open Ast
open Util
module Big_int = Nat_big_num

type mut = Immutable | Mutable

type lvar = Register of typ | Enum of typ | Local of mut * typ | Union of typquant * typ | Unbound

let no_annot = (Parse_ast.Unknown, ())

let gen_loc l = Parse_ast.Generated l

let inc_ord = Ord_aux (Ord_inc, Parse_ast.Unknown)
let dec_ord = Ord_aux (Ord_dec, Parse_ast.Unknown)

let mk_id str = Id_aux (Id str, Parse_ast.Unknown)

let mk_nc nc_aux = NC_aux (nc_aux, Parse_ast.Unknown)

let mk_nexp nexp_aux = Nexp_aux (nexp_aux, Parse_ast.Unknown)

let mk_exp exp_aux = E_aux (exp_aux, no_annot)
let unaux_exp (E_aux (exp_aux, _)) = exp_aux

let mk_pat pat_aux = P_aux (pat_aux, no_annot)
let unaux_pat (P_aux (pat_aux, _)) = pat_aux

let mk_pexp pexp_aux = Pat_aux (pexp_aux, no_annot)
                                       
let mk_lexp lexp_aux = LEXP_aux (lexp_aux, no_annot)

let mk_lit lit_aux = L_aux (lit_aux, Parse_ast.Unknown)

let mk_lit_exp lit_aux = mk_exp (E_lit (mk_lit lit_aux))

let mk_funcl id pat body = FCL_aux (FCL_Funcl (id, Pat_aux (Pat_exp (pat, body),no_annot)), no_annot)

let mk_qi_nc nc = QI_aux (QI_const nc, Parse_ast.Unknown)

let mk_qi_id bk kid =
  let kopt =
    KOpt_aux (KOpt_kind (K_aux (K_kind [BK_aux (bk, Parse_ast.Unknown)], Parse_ast.Unknown), kid), Parse_ast.Unknown)
  in
  QI_aux (QI_id kopt, Parse_ast.Unknown)

let mk_qi_kopt kopt =QI_aux (QI_id kopt, Parse_ast.Unknown)

let mk_fundef funcls =
  let tannot_opt = Typ_annot_opt_aux (Typ_annot_opt_none, Parse_ast.Unknown) in
  let effect_opt = Effect_opt_aux (Effect_opt_pure, Parse_ast.Unknown) in
  let rec_opt = Rec_aux (Rec_nonrec, Parse_ast.Unknown) in
  DEF_fundef
   (FD_aux (FD_function (rec_opt, tannot_opt, effect_opt, funcls), no_annot))

let mk_letbind pat exp = LB_aux (LB_val (pat, exp), no_annot)

let mk_val_spec vs_aux =
  DEF_spec (VS_aux (vs_aux, no_annot))

let kopt_kid (KOpt_aux (kopt_aux, _)) =
  match kopt_aux with
  | KOpt_none kid | KOpt_kind (_, kid) -> kid

let is_nat_kopt = function
  | KOpt_aux (KOpt_kind (K_aux (K_kind [BK_aux (BK_nat, _)], _), _), _) -> true
  | KOpt_aux (KOpt_none _, _) -> true
  | _ -> false

let is_order_kopt = function
  | KOpt_aux (KOpt_kind (K_aux (K_kind [BK_aux (BK_order, _)], _), _), _) -> true
  | _ -> false

let is_typ_kopt = function
  | KOpt_aux (KOpt_kind (K_aux (K_kind [BK_aux (BK_type, _)], _), _), _) -> true
  | _ -> false

let string_of_kid = function
  | Kid_aux (Var v, _) -> v

module Kid = struct
  type t = kid
  let compare kid1 kid2 = String.compare (string_of_kid kid1) (string_of_kid kid2)
end

module Id = struct
  type t = id
  let compare id1 id2 =
    match (id1, id2) with
    | Id_aux (Id x, _), Id_aux (Id y, _) -> String.compare x y
    | Id_aux (DeIid x, _), Id_aux (DeIid y, _) -> String.compare x y
    | Id_aux (Id _, _), Id_aux (DeIid _, _) -> -1
    | Id_aux (DeIid _, _), Id_aux (Id _, _) -> 1
end

module Nexp = struct
  type t = nexp
  let rec compare (Nexp_aux (nexp1, _)) (Nexp_aux (nexp2, _)) =
    let lex_ord (c1, c2) = if c1 = 0 then c2 else c1 in
    match nexp1, nexp2 with
    | Nexp_id v1, Nexp_id v2 -> Id.compare v1 v2
    | Nexp_var kid1, Nexp_var kid2 -> Kid.compare kid1 kid2
    | Nexp_constant c1, Nexp_constant c2 -> Big_int.compare c1 c2
    | Nexp_app (op1, args1), Nexp_app (op2, args2) ->
       let lex1 = Id.compare op1 op2 in
       let lex2 = List.length args1 - List.length args2 in
       let lex3 =
         if lex2 = 0 then
           List.fold_left2 (fun l n1 n2 -> if compare n1 n2 = 0 then 0 else compare n1 n2) 0 args1 args2
         else 0
       in
       lex_ord (lex1, lex_ord (lex2, lex3))
    | Nexp_times (n1a, n1b), Nexp_times (n2a, n2b)
    | Nexp_sum (n1a, n1b), Nexp_sum (n2a, n2b)
    | Nexp_minus (n1a, n1b), Nexp_minus (n2a, n2b) ->
      lex_ord (compare n1a n2a, compare n1b n2b)
    | Nexp_exp n1, Nexp_exp n2 -> compare n1 n2
    | Nexp_neg n1, Nexp_neg n2 -> compare n1 n2
    | Nexp_constant _, _ -> -1 | _, Nexp_constant _ -> 1
    | Nexp_id _, _ -> -1 | _, Nexp_id _ -> 1
    | Nexp_var _, _ -> -1 | _, Nexp_var _ -> 1
    | Nexp_neg _, _ -> -1 | _, Nexp_neg _ -> 1
    | Nexp_exp _, _ -> -1 | _, Nexp_exp _ -> 1
    | Nexp_minus _, _ -> -1 | _, Nexp_minus _ -> 1
    | Nexp_sum _, _ -> -1 | _, Nexp_sum _ -> 1
    | Nexp_times _, _ -> -1 | _, Nexp_times _ -> 1
end

module Bindings = Map.Make(Id)
module IdSet = Set.Make(Id)
module KBindings = Map.Make(Kid)
module KidSet = Set.Make(Kid)
module NexpSet = Set.Make(Nexp)

let rec nexp_identical nexp1 nexp2 = (Nexp.compare nexp1 nexp2 = 0)

let rec is_nexp_constant (Nexp_aux (nexp, _)) = match nexp with
  | Nexp_id _ | Nexp_var _ -> false
  | Nexp_constant _ -> true
  | Nexp_times (n1, n2) | Nexp_sum (n1, n2) | Nexp_minus (n1, n2) ->
    is_nexp_constant n1 && is_nexp_constant n2
  | Nexp_exp n | Nexp_neg n -> is_nexp_constant n
  | Nexp_app (_, nexps) -> List.for_all is_nexp_constant nexps

let rec nexp_simp (Nexp_aux (nexp, l)) = Nexp_aux (nexp_simp_aux nexp, l)
and nexp_simp_aux = function
  (* (n - (n - m)) often appears in foreach loops *)
  | Nexp_minus (nexp1, Nexp_aux (Nexp_minus (nexp2, Nexp_aux (n3,_)),_))
      when nexp_identical nexp1 nexp2 ->
     nexp_simp_aux n3
  | Nexp_minus (Nexp_aux (Nexp_sum (Nexp_aux (n1, _), nexp2), _), nexp3)
    when nexp_identical nexp2 nexp3 ->
     nexp_simp_aux n1
  | Nexp_sum (Nexp_aux (Nexp_minus (Nexp_aux (n1, _), nexp2), _), nexp3)
    when nexp_identical nexp2 nexp3 ->
     nexp_simp_aux n1
  | Nexp_sum (n1, n2) ->
     begin
       let (Nexp_aux (n1_simp, _) as n1) = nexp_simp n1 in
       let (Nexp_aux (n2_simp, _) as n2) = nexp_simp n2 in
       match n1_simp, n2_simp with
       | Nexp_constant c1, Nexp_constant c2 -> Nexp_constant (Big_int.add c1 c2)
       | _, Nexp_neg n2 -> Nexp_minus (n1, n2)
       | _, _ -> Nexp_sum (n1, n2)
     end
  | Nexp_times (n1, n2) ->
     begin
       let (Nexp_aux (n1_simp, _) as n1) = nexp_simp n1 in
       let (Nexp_aux (n2_simp, _) as n2) = nexp_simp n2 in
       match n1_simp, n2_simp with
       | Nexp_constant c, _ when Big_int.equal c (Big_int.of_int 1) -> n2_simp
       | _, Nexp_constant c when Big_int.equal c (Big_int.of_int 1) -> n1_simp
       | Nexp_constant c1, Nexp_constant c2 -> Nexp_constant (Big_int.mul c1 c2)
       | _, _ -> Nexp_times (n1, n2)
     end
  | Nexp_minus (n1, n2) ->
     begin
       let (Nexp_aux (n1_simp, _) as n1) = nexp_simp n1 in
       let (Nexp_aux (n2_simp, _) as n2) = nexp_simp n2 in
       match n1_simp, n2_simp with
       | Nexp_constant c1, Nexp_constant c2 -> Nexp_constant (Big_int.sub c1 c2)
       (* A vector range x['n-1 .. 0] can result in the size "('n-1) - -1" *)
       | Nexp_minus (Nexp_aux (n,_), Nexp_aux (Nexp_constant c1,_)), Nexp_constant c2
         when Big_int.equal c1 (Big_int.negate c2) -> n
       | _, _ -> Nexp_minus (n1, n2)
     end
  | nexp -> nexp

let mk_typ typ = Typ_aux (typ, Parse_ast.Unknown)
let mk_typ_arg arg = Typ_arg_aux (arg, Parse_ast.Unknown)
let mk_kid str = Kid_aux (Var ("'" ^ str), Parse_ast.Unknown)
let mk_infix_id str = Id_aux (DeIid str, Parse_ast.Unknown)

let mk_id_typ id = Typ_aux (Typ_id id, Parse_ast.Unknown)

let mk_ord ord_aux = Ord_aux (ord_aux, Parse_ast.Unknown)

let int_typ = mk_id_typ (mk_id "int")
let nat_typ = mk_id_typ (mk_id "nat")
let unit_typ = mk_id_typ (mk_id "unit")
let bit_typ = mk_id_typ (mk_id "bit")
let real_typ = mk_id_typ (mk_id "real")
let app_typ id args = mk_typ (Typ_app (id, args))
let ref_typ typ = mk_typ (Typ_app (mk_id "ref", [mk_typ_arg (Typ_arg_typ typ)]))
let register_typ typ = mk_typ (Typ_app (mk_id "register", [mk_typ_arg (Typ_arg_typ typ)]))
let atom_typ nexp =
  mk_typ (Typ_app (mk_id "atom", [mk_typ_arg (Typ_arg_nexp (nexp_simp nexp))]))
let range_typ nexp1 nexp2 =
  mk_typ (Typ_app (mk_id "range", [mk_typ_arg (Typ_arg_nexp (nexp_simp nexp1));
                                   mk_typ_arg (Typ_arg_nexp (nexp_simp nexp2))]))
let bool_typ = mk_id_typ (mk_id "bool")
let string_typ = mk_id_typ (mk_id "string")
let list_typ typ = mk_typ (Typ_app (mk_id "list", [mk_typ_arg (Typ_arg_typ typ)]))
let tuple_typ typs = mk_typ (Typ_tup typs)
let function_typ typ1 typ2 eff = mk_typ (Typ_fn (typ1, typ2, eff))

let vector_typ n ord typ =
  mk_typ (Typ_app (mk_id "vector",
                   [mk_typ_arg (Typ_arg_nexp (nexp_simp n));
                    mk_typ_arg (Typ_arg_order ord);
                    mk_typ_arg (Typ_arg_typ typ)]))

let exc_typ = mk_id_typ (mk_id "exception")

let nconstant c = Nexp_aux (Nexp_constant c, Parse_ast.Unknown)
let nint i = nconstant (Big_int.of_int i)
let nminus n1 n2 = Nexp_aux (Nexp_minus (n1, n2), Parse_ast.Unknown)
let nsum n1 n2 = Nexp_aux (Nexp_sum (n1, n2), Parse_ast.Unknown)
let ntimes n1 n2 = Nexp_aux (Nexp_times (n1, n2), Parse_ast.Unknown)
let npow2 n = Nexp_aux (Nexp_exp n, Parse_ast.Unknown)
let nvar kid = Nexp_aux (Nexp_var kid, Parse_ast.Unknown)
let nid id = Nexp_aux (Nexp_id id, Parse_ast.Unknown)
let napp id args = Nexp_aux (Nexp_app (id, args), Parse_ast.Unknown)

let nc_set kid nums = mk_nc (NC_set (kid, nums))
let nc_int_set kid ints = mk_nc (NC_set (kid, List.map Big_int.of_int ints))
let nc_eq n1 n2 = mk_nc (NC_equal (n1, n2))
let nc_neq n1 n2 = mk_nc (NC_not_equal (n1, n2))
let nc_lteq n1 n2 = NC_aux (NC_bounded_le (n1, n2), Parse_ast.Unknown)
let nc_gteq n1 n2 = NC_aux (NC_bounded_ge (n1, n2), Parse_ast.Unknown)
let nc_lt n1 n2 = nc_lteq n1 (nsum n2 (nint 1))
let nc_gt n1 n2 = nc_gteq n1 (nsum n2 (nint 1))
let nc_and nc1 nc2 = mk_nc (NC_and (nc1, nc2))
let nc_or nc1 nc2 = mk_nc (NC_or (nc1, nc2))
let nc_true = mk_nc NC_true
let nc_false = mk_nc NC_false

let rec nc_negate (NC_aux (nc, _)) =
  match nc with
  | NC_bounded_ge (n1, n2) -> nc_lt n1 n2
  | NC_bounded_le (n1, n2) -> nc_gt n1 n2
  | NC_equal (n1, n2) -> nc_neq n1 n2
  | NC_not_equal (n1, n2) -> nc_eq n1 n2
  | NC_and (n1, n2) -> mk_nc (NC_or (nc_negate n1, nc_negate n2))
  | NC_or (n1, n2) -> mk_nc (NC_and (nc_negate n1, nc_negate n2))
  | NC_false -> mk_nc NC_true
  | NC_true -> mk_nc NC_false
  | NC_set (kid, []) -> nc_false
  | NC_set (kid, [int]) -> nc_neq (nvar kid) (nconstant int)
  | NC_set (kid, int :: ints) ->
     mk_nc (NC_and (nc_neq (nvar kid) (nconstant int), nc_negate (mk_nc (NC_set (kid, ints)))))

let mk_typschm typq typ = TypSchm_aux (TypSchm_ts (typq, typ), Parse_ast.Unknown)

let mk_typquant qis = TypQ_aux (TypQ_tq qis, Parse_ast.Unknown)

let mk_fexp id exp = FE_aux (FE_Fexp (id, exp), no_annot)
let mk_fexps fexps = FES_aux (FES_Fexps (fexps, false), no_annot)

let mk_effect effs =
  Effect_aux (Effect_set (List.map (fun be_aux -> BE_aux (be_aux, Parse_ast.Unknown)) effs), Parse_ast.Unknown)

let no_effect = mk_effect []

let quant_items : typquant -> quant_item list = function
  | TypQ_aux (TypQ_tq qis, _) -> qis
  | TypQ_aux (TypQ_no_forall, _) -> []

let quant_kopts typq =
  let qi_kopt = function
    | QI_aux (QI_id kopt, _) -> [kopt]
    | QI_aux _ -> []
  in
  quant_items typq |> List.map qi_kopt |> List.concat

let quant_split typq =
  let qi_kopt = function
    | QI_aux (QI_id kopt, _) -> [kopt]
    | _ -> []
  in
  let qi_nc = function
    | QI_aux (QI_const nc, _) -> [nc]
    | _ -> []
  in
  let qis = quant_items typq in
  List.concat (List.map qi_kopt qis), List.concat (List.map qi_nc qis)

let unaux_nexp (Nexp_aux (nexp, _)) = nexp
let unaux_order (Ord_aux (ord, _)) = ord
let unaux_typ (Typ_aux (typ, _)) = typ

let rec map_exp_annot f (E_aux (exp, annot)) = E_aux (map_exp_annot_aux f exp, f annot)
and map_exp_annot_aux f = function
  | E_block xs -> E_block (List.map (map_exp_annot f) xs)
  | E_nondet xs -> E_nondet (List.map (map_exp_annot f) xs)
  | E_id id -> E_id id
  | E_ref id -> E_ref id
  | E_lit lit -> E_lit lit
  | E_cast (typ, exp) -> E_cast (typ, map_exp_annot f exp)
  | E_app (id, xs) -> E_app (id, List.map (map_exp_annot f) xs)
  | E_app_infix (x, op, y) -> E_app_infix (map_exp_annot f x, op, map_exp_annot f y)
  | E_tuple xs -> E_tuple (List.map (map_exp_annot f) xs)
  | E_if (cond, t, e) -> E_if (map_exp_annot f cond, map_exp_annot f t, map_exp_annot f e)
  | E_for (v, e1, e2, e3, o, e4) -> E_for (v, map_exp_annot f e1, map_exp_annot f e2, map_exp_annot f e3, o, map_exp_annot f e4)
  | E_loop (loop_type, e1, e2) -> E_loop (loop_type, map_exp_annot f e1, map_exp_annot f e2)
  | E_vector exps -> E_vector (List.map (map_exp_annot f) exps)
  | E_vector_access (exp1, exp2) -> E_vector_access (map_exp_annot f exp1, map_exp_annot f exp2)
  | E_vector_subrange (exp1, exp2, exp3) -> E_vector_subrange (map_exp_annot f exp1, map_exp_annot f exp2, map_exp_annot f exp3)
  | E_vector_update (exp1, exp2, exp3) -> E_vector_update (map_exp_annot f exp1, map_exp_annot f exp2, map_exp_annot f exp3)
  | E_vector_update_subrange (exp1, exp2, exp3, exp4) ->
     E_vector_update_subrange (map_exp_annot f exp1, map_exp_annot f exp2, map_exp_annot f exp3, map_exp_annot f exp4)
  | E_vector_append (exp1, exp2) -> E_vector_append (map_exp_annot f exp1, map_exp_annot f exp2)
  | E_list xs -> E_list (List.map (map_exp_annot f) xs)
  | E_cons (exp1, exp2) -> E_cons (map_exp_annot f exp1, map_exp_annot f exp2)
  | E_record fexps -> E_record (map_fexps_annot f fexps)
  | E_record_update (exp, fexps) -> E_record_update (map_exp_annot f exp, map_fexps_annot f fexps)
  | E_field (exp, id) -> E_field (map_exp_annot f exp, id)
  | E_case (exp, cases) -> E_case (map_exp_annot f exp, List.map (map_pexp_annot f) cases)
  | E_try (exp, cases) -> E_try (map_exp_annot f exp, List.map (map_pexp_annot f) cases)
  | E_let (letbind, exp) -> E_let (map_letbind_annot f letbind, map_exp_annot f exp)
  | E_assign (lexp, exp) -> E_assign (map_lexp_annot f lexp, map_exp_annot f exp)
  | E_sizeof nexp -> E_sizeof nexp
  | E_constraint nc -> E_constraint nc
  | E_exit exp -> E_exit (map_exp_annot f exp)
  | E_throw exp -> E_throw (map_exp_annot f exp)
  | E_return exp -> E_return (map_exp_annot f exp)
  | E_assert (test, msg) -> E_assert (map_exp_annot f test, map_exp_annot f msg)
  | E_internal_cast (annot, exp) -> E_internal_cast (f annot, map_exp_annot f exp)
  | E_internal_exp annot -> E_internal_exp (f annot)
  | E_sizeof_internal annot -> E_sizeof_internal (f annot)
  | E_internal_exp_user (annot1, annot2) -> E_internal_exp_user (f annot1, f annot2)
  | E_comment str -> E_comment str
  | E_comment_struc exp -> E_comment_struc (map_exp_annot f exp)
  | E_internal_value v -> E_internal_value v
  | E_var (lexp, exp1, exp2) -> E_var (map_lexp_annot f lexp, map_exp_annot f exp1, map_exp_annot f exp2)
  | E_internal_plet (pat, exp1, exp2) -> E_internal_plet (map_pat_annot f pat, map_exp_annot f exp1, map_exp_annot f exp2)
  | E_internal_return exp -> E_internal_return (map_exp_annot f exp)
and map_opt_default_annot f (Def_val_aux (df, annot)) = Def_val_aux (map_opt_default_annot_aux f df, f annot)
and map_opt_default_annot_aux f = function
  | Def_val_empty -> Def_val_empty
  | Def_val_dec exp -> Def_val_dec (map_exp_annot f exp)
and map_fexps_annot f (FES_aux (FES_Fexps (fexps, b), annot)) = FES_aux (FES_Fexps (List.map (map_fexp_annot f) fexps, b), f annot)
and map_fexp_annot f (FE_aux (FE_Fexp (id, exp), annot)) = FE_aux (FE_Fexp (id, map_exp_annot f exp), f annot)
and map_pexp_annot f (Pat_aux (pexp, annot)) = Pat_aux (map_pexp_annot_aux f pexp, f annot)
and map_pexp_annot_aux f = function
  | Pat_exp (pat, exp) -> Pat_exp (map_pat_annot f pat, map_exp_annot f exp)
  | Pat_when (pat, guard, exp) -> Pat_when (map_pat_annot f pat, map_exp_annot f guard, map_exp_annot f exp)
and map_pat_annot f (P_aux (pat, annot)) = P_aux (map_pat_annot_aux f pat, f annot)
and map_pat_annot_aux f = function
  | P_lit lit -> P_lit lit
  | P_wild -> P_wild
  | P_as (pat, id) -> P_as (map_pat_annot f pat, id)
  | P_typ (typ, pat) -> P_typ (typ, map_pat_annot f pat)
  | P_id id -> P_id id
  | P_var (pat, tpat) -> P_var (map_pat_annot f pat, tpat)
  | P_app (id, pats) -> P_app (id, List.map (map_pat_annot f) pats)
  | P_record (fpats, b) -> P_record (List.map (map_fpat_annot f) fpats, b)
  | P_tup pats -> P_tup (List.map (map_pat_annot f) pats)
  | P_list pats -> P_list (List.map (map_pat_annot f) pats)
  | P_vector_concat pats -> P_vector_concat (List.map (map_pat_annot f) pats)
  | P_vector pats -> P_vector (List.map (map_pat_annot f) pats)
  | P_cons (pat1, pat2) -> P_cons (map_pat_annot f pat1, map_pat_annot f pat2)
and map_fpat_annot f (FP_aux (FP_Fpat (id, pat), annot)) = FP_aux (FP_Fpat (id, map_pat_annot f pat), f annot)
and map_letbind_annot f (LB_aux (lb, annot)) = LB_aux (map_letbind_annot_aux f lb, f annot)
and map_letbind_annot_aux f = function
  | LB_val (pat, exp) -> LB_val (map_pat_annot f pat, map_exp_annot f exp)
and map_lexp_annot f (LEXP_aux (lexp, annot)) = LEXP_aux (map_lexp_annot_aux f lexp, f annot)
and map_lexp_annot_aux f = function
  | LEXP_id id -> LEXP_id id
  | LEXP_deref exp -> LEXP_deref (map_exp_annot f exp)
  | LEXP_memory (id, exps) -> LEXP_memory (id, List.map (map_exp_annot f) exps)
  | LEXP_cast (typ, id) -> LEXP_cast (typ, id)
  | LEXP_tup lexps -> LEXP_tup (List.map (map_lexp_annot f) lexps)
  | LEXP_vector (lexp, exp) -> LEXP_vector (map_lexp_annot f lexp, map_exp_annot f exp)
  | LEXP_vector_range (lexp, exp1, exp2) -> LEXP_vector_range (map_lexp_annot f lexp, map_exp_annot f exp1, map_exp_annot f exp2)
  | LEXP_field (lexp, id) -> LEXP_field (map_lexp_annot f lexp, id)

let id_loc = function
  | Id_aux (_, l) -> l

let kid_loc = function
  | Kid_aux (_, l) -> l

let pat_loc = function
  | P_aux (_, (l, _)) -> l

let exp_loc = function
  | E_aux (_, (l, _)) -> l

let def_loc = function
  | DEF_kind (KD_aux (_, (l, _)))
  | DEF_type (TD_aux (_, (l, _)))
  | DEF_fundef (FD_aux (_, (l, _)))
  | DEF_val (LB_aux (_, (l, _)))
  | DEF_spec (VS_aux (_, (l, _)))
  | DEF_default (DT_aux (_, l))
  | DEF_scattered (SD_aux (_, (l, _)))
  | DEF_reg_dec (DEC_aux (_, (l, _)))
  | DEF_fixity (_, _, Id_aux (_, l))
  | DEF_overload (Id_aux (_, l), _) ->
    l
  | DEF_internal_mutrec _
  | DEF_comm _ ->
    Parse_ast.Unknown

let string_of_id = function
  | Id_aux (Id v, _) -> v
  | Id_aux (DeIid v, _) -> "(deinfix " ^ v ^ ")"

let id_of_kid = function
  | Kid_aux (Var v, l) -> Id_aux (Id (String.sub v 1 (String.length v - 1)), l)

let kid_of_id = function
  | Id_aux (Id v, l) -> Kid_aux (Var ("'" ^ v), l)
  | Id_aux (DeIid v, _) -> assert false

let prepend_id str = function
  | Id_aux (Id v, l) -> Id_aux (Id (str ^ v), l)
  | Id_aux (DeIid v, l) -> Id_aux (DeIid (str ^ v), l)

let append_id id str =
  match id with
  | Id_aux (Id v, l) -> Id_aux (Id (v ^ str), l)
  | Id_aux (DeIid v, l) -> Id_aux (DeIid (v ^ str), l)
                                  
let prepend_kid str = function
  | Kid_aux (Var v, l) -> Kid_aux (Var ("'" ^ str ^ String.sub v 1 (String.length v - 1)), l)

let string_of_base_effect_aux = function
  | BE_rreg -> "rreg"
  | BE_wreg -> "wreg"
  | BE_rmem -> "rmem"
  | BE_rmemt -> "rmemt"
  | BE_wmem -> "wmem"
  | BE_eamem -> "eamem"
  | BE_exmem -> "exmem"
  | BE_wmv -> "wmv"
  | BE_wmvt -> "wmvt"
  | BE_barr -> "barr"
  | BE_depend -> "depend"
  | BE_undef -> "undef"
  | BE_unspec -> "unspec"
  | BE_nondet -> "nondet"
  | BE_escape -> "escape"
  | BE_lset -> "lset"
  | BE_lret -> "lret"

let string_of_base_kind_aux = function
  | BK_type -> "Type"
  | BK_nat -> "Nat"
  | BK_order -> "Order"

let string_of_base_kind (BK_aux (bk, _)) = string_of_base_kind_aux bk

let string_of_kind (K_aux (K_kind bks, _)) = string_of_list " -> " string_of_base_kind bks

let string_of_base_effect = function
  | BE_aux (beff, _) -> string_of_base_effect_aux beff

let string_of_effect = function
  | Effect_aux (Effect_set [], _) -> "pure"
  | Effect_aux (Effect_set beffs, _) ->
     "{" ^ string_of_list ", " string_of_base_effect beffs ^ "}"

let string_of_order = function
  | Ord_aux (Ord_var kid, _) -> string_of_kid kid
  | Ord_aux (Ord_inc, _) -> "inc"
  | Ord_aux (Ord_dec, _) -> "dec"

let rec string_of_nexp = function
  | Nexp_aux (nexp, _) -> string_of_nexp_aux nexp
and string_of_nexp_aux = function
  | Nexp_id id -> string_of_id id
  | Nexp_var kid -> string_of_kid kid
  | Nexp_constant c -> Big_int.to_string c
  | Nexp_times (n1, n2) -> "(" ^ string_of_nexp n1 ^ " * " ^ string_of_nexp n2 ^ ")"
  | Nexp_sum (n1, n2) -> "(" ^ string_of_nexp n1 ^ " + " ^ string_of_nexp n2 ^ ")"
  | Nexp_minus (n1, n2) -> "(" ^ string_of_nexp n1 ^ " - " ^ string_of_nexp n2 ^ ")"
  | Nexp_app (id, nexps) -> string_of_id id ^ "(" ^ string_of_list ", " string_of_nexp nexps ^ ")"
  | Nexp_exp n -> "2 ^ " ^ string_of_nexp n
  | Nexp_neg n -> "- " ^ string_of_nexp n

let rec string_of_typ = function
  | Typ_aux (typ, l) -> string_of_typ_aux typ
and string_of_typ_aux = function
  | Typ_id id -> string_of_id id
  | Typ_var kid -> string_of_kid kid
  | Typ_tup typs -> "(" ^ string_of_list ", " string_of_typ typs ^ ")"
  | Typ_app (id, args) -> string_of_id id ^ "<" ^ string_of_list ", " string_of_typ_arg args ^ ">"
  | Typ_fn (typ_arg, typ_ret, eff) ->
     string_of_typ typ_arg ^ " -> " ^ string_of_typ typ_ret ^ " effect " ^ string_of_effect eff
  | Typ_exist (kids, nc, typ) ->
     "exist " ^ string_of_list " " string_of_kid kids ^ ", " ^ string_of_n_constraint nc ^ ". " ^ string_of_typ typ
and string_of_typ_arg = function
  | Typ_arg_aux (typ_arg, l) -> string_of_typ_arg_aux typ_arg
and string_of_typ_arg_aux = function
  | Typ_arg_nexp n -> string_of_nexp n
  | Typ_arg_typ typ -> string_of_typ typ
  | Typ_arg_order o -> string_of_order o
and string_of_n_constraint = function
  | NC_aux (NC_equal (n1, n2), _) -> string_of_nexp n1 ^ " = " ^ string_of_nexp n2
  | NC_aux (NC_not_equal (n1, n2), _) -> string_of_nexp n1 ^ " != " ^ string_of_nexp n2
  | NC_aux (NC_bounded_ge (n1, n2), _) -> string_of_nexp n1 ^ " >= " ^ string_of_nexp n2
  | NC_aux (NC_bounded_le (n1, n2), _) -> string_of_nexp n1 ^ " <= " ^ string_of_nexp n2
  | NC_aux (NC_or (nc1, nc2), _) ->
     "(" ^ string_of_n_constraint nc1 ^ " | " ^ string_of_n_constraint nc2 ^ ")"
  | NC_aux (NC_and (nc1, nc2), _) ->
     "(" ^ string_of_n_constraint nc1 ^ " & " ^ string_of_n_constraint nc2 ^ ")"
  | NC_aux (NC_set (kid, ns), _) ->
     string_of_kid kid ^ " IN {" ^ string_of_list ", " Big_int.to_string ns ^ "}"
  | NC_aux (NC_true, _) -> "true"
  | NC_aux (NC_false, _) -> "false"

let string_of_annot = function
  | Some (_, typ, eff) ->
     "Some (_, " ^ string_of_typ typ ^ ", " ^ string_of_effect eff ^ ")"
  | None -> "None"

let string_of_quant_item_aux = function
  | QI_id (KOpt_aux (KOpt_none kid, _)) -> string_of_kid kid
  | QI_id (KOpt_aux (KOpt_kind (k, kid), _)) -> string_of_kind k ^ " " ^ string_of_kid kid
  | QI_const constr -> string_of_n_constraint constr

let string_of_quant_item = function
  | QI_aux (qi, _) -> string_of_quant_item_aux qi

let string_of_typquant_aux = function
  | TypQ_tq quants -> "forall " ^ string_of_list ", " string_of_quant_item quants
  | TypQ_no_forall -> ""

let string_of_typquant = function
  | TypQ_aux (quant, _) -> string_of_typquant_aux quant

let string_of_typschm (TypSchm_aux (TypSchm_ts (quant, typ), _)) =
  string_of_typquant quant ^ ". " ^ string_of_typ typ
let string_of_lit (L_aux (lit, _)) =
  match lit with
  | L_unit -> "()"
  | L_zero -> "bitzero"
  | L_one -> "bitone"
  | L_true -> "true"
  | L_false -> "false"
  | L_num n -> Big_int.to_string n
  | L_hex n -> "0x" ^ n
  | L_bin n -> "0b" ^ n
  | L_undef -> "undefined"
  | L_real r -> r
  | L_string str -> "\"" ^ str ^ "\""

let rec string_of_exp (E_aux (exp, _)) =
  match exp with
  | E_block exps -> "{ " ^ string_of_list "; " string_of_exp exps ^ " }"
  | E_id v -> string_of_id v
  | E_ref id -> "ref " ^ string_of_id id
  | E_sizeof nexp -> "sizeof " ^ string_of_nexp nexp
  | E_constraint nc -> "constraint(" ^ string_of_n_constraint nc ^ ")"
  | E_lit lit -> string_of_lit lit
  | E_return exp -> "return " ^ string_of_exp exp
  | E_app (f, args) -> string_of_id f ^ "(" ^ string_of_list ", " string_of_exp args ^ ")"
  | E_app_infix (x, op, y) -> "(" ^ string_of_exp x ^ " " ^ string_of_id op ^ " " ^ string_of_exp y ^ ")"
  | E_tuple exps -> "(" ^ string_of_list ", " string_of_exp exps ^ ")"
  | E_case (exp, cases) ->
     "switch " ^ string_of_exp exp ^ " { case " ^ string_of_list " case " string_of_pexp cases ^ "}"
  | E_try (exp, cases) ->
     "try " ^ string_of_exp exp ^ " catch { case " ^ string_of_list " case " string_of_pexp cases ^ "}"
  | E_let (letbind, exp) -> "let " ^ string_of_letbind letbind ^ " in " ^ string_of_exp exp
  | E_assign (lexp, bind) -> string_of_lexp lexp ^ " := " ^ string_of_exp bind
  | E_cast (typ, exp) -> "(" ^ string_of_typ typ ^ ") " ^ string_of_exp exp
  | E_vector vec -> "[" ^ string_of_list ", " string_of_exp vec ^ "]"
  | E_vector_access (v, n) -> string_of_exp v ^ "[" ^ string_of_exp n ^ "]"
  | E_vector_update (v, n, exp) -> "[" ^ string_of_exp v ^ " with " ^ string_of_exp n ^ " = " ^ string_of_exp exp ^ "]"
  | E_vector_update_subrange (v, n, m, exp) -> "[" ^ string_of_exp v ^ " with " ^ string_of_exp n ^ " .. " ^ string_of_exp m ^ " = " ^ string_of_exp exp ^ "]"
  | E_vector_subrange (v, n1, n2) -> string_of_exp v ^ "[" ^ string_of_exp n1 ^ " .. " ^ string_of_exp n2 ^ "]"
  | E_vector_append (v1, v2) -> string_of_exp v1 ^ " : " ^ string_of_exp v2
  | E_if (cond, then_branch, else_branch) ->
     "if " ^ string_of_exp cond ^ " then " ^ string_of_exp then_branch ^ " else " ^ string_of_exp else_branch
  | E_field (exp, id) -> string_of_exp exp ^ "." ^ string_of_id id
  | E_for (id, f, t, u, ord, body) ->
     "foreach ("
     ^ string_of_id id ^ " from " ^ string_of_exp f ^ " to " ^ string_of_exp t
     ^ " by " ^ string_of_exp u ^ " order " ^ string_of_order ord
     ^ ") { "
     ^ string_of_exp body
  | E_loop (While, cond, body) -> "while " ^ string_of_exp cond ^ " do " ^ string_of_exp body
  | E_loop (Until, cond, body) -> "repeat " ^ string_of_exp body ^ " until " ^ string_of_exp cond
  | E_assert (test, msg) -> "assert(" ^ string_of_exp test ^ ", " ^ string_of_exp msg ^ ")"
  | E_exit exp -> "exit " ^ string_of_exp exp
  | E_throw exp -> "throw " ^ string_of_exp exp
  | E_cons (x, xs) -> string_of_exp x ^ " :: " ^ string_of_exp xs
  | E_list xs -> "[||" ^ string_of_list ", " string_of_exp xs ^ "||]"
  | E_record_update (exp, FES_aux (FES_Fexps (fexps, _), _)) ->
     "{ " ^ string_of_exp exp ^ " with " ^ string_of_list "; " string_of_fexp fexps ^ " }"
  | E_record (FES_aux (FES_Fexps (fexps, _), _)) ->
     "{ " ^ string_of_list "; " string_of_fexp fexps ^ " }"
  | E_internal_cast _ -> "INTERNAL CAST"
  | E_internal_exp _ -> "INTERNAL EXP"
  | E_sizeof_internal _ -> "INTERNAL SIZEOF"
  | E_internal_exp_user _ -> "INTERNAL EXP USER"
  | E_comment _ -> "INTERNAL COMMENT"
  | E_comment_struc _ -> "INTERNAL COMMENT STRUC"
  | E_var _ -> "INTERNAL LET"
  | E_internal_return exp -> "internal_return (" ^ string_of_exp exp ^ ")"
  | E_internal_plet (pat, exp, body) -> "internal_plet " ^ string_of_pat pat ^ " = " ^ string_of_exp exp ^ " in " ^ string_of_exp body
  | E_nondet _ -> "NONDET"
  | E_internal_value _ -> "INTERNAL VALUE"

and string_of_fexp (FE_aux (FE_Fexp (field, exp), _)) =
  string_of_id field ^ " = " ^ string_of_exp exp
and string_of_pexp (Pat_aux (pexp, _)) =
  match pexp with
  | Pat_exp (pat, exp) -> string_of_pat pat ^ " -> " ^ string_of_exp exp
  | Pat_when (pat, guard, exp) -> string_of_pat pat ^ " when " ^ string_of_exp guard ^ " -> " ^ string_of_exp exp
and string_of_typ_pat (TP_aux (tpat_aux, _)) =
  match tpat_aux with
  | TP_wild -> "_"
  | TP_var kid -> string_of_kid kid
  | TP_app (f, tpats) -> string_of_id f ^ "(" ^ string_of_list ", " string_of_typ_pat tpats ^ ")"
and string_of_pat (P_aux (pat, l)) =
  match pat with
  | P_lit lit -> string_of_lit lit
  | P_wild -> "_"
  | P_id v -> string_of_id v
  | P_var (pat, tpat) -> string_of_pat pat ^ " as " ^ string_of_typ_pat tpat
  | P_typ (typ, pat) -> "(" ^ string_of_typ typ ^ ") " ^ string_of_pat pat
  | P_tup pats -> "(" ^ string_of_list ", " string_of_pat pats ^ ")"
  | P_app (f, pats) -> string_of_id f ^ "(" ^ string_of_list ", " string_of_pat pats ^ ")"
  | P_cons (pat1, pat2) -> string_of_pat pat1 ^ " :: " ^ string_of_pat pat2
  | P_list pats -> "[||" ^ string_of_list "," string_of_pat pats ^ "||]"
  | P_vector_concat pats -> string_of_list " : " string_of_pat pats
  | P_vector pats -> "[" ^ string_of_list ", " string_of_pat pats ^ "]"
  | P_as (pat, id) -> string_of_pat pat ^ " as " ^ string_of_id id
  | _ -> "PAT"
and string_of_lexp (LEXP_aux (lexp, _)) =
  match lexp with
  | LEXP_id v -> string_of_id v
  | LEXP_deref exp -> "*(" ^ string_of_exp exp ^ ")"
  | LEXP_cast (typ, v) -> "(" ^ string_of_typ typ ^ ") " ^ string_of_id v
  | LEXP_tup lexps -> "(" ^ string_of_list ", " string_of_lexp lexps ^ ")"
  | LEXP_vector (lexp, exp) -> string_of_lexp lexp ^ "[" ^ string_of_exp exp ^ "]"
  | LEXP_vector_range (lexp, exp1, exp2) ->
     string_of_lexp lexp ^ "[" ^ string_of_exp exp1 ^ ".." ^ string_of_exp exp2 ^ "]"
  | LEXP_field (lexp, id) -> string_of_lexp lexp ^ "." ^ string_of_id id
  | LEXP_memory (f, xs) -> string_of_id f ^ "(" ^ string_of_list ", " string_of_exp xs ^ ")"
and string_of_letbind (LB_aux (lb, l)) =
  match lb with
  | LB_val (pat, exp) -> string_of_pat pat ^ " = " ^ string_of_exp exp

let rec string_of_index_range (BF_aux (ir, _)) =
  match ir with
  | BF_single n -> Big_int.to_string n
  | BF_range (n, m) -> Big_int.to_string n ^ " .. " ^ Big_int.to_string m
  | BF_concat (ir1, ir2) -> "(" ^ string_of_index_range ir1 ^ ") : (" ^ string_of_index_range ir2 ^ ")"

let id_of_fundef (FD_aux (FD_function (_, _, _, funcls), (l, _))) =
  match (List.fold_right
           (fun (FCL_aux (FCL_Funcl (id, _), _)) id' ->
             match id' with
             | Some id' -> if string_of_id id' = string_of_id id then Some id'
                           else raise (Reporting_basic.err_typ l
                             ("Function declaration expects all definitions to have the same name, "
                              ^ string_of_id id ^ " differs from other definitions of " ^ string_of_id id'))
             | None -> Some id) funcls None)
  with
  | Some id -> id
  | None -> raise (Reporting_basic.err_typ l "funcl list is empty")

let id_of_type_def_aux = function
  | TD_abbrev (id, _, _)
  | TD_record (id, _, _, _, _)
  | TD_variant (id, _, _, _, _)
  | TD_enum (id, _, _, _)
  | TD_bitfield (id, _, _) -> id
let id_of_type_def (TD_aux (td_aux, _)) = id_of_type_def_aux td_aux

module BE = struct
  type t = base_effect
  let compare be1 be2 = String.compare (string_of_base_effect be1) (string_of_base_effect be2)
end

module BESet = Set.Make(BE)

let rec nexp_frees (Nexp_aux (nexp, l)) =
  match nexp with
  | Nexp_id _ -> raise (Reporting_basic.err_typ l "Unimplemented Nexp_id in nexp_frees")
  | Nexp_var kid -> KidSet.singleton kid
  | Nexp_constant _ -> KidSet.empty
  | Nexp_times (n1, n2) -> KidSet.union (nexp_frees n1) (nexp_frees n2)
  | Nexp_sum (n1, n2) -> KidSet.union (nexp_frees n1) (nexp_frees n2)
  | Nexp_minus (n1, n2) -> KidSet.union (nexp_frees n1) (nexp_frees n2)
  | Nexp_exp n -> nexp_frees n
  | Nexp_neg n -> nexp_frees n
  | Nexp_app (_, nexps) -> List.fold_left KidSet.union KidSet.empty (List.map nexp_frees nexps)

let rec lexp_to_exp (LEXP_aux (lexp_aux, annot) as le) =
  let rewrap e_aux = E_aux (e_aux, annot) in
  match lexp_aux with
  | LEXP_id id | LEXP_cast (_, id) -> rewrap (E_id id)
  | LEXP_tup les ->
    let get_id (LEXP_aux(lexp,((l,_) as annot)) as le) = match lexp with
      | LEXP_id id | LEXP_cast (_, id) -> E_aux (E_id id, annot)
      | _ ->
        raise (Reporting_basic.err_unreachable l
          ("Unsupported sub-lexp " ^ string_of_lexp le ^ " in tuple")) in
    rewrap (E_tuple (List.map get_id les))
  | LEXP_vector (lexp, e) -> rewrap (E_vector_access (lexp_to_exp lexp, e))
  | LEXP_vector_range (lexp, e1, e2) -> rewrap (E_vector_subrange (lexp_to_exp lexp, e1, e2))
  | LEXP_field (lexp, id) -> rewrap (E_field (lexp_to_exp lexp, id))
  | LEXP_memory (id, exps) -> rewrap (E_app (id, exps))
  | LEXP_deref exp -> rewrap (E_app (mk_id "reg_deref", [exp]))

let destruct_range (Typ_aux (typ_aux, _)) =
  match typ_aux with
  | Typ_app (f, [Typ_arg_aux (Typ_arg_nexp n, _)])
       when string_of_id f = "atom" -> Some (n, n)
  | Typ_app (f, [Typ_arg_aux (Typ_arg_nexp n1, _); Typ_arg_aux (Typ_arg_nexp n2, _)])
       when string_of_id f = "range" -> Some (n1, n2)
  | _ -> None

let rec is_number (Typ_aux (t,_)) =
  match t with
  | Typ_id (Id_aux (Id "int", _))
  | Typ_id (Id_aux (Id "nat", _))
  | Typ_app (Id_aux (Id "range", _),_)
  | Typ_app (Id_aux (Id "implicit", _),_)
  | Typ_app (Id_aux (Id "atom", _),_) -> true
  | _ -> false

let is_reftyp (Typ_aux (typ_aux, _)) = match typ_aux with
  | Typ_app (id, _) -> string_of_id id = "register" || string_of_id id = "reg"
  | _ -> false

let rec is_vector_typ = function
  | Typ_aux (Typ_app (Id_aux (Id "vector",_), [_;_;_]), _) -> true
  | Typ_aux (Typ_app (Id_aux (Id "register",_), [Typ_arg_aux (Typ_arg_typ rtyp,_)]), _) ->
    is_vector_typ rtyp
  | _ -> false

let typ_app_args_of = function
  | Typ_aux (Typ_app (Id_aux (Id c,_), targs), l) ->
    (c, List.map (fun (Typ_arg_aux (a,_)) -> a) targs, l)
  | Typ_aux (_, l) as typ ->
     raise (Reporting_basic.err_typ l
       ("typ_app_args_of called on non-app type " ^ string_of_typ typ))

let rec vector_typ_args_of typ = match typ_app_args_of typ with
  | ("vector", [Typ_arg_nexp len; Typ_arg_order ord; Typ_arg_typ etyp], l) ->
     begin
       match ord with
       | Ord_aux (Ord_inc, _) -> (nint 0, nexp_simp len, ord, etyp)
       | Ord_aux (Ord_dec, _) -> (nexp_simp (nminus len (nint 1)), nexp_simp len, ord, etyp) (* FIXME to return 3 arguments *)
       | _ -> raise (Reporting_basic.err_typ l "Can't calculate start index without order")
     end
  | ("register", [Typ_arg_typ rtyp], _) -> vector_typ_args_of rtyp
  | (_, _, l) ->
     raise (Reporting_basic.err_typ l
       ("vector_typ_args_of called on non-vector type " ^ string_of_typ typ))

let is_order_inc = function
  | Ord_aux (Ord_inc, _) -> true
  | Ord_aux (Ord_dec, _) -> false
  | Ord_aux (Ord_var _, l) ->
    raise (Reporting_basic.err_unreachable l "is_order_inc called on vector with variable ordering")

let is_bit_typ = function
  | Typ_aux (Typ_id (Id_aux (Id "bit", _)), _) -> true
  | _ -> false

let is_bitvector_typ typ =
  if is_vector_typ typ then
    let (_,_,_,etyp) = vector_typ_args_of typ in
    is_bit_typ etyp
  else false

let has_effect (Effect_aux (eff,_)) searched_for = match eff with
  | Effect_set effs ->
    List.exists (fun (BE_aux (be,_)) -> be = searched_for) effs

let effect_set (Effect_aux (eff,_)) = match eff with
  | Effect_set effs -> BESet.of_list effs

(* Utilities for constructing effect sets *)

let union_effects e1 e2 =
  match e1, e2 with
  | Effect_aux (Effect_set base_effs1, _), Effect_aux (Effect_set base_effs2, _) ->
     let base_effs3 = BESet.elements (BESet.of_list (base_effs1 @ base_effs2)) in
     Effect_aux (Effect_set base_effs3, Parse_ast.Unknown)

let equal_effects e1 e2 =
  match e1, e2 with
  | Effect_aux (Effect_set base_effs1, _), Effect_aux (Effect_set base_effs2, _) ->
     BESet.compare (BESet.of_list base_effs1) (BESet.of_list base_effs2) = 0

let rec tyvars_of_nexp (Nexp_aux (nexp,_)) =
  match nexp with
  | Nexp_id _
  | Nexp_constant _ -> KidSet.empty
  | Nexp_var kid -> KidSet.singleton kid
  | Nexp_times (n1,n2)
  | Nexp_sum (n1,n2)
  | Nexp_minus (n1,n2) -> KidSet.union (tyvars_of_nexp n1) (tyvars_of_nexp n2)
  | Nexp_exp n
  | Nexp_neg n -> tyvars_of_nexp n
  | Nexp_app (_, nexps) -> List.fold_left KidSet.union KidSet.empty (List.map tyvars_of_nexp nexps)

let rec tyvars_of_nc (NC_aux (nc, _)) =
  match nc with
  | NC_equal (nexp1, nexp2)
  | NC_bounded_ge (nexp1, nexp2)
  | NC_bounded_le (nexp1, nexp2)
  | NC_not_equal (nexp1, nexp2) ->
     KidSet.union (tyvars_of_nexp nexp1) (tyvars_of_nexp nexp2)
  | NC_set (kid, _) -> KidSet.singleton kid
  | NC_or (nc1, nc2)
  | NC_and (nc1, nc2) ->
     KidSet.union (tyvars_of_nc nc1) (tyvars_of_nc nc2)
  | NC_true
  | NC_false -> KidSet.empty

let rec tyvars_of_typ (Typ_aux (t,_)) =
  match t with
  | Typ_id _ -> KidSet.empty
  | Typ_var kid -> KidSet.singleton kid
  | Typ_fn (t1,t2,_) -> KidSet.union (tyvars_of_typ t1) (tyvars_of_typ t2)
  | Typ_tup ts ->
     List.fold_left (fun s t -> KidSet.union s (tyvars_of_typ t))
       KidSet.empty ts
  | Typ_app (_,tas) -> 
     List.fold_left (fun s ta -> KidSet.union s (tyvars_of_typ_arg ta))
       KidSet.empty tas
  | Typ_exist (kids, nc, t) ->
     let s = KidSet.union (tyvars_of_typ t) (tyvars_of_nc nc) in
     List.fold_left (fun s k -> KidSet.remove k s) s kids
and tyvars_of_typ_arg (Typ_arg_aux (ta,_)) =
  match ta with
  | Typ_arg_nexp nexp -> tyvars_of_nexp nexp
  | Typ_arg_typ typ -> tyvars_of_typ typ
  | Typ_arg_order _ -> KidSet.empty

let is_kid_generated kid = String.contains (string_of_kid kid) '#'

let rec undefined_of_typ mwords l annot (Typ_aux (typ_aux, _) as typ) =
  let wrap e_aux typ = E_aux (e_aux, (l, annot typ)) in
  match typ_aux with
  | Typ_id id ->
     wrap (E_app (prepend_id "undefined_" id, [wrap (E_lit (mk_lit L_unit)) unit_typ])) typ
  | Typ_app (_,[size;_;_]) when mwords && is_bitvector_typ typ ->
     wrap (E_app (mk_id "undefined_bitvector",
       undefined_of_typ_args mwords l annot size)) typ
  | Typ_app (atom, [Typ_arg_aux (Typ_arg_nexp i, _)]) when string_of_id atom = "atom" ->
     wrap (E_sizeof i) typ
  | Typ_app (id, args) ->
     wrap (E_app (prepend_id "undefined_" id,
                  List.concat (List.map (undefined_of_typ_args mwords l annot) args))) typ
  | Typ_tup typs ->
     wrap (E_tuple (List.map (undefined_of_typ mwords l annot) typs)) typ
  | Typ_var kid ->
     (* Undefined monomorphism restriction in the type checker should
        guarantee that the typ_(kid) parameter was always one created
        in an undefined_(type) function created in
        initial_check.ml. i.e. the rewriter should only encounter this
        case when re-writing those functions. *)
     wrap (E_id (prepend_id "typ_" (id_of_kid kid))) typ
  | Typ_fn _ | Typ_exist _ -> assert false (* Typ_exist should be re-written *)
and undefined_of_typ_args mwords l annot (Typ_arg_aux (typ_arg_aux, _) as typ_arg) =
  match typ_arg_aux with
  | Typ_arg_nexp n -> [E_aux (E_sizeof n, (l, annot (atom_typ n)))]
  | Typ_arg_typ typ -> [undefined_of_typ mwords l annot typ]
  | Typ_arg_order _ -> []

let destruct_pexp (Pat_aux (pexp,ann)) =
  match pexp with
  | Pat_exp (pat,exp) -> pat,None,exp,ann
  | Pat_when (pat,guard,exp) -> pat,Some guard,exp,ann

let construct_pexp (pat,guard,exp,ann) =
  match guard with
  | None -> Pat_aux (Pat_exp (pat,exp),ann)
  | Some guard -> Pat_aux (Pat_when (pat,guard,exp),ann)

let is_valspec id = function
  | DEF_spec (VS_aux (VS_val_spec (_, id', _, _), _)) when Id.compare id id' = 0 -> true
  | _ -> false

let is_fundef id = function
  | DEF_fundef (FD_aux (FD_function (_, _, _, FCL_aux (FCL_Funcl (id', _), _) :: _), _)) when Id.compare id' id = 0 -> true
  | _ -> false

let rename_funcl id (FCL_aux (FCL_Funcl (_, pexp), annot)) = FCL_aux (FCL_Funcl (id, pexp), annot)

let rename_fundef id (FD_aux (FD_function (ropt, topt, eopt, funcls), annot)) =
  FD_aux (FD_function (ropt, topt, eopt, List.map (rename_funcl id) funcls), annot)

let rec split_defs' f defs acc =
  match defs with
  | [] -> None
  | def :: defs when f def -> Some (acc, def, defs)
  | def :: defs -> split_defs' f defs (def :: acc)

let split_defs f (Defs defs) =
  match split_defs' f defs [] with
  | None -> None
  | Some (pre_defs, def, post_defs) ->
     Some (Defs (List.rev pre_defs), def, Defs post_defs)

let append_ast (Defs ast1) (Defs ast2) = Defs (ast1 @ ast2)

let type_union_id (Tu_aux (aux, _)) = match aux with
  | Tu_id id -> id
  | Tu_ty_id (_, id) -> id


let rec pat_ids (P_aux (pat_aux, _)) =
  match pat_aux with
  | P_lit _ | P_wild -> IdSet.empty
  | P_id id -> IdSet.singleton id
  | P_as (pat, id) -> IdSet.add id (pat_ids pat)
  | P_var (pat, _) | P_typ (_, pat) -> pat_ids pat
  | P_app (_, pats) | P_tup pats | P_vector pats | P_vector_concat pats | P_list pats ->
     List.fold_right IdSet.union (List.map pat_ids pats) IdSet.empty
  | P_cons (pat1, pat2) ->
     IdSet.union (pat_ids pat1) (pat_ids pat2)
  | P_record (fpats, _) ->
     List.fold_right IdSet.union (List.map fpat_ids fpats) IdSet.empty
and fpat_ids (FP_aux (FP_Fpat (_, pat), _)) = pat_ids pat

let rec subst id value (E_aux (e_aux, annot) as exp) =
  let wrap e_aux = E_aux (e_aux, annot) in
  let e_aux = match e_aux with
    | E_block exps -> E_block (List.map (subst id value) exps)
    | E_nondet exps -> E_nondet (List.map (subst id value) exps)
    | E_id id' -> if Id.compare id id' = 0 then unaux_exp value else E_id id'
    | E_lit lit -> E_lit lit
    | E_cast (typ, exp) -> E_cast (typ, subst id value exp)

    | E_app (fn, exps) -> E_app (fn, List.map (subst id value) exps)
    | E_app_infix (exp1, op, exp2) -> E_app_infix (subst id value exp1, op, subst id value exp2)

    | E_tuple exps -> E_tuple (List.map (subst id value) exps)

    | E_if (cond, then_exp, else_exp) ->
       E_if (subst id value cond, subst id value then_exp, subst id value else_exp)

    | E_loop (loop, cond, body) ->
       E_loop (loop, subst id value cond, subst id value body)
    | E_for (id', exp1, exp2, exp3, order, body) when Id.compare id id' = 0 ->
       E_for (id', exp1, exp2, exp3, order, body)
    | E_for (id', exp1, exp2, exp3, order, body) ->
       E_for (id', subst id value exp1, subst id value exp2, subst id value exp3, order, subst id value body)

    | E_vector exps -> E_vector (List.map (subst id value) exps)
    | E_vector_access (exp1, exp2) -> E_vector_access (subst id value exp1, subst id value exp2)
    | E_vector_subrange (exp1, exp2, exp3) -> E_vector_subrange (subst id value exp1, subst id value exp2, subst id value exp3)
    | E_vector_update (exp1, exp2, exp3) -> E_vector_update (subst id value exp1, subst id value exp2, subst id value exp3)
    | E_vector_update_subrange (exp1, exp2, exp3, exp4) ->
       E_vector_update_subrange (subst id value exp1, subst id value exp2, subst id value exp3, subst id value exp4)
    | E_vector_append (exp1, exp2) -> E_vector_append (subst id value exp1, subst id value exp2)

    | E_list exps -> E_list (List.map (subst id value) exps)
    | E_cons (exp1, exp2) -> E_cons (subst id value exp1, subst id value exp2)

    | E_record fexps -> E_record (subst_fexps id value fexps)
    | E_record_update (exp, fexps) -> E_record_update (subst id value exp, subst_fexps id value fexps)
    | E_field (exp, id') -> E_field (subst id value exp, id')

    | E_case (exp, pexps) ->
       E_case (subst id value exp, List.map (subst_pexp id value) pexps)

    | E_let (LB_aux (LB_val (pat, bind), lb_annot), body) ->
       E_let (LB_aux (LB_val (pat, subst id value bind), lb_annot),
              if IdSet.mem id (pat_ids pat) then body else subst id value body)

    | E_assign (lexp, exp) -> E_assign (subst_lexp id value lexp, subst id value exp) (* Shadowing... *)

    (* Should be re-written *)
    | E_sizeof nexp -> E_sizeof nexp
    | E_constraint nc -> E_constraint nc

    | E_return exp -> E_return (subst id value exp)
    | E_exit exp -> E_exit (subst id value exp)
    (* Not sure about this, but id should always be immutable while id' must be mutable so should be ok. *)
    | E_ref id' -> E_ref id'
    | E_throw exp -> E_throw (subst id value exp)

    | E_try (exp, pexps) ->
       E_try (subst id value exp, List.map (subst_pexp id value) pexps)

    | E_assert (exp1, exp2) -> E_assert (subst id value exp1, subst id value exp2)

    | E_internal_value v -> E_internal_value v
    | _ -> failwith ("subst " ^ string_of_exp exp)
  in
  wrap e_aux

and subst_pexp id value (Pat_aux (pexp_aux, annot)) =
  let pexp_aux = match pexp_aux with
    | Pat_exp (pat, exp) when IdSet.mem id (pat_ids pat) -> Pat_exp (pat, exp)
    | Pat_exp (pat, exp) -> Pat_exp (pat, subst id value exp)
    | Pat_when (pat, guard, exp) when IdSet.mem id (pat_ids pat) -> Pat_when (pat, guard, exp)
    | Pat_when (pat, guard, exp) -> Pat_when (pat, subst id value guard, subst id value exp)
  in
  Pat_aux (pexp_aux, annot)


and subst_fexps id value (FES_aux (FES_Fexps (fexps, flag), annot)) =
  FES_aux (FES_Fexps (List.map (subst_fexp id value) fexps, flag), annot)

and subst_fexp id value (FE_aux (FE_Fexp (id', exp), annot)) =
  FE_aux (FE_Fexp (id', subst id value exp), annot)

and subst_lexp id value (LEXP_aux (lexp_aux, annot) as lexp) =
  let wrap lexp_aux = LEXP_aux (lexp_aux, annot) in
  let lexp_aux = match lexp_aux with
    | LEXP_deref exp -> LEXP_deref (subst id value exp)
    | LEXP_id id' -> LEXP_id id'
    | LEXP_memory (f, exps) -> LEXP_memory (f, List.map (subst id value) exps)
    | LEXP_cast (typ, id') -> LEXP_cast (typ, id')
    | LEXP_tup lexps -> LEXP_tup (List.map (subst_lexp id value) lexps)
    | LEXP_vector (lexp, exp) -> LEXP_vector (subst_lexp id value lexp, subst id value exp)
    | LEXP_vector_range (lexp, exp1, exp2) -> LEXP_vector_range (subst_lexp id value lexp, subst id value exp1, subst id value exp2)
    | LEXP_field (lexp, id') -> LEXP_field (subst_lexp id value lexp, id')
  in
  wrap lexp_aux
