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

open Type_internal
open Ast
open Type_internal

(*Envs is a tuple of used names (currently unused), map from id to kind, default order for vector types and literal vectors *)
type envs = Nameset.t * kind Envmap.t * Ast.order 
type 'a envs_out = 'a * envs

let id_to_string (Id_aux(id,l)) =
  match id with | Id(x) | DeIid(x) -> x

let var_to_string (Kid_aux(Var v,l)) = v

let typquant_to_quantkinds k_env typquant = 
  match typquant with
  | TypQ_aux(tq,_) ->
    (match tq with
    | TypQ_no_forall -> []
    | TypQ_tq(qlist) ->
      List.fold_right
        (fun (QI_aux(qi,_)) rst ->
          match qi with
          | QI_const _ -> rst
          | QI_id(ki) -> begin
            match ki with 
            | KOpt_aux(KOpt_none(v),l) | KOpt_aux(KOpt_kind(_,v),l) -> 
              (match Envmap.apply k_env (var_to_string v) with
              | Some(typ) -> typ::rst
              | None -> raise (Reporting_basic.err_unreachable l "Envmap didn't get an entry during typschm processing"))
          end)
        qlist
        [])

let typ_error l msg opt_id opt_var opt_kind =
  let full_msg = (msg ^
                  (match opt_id, opt_var, opt_kind with
                   | Some(id),None,Some(kind) -> (id_to_string id) ^ " of " ^ (kind_to_string kind)
                   | Some(id),None,None -> ": " ^ (id_to_string id)
                   | None,Some(v),Some(kind) -> (var_to_string v) ^ " of " ^ (kind_to_string kind)
                   | None,Some(v),None -> ": " ^ (var_to_string v)
                   | None,None,Some(kind) -> " " ^ (kind_to_string kind)
                   | _ -> "")) in
  Reporting_basic.report_error (Reporting_basic.Err_type(l, full_msg))
                
let to_base_kind (BK_aux(k,l')) =
  match k with
  | BK_type -> BK_aux(BK_type,l'), { k = K_Typ}
  | BK_nat -> BK_aux(BK_nat,l'), { k = K_Nat }
  | BK_order -> BK_aux(BK_order,l'), { k = K_Ord }
  | BK_effect -> BK_aux(BK_effect,l'), { k = K_Efct }

let to_kind (k_env : kind Envmap.t) (K_aux(K_kind(klst),l)) : (Ast.kind * kind) =
  match klst with
  | [] -> raise (Reporting_basic.err_unreachable l "Kind with empty kindlist encountered")
  | [k] -> let k_ast,k_typ = to_base_kind k in
           K_aux(K_kind([k_ast]),l), k_typ
  | ks -> let k_pairs = List.map to_base_kind ks in
          let reverse_typs = List.rev (List.map snd k_pairs) in
          let ret,args = List.hd reverse_typs, List.rev (List.tl reverse_typs) in
          match ret.k with
          | K_Typ -> K_aux(K_kind(List.map fst k_pairs), l), { k = K_Lam(args,ret) }
          | _ -> typ_error l "Type constructor must have an -> kind ending in Type" None None None

let rec typ_to_string (Typ_aux(t,_)) = match t with
  | Typ_id i -> id_to_string i
  | Typ_var (Kid_aux (Var i,_)) -> i
  | _ -> "bigger than var"

and nexp_to_string (Nexp_aux(n,_)) = match n with
  | Nexp_id i -> id_to_string i
  | Nexp_var (Kid_aux (Var i,_)) -> i
  | _ -> "nexp bigger than var"

let rec to_typ (k_env : kind Envmap.t) (def_ord : Ast.order) (t: Ast.typ) : Ast.typ =
  match t with
  | Typ_aux(t,l) ->
    Typ_aux( (match t with 
              | Typ_id(id) -> 
                let mk = Envmap.apply k_env (id_to_string id) in
                (match mk with
                 | Some(k) ->
                   (match k.k with
                    | K_Typ -> Typ_id id
                    | K_infer -> k.k <- K_Typ; Typ_id id
                    | _ -> typ_error l "Required an identifier with kind Type, encountered " (Some id) None (Some k))
                 | None -> typ_error l "Encountered an unbound type identifier" (Some id) None None)
              | Typ_var(v) -> 
                let mk = Envmap.apply k_env (var_to_string v) in
                (match mk with
                 | Some(k) -> (match k.k with
                     | K_Typ -> Typ_var v
                     | K_infer -> k.k <- K_Typ; Typ_var v
                     | _ -> typ_error l "Required a variable with kind Type, encountered " None (Some v) (Some k))
                | None -> typ_error l "Encountered an unbound variable" None (Some v) None)
              | Typ_fn(arg,ret,efct) -> Typ_fn( (to_typ k_env def_ord arg),
                                                (to_typ k_env def_ord ret),
                                                (to_effects k_env efct))
              | Typ_tup(typs) -> Typ_tup( List.map (to_typ k_env def_ord) typs)
              | Typ_app(id,typs) ->
                let k = Envmap.apply k_env (id_to_string id) in
                (match k with 
                 | Some({k = K_Lam(args,t)}) -> 
                   if ((List.length args) = (List.length typs))
                   then
                     Typ_app(id,(List.map2 (fun k a -> (to_typ_arg k_env def_ord k a)) args typs))
                   else typ_error l "Type constructor given incorrect number of arguments" (Some id) None None
                 | None ->
                   typ_error l "Required a type constructor, encountered an unbound identifier" (Some id) None None
                 | _ -> typ_error l "Required a type constructor, encountered a base kind variable" (Some id) None None)
              | _ ->
                typ_error l "Required an item of kind Type, encountered an illegal form for this kind" None None None
      ), l)

and to_nexp (k_env : kind Envmap.t) (n: Ast.nexp) : Ast.nexp =
  match n with
  | Nexp_aux(t,l) ->
    (match t with
     | Nexp_id i ->
       let mk = Envmap.apply k_env (id_to_string i) in
       (match mk with
        | Some(k) -> Nexp_aux((match k.k with
            | K_Nat -> Nexp_id i
            | K_infer -> k.k <- K_Nat; Nexp_id i
            | _ -> typ_error l "Required a variable with kind Nat, encountered " (Some i) None (Some k)),l)
       | None -> typ_error l "Encountered an unbound variable" (Some i) None None)       
    | Nexp_var(v) ->                
      let mk = Envmap.apply k_env (var_to_string v) in
      (match mk with
       | Some(k) -> Nexp_aux((match k.k with
           | K_Nat -> Nexp_var v
           | K_infer -> k.k <- K_Nat; Nexp_var v
           | _ -> typ_error l "Required a variable with kind Nat, encountered " None (Some v) (Some k)),l)
       | None -> typ_error l "Encountered an unbound variable" None (Some v) None)
    | Nexp_constant(i) -> Nexp_aux(Nexp_constant(i),l)
    | Nexp_sum(t1,t2) ->
      let n1 = to_nexp k_env t1 in
      let n2 = to_nexp k_env t2 in
      Nexp_aux(Nexp_sum(n1,n2),l)
    | Nexp_exp(t1) -> Nexp_aux(Nexp_exp(to_nexp k_env t1),l)
    | Nexp_neg(t1) -> Nexp_aux(Nexp_neg(to_nexp k_env t1),l)
    | Nexp_times(t1,t2) ->
      let n1 = to_nexp k_env t1 in
      let n2 = to_nexp k_env t2 in
      Nexp_aux(Nexp_times(n1,n2),l)
    | Nexp_minus(t1,t2) ->
      let n1 = to_nexp k_env t1 in
      let n2 = to_nexp k_env t2 in
      Nexp_aux(Nexp_minus(n1,n2),l))
    
and to_order (k_env : kind Envmap.t) (def_ord : Ast.order) (o: Ast.order) : Ast.order =
  match o with
  | Ord_aux(t,l) ->
    (match t with
      | Ord_var(v) -> 
        let mk = Envmap.apply k_env (var_to_string v) in
        (match mk with
         | Some(k) -> (match k.k with
             | K_Ord -> Ord_aux(Ord_var v, l)
             | K_infer -> k.k <- K_Ord; Ord_aux(Ord_var v,l)
             | _ -> typ_error l "Required a variable with kind Order, encountered " None (Some v) (Some k))
         | None -> typ_error l "Encountered an unbound variable" None (Some v) None)
      | Ord_inc -> Ord_aux(Ord_inc,l)
      | Ord_dec -> Ord_aux(Ord_dec,l)
    )

and to_effects (k_env : kind Envmap.t) (e : Ast.effect) : Ast.effect =
  match e with
  | Effect_aux(t,l) ->
    Effect_aux( (match t with
        | Effect_var(v) ->  
          let mk = Envmap.apply k_env (var_to_string v) in
          (match mk with
           | Some(k) -> (match k.k with
               | K_Efct -> Effect_var v
               | K_infer -> k.k <- K_Efct; Effect_var v
               | _ -> typ_error l "Required a variable with kind Effect, encountered " None (Some v) (Some k))
           | None -> typ_error l "Encountered an unbound variable" None (Some v) None)
        | Effect_set(effects) -> Effect_set(effects)
    ), l)

and to_typ_arg (k_env : kind Envmap.t) (def_ord : Ast.order) (kind : kind) (arg : Ast.typ_arg) : Ast.typ_arg =
  let l,ta = (match arg with Typ_arg_aux(ta,l) -> l,ta) in
  Typ_arg_aux (  
    (match kind.k,ta with 
    | K_Typ,Typ_arg_typ t     -> Typ_arg_typ (to_typ k_env def_ord t)
    | K_Nat,Typ_arg_nexp n    -> Typ_arg_nexp (to_nexp k_env n)
    | K_Ord,Typ_arg_order o   -> Typ_arg_order (to_order k_env def_ord o)
    | K_Efct,Typ_arg_effect e -> Typ_arg_effect (to_effects k_env e)
    | (K_Lam _ | K_infer | K_Val),_ -> 
      raise (Reporting_basic.err_unreachable l "To_ast_typ_arg received Lam kind or infer kind")
    | _ ->
      let tn_str = 
        (match ta with
         | Typ_arg_typ t -> typ_to_string t
         | Typ_arg_nexp n -> nexp_to_string n
         | _ -> "order or effect") in
      typ_error l ("Kind declaration and kind of type argument, " ^ tn_str ^ " don't match here")
        None None (Some kind)), 
    l)

let to_nexp_constraint (k_env : kind Envmap.t) (c : n_constraint) : n_constraint =
  match c with 
  | NC_aux(nc,l) ->
    NC_aux( (match nc with
             | NC_fixed(t1,t2) -> 
               let n1 = to_nexp k_env t1 in
               let n2 = to_nexp k_env t2 in
               NC_fixed(n1,n2)
             | NC_bounded_ge(t1,t2) ->
               let n1 = to_nexp k_env t1 in
               let n2 = to_nexp k_env t2 in
               NC_bounded_ge(n1,n2)
             | NC_bounded_le(t1,t2) ->
               let n1 = to_nexp k_env t1 in
               let n2 = to_nexp k_env t2 in
               NC_bounded_le(n1,n2)
             | NC_not_equal(t1,t2) ->
               let n1 = to_nexp k_env t1 in
               let n2 = to_nexp k_env t2 in
               NC_not_equal(t1,t2)
             | NC_nat_set_bounded(id, bounds) ->
               NC_nat_set_bounded(id, bounds)
    ), l)               

(* Transforms a typquant while building first the kind environment of declared variables, and also the kind environment in context *)
let to_typquant (k_env: kind Envmap.t) (tq : typquant) : typquant * kind Envmap.t * kind Envmap.t =
  let opt_kind_to_ast k_env local_names local_env (KOpt_aux(ki,l)) =
    let v, key, kind, ktyp =
      match ki with
      | KOpt_none(v) ->
        let key = var_to_string v in
        let kind,ktyp =
          if (Envmap.in_dom key k_env) then None,(Envmap.apply k_env key)
          else None,(Some{ k = K_infer }) in
        v,key,kind, ktyp
      | KOpt_kind(k,v) ->
        let key = var_to_string v in
        let kind,ktyp = to_kind k_env k in
        v,key,Some(kind),Some(ktyp)
    in
    if (Nameset.mem key local_names)
    then typ_error l "Encountered duplicate name in type scheme" None (Some v) None
    else 
      let local_names = Nameset.add key local_names in
      let kopt,k_env,k_env_local = (match kind,ktyp with
        | Some(k),Some(kt) -> KOpt_kind(k,v), (Envmap.insert k_env (key,kt)), (Envmap.insert local_env (key,kt))
        | None, Some(kt) -> KOpt_none(v), (Envmap.insert k_env (key,kt)), (Envmap.insert local_env (key,kt))
        | _ -> raise (Reporting_basic.err_unreachable l "Envmap in dom is true but apply gives None")) in
      KOpt_aux(kopt,l),k_env,local_names,k_env_local
  in
  match tq with
  | TypQ_aux(tqa,l) ->
    (match tqa with
    | TypQ_no_forall -> TypQ_aux(TypQ_no_forall,l), k_env, Envmap.empty
    | TypQ_tq(qlist) ->
      let rec to_q_items k_env local_names local_env = function
        | [] -> [],k_env,local_env
        | q::qs ->
          (match q with
           | QI_aux(qi,l) ->
             (match qi with
              | QI_const(n_const) -> 
                let c = QI_aux(QI_const(to_nexp_constraint k_env n_const),l) in
                        let qis,k_env,local_env = to_q_items k_env local_names local_env qs in
                        (c::qis),k_env,local_env
                      | QI_id(kid) ->
                        let kid,k_env,local_names,local_env = opt_kind_to_ast k_env local_names local_env kid in
                        let c = QI_aux(QI_id(kid),l) in
                        let qis,k_env,local_env = to_q_items k_env local_names local_env qs in
                        (c::qis),k_env,local_env))      
      in
      let lst,k_env,local_env = to_q_items k_env Nameset.empty Envmap.empty qlist in
      TypQ_aux(TypQ_tq(lst),l), k_env, local_env)

let to_typschm (k_env:kind Envmap.t) (def_ord:Ast.order) (tschm:Ast.typschm)
  :Ast.typschm * kind Envmap.t * kind Envmap.t =
  match tschm with
  | TypSchm_aux(ts,l) -> 
    (match ts with | TypSchm_ts(tquant,t) ->
      let tq,k_env,local_env = to_typquant k_env tquant in
      let typ = to_typ k_env def_ord t in
      TypSchm_aux(TypSchm_ts(tq,typ),l),k_env,local_env)

let rec to_pat (k_env : kind Envmap.t) (def_ord : Ast.order) (P_aux(pat,(l,_)) : tannot pat) : tannot pat = 
  P_aux(
    (match pat with 
    | P_lit(lit) -> P_lit(lit)
    | P_wild -> P_wild
    | P_as(pat,id) -> P_as(to_pat k_env def_ord pat, id)
    | P_typ(typ,pat) -> P_typ(to_typ k_env def_ord typ,to_pat k_env def_ord pat)
    | P_id(id) -> P_id(id)
    | P_app(id,pats) ->
      if pats = [] 
      then P_id (id)
      else P_app(id, List.map (to_pat k_env def_ord) pats)
    | P_record(fpats,_) -> 
      P_record(List.map 
                 (fun (FP_aux(FP_Fpat(id,fp),(l,_))) -> 
                      FP_aux(FP_Fpat(id, to_pat k_env def_ord fp),(l,NoTyp)))
                 fpats, false)
    | P_vector(pats) -> P_vector(List.map (to_pat k_env def_ord) pats)
    | P_vector_indexed(ipats) -> P_vector_indexed(List.map (fun (i,pat) -> i,to_pat k_env def_ord pat) ipats)
    | P_vector_concat(pats) -> P_vector_concat(List.map (to_pat k_env def_ord) pats)
    | P_tup(pats) -> P_tup(List.map (to_pat k_env def_ord) pats)
    | P_list(pats) -> P_list(List.map (to_pat k_env def_ord) pats)
    ), (l,NoTyp))


let rec to_letbind (k_env : kind Envmap.t) (def_ord : Ast.order) (LB_aux(lb,(l,_)) : tannot letbind) : tannot letbind =
  LB_aux(
    (match lb with
    | LB_val_explicit(typschm,pat,exp) ->
      let typsch, k_env, _  = to_typschm k_env def_ord typschm in
      LB_val_explicit(typsch,to_pat k_env def_ord pat, to_exp k_env def_ord exp)
    | LB_val_implicit(pat,exp) ->
      LB_val_implicit(to_pat k_env def_ord pat, to_exp k_env def_ord exp)
    ), (l,NoTyp))

and to_exp (k_env : kind Envmap.t) (def_ord : Ast.order) (E_aux(exp,(l,_)) :  exp) : exp = 
  E_aux(
    (match exp with
    | E_block(exps) -> E_block(List.map (to_exp k_env def_ord) exps)
    | E_nondet(exps) -> E_nondet(List.map (to_exp k_env def_ord) exps)
    | E_id(id) -> E_id(id)
    | E_lit(lit) -> E_lit(lit)
    | E_cast(typ,exp) -> E_cast(to_typ k_env def_ord typ, to_exp k_env def_ord exp)
    | E_app(f,args) -> 
      (match List.map (to_exp k_env def_ord) args with
        | [] -> E_app(f, [])
        | [E_aux(E_tuple(exps),_)] -> E_app(f, exps)
        | exps -> E_app(f, exps))
    | E_app_infix(left,op,right) -> 
      E_app_infix(to_exp k_env def_ord left, op, to_exp k_env def_ord right)
    | E_tuple(exps) -> E_tuple(List.map (to_exp k_env def_ord) exps)
    | E_if(e1,e2,e3) -> E_if(to_exp k_env def_ord e1, to_exp k_env def_ord e2, to_exp k_env def_ord e3)
    | E_for(id,e1,e2,e3,atyp,e4) -> 
      E_for(id,to_exp k_env def_ord e1, to_exp k_env def_ord e2,
            to_exp k_env def_ord e3,to_order k_env def_ord atyp, to_exp k_env def_ord e4)
    | E_vector(exps) -> E_vector(List.map (to_exp k_env def_ord) exps)
    | E_vector_indexed(iexps,Def_val_aux(default,(dl,_))) -> 
      E_vector_indexed (to_iexps true k_env def_ord iexps, 
                        Def_val_aux((match default with
                            | Def_val_empty -> Def_val_empty
                            | Def_val_dec e -> Def_val_dec (to_exp k_env def_ord e)),(dl,NoTyp)))
    | E_vector_access(vexp,exp) -> E_vector_access(to_exp k_env def_ord vexp, to_exp k_env def_ord exp)
    | E_vector_subrange(vex,exp1,exp2) -> 
      E_vector_subrange(to_exp k_env def_ord vex, to_exp k_env def_ord exp1, to_exp k_env def_ord exp2)
    | E_vector_update(vex,exp1,exp2) -> 
      E_vector_update(to_exp k_env def_ord vex, to_exp k_env def_ord exp1, to_exp k_env def_ord exp2)
    | E_vector_update_subrange(vex,e1,e2,e3) -> 
      E_vector_update_subrange(to_exp k_env def_ord vex, to_exp k_env def_ord e1, 
                               to_exp k_env def_ord e2, to_exp k_env def_ord e3)
    | E_vector_append(e1,e2) -> E_vector_append(to_exp k_env def_ord e1,to_exp k_env def_ord e2)
    | E_list(exps) -> E_list(List.map (to_exp k_env def_ord) exps)
    | E_cons(e1,e2) -> E_cons(to_exp k_env def_ord e1, to_exp k_env def_ord e2)
    | E_record(fexps) ->
      (match to_fexps true k_env def_ord fexps with
       | Some(fexps) -> E_record(fexps)
       | None -> raise (Reporting_basic.err_unreachable l "to_fexps with true returned none"))
    | E_record_update(exp,fexps) -> 
      (match to_fexps true k_env def_ord fexps with
      | Some(fexps) -> E_record_update(to_exp k_env def_ord exp, fexps)
      | _ -> raise (Reporting_basic.err_unreachable l "to_fexps with true returned none"))
    | E_field(exp,id) -> E_field(to_exp k_env def_ord exp, id)
    | E_case(exp,pexps) -> E_case(to_exp k_env def_ord exp, List.map (to_case k_env def_ord) pexps)
    | E_let(leb,exp) -> E_let(to_letbind k_env def_ord leb, to_exp k_env def_ord exp)
    | E_assign(lexp,exp) -> E_assign(to_lexp k_env def_ord lexp, to_exp k_env def_ord exp)
    | E_sizeof(nexp) -> E_sizeof(to_nexp k_env nexp)
    | E_exit exp -> E_exit(to_exp k_env def_ord exp)
    | E_return exp -> E_return(to_exp k_env def_ord exp)
    | E_assert(cond,msg) -> E_assert(to_exp k_env def_ord cond, to_exp k_env def_ord msg)
    | E_comment s -> E_comment s
    | E_comment_struc e -> E_comment_struc e
    | _ -> raise (Reporting_basic.err_unreachable l "to_exp given internal node")
    ), (l,NoTyp))

and to_lexp (k_env : kind Envmap.t) (def_ord : Ast.order) (LEXP_aux(exp,(l,_)) : tannot lexp) : tannot lexp = 
  LEXP_aux(
    (match exp with
    | LEXP_id(id) -> LEXP_id(id)
    | LEXP_memory(f,args) -> 
      (match List.map (to_exp k_env def_ord) args with
       | [] -> LEXP_memory(f,[])
       | [E_aux(E_tuple exps,_)] -> LEXP_memory(f,exps)
       | args -> LEXP_memory(f, args))
    | LEXP_cast(typ,id) ->
      LEXP_cast(to_typ k_env def_ord typ, id)
    | LEXP_tup tups ->
       let ltups = List.map (to_lexp k_env def_ord) tups in
       let is_ok_in_tup (LEXP_aux (le,(l,_))) =
         match le with
         | LEXP_id _ | LEXP_cast _ | LEXP_vector _ | LEXP_field _ | LEXP_vector_range _ | LEXP_tup _ -> ()
         | LEXP_memory _  ->
           typ_error l "only identifiers, fields, and vectors may be set in a tuple" None None None in
       List.iter is_ok_in_tup ltups;
       LEXP_tup(ltups)
    | LEXP_vector(vexp,exp) -> LEXP_vector(to_lexp k_env def_ord vexp, to_exp k_env def_ord exp)
    | LEXP_vector_range(vexp,exp1,exp2) -> 
      LEXP_vector_range(to_lexp k_env def_ord vexp, to_exp k_env def_ord exp1, to_exp k_env def_ord exp2)
    | LEXP_field(fexp,id) -> LEXP_field(to_lexp k_env def_ord fexp, id))
  , (l,NoTyp))

and to_case (k_env : kind Envmap.t) (def_ord : Ast.order) (Pat_aux(pex,(l,_)) : tannot pexp) : tannot pexp =
  match pex with 
  | Pat_exp(pat,exp) -> Pat_aux(Pat_exp(to_pat k_env def_ord pat, to_exp k_env def_ord exp),(l,NoTyp))

and to_fexps (fail_on_error:bool) (k_env:kind Envmap.t) (def_ord:Ast.order) (FES_aux (FES_Fexps(fexps,_),(l,_)))
  : tannot fexps option =
  let wrap fs = FES_aux (FES_Fexps(fs,false),(l,NoTyp)) in
  match fexps with
  | [] -> if fail_on_error then typ_error l "Record or record update must include fields" None None None
    else None
  | fexp::exps ->
    match fexp with
    | FE_aux(FE_Fexp(id,exp),(fl,_)) ->
      (match (to_fexps false k_env def_ord (wrap exps)) with
       | Some(FES_aux(FES_Fexps(fexps,_),(l,_))) ->
         Some(wrap(fexp::fexps))
       | None ->
         Some(wrap([fexp])))

and to_iexps (fail_on_error:bool) (k_env:kind Envmap.t) (def_ord:Ast.order) (iexps: (int * exp) list)
  :(int * exp) list =
  match iexps with
  | [] -> []
  | (i,exp)::exps ->
    (i, to_exp k_env def_ord exp)::to_iexps fail_on_error k_env def_ord exps
      
let to_default (names, k_env, default_order) (default : tannot default_spec) : (tannot default_spec) envs_out =
  match default with
  | DT_aux(df,l) ->
    (match df with 
    | DT_kind(bk,v) ->
      let k,k_typ = to_base_kind bk in
      let key = var_to_string v in
      DT_aux(DT_kind(k,v),l),(names,(Envmap.insert k_env (key,k_typ)),default_order)
    | DT_typ(typschm,id) ->
      let tps,_,_ = to_typschm k_env default_order typschm in
      DT_aux(DT_typ(tps,id),l),(names,k_env,default_order)
    | DT_order(o) ->
      (match o with
       | Ord_aux(Ord_inc,lo) ->
         let default_order = Ord_aux(Ord_inc,lo) in
         DT_aux(DT_order default_order,l),(names,k_env,default_order)
       | Ord_aux(Ord_dec,lo) ->
         let default_order = Ord_aux(Ord_dec,lo) in
         DT_aux(DT_order default_order,l),(names,k_env,default_order)
       | _ -> typ_error l "Default order must be Inc or Dec" None None None))

let to_spec (names,k_env,default_order) (val_: tannot val_spec) : (tannot val_spec) envs_out =
  match val_ with
  | VS_aux(vs,(l,_)) ->
    (match vs with
    | VS_val_spec(ts,id) ->
      let typsch,_,_ = to_typschm k_env default_order ts in
      VS_aux(VS_val_spec(typsch, id),(l,NoTyp)),(names,k_env,default_order)
    | VS_extern_spec(ts,id,s) ->
      let typsch,_,_ = to_typschm k_env default_order ts in
      VS_aux(VS_extern_spec(typsch,id,s),(l,NoTyp)),(names,k_env,default_order)
    | VS_extern_no_rename(ts,id) ->
      let typsch,_,_ = to_typschm k_env default_order ts in
       VS_aux(VS_extern_no_rename(typsch,id),(l,NoTyp)),(names,k_env,default_order))
    
let to_namescm ns = ns

let rec to_range (BF_aux(r,l)) = (* TODO add check that ranges are sensible for some definition of sensible *)
  BF_aux(
    (match r with
    | BF_single(i) -> BF_single(i)
    | BF_range(i1,i2) -> BF_range(i1,i2)
    | BF_concat(ir1,ir2) -> BF_concat( to_range ir1, to_range ir2)),
    l)

let to_type_union k_env default_order (Tu_aux(tu,l)) =
  match tu with
    | Tu_ty_id(atyp,id) -> (Tu_aux(Tu_ty_id ((to_typ k_env default_order atyp),id),l))
    | Tu_id id -> (Tu_aux(Tu_id(id),l)) 

let to_typedef (names,k_env,def_ord) (td: tannot type_def) : (tannot type_def) envs_out =
  match td with
  |TD_aux(td,(l,_)) ->
  (match td with 
  | TD_abbrev(id,name_scm_opt,typschm) ->
    let key = id_to_string id in
    let typschm,k_env,_ = to_typschm k_env def_ord typschm in
    let td_abrv = TD_aux(TD_abbrev(id,to_namescm name_scm_opt,typschm),(l,NoTyp)) in
    let typ = (match typschm with 
      | TypSchm_aux(TypSchm_ts(tq,typ), _) ->
        begin match (typquant_to_quantkinds k_env tq) with
        | [] -> {k = K_Typ}
        | typs -> {k= K_Lam(typs,{k=K_Typ})}
        end) in
    td_abrv,(names,Envmap.insert k_env (key,typ),def_ord)
  | TD_record(id,name_scm_opt,typq,fields,_) -> 
    let key = id_to_string id in
    let typq,k_env,_ = to_typquant k_env typq in
    let fields = List.map (fun (atyp,id) -> (to_typ k_env def_ord atyp),id) fields in (* Add check that all arms have unique names locally *)
    let td_rec = TD_aux(TD_record(id,to_namescm name_scm_opt,typq,fields,false),(l,NoTyp)) in
    let typ = (match (typquant_to_quantkinds k_env typq) with
      | [ ] -> {k = K_Typ}
      | typs -> {k = K_Lam(typs,{k=K_Typ})}) in
    td_rec, (names,Envmap.insert k_env (key,typ), def_ord)
  | TD_variant(id,name_scm_opt,typq,arms,_) ->
    let key = id_to_string id in
    let typq,k_env,_ = to_typquant k_env typq in
    let arms = List.map (to_type_union k_env def_ord) arms in (* Add check that all arms have unique names *)
    let td_var = TD_aux(TD_variant(id,to_namescm name_scm_opt,typq,arms,false),(l,NoTyp)) in
    let typ = (match (typquant_to_quantkinds k_env typq) with
      | [ ] -> {k = K_Typ}
      | typs -> {k = K_Lam(typs,{k=K_Typ})}) in
    td_var, (names,Envmap.insert k_env (key,typ), def_ord)
  | TD_enum(id,name_scm_opt,enums,_) -> 
    let key = id_to_string id in
    let keys = List.map id_to_string enums in
    let td_enum = TD_aux(TD_enum(id,to_namescm name_scm_opt,enums,false),(l,NoTyp)) in (* Add check that all enums have unique names *)
    let k_env = List.fold_right (fun k k_env -> Envmap.insert k_env (k,{k=K_Nat})) keys (Envmap.insert k_env (key,{k=K_Typ})) in
    td_enum, (names,k_env,def_ord)
  | TD_register(id,t1,t2,ranges) -> 
    let key = id_to_string id in
    let n1 = to_nexp k_env t1 in
    let n2 = to_nexp k_env t2 in
    let ranges = List.map (fun (range,id) -> (to_range range),id) ranges in
    TD_aux(TD_register(id,n1,n2,ranges),(l,NoTyp)), (names,Envmap.insert k_env (key, {k=K_Typ}),def_ord))

let to_kinddef (names,k_env,def_ord) (kd: tannot kind_def) : (tannot kind_def) envs_out =
  match kd with
  |KD_aux(td,(l,_)) ->
    (match td with 
     | KD_abbrev(kind,id,name_scm_opt,typschm) ->
       let key = id_to_string id in
       let _,k = to_kind k_env kind in
       (match k.k with
        | K_Typ | K_Lam _ ->
          let typschm,k_env,_ = to_typschm k_env def_ord typschm in
          let kd_abrv = KD_aux(KD_abbrev(kind,id,to_namescm name_scm_opt,typschm),(l,NoTyp)) in
          let typ = (match typschm with 
              | TypSchm_aux(TypSchm_ts(tq,typ), _) ->
                begin match (typquant_to_quantkinds k_env tq) with
                  | [] -> {k = K_Typ}
                  | typs -> {k= K_Lam(typs,{k=K_Typ})}
                end) in
          kd_abrv,(names,Envmap.insert k_env (key,typ),def_ord)
        | _ -> typ_error l "Def abbreviation with type scheme had declared kind other than Type" None None (Some k))
     | KD_nabbrev(kind,id,name_scm_opt,nexp) ->
       let key = id_to_string id in
       let _,k = to_kind k_env kind in
       (match k.k with
        | K_Nat ->
          let nexp = to_nexp k_env nexp in
          let kd_nabrv = KD_aux(KD_nabbrev(kind,id,to_namescm name_scm_opt, nexp),(l,NoTyp)) in
          kd_nabrv,(names,Envmap.insert k_env (key,k),def_ord)
        | _ -> typ_error l "Def abbreviation binding a number declared with kind other than Nat" None None (Some k))
     | KD_record(kind,id,name_scm_opt,typq,fields,_) -> 
       let key = id_to_string id in
       let _,k = to_kind k_env kind in
       let typq,k_env,_ = to_typquant k_env typq in
       (match k.k with
        | K_Typ | K_Lam _ ->
          let fields = List.map (fun (atyp,id) -> (to_typ k_env def_ord atyp),id) fields in (* Add check that all arms have unique names locally *)
          let kd_rec = KD_aux(KD_record(kind,id,to_namescm name_scm_opt,typq,fields,false),(l,NoTyp)) in
          let typ = (match (typquant_to_quantkinds k_env typq) with
              | [ ] -> {k = K_Typ}
              | typs -> {k = K_Lam(typs,{k=K_Typ})}) in
          kd_rec, (names,Envmap.insert k_env (key,typ), def_ord)
        | _ -> typ_error l "Def abbreviation binding a record has kind other than Type" None None (Some k))
     | KD_variant(kind,id,name_scm_opt,typq,arms,_) ->
       let key = id_to_string id in
       let _,k = to_kind k_env kind in
       let typq,k_env,_ = to_typquant k_env typq in
       (match k.k with
        | K_Typ | K_Lam _ ->
          let arms = List.map (to_type_union k_env def_ord) arms in (* Add check that all arms have unique names *)
          let kd_var = KD_aux(KD_variant(kind,id,to_namescm name_scm_opt,typq,arms,false),(l,NoTyp)) in
          let typ = (match (typquant_to_quantkinds k_env typq) with
              | [ ] -> {k = K_Typ}
              | typs -> {k = K_Lam(typs,{k=K_Typ})}) in
          kd_var, (names,Envmap.insert k_env (key,typ), def_ord)
        | _ -> typ_error l "Def abbreviation binding a variant has kind other than Type" None None (Some k))
     | KD_enum(kind,id,name_scm_opt,enums,_) -> 
       let key = id_to_string id in
       let keys = List.map id_to_string enums in
       let _,k= to_kind k_env kind in
       (match k.k with
        | K_Typ ->
          let kd_enum = KD_aux(KD_enum(kind,id,to_namescm name_scm_opt,enums,false),(l,NoTyp)) in (* Add check that all enums have unique names *)
          let k_env = List.fold_right (fun k k_env -> Envmap.insert k_env (k,{k=K_Nat})) keys (Envmap.insert k_env (key,{k=K_Typ})) in
          kd_enum, (names,k_env,def_ord)
        | _ -> typ_error l "Def abbreviation binding an enum has kind other than Type" None None (Some k))
     | KD_register(kind,id,t1,t2,ranges) -> 
       let key = id_to_string id in
       let n1 = to_nexp k_env t1 in
       let n2 = to_nexp k_env t2 in
       let _,k = to_kind k_env kind in
       match k.k with
       | K_Typ ->
         let ranges = List.map (fun (range,id) -> (to_range range),id) ranges in
         KD_aux(KD_register(kind,id,n1,n2,ranges),(l,NoTyp)), (names,Envmap.insert k_env (key, {k=K_Typ}),def_ord)
       | _ -> typ_error l "Def abbreviation binding a register type has kind other than Type" None None (Some k))


let to_tannot_opt (k_env:kind Envmap.t) (def_ord:Ast.order) (Typ_annot_opt_aux(tp,l))
  :tannot_opt * kind Envmap.t * kind Envmap.t=
  match tp with
  | Typ_annot_opt_some(tq,typ) ->
    let typq,k_env,k_local = to_typquant k_env tq in
    Typ_annot_opt_aux(Typ_annot_opt_some(typq,to_typ k_env def_ord typ),l),k_env,k_local

let to_effects_opt (k_env : kind Envmap.t) (Effect_opt_aux(e,l)) : effect_opt =
  match e with
  | Effect_opt_pure -> Effect_opt_aux(Effect_opt_pure,l)
  | Effect_opt_effect(typ) -> Effect_opt_aux(Effect_opt_effect(to_effects k_env typ),l)

let to_funcl (names,k_env,def_ord) (FCL_aux(fcl,(l,_)) : tannot funcl) : (tannot funcl) =
  match fcl with
  | FCL_Funcl(id,pat,exp) -> 
    FCL_aux(FCL_Funcl(id, to_pat k_env def_ord pat, to_exp k_env def_ord exp),(l,NoTyp))

let to_fundef  (names,k_env,def_ord) (FD_aux(fd,(l,_)): tannot fundef) : (tannot fundef) envs_out = 
  match fd with
  | FD_function(rec_opt,tannot_opt,effects_opt,funcls) -> 
    let tannot_opt, k_env,_ = to_tannot_opt k_env def_ord tannot_opt in
    FD_aux(FD_function(rec_opt, tannot_opt, to_effects_opt k_env effects_opt,
                       List.map (to_funcl (names, k_env, def_ord)) funcls), (l,NoTyp)), (names,k_env,def_ord)
    
type def_progress =
    No_def
  | Def_place_holder of id * Parse_ast.l
  | Finished of tannot def

type partial_def = ((tannot def) * bool) ref * kind Envmap.t

let rec def_in_progress (id : id) (partial_defs : (id * partial_def) list) : partial_def option =
  match partial_defs with
  | [] -> None
  | (n,pd)::defs -> 
    (match n,id with
    | Id_aux(Id(n),_), Id_aux(Id(i),_) -> if (n = i) then Some(pd) else def_in_progress id defs
    | _,_ -> def_in_progress id defs)

let to_alias_spec k_env def_ord (AL_aux(ae,(le,_))) = 
  AL_aux(
    (match ae with
      | AL_subreg(reg, field) -> AL_subreg(reg, field)
      | AL_bit(reg,range) -> AL_bit(reg,to_exp k_env def_ord range)
      | AL_slice(reg,base,stop) ->
        AL_slice(reg,to_exp k_env def_ord base,to_exp k_env def_ord stop)
      | AL_concat(first,second) -> AL_concat(first,second)
    ), (le,NoTyp))

let to_dec (names,k_env,def_ord) (DEC_aux(regdec,(l,_))) =
  DEC_aux(
    (match regdec with
      | DEC_reg(typ,id) ->
        DEC_reg(to_typ k_env def_ord typ,id)
      | DEC_alias(id,ae) ->
        DEC_alias(id,to_alias_spec k_env def_ord ae)
      | DEC_typ_alias(typ,id,ae) ->
        DEC_typ_alias(to_typ k_env def_ord typ,id,to_alias_spec k_env def_ord ae)
    ),(l,NoTyp))
      
let to_def (names, k_env, def_ord) partial_defs def : def_progress envs_out * (id * partial_def) list = 
  let envs = (names,k_env,def_ord) in
  match def with
  | DEF_kind(k_def) ->
    let kd,envs = to_kinddef envs k_def in
    ((Finished(DEF_kind(kd))),envs),partial_defs
  | DEF_type(t_def) -> 
    let td,envs = to_typedef envs t_def in
    ((Finished(DEF_type(td))),envs),partial_defs
  | DEF_fundef(f_def) -> 
    let fd,envs = to_fundef envs f_def in
    ((Finished(DEF_fundef(fd))),envs),partial_defs
  | DEF_val(lbind) -> 
    let lb = to_letbind k_env def_ord lbind in
    ((Finished(DEF_val(lb))),envs),partial_defs
  | DEF_spec(val_spec) -> 
    let vs,envs = to_spec envs val_spec in
    ((Finished(DEF_spec(vs))),envs),partial_defs
  | DEF_default(typ_spec) -> 
    let default,envs = to_default envs typ_spec in
    ((Finished(DEF_default(default))),envs),partial_defs
  | DEF_comm c-> ((Finished(DEF_comm c)),envs),partial_defs
  | DEF_reg_dec(dec) ->
    let d = to_dec envs dec in
    ((Finished(DEF_reg_dec(d))),envs),partial_defs
  | DEF_scattered(SD_aux(sd,(l,_))) ->
    (match sd with
    | SD_scattered_function(rec_opt, tannot_opt, effects_opt, id) ->
      let tannot,k_env',k_local = to_tannot_opt k_env def_ord tannot_opt in
      let effects_opt = to_effects_opt k_env' effects_opt in
      (match (def_in_progress id partial_defs) with
       | None ->
         let partial_def = ref ((DEF_fundef(FD_aux(FD_function(rec_opt,tannot,effects_opt,[]),(l,NoTyp)))),false) in
         (No_def,envs),((id,(partial_def,k_local))::partial_defs)
       | Some(d,k) ->
         typ_error l
           "Scattered function definition header name already in use by scattered definition" (Some id) None None)
    | SD_scattered_funcl(funcl) -> 
      (match funcl with
       | FCL_aux(FCL_Funcl(id,_,_),_) -> 
         (match (def_in_progress id partial_defs) with
          | None ->
            typ_error l
              "Scattered function definition clause does not match any exisiting function definition headers"
              (Some id) None None
          | Some(d,k) ->
            (match !d with
             | DEF_fundef(FD_aux(FD_function(r,t,e,fcls),fl)),false -> 
               let funcl = to_funcl (names,Envmap.union k k_env,def_ord) funcl in 
               d:= DEF_fundef(FD_aux(FD_function(r,t,e,fcls@[funcl]),fl)),false;
               (No_def,envs),partial_defs
             | _,true -> typ_error l "Scattered funciton definition clauses extends ended defintion" (Some id) None None
             | _ -> typ_error l
                      "Scattered function definition clause matches an existing scattered type definition header"
                      (Some id) None None)))
    | SD_scattered_variant(id,naming_scheme_opt,typquant) -> 
      let name = to_namescm naming_scheme_opt in
      let typq, k_env',_ = to_typquant k_env typquant in
      let kind = (match (typquant_to_quantkinds k_env' typq) with
        | [ ] -> {k = K_Typ}
        | typs -> {k = K_Lam(typs,{k=K_Typ})}) in
      (match (def_in_progress id partial_defs) with
       | None -> let partial_def = ref ((DEF_type(TD_aux(TD_variant(id,name,typq,[],false),(l,NoTyp)))),false) in
         (Def_place_holder(id,l),
          (names,Envmap.insert k_env ((id_to_string id),kind),def_ord)),(id,(partial_def,k_env'))::partial_defs
       | Some(d,k) ->
         typ_error l "Scattered type definition header name already in use by scattered definition" (Some id) None None)
    | SD_scattered_unioncl(id,tu) -> 
      (match (def_in_progress id partial_defs) with
       | None -> typ_error l
                   "Scattered type definition clause does not match any existing type definition headers"
                   (Some id) None None
       | Some(d,k) ->
         (match !d with
          | DEF_type(TD_aux(TD_variant(id,name,typq,arms,false),tl)), false -> 
            d:= DEF_type(TD_aux(TD_variant(id,name,typq,arms@[to_type_union k def_ord tu],false),tl)),false;
            (No_def,envs),partial_defs
          | _,true -> typ_error l "Scattered type definition clause extends ended definition" (Some id) None None
          | _ -> typ_error l
                   "Scattered type definition clause matches an existing scattered function definition header"
                   (Some id) None None))
    | SD_scattered_end(id) ->
      (match (def_in_progress id partial_defs) with
      | None -> typ_error l "Scattered definition end does not match any open scattered definitions" (Some id) None None
      | Some(d,k) ->
        (match !d with
        | (DEF_type(_) as def),false ->
          d:= (def,true);
          (No_def,envs),partial_defs
        | (DEF_fundef(_) as def),false ->
          d:= (def,true);
          ((Finished def), envs),partial_defs
        | _, true -> 
          typ_error l "Scattered definition ended multiple times" (Some id) None None
        | _ -> raise (Reporting_basic.err_unreachable l "Something in partial_defs other than fundef and type"))))
    
let rec to_defs_helper envs partial_defs = function
  | [] -> ([],envs,partial_defs)
  | d::ds  -> let ((d', envs), partial_defs) = to_def envs partial_defs d in
              let (defs,envs,partial_defs) = to_defs_helper envs partial_defs ds in
              (match d' with
              | Finished def -> (def::defs,envs, partial_defs)
              | No_def -> defs,envs,partial_defs
              | Def_place_holder(id,l) -> 
                (match (def_in_progress id partial_defs) with
                 | None ->
                   raise
                     (Reporting_basic.err_unreachable l "Id stored in place holder not retrievable from partial defs")
                 | Some(d,k) -> 
                   if (snd !d) 
                   then (fst !d) :: defs, envs, partial_defs
                   else typ_error l "Scattered type definition never ended" (Some id) None None))                

let to_checked_ast (default_names : Nameset.t) (kind_env : kind Envmap.t) (def_ord : Ast.order) (Defs(defs)) =
  let defs,(_,k_env,def_ord),partial_defs = to_defs_helper (default_names,kind_env,def_ord) [] defs in
  List.iter 
    (fun (id,(d,k)) -> 
      (match !d with
      | (d,false) -> typ_error Parse_ast.Unknown "Scattered definition never ended" (Some id) None None
      | (_, true) -> ()))
    partial_defs;
  (Defs defs),k_env,def_ord
