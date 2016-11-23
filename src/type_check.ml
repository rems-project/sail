open Big_int
open Ast
open Type_internal
type kind = Type_internal.kind
type typ = Type_internal.t
type 'a exp = 'a Ast.exp
type 'a emap = 'a Envmap.t

type envs = Env of def_envs * tannot emap * bounds_env * t_arg emap
type 'a envs_out = 'a * envs

let id_to_string (Id_aux(id,l)) =
  match id with
    | Id(s) -> s
    | DeIid(s) -> s

let get_e_typ (E_aux(_,(_,a))) =
  match a with
  | Base((_,t),_,_,_,_,_) -> t
  | _ -> new_t ()

let typ_error l msg  = raise (Reporting_basic.err_typ l msg)

let rec field_equivs fields fmaps = 
  match fields with
    | [] -> Some []
    | (FP_aux(FP_Fpat(id,pat),(l,annot)))::fields -> 
      if (List.mem_assoc (id_to_string id) fmaps)
      then match (field_equivs fields fmaps) with
        | None -> None
        | Some [] -> None
        | Some fs -> Some(((List.assoc (id_to_string id) fmaps),id,l,pat)::fs)
      else None

let rec fields_to_rec fields rec_env = 
  match rec_env with
    | [] -> None
    | (id,Register,tannot,fmaps)::rec_env -> fields_to_rec fields rec_env
    | (id,Record,tannot,fmaps)::rec_env ->
      if (List.length fields) = (List.length fmaps) then
        match field_equivs fields fmaps with
          | Some(ftyps) -> Some(id,tannot,ftyps)
          | None -> fields_to_rec fields rec_env
      else fields_to_rec fields rec_env

let kind_to_k (K_aux((K_kind baseks),l)) =
  let bk_to_k (BK_aux(bk,l')) =
    match bk with
      | BK_type -> { k = K_Typ}
      | BK_nat -> { k = K_Nat}
      | BK_order -> { k = K_Ord} 
      | BK_effect -> { k = K_Efct}
  in
  match baseks with
    | [] -> raise (Reporting_basic.err_unreachable l "Empty kind")
    | [bk] -> bk_to_k bk
    | bks -> (match List.rev bks with
             | [] -> raise (Reporting_basic.err_unreachable l "Empty after reverse")
             | out::args -> {k = K_Lam( List.map bk_to_k (List.rev args), bk_to_k out) })

let rec has_typ_app check_nested name (Typ_aux(typ,_)) =
  match typ with
    | Typ_id i -> name = (id_to_string i) 
    | Typ_tup ts -> List.exists (has_typ_app check_nested name) ts
    | Typ_app(i,args) -> name = (id_to_string i) || 
                         (check_nested && (List.exists (has_typ_app_ta check_nested name) args))
    | _ -> false
and has_typ_app_ta check_nested name (Typ_arg_aux(ta,_)) =
  match ta with
    | Typ_arg_typ t -> has_typ_app check_nested name t
    | _ -> false

let rec extract_if_first recur name (Typ_aux(typ,l)) =
  match (typ,recur) with
    | (Typ_id i,_) | (Typ_app(i,_),_) -> 
      if name = (id_to_string i) then Some(typ, Typ_aux(Typ_id (Id_aux (Id "unit", l)),l)) else None
    | (Typ_tup[t'],true) -> extract_if_first false name t'
    | (Typ_tup[t1;t2],true) -> (match extract_if_first false name t1 with
      | Some(t,_) -> Some(t,t2)
      | None -> None)
    | (Typ_tup(t'::ts),true) -> (match (extract_if_first false name t') with
        | Some(t,_) -> Some(t, Typ_aux(Typ_tup ts,l))
        | None -> None)
    | _ -> None

let rec typ_to_t envs imp_ok fun_ok (Typ_aux(typ,l)) =
  let (Env(d_env,t_env,b_env,tp_env)) = envs in
  let trans t = typ_to_t envs false false t in 
  match typ with
  | Typ_id i ->
    let t_init = {t = Tid (id_to_string i)} in
    let t_abbrev,_ = get_abbrev d_env t_init in
    t_abbrev
  | Typ_var (Kid_aux((Var i),l')) -> {t = Tvar i}
  | Typ_fn (ty1,ty2,e) -> 
    if fun_ok 
    then 
      if has_typ_app false "implicit" ty1 
      then 
        if imp_ok 
        then (match extract_if_first true "implicit" ty1 with
            | Some(imp,new_ty1) -> (match imp with
                | Typ_app(_,[Typ_arg_aux(Typ_arg_nexp ((Nexp_aux(n,l')) as ne),_)]) -> 
                  {t = Tfn (trans new_ty1, trans ty2, IP_user (anexp_to_nexp envs ne), aeffect_to_effect e)}
                | _ -> typ_error l "Declaring an implicit parameter requires a Nat specification")
            | None -> typ_error l "A function type with an implicit parameter must declare the implicit first")
        else typ_error l "This function has one (or more) implicit parameter(s) not permitted here"
      else {t = Tfn (trans ty1,trans ty2,IP_none,aeffect_to_effect e)}
    else typ_error l "Function types are only permitted at the top level."
  | Typ_tup(tys) -> {t = Ttup (List.map trans tys) }
  | Typ_app(i,args) -> {t = Tapp (id_to_string i,List.map (typ_arg_to_targ envs) args) }
  | Typ_wild -> new_t ()
and typ_arg_to_targ envs (Typ_arg_aux(ta,l)) = 
  match ta with
    | Typ_arg_nexp n -> TA_nexp (anexp_to_nexp envs n)
    | Typ_arg_typ t -> TA_typ (typ_to_t envs false false t)
    | Typ_arg_order o -> TA_ord (aorder_to_ord o)
    | Typ_arg_effect e -> TA_eft (aeffect_to_effect e)
and anexp_to_nexp envs ((Nexp_aux(n,l)) : Ast.nexp) : nexp =
  let (Env(d_env,t_env,b_env,tp_env)) = envs in
  match n with
  | Nexp_var (Kid_aux((Var i),l')) -> mk_nv i
  | Nexp_id id ->
    let s = id_to_string id in
    (match Envmap.apply d_env.nabbrevs s with
     |Some n -> n
     | None -> typ_error l ("Unbound nat id " ^ s))
  | Nexp_constant i -> mk_c_int i
  | Nexp_times(n1,n2) -> mk_mult (anexp_to_nexp envs n1) (anexp_to_nexp envs n2)
  | Nexp_sum(n1,n2) -> mk_add (anexp_to_nexp envs n1) (anexp_to_nexp envs n2)
  | Nexp_minus(n1,n2) -> mk_sub (anexp_to_nexp envs n1) (anexp_to_nexp envs n2)
  | Nexp_exp n -> mk_2n(anexp_to_nexp envs n)
  | Nexp_neg n -> mk_neg(anexp_to_nexp envs n)
and aeffect_to_effect ((Effect_aux(e,l)) : Ast.effect) : effect = 
  match e with
    | Effect_var (Kid_aux((Var i),l')) -> {effect = Evar i}
    | Effect_set effects -> {effect = Eset effects}
and aorder_to_ord (Ord_aux(o,l) : Ast.order) = 
  match o with
    | Ord_var (Kid_aux((Var i),l')) -> {order = Ovar i}
    | Ord_inc -> {order = Oinc}
    | Ord_dec -> {order = Odec}

let rec quants_to_consts ((Env (d_env,t_env,b_env,tp_env)) as env) qis : (t_params * t_arg list * nexp_range list) =
  match qis with 
    | [] -> [],[],[]
    | (QI_aux(qi,l))::qis ->
      let (ids,typarms,cs) = quants_to_consts env qis in
      (match qi with
        | QI_id(KOpt_aux(ki,l')) -> 
          (match ki with 
            | KOpt_none (Kid_aux((Var i),l'')) -> 
              (match Envmap.apply d_env.k_env i with
                | Some k -> 
                  let targ = match k.k with 
                    | K_Typ  -> TA_typ {t = Tvar i}
                    | K_Nat  -> TA_nexp (mk_nv i)                      
                    | K_Ord  -> TA_ord { order = Ovar i}
                    | K_Efct -> TA_eft { effect = Evar i}
                    | _ -> raise (Reporting_basic.err_unreachable l'' "illegal kind allowed") in
                  ((i,k)::ids,targ::typarms,cs)
                | None -> raise (Reporting_basic.err_unreachable l'' "Unkinded id without default after initial check"))
            | KOpt_kind(kind,Kid_aux((Var i),l'')) -> 
              let k = kind_to_k kind in
              let targ = match k.k with
                | K_Typ  -> TA_typ {t = Tvar i}
                | K_Nat  -> TA_nexp (mk_nv i)                      
                | K_Ord  -> TA_ord { order = Ovar i}
                | K_Efct -> TA_eft { effect = Evar i}
                | K_Lam _ -> typ_error l'' "kind -> kind not permitted here"
                | _ -> raise (Reporting_basic.err_unreachable l'' "Kind either infer or internal here")  in
              ((i,k)::ids,targ::typarms,cs))
        | QI_const(NC_aux(nconst,l')) -> 
          (*TODO: somehow the requirement vs best guarantee needs to be derived from user or context*)
          (match nconst with
           | NC_fixed(n1,n2) ->
             (ids,typarms,Eq(Specc l',anexp_to_nexp env n1,anexp_to_nexp env n2)::cs)
           | NC_bounded_ge(n1,n2) ->
             (ids,typarms,GtEq(Specc l',Guarantee,anexp_to_nexp env n1,anexp_to_nexp env n2)::cs)
           | NC_bounded_le(n1,n2) ->
             (ids,typarms,LtEq(Specc l',Guarantee,anexp_to_nexp env n1,anexp_to_nexp env n2)::cs)
           | NC_nat_set_bounded(Kid_aux((Var i),l''), bounds) -> (ids,typarms,In(Specc l',i,bounds)::cs)))

let typq_to_params envs (TypQ_aux(tq,l)) =
  match tq with
    | TypQ_tq(qis) -> quants_to_consts envs qis
    | TypQ_no_forall -> [],[],[]

let typschm_to_tannot envs imp_parm_ok fun_ok ((TypSchm_aux(typschm,l)):typschm) (tag : tag) : tannot = 
  match typschm with
    | TypSchm_ts(tq,typ) -> 
      let t = typ_to_t envs imp_parm_ok fun_ok typ in
      let (ids,_,constraints) = typq_to_params envs tq in
      Base((ids,t),tag,constraints,pure_e,pure_e,nob)

let into_register_typ t =
  match t.t with
    | Tapp("register",_) -> t
    | Tabbrev(ti,{t=Tapp("register",_)}) -> t
    | _ -> {t=Tapp("register",[TA_typ t])}
        
let into_register d_env (t : tannot) : tannot =
  match t with
    | Base((ids,ty),tag,constraints,eftl,eftr,bindings) -> 
      let ty',_ =  get_abbrev d_env ty in
      Base((ids,into_register_typ ty'),tag,constraints,eftl,eftr,bindings)
    | t -> t

let rec check_pattern envs emp_tag expect_t (P_aux(p,(l,annot))) : ((tannot pat) * (tannot emap) * nexp_range list * bounds_env * t)  =
  let (Env(d_env,t_env,b_env,tp_env)) = envs in
  (*let _ = Printf.eprintf "checking pattern with expected type %s\n" (t_to_string expect_t) in*)
  let expect_t,cs = get_abbrev d_env expect_t in
  (*let _ = Printf.eprintf "check pattern expect_t after abbrev %s\n" (t_to_string expect_t) in*)
  let expect_actual = match expect_t.t with | Tabbrev(_,t) -> t | _ -> expect_t in
  match p with
    | P_lit (L_aux(lit,l')) ->
      let t,lit =
        (match lit with
          | L_unit  -> unit_t,lit 
          | L_zero  -> bit_t,lit
          | L_one   -> bit_t,lit
          | L_true  -> bit_t,L_one
          | L_false -> bit_t,L_zero
          | L_num i -> 
            (match expect_actual.t with
              | Tid "bit" -> 
                if i = 0 then bit_t,L_zero 
                else if i = 1 then bit_t,L_one
                else {t = Tapp("atom",
                               [TA_nexp (mk_c_int i)])},lit
              | _ -> {t = Tapp("atom",
                               [TA_nexp (mk_c_int i)])},lit)
          | L_hex s -> 
            let size = big_int_of_int ((String.length s) * 4) in
            let is_inc = match d_env.default_o.order with | Oinc -> true | _ -> false in
            {t = Tapp("vector",
                      [TA_nexp (if is_inc then n_zero else mk_c(sub_big_int size one));
                       TA_nexp (mk_c size);
                       TA_ord d_env.default_o; TA_typ{t=Tid "bit"}])},lit
          | L_bin s -> 
            let size = big_int_of_int (String.length s) in
            let is_inc = match d_env.default_o.order with | Oinc -> true | _ -> false in
            {t = Tapp("vector",
                      [TA_nexp(if is_inc then n_zero else mk_c(sub_big_int size one));
                       TA_nexp (mk_c size);
                       TA_ord d_env.default_o;TA_typ{t = Tid"bit"}])},lit
          | L_string s -> {t = Tid "string"},lit
          | L_undef -> typ_error l' "Cannot pattern match on undefined") in
      (*let _ = Printf.eprintf "checking pattern literal. expected type is %s. t is %s\n"
        (t_to_string expect_t) (t_to_string t) in*)
      let t',cs' = type_consistent (Patt l) d_env Require true t expect_t in
      let cs_l = cs@cs' in
      (P_aux(P_lit(L_aux(lit,l')),(l,cons_tag_annot t emp_tag cs_l)),Envmap.empty,cs_l,nob,t)
    | P_wild -> 
      (P_aux(p,(l,cons_tag_annot expect_t emp_tag cs)),Envmap.empty,cs,nob,expect_t)
    | P_as(pat,id) ->
      let v = id_to_string id in
      let (pat',env,constraints,bounds,t) = check_pattern envs emp_tag expect_t pat in
      let bounds = extract_bounds d_env v t in
      let tannot = Base(([],t),emp_tag,cs,pure_e,pure_e,bounds) in
      (P_aux(P_as(pat',id),(l,tannot)),Envmap.insert env (v,tannot),cs@constraints,bounds,t)
    | P_typ(typ,pat) -> 
      let t = typ_to_t envs false false typ in
      let t = typ_subst tp_env false t in
      let (pat',env,constraints,bounds,u) = check_pattern envs emp_tag t pat in
      let t,cs_consistent = type_consistent (Patt l) d_env Guarantee false t expect_t in
      (P_aux(P_typ(typ,pat'),(l,tag_annot t emp_tag)),env,cs@constraints@cs_consistent,bounds,t)
    | P_id id -> 
      let i = id_to_string id in
      let default_bounds = extract_bounds d_env i expect_t in
      let default = let id_annot = Base(([],expect_t),emp_tag,cs,pure_e,pure_e,default_bounds) in
                    let pat_annot = match is_enum_typ d_env expect_t with
                      | None -> id_annot
                      | Some n -> Base(([],expect_t), Enum n, cs,pure_e,pure_e,default_bounds) in
                    (P_aux(p,(l,pat_annot)),Envmap.from_list [(i,id_annot)],cs,default_bounds,expect_t) in
      (match Envmap.apply t_env i with
       | Some(Base((params,t),Constructor n,cs,efl,efr,bounds)) ->
          let t,cs,ef,_ = subst params false false t cs efl in
          (match t.t with
            | Tfn({t = Tid "unit"},t',_,ef) ->
              if conforms_to_t d_env true false t' expect_t 
              then
                let tp,cp = type_consistent (Expr l) d_env Guarantee false t' expect_t in
                (P_aux(P_app(id,[]),(l,tag_annot t (Constructor n))),Envmap.empty,cs@cp,bounds,tp)
              else default
            | Tfn(t1,t',_,e) ->
              if conforms_to_t d_env true false t' expect_t
              then typ_error l ("Constructor " ^ i ^ " expects arguments of type " ^ (t_to_string t) ^ ", found none")
              else default
            | _ -> raise (Reporting_basic.err_unreachable l "Constructor tannot does not have function type"))
        | Some(Base((params,t),Enum max,cs,efl,efr,bounds)) ->
          let t,cs,ef,_ = subst params false false t cs efl in
          if conforms_to_t d_env false false t expect_t
          then 
            let tp,cp = type_consistent (Expr l) d_env Guarantee false t expect_t in
            (P_aux(P_app(id,[]),(l,tag_annot t (Enum max))),Envmap.empty,cs@cp,bounds,tp)
          else default
        | _ -> default)
    | P_app(id,pats) -> 
      let i = id_to_string id in
      (*let _ = Printf.eprintf "checking constructor pattern %s\n" i in*)
      (match Envmap.apply t_env i with
        | None | Some NoTyp | Some Overload _ -> typ_error l ("Constructor " ^ i ^ " in pattern is undefined")
        | Some(Base((params,t),Constructor n,constraints,efl,efr,bounds)) -> 
          let t,dec_cs,_,_ = subst params false false t constraints efl in
          (match t.t with
            | Tid id -> if pats = [] 
              then let t',ret_cs = type_consistent (Patt l) d_env Guarantee false t expect_t in
                   (P_aux(p,(l,cons_tag_annot t' (Constructor n) dec_cs)), Envmap.empty,dec_cs@ret_cs,nob,t')
              else typ_error l ("Constructor " ^ i ^ " does not expect arguments")
            | Tfn(t1,t2,IP_none,ef) ->
              let t',ret_cs = type_consistent (Patt l) d_env Guarantee false t2 expect_t in
              (match pats with
              | [] -> let _ = type_consistent (Patt l) d_env Guarantee false unit_t t1 in
                      (P_aux(P_app(id,[]),(l,cons_tag_annot t' (Constructor n) dec_cs)),
                       Envmap.empty,dec_cs@ret_cs,nob,t')
              | [p] -> let (p',env,p_cs,bounds,u) = check_pattern envs emp_tag t1 p in
                       (P_aux(P_app(id,[p']),
                              (l,cons_tag_annot t' (Constructor n) dec_cs)),env,dec_cs@p_cs@ret_cs,bounds,t')
              | pats -> let (pats',env,p_cs,bounds,u) = 
                          match check_pattern envs emp_tag t1 (P_aux(P_tup(pats),(l,annot))) with
                          | ((P_aux(P_tup(pats'),_)),env,constraints,bounds,u) -> (pats',env,constraints,bounds,u)
                          | _ -> assert false in
                        (P_aux(P_app(id,pats'),
                               (l,cons_tag_annot t' (Constructor n) dec_cs)),env,dec_cs@p_cs@ret_cs,bounds,t'))
            | _ -> typ_error l ("Identifier " ^ i ^ " must be a union constructor"))
        | Some(Base((params,t),tag,constraints,efl,efr,bounds)) -> 
          typ_error l ("Identifier " ^ i ^ " used in pattern is not a union constructor"))
    | P_record(fpats,_) -> 
      (match (fields_to_rec fpats d_env.rec_env) with
        | None -> typ_error l ("No struct exists with the listed fields")
        | Some(id,tannot,typ_pats) ->
          (match tannot with
            | (Base((vs,t),tag,cs,eft,_,bounds)) ->
              (*let tup = {t = Ttup(List.map (fun (t,_,_,_) -> t) typ_pats)} in*)
              (*let ft = {t = Tfn(tup,t, IP_none,pure_e) } in*)
              let (ft_subst,cs,_,_) = subst vs false false t cs pure_e in
              let subst_rtyp,subst_typs = 
                match ft_subst.t with | Tfn({t=Ttup tups},rt,_,_) -> rt,tups 
                  | _ -> raise (Reporting_basic.err_unreachable l "fields_to_rec gave a non function type") in
              let pat_checks = 
                List.map2 (fun (_,id,l,pat) styp -> 
                  let (pat,env,constraints,new_bounds,u) = check_pattern envs emp_tag styp pat in
                  let pat = FP_aux(FP_Fpat(id,pat),(l,Base(([],styp),tag,constraints,pure_e,pure_e,new_bounds))) in
                  (pat,env,constraints,new_bounds)) typ_pats subst_typs in
              let pats' = List.map (fun (a,_,_,_) -> a) pat_checks in
              (*Need to check for variable duplication here*)
              let env = List.fold_right (fun (_,env,_,_) env' -> Envmap.union env env') pat_checks Envmap.empty in
              let constraints = (List.fold_right (fun (_,_,cs,_) cons -> cs@cons) pat_checks [])@cs in
              let bounds = List.fold_right (fun (_,_,_,bounds) b_env -> merge_bounds bounds b_env) pat_checks nob in
              let t',cs' = type_consistent (Patt l) d_env Guarantee false ft_subst expect_t in
              (P_aux((P_record(pats',false)),(l,cons_tag_annot t' emp_tag (cs@cs'))),env,constraints@cs',bounds,t')
            | _ -> raise (Reporting_basic.err_unreachable l "fields_to_rec returned a non Base tannot")))
    | P_vector pats -> 
      let (item_t, base, rise, ord) = match expect_actual.t with 
        | Tapp("vector",[TA_nexp b;TA_nexp r;TA_ord o;TA_typ i]) -> (i,b,r,o)
        | Tuvar _ -> (new_t (),new_n (),new_n(), d_env.default_o) 
        | _ -> typ_error l ("Expected a " ^ t_to_string expect_actual ^ " but found a vector") in
      let (pats',ts,t_envs,constraints,bounds) = 
        List.fold_right 
          (fun pat (pats,ts,t_envs,constraints,bounds) -> 
            let (pat',t_env,cons,bs,t) = check_pattern envs emp_tag item_t pat in 
            ((pat'::pats),(t::ts),(t_env::t_envs),(cons@constraints),merge_bounds bs bounds))
          pats ([],[],[],[],nob) in
      let env = List.fold_right (fun e env -> Envmap.union e env) t_envs Envmap.empty in (*Need to check for non-duplication of variables*)
      let (u,cs) = List.fold_right (fun u (t,cs) ->
          let t',cs = type_consistent (Patt l) d_env Require true u t in t',cs) ts (item_t,[]) in
      let len = List.length ts in
      let t = 
        match (ord.order,d_env.default_o.order) with
        | (Oinc,_) | (Ovar _, Oinc) | (Ouvar _,Oinc) -> 
          {t = Tapp("vector",[TA_nexp n_zero;
                              TA_nexp (mk_c_int len);
                              TA_ord{order=Oinc};
                              TA_typ u])}
        | (Odec,_) | (Ovar _, Odec) | (Ouvar _,Odec) -> 
          {t= Tapp("vector", [TA_nexp (mk_c (if len = 0 then zero else (big_int_of_int (len -1))));
                              TA_nexp (mk_c_int len);
                              TA_ord{order=Odec};
                              TA_typ u;])}
        | _ -> raise (Reporting_basic.err_unreachable l "Default order not set") in
      let _,v_cs = type_consistent (Patt l) d_env Guarantee true t expect_t in
      (*TODO Should gather the constraints here, with regard to the expected base and rise, and potentially reset them above*)
      (P_aux(P_vector(pats'),(l,cons_tag_annot t emp_tag (cs@v_cs))), env,cs@v_cs@constraints,bounds,t) 
    | P_vector_indexed(ipats) -> 
      let item_t = match expect_actual.t with
        | Tapp("vector",[b;r;o;TA_typ i]) -> i
        | Tuvar _ -> new_t () 
        | _ -> typ_error l ("Expected a vector by pattern form, but a " ^ t_to_string expect_actual ^ " by type") in
      let (is,pats) = List.split ipats in
      let (fst,lst) = (List.hd is),(List.hd (List.rev is)) in
      let inc_or_dec = 
        if fst < lst then
          (let _ = List.fold_left 
             (fun i1 i2 -> if i1 < i2 then i2 
               else typ_error l "Indexed vector pattern was inconsistently increasing") fst (List.tl is) in
           true)
        else if lst < fst then
          (let _ = List.fold_left
             (fun i1 i2 -> if i1 > i2 then i2
               else typ_error l "Indexed vector pattern was inconsistently decreasing") fst (List.tl is) in
           false)
        else typ_error l "Indexed vector cannot be determined as either increasing or decreasing" in
      let base,rise = new_n (), new_n () in
      let (pats',ts,t_envs,constraints,bounds) = 
        List.fold_right 
          (fun (i,pat) (pats,ts,t_envs,constraints,bounds) -> 
            let (pat',env,cons,new_bounds,t) = check_pattern envs emp_tag item_t pat in 
            (((i,pat')::pats),(t::ts),(env::t_envs),(cons@constraints),merge_bounds new_bounds bounds))
          ipats ([],[],[],[],nob) in
      let co = Patt l in
      let env = List.fold_right (fun e env -> Envmap.union e env) t_envs Envmap.empty in (*TODO Need to check for non-duplication of variables*)
      let (u,cs) = List.fold_right (fun u (t,cs) -> type_consistent co d_env Require true u t) ts (item_t,[]) in
      let t = {t = Tapp("vector",[(TA_nexp base);(TA_nexp rise);
                                  (TA_ord{order=(if inc_or_dec then Oinc else Odec)});(TA_typ u)])} in
      let cs = if inc_or_dec 
        then [LtEq(co, Require, base, mk_c_int fst); GtEq(co,Require, rise, mk_c_int(lst-fst));]@cs
        else [GtEq(co, Require, base, mk_c_int fst); LtEq(co,Require, rise, mk_c_int(fst -lst));]@cs in
      (P_aux(P_vector_indexed(pats'),(l,cons_tag_annot  t emp_tag cs)), env,constraints@cs,bounds,t)
    | P_tup(pats) -> 
      let item_ts = match expect_actual.t with
        | Ttup ts ->
          if (List.length ts) = (List.length pats) 
          then ts
          else typ_error l ("Expected a pattern with a tuple with " ^ (string_of_int (List.length ts)) ^ " elements")
        | Tuvar _ -> List.map (fun _ -> new_t ()) pats 
        | _ -> typ_error l ("Expected a tuple by pattern form, but a " ^ (t_to_string expect_actual) ^ " by type") in
      let (pats',ts,t_envs,constraints,bounds) = 
        List.fold_right 
          (fun (pat,t) (pats,ts,t_envs,constraints,bounds) -> 
            let (pat',env,cons,new_bounds,t) = check_pattern envs emp_tag t pat in 
            ((pat'::pats),(t::ts),(env::t_envs),cons@constraints,merge_bounds new_bounds bounds))
          (List.combine pats item_ts) ([],[],[],[],nob) in
      let env = List.fold_right (fun e env -> Envmap.union e env) t_envs Envmap.empty in (*Need to check for non-duplication of variables*)
      let t = {t = Ttup ts} in
      (P_aux(P_tup(pats'),(l,tag_annot t emp_tag)), env,constraints,bounds,t)
    | P_vector_concat pats -> 
      let item_t,base,rise,order = 
        match expect_t.t with 
          | Tapp("vector",[TA_nexp(b);TA_nexp(r);TA_ord(o);TA_typ item])
          | Tabbrev(_,{t=Tapp("vector",[TA_nexp(b);TA_nexp(r);TA_ord(o);TA_typ item])}) -> item,b,r,o
          | _ -> new_t (),new_n (), new_n (), d_env.default_o in
      let vec_ti _ = {t= Tapp("vector",[TA_nexp (new_n ());TA_nexp (new_n ());TA_ord order;TA_typ item_t])} in
      let (pats',ts,envs,constraints,bounds) = 
        List.fold_right 
          (fun pat (pats,ts,t_envs,constraints,bounds) -> 
            let (pat',env,cons,new_bounds,t) = check_pattern envs emp_tag (vec_ti ()) pat in 
            (pat'::pats,t::ts,env::t_envs,cons@constraints,merge_bounds new_bounds bounds))
          pats ([],[],[],[],nob) in
      let env = 
        List.fold_right (fun e env -> Envmap.union e env) envs Envmap.empty in (*Need to check for non-duplication of variables*)
      let t = {t = Tapp("vector",[(TA_nexp base);(TA_nexp rise);(TA_ord order);(TA_typ item_t)])} in
      let base_c,r1 = match (List.hd ts).t with
        | Tapp("vector",[(TA_nexp b);(TA_nexp r);(TA_ord o);(TA_typ u)]) -> b,r
        | _ -> raise (Reporting_basic.err_unreachable l "vector concat pattern impossibility") in
      let range_c = List.fold_right 
        (fun t rn ->
          match t.t with
            | Tapp("vector",[(TA_nexp b);(TA_nexp r);(TA_ord o);(TA_typ u)]) -> mk_add r rn
            | _ -> raise (Reporting_basic.err_unreachable l "vector concat pattern impossibility") ) (List.tl ts) r1 in
      let cs = [Eq((Patt l),rise,range_c)]@cs in
      (P_aux(P_vector_concat(pats'),(l,cons_tag_annot t emp_tag cs)), env,constraints@cs,bounds,t)
    | P_list(pats) -> 
      let item_t = match expect_actual.t with
        | Tapp("list",[TA_typ i]) -> i
        | Tuvar _ -> new_t () 
        | _ -> typ_error l ("Expected a list here by pattern form, but expected a " ^ t_to_string expect_actual ^ " by type") in
      let (pats',ts,envs,constraints,bounds) = 
        List.fold_right 
          (fun pat (pats,ts,t_envs,constraints,bounds) -> 
            let (pat',env,cons,new_bounds,t) = check_pattern envs emp_tag item_t pat in 
            (pat'::pats,t::ts,env::t_envs,cons@constraints,merge_bounds new_bounds bounds))
          pats ([],[],[],[],nob) in
      let env = List.fold_right (fun e env -> Envmap.union e env) envs Envmap.empty in (*TODO Need to check for non-duplication of variables*)
      let u,cs = List.fold_right (fun u (t,cs) -> let t',cs' = type_consistent (Patt l) d_env Require true u t in t',cs@cs') ts (item_t,[]) in
      let t = {t = Tapp("list",[TA_typ u])} in
      (P_aux(P_list(pats'),(l,cons_tag_annot  t emp_tag cs)), env,constraints@cs,bounds,t)

let rec check_pattern_after_constraint_res envs concrete_length_req expect_t (P_aux(p,(l,annot))) : t  =
  let check_pat = check_pattern_after_constraint_res envs in
  let (Env(d_env,t_env,b_env,tp_env)) = envs in
  (*let _ = Printf.eprintf "checking pattern after constraints with expected type %s\n" (t_to_string expect_t) in*)
  let expect_t,_ = get_abbrev d_env expect_t in
  (*let _ = Printf.eprintf "check pattern after constraints expect_t after abbrev %s\n" (t_to_string expect_t) in*)
  let expect_actual = match expect_t.t with | Tabbrev(_,t) -> t | _ -> expect_t in
  let t_inferred = match annot with
    | Base((_,t),tag,cs,_,_,_) -> t
    | _ -> failwith "Inference pass did not annotate a pattern with Base annot" in
  match p with
  | P_lit (L_aux(lit,l')) ->
    let t_from_lit = (match lit with
        | L_unit  -> unit_t 
        | L_zero | L_one | L_true | L_false -> bit_t
        | L_num i -> 
          (match expect_actual.t with
           | Tid "bit" -> if i = 0 || i = 1 then bit_t else typ_error l' "Given number but expected bit"
           | _ -> {t = Tapp("atom", [TA_nexp (mk_c_int i)])})
        | L_hex s -> 
          let size = big_int_of_int ((String.length s) * 4) in
          let is_inc = match d_env.default_o.order with | Oinc -> true | _ -> false in
          mk_vector bit_t d_env.default_o (if is_inc then n_zero else mk_c (sub_big_int size one)) (mk_c size)
        | L_bin s -> 
          let size = big_int_of_int (String.length s) in
          let is_inc = match d_env.default_o.order with | Oinc -> true | _ -> false in
          mk_vector bit_t d_env.default_o (if is_inc then n_zero else mk_c(sub_big_int size one)) (mk_c size)
        | L_string s -> string_t
        | L_undef -> typ_error l' "Cannot pattern match on undefined") in
    let t_c,_ = type_consistent (Patt l) d_env Require true t_from_lit t_inferred in
    let t,_   = type_consistent (Patt l) d_env Require true t_c expect_t in
    t
  | P_wild ->
    let t,_ = type_consistent (Patt l) d_env Require true t_inferred expect_t in t
  | P_as(pat,id) -> check_pat concrete_length_req expect_t pat
  | P_typ(typ,pat) -> 
    let tdec = typ_to_t envs false false typ in
    let tdec = typ_subst tp_env false tdec in
    let default _ = let tdec = check_pat false tdec pat in
      let t,_ = type_consistent (Patt l) d_env Guarantee false tdec t_inferred in
      let t,_ = type_consistent (Patt l) d_env Guarantee false t expect_t in
      t
    in
    (match tdec.t, concrete_length_req with
     | Tapp ("vector", [_;TA_nexp {nexp = Nconst _};_;_]), true -> default ()
     | Tapp ("vector",_), true ->
       (try (let tdec = check_pat true tdec pat in
            let t,_ = type_consistent (Patt l) d_env Guarantee false tdec t_inferred in
            let t,_ = type_consistent (Patt l) d_env Guarantee false t expect_t in t) with
       | Reporting_basic.Fatal_error(Reporting_basic.Err_type _) ->
         typ_error l "Type annotation does not provide a concrete vector length and one cannot be inferred")
     | _ -> default ())
  | P_id id -> 
    let i = id_to_string id in
    let default t =
      let t,_ = type_consistent (Patt l) d_env Guarantee false t t_inferred in
      let t,_ = type_consistent (Patt l) d_env Guarantee false t expect_t in t in
    (match Envmap.apply t_env i with
     | Some(Base((params,t),Constructor n,cs,efl,efr,bounds)) ->
       let t,cs,ef,_ = subst params false false t cs efl in
       (match t.t with
        | Tfn({t = Tid "unit"},t',IP_none,ef) -> 
          if conforms_to_t d_env false false t' expect_t then default t' else default t
        | Tfn(t1,t',IP_none,e) -> 
          if conforms_to_t d_env false false t' expect_t
          then typ_error l ("Constructor " ^ i ^ " expects arguments of type " ^ (t_to_string t) ^ ", found none")
          else default t'
        | _ -> raise (Reporting_basic.err_unreachable l "Constructor tannot does not have function type"))
     | Some(Base((params,t),Enum max,cs,efl,efr,bounds)) -> 
       let t,cs,ef,_ = subst params false false t cs efl in default t
     | _ -> (match t_inferred.t, concrete_length_req with
         | Tapp ("vector", [_;TA_nexp {nexp = Nconst _};_;_]), true -> default t_inferred
         | Tapp ("vector", _), true ->
           typ_error l ("Unable to infer a vector length for paramter " ^ i ^ ", a type annotation may be required.")
         | _ -> default t_inferred))
    | P_app(id,pats) -> 
      let i = id_to_string id in
      (*let _ = Printf.eprintf "checking constructor pattern %s\n" i in*)
      (match Envmap.apply t_env i with
        | None | Some NoTyp | Some Overload _ -> typ_error l ("Constructor " ^ i ^ " in pattern is undefined")
        | Some(Base((params,t),Constructor n,constraints,efl,efr,bounds)) -> 
          let t,dec_cs,_,_ = subst params false false t constraints efl in
          (match t.t with
            | Tid id -> if pats = [] 
              then let t',ret_cs = type_consistent (Patt l) d_env Guarantee false t expect_t in t'
              else typ_error l ("Constructor " ^ i ^ " does not expect arguments")
            | Tfn(t1,t2,IP_none,ef) ->
              let t',ret_cs = type_consistent (Patt l) d_env Guarantee false t2 expect_t in
              (match pats with
              | [] -> let _ = type_consistent (Patt l) d_env Guarantee false unit_t t1 in t'
              | [p] -> check_pat concrete_length_req t1 p 
              | pats -> check_pat concrete_length_req t1 (P_aux(P_tup(pats),(l,annot))))
            | _ -> typ_error l ("Identifier " ^ i ^ " must be a union constructor"))
        | Some(Base((params,t),tag,constraints,efl,efr,bounds)) -> 
          typ_error l ("Identifier " ^ i ^ " used in pattern is not a union constructor"))
    | P_record(fpats,_) -> 
      (match (fields_to_rec fpats d_env.rec_env) with
        | None -> typ_error l ("No struct exists with the listed fields")
        | Some(id,tannot,typ_pats) ->
          (match tannot with
            | (Base((vs,t),tag,cs,eft,_,bounds)) ->
              let (ft_subst,cs,_,_) = subst vs false false t cs pure_e in
              let subst_rtyp,subst_typs = 
                match ft_subst.t with | Tfn({t=Ttup tups},rt,_,_) -> rt,tups 
                  | _ -> raise (Reporting_basic.err_unreachable l "fields_to_rec gave a non function type") in
              let _ = 
                List.map2 (fun (_,id,l,pat) styp -> check_pat concrete_length_req styp pat) typ_pats subst_typs in
              let t',cs' = type_consistent (Patt l) d_env Guarantee false ft_subst expect_t in t'
            | _ -> raise (Reporting_basic.err_unreachable l "fields_to_rec returned a non Base tannot")))
    | P_vector pats -> 
      let (item_t, base, rise, ord) = match expect_actual.t with 
        | Tapp("vector",[TA_nexp b;TA_nexp r;TA_ord o;TA_typ i]) -> (i,b,r,o)
        | Tuvar _ -> (new_t (),new_n (),new_n(), d_env.default_o) 
        | _ -> typ_error l ("Expected a " ^ t_to_string expect_actual ^ " but found a vector") in
      let ts = List.map (check_pat false item_t) pats in
      let (u,cs) = List.fold_right (fun u (t,cs) ->
          let t',cs = type_consistent (Patt l) d_env Require true u t in t',cs) ts (item_t,[]) in
      let len = List.length ts in
      let t = 
        match (ord.order,d_env.default_o.order) with
        | (Oinc,_) | (Ovar _, Oinc) | (Ouvar _,Oinc) -> 
          {t = Tapp("vector",[TA_nexp n_zero;
                              TA_nexp (mk_c_int len);
                              TA_ord{order=Oinc};
                              TA_typ u])}
        | (Odec,_) | (Ovar _, Odec) | (Ouvar _,Odec) -> 
          {t= Tapp("vector", [TA_nexp (mk_c (if len = 0 then zero else (big_int_of_int (len -1))));
                              TA_nexp (mk_c_int len);
                              TA_ord{order=Odec};
                              TA_typ u;])}
        | _ -> raise (Reporting_basic.err_unreachable l "Default order not set") in
      let _,_ = type_consistent (Patt l) d_env Guarantee true t expect_t in t
    | P_vector_indexed(ipats) -> 
      let item_t = match expect_actual.t with
        | Tapp("vector",[b;r;o;TA_typ i]) -> i
        | Tuvar _ -> new_t () 
        | _ -> typ_error l ("Expected a vector by pattern form, but a " ^ t_to_string expect_actual ^ " by type") in
      let (is,pats) = List.split ipats in
      let (fst,lst) = (List.hd is),(List.hd (List.rev is)) in
      let inc_or_dec = 
        if fst < lst then
          (let _ = List.fold_left 
             (fun i1 i2 -> if i1 < i2 then i2 
               else typ_error l "Indexed vector pattern was inconsistently increasing") fst (List.tl is) in
           true)
        else if lst < fst then
          (let _ = List.fold_left
             (fun i1 i2 -> if i1 > i2 then i2
               else typ_error l "Indexed vector pattern was inconsistently decreasing") fst (List.tl is) in
           false)
        else typ_error l "Indexed vector cannot be determined as either increasing or decreasing" in
      let base,rise = new_n (), new_n () in
      let ts = List.map (fun (_,pat) -> check_pat concrete_length_req item_t pat) ipats in
      let co = Patt l in
      let (u,cs) = List.fold_right (fun u (t,cs) -> type_consistent co d_env Require true u t) ts (item_t,[]) in
      {t = Tapp("vector",[(TA_nexp base);(TA_nexp rise);
                          (TA_ord{order=(if inc_or_dec then Oinc else Odec)});(TA_typ u)])}
    | P_tup(pats) -> 
      let item_ts = match expect_actual.t with
        | Ttup ts ->
          if (List.length ts) = (List.length pats) 
          then ts
          else typ_error l ("Expected a pattern with a tuple with " ^
                            (string_of_int (List.length ts)) ^ " elements, found one with " ^
                            (string_of_int (List.length pats)))
        | Tuvar _ -> List.map (fun _ -> new_t ()) pats 
        | _ -> typ_error l ("Expected a tuple by pattern form, but a " ^ (t_to_string expect_actual) ^ " by type") in
      let ts = List.map (fun (pat,t) -> check_pat false t pat) (List.combine pats item_ts) in
      {t = Ttup ts}
    | P_vector_concat pats -> 
      let item_t,base,rise,order = 
        match expect_t.t with 
          | Tapp("vector",[TA_nexp(b);TA_nexp(r);TA_ord(o);TA_typ item])
          | Tabbrev(_,{t=Tapp("vector",[TA_nexp(b);TA_nexp(r);TA_ord(o);TA_typ item])}) -> item,b,r,o
          | _ -> new_t (),new_n (), new_n (), d_env.default_o in
      let vec_ti _ = {t= Tapp("vector",[TA_nexp (new_n ());TA_nexp (new_n ());TA_ord order;TA_typ item_t])} in
      let _ =
        let rec walk = function
          | [] -> []
          | [p] ->
            [check_pat concrete_length_req (*use enclosing pattern status in case of nested concats*) (vec_ti ()) p]
          | p::ps -> (check_pat true (vec_ti ()) p)::(walk ps) in
        walk pats in
      {t = Tapp("vector",[(TA_nexp base);(TA_nexp rise);(TA_ord order);(TA_typ item_t)])}
    | P_list(pats) -> 
      let item_t = match expect_actual.t with
        | Tapp("list",[TA_typ i]) -> i
        | Tuvar _ -> new_t () 
        | _ -> typ_error l ("Expected a list here by pattern form, but expected a " ^ t_to_string expect_actual ^ " by type") in
      let ts = List.map (check_pat false item_t) pats in
      let u = List.fold_right (fun u t -> let t',_ = type_consistent (Patt l) d_env Require true u t in t') ts item_t in
      {t = Tapp("list",[TA_typ u])}

let simp_exp e l t = E_aux(e,(l,simple_annot t))

(*widen lets outer expressions control whether inner expressions should widen in the presence of literals or not.
        also controls whether we consider vector base to be unconstrained or constrained
  This is relevent largely for vector accesses and sub ranges, 
  where if there's a constant we really want to look at that constant,
  and if there's a known vector base, we want to use that directly, vs assignments or branching values *)
let rec check_exp envs (imp_param:nexp option) (widen_num:bool) (widen_vec:bool)
    (ret_t:t) (expect_t:t) (E_aux(e,(l,annot)):tannot exp)
  : (tannot exp * t * tannot emap * nexp_range list * bounds_env * effect) =
  let Env(d_env,t_env,b_env,tp_env) = envs in
  let expect_t,_ = get_abbrev d_env expect_t in
  let expect_t_actual = match expect_t.t with | Tabbrev(_,t) -> t | _ -> expect_t in
  let ret_t,_ = get_abbrev d_env ret_t in
  let rebuild annot = E_aux(e,(l,annot)) in
  match e with
    | E_block exps -> 
      let (exps',annot',sc,t,ef) = check_block envs imp_param ret_t expect_t exps in
      (E_aux(E_block(exps'),(l,annot')),t,Envmap.empty,sc,nob,ef)
    | E_nondet exps ->
      let base_ef = add_effect (BE_aux(BE_nondet,l)) pure_e in
      let (ces, sc, ef)  = 
        List.fold_right
          (fun e (es,sc,ef) ->
             let (e,_,_,sc',_,ef') = (check_exp envs imp_param true true ret_t unit_t e) in
             (e::es,sc@sc',union_effects ef ef')) exps ([],[],base_ef) in
      let _,_ = type_consistent (Expr l) d_env Require false unit_t expect_t in
      (E_aux (E_nondet ces,(l,cons_efs_annot unit_t sc base_ef ef)),unit_t,t_env,sc,nob,ef)
    | E_id id -> 
      let i = id_to_string id in
      (match Envmap.apply t_env i with
      | Some(Base((params,t),(Constructor n),cs,ef,_,bounds)) ->
        let t,cs,ef,_ = subst params false false t cs ef in
        (match t.t with
        | Tfn({t = Tid "unit"},t',IP_none,ef) -> 
          let e = E_aux(E_app(id, []),
                        (l, (Base(([],{t=Tfn(unit_t,t',IP_none,ef)}), (Constructor n), cs, ef,pure_e, bounds)))) in
          let t',cs',ef',e' = type_coerce (Expr l) d_env Require false false b_env t' e expect_t in
          (e',t',t_env,cs@cs',nob,union_effects ef ef')
        | Tfn(t1,t',IP_none,e) -> 
          typ_error l ("Constructor " ^ i ^ " expects arguments of type " ^ (t_to_string t) ^ ", found none")
        | _ -> raise (Reporting_basic.err_unreachable l "Constructor tannot does not have function type"))
      | Some(Base((params,t),(Enum max),cs,ef,_,bounds)) ->
        let t',cs,_,_ = subst params false false t cs ef in
        let t',cs',ef',e' = 
          type_coerce (Expr l) d_env Require false false b_env t'
            (rebuild (cons_tag_annot t' (Enum max) cs)) expect_t in
        (e',t',t_env,cs@cs',nob,ef')
      | Some(Base(tp,Default,cs,ef,_,_)) | Some(Base(tp,Spec,cs,ef,_,_)) ->
        typ_error l ("Identifier " ^ i ^ " must be defined, not just specified, before use")
      | Some(Base((params,t),tag,cs,ef,_,bounds)) ->
        let ((t,cs,ef,_),is_alias) = 
          match tag with | Emp_global | External _ -> (subst params false false t cs ef),false 
            | Alias alias_inf -> (t,cs, add_effect (BE_aux(BE_rreg, Parse_ast.Unknown)) ef, Envmap.empty),true 
            | _ -> (t,cs,ef,Envmap.empty),false 
        in
        let t,cs' = get_abbrev d_env t in
        let cs = cs@cs' in
        let t_actual = match t.t with
          | Tabbrev(_,t) -> t 
          | _ -> t in
        (*let _ = Printf.eprintf "On general id check of %s, expect_t %s, t %s, tactual %s, expect_actual %s\n"
            (id_to_string id)
            (t_to_string expect_t) (t_to_string t) (t_to_string t_actual) (t_to_string expect_t_actual) in*)
        (match t_actual.t,expect_t_actual.t with 
         | Tfn _,_ -> typ_error l
                        ("Identifier " ^ (id_to_string id) ^ " is bound to a function and cannot be used as a value")
         | Tapp("register",[TA_typ(t')]),Tapp("register",[TA_typ(expect_t')]) -> 
           let tannot = Base(([],t),(match tag with | External _ -> Emp_global | _ -> tag),
                             cs,pure_e,pure_e,bounds) in
           let t',cs' = type_consistent (Expr l) d_env Require widen_vec t' expect_t' in
           (rebuild tannot,t,t_env,cs@cs',bounds,ef)
         | Tapp("register",[TA_typ(t')]),Tuvar _ ->
           (*let ef' = add_effect (BE_aux(BE_rreg,l)) ef in
             let tannot = Base(([],t),(if is_alias then tag else External (Some i)),cs,ef',ef',bounds) in*)
           let tannot = Base(([],t),
                             (if is_alias then tag else (if tag = Emp_local then tag else Emp_global)),
                             cs,pure_e,pure_e,bounds) in
           let _,cs',ef',e' =
             type_coerce (Expr l) d_env Require false widen_vec b_env t' (rebuild tannot) expect_t_actual in
           (e',t,t_env,cs@cs',bounds,ef')
         | Tapp("register",[TA_typ(t')]),_ ->
           let ef' = add_effect (BE_aux(BE_rreg,l)) ef in
           let tannot = Base(([],t),(if is_alias then tag else External (Some i)),cs,ef',ef',bounds) in
           let t',cs',_,e' =
             type_coerce (Expr l) d_env Require false widen_vec b_env t' (rebuild tannot) expect_t_actual in
           (e',t',t_env,cs@cs',bounds,ef')
         | Tapp("reg",[TA_typ(t')]),_ ->
           let tannot = cons_bs_annot t cs bounds in
           let t',cs',_,e' =
             type_coerce (Expr l) d_env Require false widen_num b_env t' (rebuild tannot) expect_t_actual in
           (e',t',t_env,cs@cs',bounds,pure_e)
        | _ -> 
          let t',cs',ef',e' = type_coerce (Expr l) d_env Require false widen_num b_env
              t (rebuild (Base(([],t),tag,cs,pure_e,ef,bounds))) expect_t in
          (e',t',t_env,cs@cs',bounds,union_effects ef ef')
        )
      | Some NoTyp | Some Overload _ | None -> typ_error l ("Identifier " ^ (id_to_string id) ^ " is unbound"))
    | E_lit (L_aux(lit,l')) ->
      let e,cs,effect = (match lit with
        | L_unit  -> (rebuild (simple_annot unit_t)),[],pure_e
        | L_zero  -> 
          (match expect_t_actual.t with
          | Tid "bool" -> simp_exp (E_lit(L_aux(L_zero,l'))) l bool_t,[],pure_e
          | _ -> simp_exp e l bit_t,[],pure_e)
        | L_one   -> 
          (match expect_t_actual.t with
          | Tid "bool" -> simp_exp (E_lit(L_aux(L_one,l'))) l bool_t,[],pure_e
          | _ -> simp_exp e l bit_t,[],pure_e)
        | L_true  -> simp_exp e l bool_t,[],pure_e
        | L_false -> simp_exp e l bool_t,[],pure_e
        | L_num i -> 
          (*let _ = Printf.eprintf "expected type of number literal %i is %s\n" i (t_to_string expect_t_actual) in*)
          (match expect_t_actual.t with
          | Tid "bit" | Toptions({t=Tid"bit"},_) -> 
            if i = 0 then simp_exp (E_lit(L_aux(L_zero,l'))) l bit_t,[],pure_e
            else if i = 1 then simp_exp (E_lit(L_aux(L_one,l'))) l bit_t,[],pure_e
            else typ_error l ("Expected a bit, found " ^ string_of_int i)
          | Tid "bool" | Toptions({t=Tid"bool"},_)->
            if i = 0 then simp_exp (E_lit(L_aux(L_zero,l'))) l bit_t,[],pure_e
            else if i = 1 then simp_exp (E_lit(L_aux(L_one,l'))) l bit_t ,[],pure_e
            else typ_error l ("Expected bool or a bit, found " ^ string_of_int i)
          | Tapp ("vector",[TA_nexp base;TA_nexp rise;TA_ord o;(TA_typ {t=Tid "bit"})]) ->
            let n = mk_c_int i in
            let t = {t=Tapp("atom", [TA_nexp n;])} in
            let cs = [LtEq(Expr l,Guarantee,n,mk_sub (mk_2n rise) n_one)] in
            let f = match o.order with | Oinc -> "to_vec_inc" | Odec -> "to_vec_dec" | _ -> "to_vec_inc" in
            (*let _ = Printf.eprintf "adding a call to to_vec_*: bounds are %s\n" (bounds_to_string b_env) in*)
            let internal_tannot = (l,(cons_bs_annot {t = Tapp("implicit",[TA_nexp rise])} [] b_env)) in
            let tannot = (l,cons_tag_annot expect_t (External (Some f)) cs) in
            E_aux(E_app((Id_aux((Id f),l)),
                        [(E_aux (E_internal_exp(internal_tannot), tannot));simp_exp e l t]),tannot),cs,pure_e
          | _ -> simp_exp e l {t = Tapp("atom", [TA_nexp (mk_c_int i)])},[],pure_e)
        | L_hex s -> 
          let size = (String.length s) * 4 in
          let start = match d_env.default_o.order with
                      | Oinc -> n_zero | Odec -> mk_c_int (size - 1) | _ -> n_zero in
          simp_exp e l {t = Tapp("vector",
                                 [TA_nexp start;
                                  TA_nexp (mk_c_int size);
                                  TA_ord d_env.default_o;TA_typ{t = Tid "bit"}])},[],pure_e
        | L_bin s -> 
          let size = String.length s in
          let start = match d_env.default_o.order with
                       | Oinc -> n_zero | Odec -> mk_c_int (size -1) | _ -> n_zero in
          simp_exp e l {t = Tapp("vector",
                                 [TA_nexp start;
                                  TA_nexp (mk_c_int size);
                                  TA_ord d_env.default_o ;TA_typ{t = Tid"bit"}])},[],pure_e
        | L_string s -> simp_exp e l {t = Tid "string"},[],pure_e
        | L_undef -> 
          let ef = {effect=Eset[BE_aux(BE_undef,l)]} in
          (match expect_t_actual.t with
            | Tapp ("vector",[TA_nexp base;TA_nexp rise;TA_ord o;(TA_typ {t=Tid "bit"})]) 
            | Toptions({t = Tapp ("vector",[TA_nexp base;TA_nexp rise;TA_ord o;(TA_typ {t=Tid "bit"})])}, None) ->
              let f = match o.order with | Oinc -> "to_vec_inc_undef" | Odec -> "to_vec_dec_undef" 
                                         | _ -> (match d_env.default_o.order with
                                             | Oinc -> "to_vec_inc_undef" | Odec -> "to_vec_dec_undef"
                                             | _ -> "to_vec_inc_undef") in
              let _ = set_imp_param rise in
              let internal_tannot = (l,(cons_bs_annot {t = Tapp("implicit",[TA_nexp rise])} [] b_env)) in
              let tannot = (l,Base(([],{t = Tapp("vector",[TA_nexp base; TA_nexp rise; TA_ord o; TA_typ bit_t])}),
                                   External (Some f),[],ef,ef,b_env)) in
              E_aux(E_app((Id_aux((Id f),l)),
                          [(E_aux (E_internal_exp(internal_tannot), tannot));]),tannot),[],ef
            | _ -> simp_exp e l (new_t ()),[],ef)) in
      let t',cs',_,e' = type_coerce (Expr l) d_env Require false widen_num b_env (get_e_typ e) e expect_t in
      (e',t',t_env,cs@cs',nob,effect)
    | E_cast(typ,e) ->
      let cast_t = typ_to_t envs false false typ in
      let cast_t,cs_a = get_abbrev d_env cast_t in
      let cast_t = typ_subst tp_env false cast_t in
      let ct = {t = Toptions(cast_t,None)} in
      let (e',u,t_env,cs,bounds,ef) = check_exp envs imp_param true true ret_t ct e in
      (*let _ = Printf.eprintf "Type checking cast: cast_t is %s constraints after checking e are %s\n" 
        (t_to_string cast_t) (constraints_to_string cs) in*)
      let t',cs2,ef',e' = type_coerce (Expr l) d_env Require true true b_env u e' cast_t in
      (*let _ = Printf.eprintf "Type checking cast: after first coerce with u %s, t' %s is and constraints are %s\n" 
        (t_to_string u) (t_to_string t') (constraints_to_string cs2) in*)
      let t',cs3,ef'',e'' = type_coerce (Expr l) d_env Guarantee false false b_env cast_t e' expect_t in 
      (*let _ = Printf.eprintf "Type checking cast: after second coerce expect_t %s, t' %s and constraints are %s\n" 
        (t_to_string expect_t) (t_to_string t') (constraints_to_string cs3) in*)
      (e'',t',t_env,cs_a@cs@cs2@cs3,bounds,union_effects ef' (union_effects ef'' ef))
    | E_app(id,parms) -> 
      let i = id_to_string id in
      let check_parms p_typ parms = (match parms with
        | [] | [(E_aux (E_lit (L_aux (L_unit,_)),_))] 
          -> let (_,cs') = type_consistent (Expr l) d_env Require false unit_t p_typ in [],unit_t,cs',pure_e 
        | [parm] -> let (parm',arg_t,t_env,cs',_,ef_p) = check_exp envs imp_param true true ret_t p_typ parm
          in [parm'],arg_t,cs',ef_p
        | parms -> 
          (match check_exp envs imp_param true true ret_t p_typ (E_aux (E_tuple parms,(l,NoTyp))) with
          | ((E_aux(E_tuple parms',tannot')),arg_t,t_env,cs',_,ef_p) -> parms',arg_t,cs',ef_p
          | _ ->
            raise (Reporting_basic.err_unreachable l
                     "check_exp, given a tuple and a tuple type, didn't return a tuple"))) 
      in
      let coerce_parms arg_t parms expect_arg_t =
        (match parms with
        | [] | [(E_aux (E_lit (L_aux(L_unit, _)), _))] -> [],pure_e,[]
        | [parm] -> 
          let _,cs,ef,parm' = 
            type_coerce (Expr l) d_env Guarantee false false b_env arg_t parm expect_arg_t in [parm'],ef,cs
        | parms ->
          (match type_coerce (Expr l) d_env Guarantee false false b_env arg_t
                   (E_aux (E_tuple parms,(l,NoTyp))) expect_arg_t with
          | (_,cs,ef,(E_aux(E_tuple parms',tannot'))) -> (parms',ef,cs)
          | _ ->
            raise (Reporting_basic.err_unreachable l "type coerce given tuple and tuple type returned non-tuple"))) 
      in
      let check_result ret imp tag cs ef efr parms =    
        match (imp,imp_param) with
          | (IP_length n ,None) | (IP_user n,None) | (IP_start n,None) ->
            (*let _ = Printf.eprintf "app of %s implicit required, no imp_param %s\n!"  i (n_to_string n) in*)
            let internal_exp = 
              let _ = set_imp_param n in
              let implicit = {t= Tapp("implicit",[TA_nexp n])} in
              let annot_i = Base(([],implicit),Emp_local,[],pure_e,pure_e,b_env) in
              E_aux(E_internal_exp((l,annot_i)),(l,simple_annot nat_t)) in
            type_coerce (Expr l) d_env Require false true b_env ret 
              (E_aux (E_app(id, internal_exp::parms),(l,(Base(([],ret),tag,cs,ef,efr,nob))))) expect_t
          | (IP_length n ,Some ne) | (IP_user n,Some ne) | (IP_start n,Some ne) ->
            (*let _ = Printf.eprintf "app of %s implicit length or var required %s with imp_param %s\n" 
              i (n_to_string n) (n_to_string ne) in
            let _ = Printf.eprintf "and expected type is %s and return type is %s\n"
              (t_to_string expect_t) (t_to_string ret) in*)
            let _ = set_imp_param n; set_imp_param ne in
            let internal_exp = 
              let implicit_user = {t = Tapp("implicit",[TA_nexp ne])} in
              let implicit = {t= Tapp("implicit",[TA_nexp n])} in
              let annot_iu = Base(([],implicit_user),Emp_local,[],pure_e,pure_e,b_env)in
              let annot_i = Base(([],implicit),Emp_local,[],pure_e,pure_e,b_env) in
              E_aux (E_internal_exp_user((l, annot_iu),(l,annot_i)), (l,simple_annot nat_t))
            in
            type_coerce (Expr l) d_env Require false true b_env ret 
              (E_aux (E_app(id,internal_exp::parms),(l,(Base(([],ret),tag,cs,ef,efr,nob))))) expect_t
          | (IP_none,_) -> 
          (*let _ = Printf.eprintf "no implicit: ret %s and expect_t %s\n" 
            (t_to_string ret) (t_to_string expect_t) in*)
            type_coerce (Expr l) d_env Require false true b_env ret 
              (E_aux (E_app(id, parms),(l,(Base(([],ret),tag,cs,ef,efr,nob))))) expect_t
      in
      (match Envmap.apply t_env i with
      | Some(Base(tp,Enum _,_,_,_,_)) ->
        typ_error l ("Expected function with name " ^ i ^ " but found an enumeration identifier")
      | Some(Base(tp,Default,_,_,_,_)) ->
        typ_error l ("Function " ^ i ^ " must be specified, not just declared as a default, before use")
      | Some(Base((params,t),tag,cs,efl,_,bounds)) ->
        (*let _ = Printf.eprintf "Going to check func call %s with unsubstituted types %s and constraints %s \n"
          i (t_to_string t) (constraints_to_string cs) in*)
        let t,cs,efl,_ = subst params false false t cs efl in
        (match t.t with
        | Tfn(arg,ret,imp,efl') ->
          (*let _ = Printf.eprintf "Checking funcation call of %s\n" i in
          let _ = Printf.eprintf "Substituted types and constraints are %s and %s\n" 
            (t_to_string t) (constraints_to_string cs) in*)
          let ret,_ = get_abbrev d_env ret in 
          let parms,arg_t,cs_p,ef_p = check_parms arg parms in
          (*let _ = Printf.eprintf "Checked parms of %s\n" i in*)
          let (ret_t,cs_r,ef_r,e') = check_result ret imp tag cs efl' (union_effects efl' ef_p) parms in
          (*let _ = Printf.eprintf "Checked result of %s and constraints are %s\n" 
            i (constraints_to_string cs_r) in*)
          (e',ret_t,t_env,cs@cs_p@cs_r, bounds,union_effects efl' (union_effects ef_p ef_r))
        | _ -> typ_error l
                 ("Expected a function or constructor, found identifier " ^ i ^ " bound to type " ^
                  (t_to_string t)))
      | Some(Overload(Base((params,t),tag,cs,efl,_,_),overload_return,variants)) ->
        let t_p,cs_p,ef_p,_ = subst params false false t cs efl in
        let args,arg_t,arg_cs,arg_ef = 
          (match t_p.t with
          | Tfn(arg,ret,_,ef') -> check_parms arg parms 
          | _ -> 
            typ_error l ("Expected a function or constructor, found identifier " ^ i
                         ^ " bound to type " ^ (t_to_string t))) in
        (match (select_overload_variant d_env true overload_return variants arg_t) with
          | [] -> typ_error l 
            ("No function found with name " ^ i ^ " that expects parameters " ^ (t_to_string arg_t))
          | [Base((params,t),tag,cs,efl,_,bounds)] ->
            (match t.t with
             | Tfn(arg,ret,imp,ef') ->
               let ret,_ = get_abbrev d_env ret in
               let args',arg_ef',arg_cs' = coerce_parms arg_t args arg in
               let cummulative_effects = union_effects (union_effects arg_ef arg_ef') (union_effects ef' ef_p) in
               let (ret_t,cs_r,ef_r,e') = check_result ret imp tag cs ef' cummulative_effects args' in
               (e',ret_t,t_env,cs_p@arg_cs@arg_cs'@cs_r,nob,
                union_effects ef_r cummulative_effects)
             | _ -> raise (Reporting_basic.err_unreachable l "Overloaded variant not a function"))
          | variants' ->
            (match select_overload_variant d_env false true variants' expect_t with
             | [] ->
               typ_error l ("No function found with name " ^ i ^ ", expecting parameters " ^
                            (t_to_string arg_t) ^ " and returning " ^ (t_to_string expect_t))
             | [Base((params,t),tag,cs,efl,_,bounds)] ->
               (match t.t with
                |Tfn(arg,ret,imp,ef') ->
                  let ret,_ = get_abbrev d_env ret in
                  let args',arg_ef',arg_cs' = coerce_parms arg_t args arg in
                  let cummulative_effects = union_effects (union_effects arg_ef arg_ef') (union_effects ef' ef_p) in
                  let (ret_t,cs_r,ef_r,e') = check_result ret imp tag cs ef' cummulative_effects args' in
                  (e',ret_t,t_env,cs_p@arg_cs@arg_cs'@cs_r,nob,union_effects ef_r cummulative_effects)
                | _ -> raise (Reporting_basic.err_unreachable l "Overloaded variant not a function"))
             | _ -> 
               typ_error l ("More than one definition of " ^ i ^ " found with type " ^
                            (t_to_string arg_t) ^ " -> " ^ (t_to_string expect_t) ^ ". A cast may be required")))
      | _ -> typ_error l ("Unbound function " ^ i))
    | E_app_infix(lft,op,rht) -> 
      let i = id_to_string op in
      let check_parms arg_t lft rht =
        match check_exp envs imp_param true true ret_t arg_t (E_aux(E_tuple [lft;rht],(l,NoTyp))) with
        | ((E_aux(E_tuple [lft';rht'],_)),arg_t,_,cs',_,ef') -> (lft',rht',arg_t,cs',ef')
        | _ -> 
          raise (Reporting_basic.err_unreachable l "check exp given tuple and tuple type and returned non-tuple") 
      in
      let check_result ret imp tag cs ef efr lft rht =
        match imp with
          | _ -> (*implicit isn't allowed at the moment on any infix functions *)
            type_coerce (Expr l) d_env Require false true b_env ret 
              (E_aux (E_app_infix(lft,op,rht),(l,(Base(([],ret),tag,cs,ef,efr,nob))))) expect_t 
      in
      (match Envmap.apply t_env i with
      | Some(Base(tp,Enum _,cs,ef,_,b)) -> 
        typ_error l ("Expected function with name " ^ i ^ " but found an enumeration identifier")
      | Some(Base(tp,Default,cs,ef,_,b)) -> 
        typ_error l ("Function " ^ i ^ " must be defined, not just declared as default, before use")
      | Some(Base((params,t),tag,cs,ef,_,b)) ->
        let t,cs,ef,_ = subst params false false t cs ef in
        (match t.t with
        | Tfn(arg,ret,imp,ef) -> 
          let (lft',rht',arg_t,cs_p,ef_p) = check_parms arg lft rht in
          let cummulative_effects = union_effects ef ef_p in
          let ret_t,cs_r',ef_r,e' = check_result ret imp tag cs ef cummulative_effects lft' rht' in
          (e',ret_t,t_env,cs@cs_p@cs_r',nob,union_effects ef_r cummulative_effects)
        | _ -> 
          typ_error l ("Expected a function, found identifier " ^ i ^ " bound to type " ^ (t_to_string t)))
      | Some(Overload(Base((params,t),tag,cs,ef,_,_),overload_return,variants)) ->
        let t_p,cs_p,ef_p,_ = subst params false false t cs ef in
        let lft',rht',arg_t,arg_cs,arg_ef =  
          (match t_p.t with
          | Tfn(arg,ret,_,ef') -> check_parms arg lft rht
          | _ -> typ_error l ("Expected a function, found identifier " ^ i ^ " bound to type " ^ (t_to_string t))) in
        (*let _ = Printf.eprintf "Looking for overloaded function %s, generic type is %s, arg_t is %s\n"
            i (t_to_string t_p) (t_to_string arg_t) in*)
        (match (select_overload_variant d_env true overload_return variants arg_t) with
        | [] -> 
          typ_error l ("No function found with name " ^ i ^
                          " that expects parameters " ^ (t_to_string arg_t))
        | [Base((params,t),tag,cs,ef,_,b)] ->
          (*let _ = Printf.eprintf "Selected an overloaded function for %s,
            variant with function type %s for actual type %s\n" i (t_to_string t) (t_to_string arg_t) in*)
          (match t.t with
          | Tfn(arg,ret,imp,ef') ->
            (match arg.t,arg_t.t with
            | Ttup([tlft;trght]),Ttup([tlft_t;trght_t]) ->
              let (lft',rht',arg_t,cs_p,ef_p) = check_parms arg lft rht in
              let cummulative_effects = union_effects ef' (union_effects arg_ef ef_p) in
              let (ret_t,cs_r,ef_r,e') = check_result ret imp tag cs ef cummulative_effects lft' rht' in
              (e',ret_t,t_env,cs_p@arg_cs@cs@cs_r,nob, union_effects ef_r cummulative_effects)
            |_ -> raise (Reporting_basic.err_unreachable l "function no longer has tuple type"))
          | _ -> raise (Reporting_basic.err_unreachable l "overload variant does not have function"))
        | variants ->
          (*let _ = Printf.eprintf "Number of variants found before looking at return value %i\n%!" 
            (List.length variants) in*)
          (match (select_overload_variant d_env false true variants expect_t) with
            | [] -> 
              typ_error l ("No matching function found with name " ^ i ^ " that expects parameters " ^
                              (t_to_string arg_t) ^ " returning " ^ (t_to_string expect_t))
            | [Base((params,t),tag,cs,ef,_,b)] -> 
          (*let _ = Printf.eprintf "Selected an overloaded function for %s,
            variant with function type %s for actual type %s\n" i (t_to_string t) (t_to_string arg_t) in*)
              (match t.t with
                | Tfn(arg,ret,imp,ef') ->
                  (match arg.t,arg_t.t with
                    | Ttup([tlft;trght]),Ttup([tlft_t;trght_t]) ->
                      let (lft',rht',arg_t,cs_p,ef_p) = check_parms arg lft rht in
                      let cummulative_effects = union_effects ef' (union_effects ef_p arg_ef) in
                      let (ret_t,cs_r,ef_r,e') = check_result ret imp tag cs ef cummulative_effects lft' rht' in
                      (e',ret_t,t_env,cs_p@arg_cs@cs@cs_r,nob, union_effects ef_r cummulative_effects)
                    |_ -> raise (Reporting_basic.err_unreachable l "function no longer has tuple type"))
                | _ -> raise (Reporting_basic.err_unreachable l "overload variant does not have function"))
            | _ -> 
              typ_error l ("More than one variant of " ^ i ^ " found with type "
                           ^ (t_to_string arg_t) ^ " -> " ^ (t_to_string expect_t) ^ ". A cast may be required")))
      | _ -> typ_error l ("Unbound infix function " ^ i))
    | E_tuple(exps) ->
      (match expect_t_actual.t with
      | Ttup ts ->
        let tl = List.length ts in
        let el = List.length exps in
        if tl = el then
          let exps,typs,consts,effect = 
            List.fold_right2 
              (fun e t (exps,typs,consts,effect) -> 
                 let (e',t',_,c,_,ef) =
                   check_exp envs imp_param true true ret_t t e in
                 ((e'::exps),(t'::typs),c@consts,union_effects ef effect))
              exps ts ([],[],[],pure_e) in
          let t = {t = Ttup typs} in
          (E_aux(E_tuple(exps),(l,simple_annot_efr t effect)),t,t_env,consts,nob,effect)
        else typ_error l ("Expected a tuple with " ^ (string_of_int tl) ^
                          " arguments; found one with " ^ (string_of_int el))
      | _ ->
        let exps,typs,consts,effect = 
          List.fold_right 
            (fun e (exps,typs,consts,effect) -> 
              let (e',t,_,c,_,ef) = check_exp envs imp_param true true ret_t (new_t ()) e in
              ((e'::exps),(t::typs),c@consts,union_effects ef effect))
            exps ([],[],[],pure_e) in
        let t = { t=Ttup typs } in
        let t',cs',ef',e' = 
          type_coerce (Expr l) d_env Guarantee false false b_env
            t (E_aux(E_tuple(exps),(l,simple_annot_efr t effect))) expect_t in
        (e',t',t_env,consts@cs',nob,union_effects ef' effect))
    | E_if(cond,then_,else_) ->
      let (cond',_,_,c1,_,ef1) = check_exp envs imp_param true true ret_t bit_t cond in
      let (c1,c1p,c1n) = split_conditional_constraints c1 in
      (match expect_t.t with
      | Tuvar _ -> 
        let then',then_t,then_env,then_c,then_bs,then_ef =
          check_exp envs imp_param true true ret_t (new_t ()) then_ in
        let else',else_t,else_env,else_c,else_bs,else_ef =
          check_exp envs imp_param true true ret_t (new_t ()) else_ in
        (*TOTHINK Possibly I should first consistency check else and then, with Guarantee,
          then check against expect_t with Require*)
        let then_t',then_c' = type_consistent (Expr l) d_env Require true then_t expect_t in
        let else_t',else_c' = type_consistent (Expr l) d_env Require true else_t expect_t  in
        let t_cs = CondCons((Expr l),Positive,None,c1p,then_c@then_c') in
        let e_cs = CondCons((Expr l),Negative,None,c1n,else_c@else_c') in
        let sub_effects = union_effects ef1 (union_effects then_ef else_ef) in
        let resulting_env = Envmap.intersect_merge (tannot_merge (Expr l) d_env true) then_env else_env in
        (E_aux(E_if(cond',then',else'),(l,simple_annot_efr expect_t sub_effects)),
         expect_t, resulting_env,
         c1@[BranchCons(Expr l, None, [t_cs;e_cs])],
         merge_bounds then_bs else_bs, (*TODO Should be an intersecting merge*)
         sub_effects)
      | _ ->
        let then',then_t,then_env,then_c,then_bs,then_ef = check_exp envs imp_param true true ret_t expect_t then_ in
        let else',else_t,else_env,else_c,else_bs,else_ef = check_exp envs imp_param true true ret_t expect_t else_ in
        let t_cs = CondCons((Expr l),Positive,None,c1,then_c) in
        let e_cs = CondCons((Expr l),Negative,None,[],else_c) in
        let sub_effects = union_effects ef1 (union_effects then_ef else_ef) in
        (E_aux(E_if(cond',then',else'),(l,simple_annot_efr expect_t sub_effects)),
         expect_t,Envmap.intersect_merge (tannot_merge (Expr l) d_env true) then_env else_env,
         c1@[BranchCons(Expr l, None, [t_cs;e_cs])],
         merge_bounds then_bs else_bs,
         sub_effects))
    | E_for(id,from,to_,step,order,block) -> 
      (*TOTHINK Instead of making up new ns here, perhaps I should instead make sure they conform to range 
        without coercion as these nu variables are likely floating*)
      let f,t,s = new_n(),new_n(),new_n() in
      let ft,tt,st = mk_atom f, mk_atom t, mk_atom s in
      let from',from_t,_,from_c,_,from_ef = check_exp envs imp_param false false ret_t ft from in
      let to_',to_t,_,to_c,_,to_ef = check_exp envs imp_param false false ret_t tt to_ in
      let step',step_t,_,step_c,_,step_ef = check_exp envs imp_param false false ret_t st step in
      let new_annot,local_cs = 
        match (aorder_to_ord order).order with
          | Oinc ->
            (simple_annot {t=Tapp("range",[TA_nexp f;TA_nexp t])},[LtEq((Expr l),Guarantee ,f,t)])
          | Odec ->
            (simple_annot {t=Tapp("range",[TA_nexp t; TA_nexp f])},[GtEq((Expr l),Guarantee,f,t)])
          | _ -> (typ_error l "Order specification in a foreach loop must be either inc or dec, not polymorphic")
      in 
      (*TODO Might want to extend bounds here for the introduced variable*)
      let (block',b_t,_,b_c,_,b_ef)=
        check_exp (Env(d_env,Envmap.insert t_env (id_to_string id,new_annot),b_env,tp_env))
          imp_param true true ret_t expect_t block
      in
      let sub_effects = union_effects b_ef (union_effects step_ef (union_effects to_ef from_ef)) in
      (E_aux(E_for(id,from',to_',step',order,block'),(l,constrained_annot_efr b_t local_cs sub_effects)),expect_t,
       Envmap.empty,
       b_c@from_c@to_c@step_c@local_cs,nob,sub_effects)
    | E_vector(es) ->
      let item_t,ord = match expect_t_actual.t with
        | Tapp("vector",[base;rise;TA_ord ord;TA_typ item_t]) -> item_t,ord
        | _ -> new_t (),d_env.default_o in
      let es,cs,effect,item_t = (List.fold_right 
                            (fun (e,t,_,c,_,ef) (es,cs,effect,_) -> (e::es),(c@cs),union_effects ef effect,t)
                            (List.map (check_exp envs imp_param true true ret_t item_t) es) ([],[],pure_e,item_t)) in
      let len = List.length es in
      let t = match ord.order,d_env.default_o.order with
        | (Oinc,_) | (Ouvar _,Oinc) | (Ovar _,Oinc) -> 
          {t = Tapp("vector", [TA_nexp n_zero; TA_nexp (mk_c_int len);
                               TA_ord {order = Oinc}; TA_typ item_t])}
        | (Odec,_) | (Ouvar _,Odec) | (Ovar _,Odec) -> 
          {t = Tapp("vector",[TA_nexp (mk_c_int (len-1));
                              TA_nexp (mk_c_int len);
                              TA_ord {order= Odec}; TA_typ item_t])} 
        | _ -> raise (Reporting_basic.err_unreachable l "Default order was neither inc or dec") in
      let t',cs',ef',e' = type_coerce (Expr l) d_env Guarantee false true b_env t 
          (E_aux(E_vector es,(l,simple_annot_efr t effect))) expect_t in
      (e',t',t_env,cs@cs',nob,union_effects effect ef')
    | E_vector_indexed(eis,(Def_val_aux(default,(ld,annot)))) ->
      let item_t,base_n,rise_n = match expect_t_actual.t with
        | Tapp("vector",[TA_nexp base;TA_nexp rise;ord;TA_typ item_t]) -> item_t,base,rise
        | _ -> new_t (),new_n (), new_n () in
      let first,last = fst (List.hd eis), fst (List.hd (List.rev eis)) in
      let is_inc = first <= last in
      let es,cs,effect,contains_skip,_ =
        (List.fold_right 
           (fun ((i,e),c,ef) (es,cs,effect,skips,prev) -> 
              (*let _ = Printf.eprintf "Checking increasing %b %i %i\n" is_increasing prev i in*)
              let (esn, csn, efn) = (((i,e)::es), (c@cs), union_effects ef effect) in
              if (is_inc && prev > i)
              then (esn,csn,efn,(((prev-i) > 1) || skips),i)
              else if prev < i 
              then (esn,csn,efn,(((i-prev) > 1) || skips),i)
              else if i = prev
              then (typ_error l ("Indexed vector contains a duplicate definition of index " ^ (string_of_int i)))
              else (typ_error l ("Indexed vector is not consistently " ^
                                 (if is_inc then "increasing" else "decreasing"))))
           (List.map (fun (i,e) ->
                let (e,_,_,cs,_,eft) = (check_exp envs imp_param true true ret_t item_t e) in ((i,e),cs,eft))
              eis) ([],[],pure_e,false,(if is_inc then (last+1) else (last-1)))) in
      let (default',fully_enumerate,cs_d,ef_d) = match (default,contains_skip) with
        | (Def_val_empty,false) -> (Def_val_aux(Def_val_empty,(ld,simple_annot item_t)),true,[],pure_e)
        | (Def_val_empty,true)  -> 
          let ef = add_effect (BE_aux(BE_unspec,l)) pure_e in
          let de = E_aux(E_lit (L_aux(L_undef,l)), (l,simple_annot item_t)) in
          (Def_val_aux(Def_val_dec de, (l, cons_efs_annot item_t [] ef ef)),false,[],ef)
        | (Def_val_dec e,_) -> let (de,t,_,cs_d,_,ef_d) = (check_exp envs imp_param true true ret_t item_t e) in
          (*Check that ef_d doesn't write to memory or registers? *)
          (Def_val_aux(Def_val_dec de,(ld,cons_efs_annot item_t cs_d pure_e ef_d)),false,cs_d,ef_d) in
      let (base_bound,length_bound,cs_bounds) = 
        if fully_enumerate
        then (mk_c_int first, mk_c_int (List.length eis),[])
        else (base_n,rise_n,[LtEq(Expr l,Require, base_n,mk_c_int first);
                             GtEq(Expr l,Require, rise_n,mk_c_int (List.length eis))]) 
      in             
      let t = {t = Tapp("vector",
                        [TA_nexp(base_bound);TA_nexp length_bound;
                         TA_ord({order= if is_inc then Oinc else Odec});TA_typ item_t])} in
      let sub_effects = union_effects ef_d effect in
      let t',cs',ef',e' = type_coerce (Expr l) d_env Require false false b_env t 
          (E_aux (E_vector_indexed(es,default'),(l,simple_annot_efr t sub_effects))) expect_t in
      (e',t',t_env,cs@cs_d@cs_bounds@cs',nob,union_effects ef' sub_effects)
    | E_vector_access(vec,i) ->
      let base,len,ord = new_n(),new_n(),new_o() in
      let item_t = new_t () in
      let index = new_n () in
      let vt = {t= Tapp("vector",[TA_nexp base;TA_nexp len;TA_ord ord; TA_typ item_t])} in
      let (vec',t',cs,ef),va_lef,tag = recheck_for_register envs imp_param false false ret_t vt vec in
      let it = mk_atom index in
      let (i',ti',_,cs_i,_,ef_i) = check_exp envs imp_param false false ret_t it i in
      let ord,item_t = match t'.t with
        | Tabbrev(_,{t=Tapp("vector",[_;_;TA_ord ord;TA_typ t])}) | Tapp("vector",[_;_;TA_ord ord;TA_typ t])
        | Tabbrev(_,{t=Tapp("register",[TA_typ{t=Tapp ("vector",[_;_;TA_ord ord;TA_typ t])}])})
        | Tapp("register", [TA_typ{t=Tapp ("vector",[_;_;TA_ord ord;TA_typ t])}]) -> ord,t
        | _ -> ord,item_t in
      let oinc_max_access = mk_sub (mk_add base len) n_one in
      let odec_min_access = mk_add (mk_sub base len) n_one in 
      let cs_loc = 
        match (ord.order,d_env.default_o.order) with
          | (Oinc,_) ->
            [LtEq((Expr l),Require,base,index);LtEq((Expr l),Require, index,oinc_max_access);] 
          | (Odec,_) -> 
            [GtEq((Expr l),Require,base,index); GtEq((Expr l),Require,index,odec_min_access);]
          | (_,Oinc) -> 
            [LtEq((Expr l),Require,base,index);LtEq((Expr l),Require, index,oinc_max_access);] 
          | (_,Odec) ->
            [GtEq((Expr l),Require,base,index); GtEq((Expr l),Require,index,odec_min_access);]
          | _ -> typ_error l "A vector must be either increasing or decreasing to access a single element"
      in 
      (*let _ = Printf.eprintf "Type checking vector access. item_t is %s and expect_t is %s\n" 
        (t_to_string item_t) (t_to_string expect_t) in*)
      let sub_effects = union_effects (union_effects va_lef ef) ef_i in
      let t',cs',ef',e'=type_coerce (Expr l) d_env Require false true b_env item_t 
        (E_aux(E_vector_access(vec',i'),(l,tag_efs_annot item_t tag va_lef sub_effects))) expect_t in
      (e',t',t_env,cs_loc@cs_i@cs@cs',nob,union_effects ef' sub_effects)
    | E_vector_subrange(vec,i1,i2) ->
      (*let _ = Printf.eprintf "checking e_vector_subrange: expect_t is %s\n" (t_to_string expect_t) in*)
      let base,length,ord = new_n(),new_n(),new_o() in
      let new_length = new_n() in
      let n1_start = new_n() in
      let n2_end = new_n() in
      let item_t = match expect_t_actual.t with
        | Tapp("vector",[TA_nexp base_n;TA_nexp rise_n; TA_ord ord_n; TA_typ item_t]) -> item_t
        | _ -> new_t() in
      let vt = {t=Tapp("vector",[TA_nexp base;TA_nexp length;TA_ord ord;TA_typ item_t])} in
      let (vec',vt',cs,ef),v_efs,tag = recheck_for_register envs imp_param false false ret_t vt vec in      
      let i1t = {t=Tapp("atom",[TA_nexp n1_start])} in
      let (i1', ti1, _,cs_i1,_,ef_i1) = check_exp envs imp_param false false ret_t i1t i1 in
      let i2t = {t=Tapp("atom",[TA_nexp n2_end])} in
      let (i2', ti2, _,cs_i2,_,ef_i2) = check_exp envs imp_param false false ret_t i2t i2 in
      let cs_loc =
        match (ord.order,d_env.default_o.order) with
          | (Oinc,_) -> 
            [LtEq((Expr l), Require, base, n1_start);
             LtEq((Expr l), Require, n1_start, n2_end);
             LtEq((Expr l), Require, n2_end, mk_sub (mk_add base length) n_one);
             Eq((Expr l), new_length, mk_add (mk_sub n2_end n1_start) n_one)]
          | (Odec,_) ->
            [GtEq((Expr l), Require, base, n1_start);
             GtEq((Expr l), Require, n1_start, n2_end);
             GtEq((Expr l), Require, n2_end, mk_add (mk_sub base length) n_one);
             Eq((Expr l), new_length, mk_add (mk_sub n1_start n2_end) n_one)]       
          | (_,Oinc) ->
            [LtEq((Expr l), Require, base, n1_start);
             LtEq((Expr l), Require, n1_start, n2_end);
             LtEq((Expr l), Require, n2_end, mk_sub (mk_add base length) n_one);
             Eq((Expr l), new_length, mk_add (mk_sub n2_end n1_start) n_one)]
          | (_,Odec) -> 
            [GtEq((Expr l), Require, base, n1_start);
             GtEq((Expr l), Require, n1_start, n2_end);
             GtEq((Expr l), Require, n2_end, mk_add (mk_sub base length) n_one);
             Eq((Expr l), new_length, mk_add (mk_sub n1_start n2_end) n_one)]
          | _ -> typ_error l "A vector must be either increasing or decreasing to access a slice" in
      let nt = {t = Tapp("vector", [TA_nexp n1_start; TA_nexp new_length; TA_ord ord; TA_typ item_t]) } in
      let sub_effects = union_effects v_efs (union_effects ef (union_effects ef_i1 ef_i2)) in
      let (t,cs3,ef3,e') = 
        type_coerce (Expr l) d_env Require false true b_env nt 
          (E_aux(E_vector_subrange(vec',i1',i2'),(l,Base(([], nt),tag, cs_loc,v_efs, sub_effects,nob)))) expect_t in
      (e',t,t_env,cs3@cs@cs_i1@cs_i2@cs_loc,nob,union_effects ef3 sub_effects)
    | E_vector_update(vec,i,e) ->
      let base,rise,ord = new_n(),new_n(),new_o() in
      let min,m_rise = new_n(),new_n() in
      let item_t = match expect_t_actual.t with
        | Tapp("vector",[TA_nexp base_n;TA_nexp rise_n; TA_ord ord_n; TA_typ item_t]) -> item_t
        | _ -> new_t() in
      let vt = {t=Tapp("vector",[TA_nexp base;TA_nexp rise;TA_ord ord;TA_typ item_t])} in
      let (vec',t',_,cs,_,ef) = check_exp envs imp_param true true ret_t vt vec in
      let it = {t=Tapp("range",[TA_nexp min;TA_nexp m_rise])} in
      let (i', ti, _,cs_i,_,ef_i) = check_exp envs imp_param false false ret_t it i in
      let (e', te, _,cs_e,_,ef_e) = check_exp envs imp_param true true ret_t item_t e in
      let cs_loc = 
        match (ord.order,d_env.default_o.order) with
          | (Oinc,_) ->
            [LtEq((Expr l),Require,base,min); LtEq((Expr l),Require,mk_add min m_rise,mk_add base rise)] 
          | (Odec,_) -> 
            [GtEq((Expr l),Require,base,min); LtEq((Expr l),Require,mk_add min m_rise,mk_sub base rise)]
          | (_,Oinc) ->
            [LtEq((Expr l),Require,base,min); LtEq((Expr l),Require,mk_add min m_rise, mk_add base rise)]
          | (_,Odec) -> 
            [GtEq((Expr l),Require,base,min); LtEq((Expr l),Require,mk_add min m_rise,mk_sub base rise)]
          | _ -> typ_error l "A vector must be either increasing or decreasing to change a single element"
      in      
      let nt = {t=Tapp("vector",[TA_nexp base;TA_nexp rise; TA_ord ord;TA_typ item_t])} in
      let sub_effects = union_effects ef (union_effects ef_i ef_e) in
      let (t,cs3,ef3,e') = 
        type_coerce (Expr l) d_env Require false false b_env nt 
          (E_aux(E_vector_update(vec',i',e'),(l,constrained_annot_efr nt cs_loc sub_effects))) expect_t in
      (e',t,t_env,cs3@cs@cs_i@cs_e@cs_loc,nob,(union_effects ef3 sub_effects))
    | E_vector_update_subrange(vec,i1,i2,e) ->
      let base,rise,ord = new_n(),new_n(),new_o() in
      let min1,m_rise1 = new_n(),new_n() in
      let min2,m_rise2 = new_n(),new_n() in
      let item_t = match expect_t_actual.t with
        | Tapp("vector",[TA_nexp base_n;TA_nexp rise_n; TA_ord ord_n; TA_typ item_t]) -> item_t
        | _ -> new_t() in
      let vt = {t=Tapp("vector",[TA_nexp base;TA_nexp rise;TA_ord ord;TA_typ item_t])} in
      let (vec',t',_,cs,_,ef) = check_exp envs imp_param true true ret_t vt vec in
      let i1t = {t=Tapp("range",[TA_nexp min1;TA_nexp m_rise1])} in
      let (i1', ti1, _,cs_i1,_,ef_i1) = check_exp envs imp_param false false ret_t i1t i1 in
      let i2t = {t=Tapp("range",[TA_nexp min2;TA_nexp m_rise2])} in
      let (i2', ti2, _,cs_i2,_,ef_i2) = check_exp envs imp_param false false ret_t i2t i2 in
      let (e',item_t',_,cs_e,_,ef_e) =
        try check_exp envs imp_param true true ret_t item_t e with
          | _ ->
            let (base_e,rise_e) = new_n(),new_n() in
            let (e',ti',env_e,cs_e,bs_e,ef_e) = 
              check_exp envs imp_param true true ret_t
                {t=Tapp("vector",[TA_nexp base_e;TA_nexp rise_e;TA_ord ord;TA_typ item_t])} e 
            in
            let cs_add = [Eq((Expr l),base_e,min1);LtEq((Expr l),Guarantee,rise,m_rise2)] in
            (e',ti',env_e,cs_e@cs_add,bs_e,ef_e) in          
      let cs_loc =
        match (ord.order,d_env.default_o.order) with
          | (Oinc,_) -> 
            [LtEq((Expr l),Require,base,min1); LtEq((Expr l),Require,mk_add min1 m_rise1,mk_add min2 m_rise2); 
             LtEq((Expr l),Require,mk_add min2 m_rise2,mk_add base rise);]
          | (Odec,_) ->
            [GtEq((Expr l),Require,base,mk_add min1 m_rise1); 
             GtEq((Expr l),Require,mk_add min1 m_rise1,mk_add min2 m_rise2);
             GtEq((Expr l),Require,mk_add min2 m_rise2,mk_sub base rise);]
          | (_,Oinc) -> 
            [LtEq((Expr l),Require,base,min1); LtEq((Expr l),Require,mk_add min1 m_rise1,mk_add min2 m_rise2); 
             LtEq((Expr l),Require,mk_add min2 m_rise2,mk_add base rise);]
          | (_,Odec) ->             
            [GtEq((Expr l),Require,base,mk_add min1 m_rise1); 
             GtEq((Expr l),Require,mk_add min1 m_rise1,mk_add min2 m_rise2);
             GtEq((Expr l),Require,mk_add min2 m_rise2,mk_sub base rise);]
          | _ -> typ_error l "A vector must be either increasing or decreasing to modify a slice" in
      let nt = {t=Tapp("vector",[TA_nexp base;TA_nexp rise; TA_ord ord;TA_typ item_t])} in
      let sub_effects = union_effects ef (union_effects ef_i1 (union_effects ef_i2 ef_e)) in
      let (t,cs3,ef3,e') = 
        type_coerce (Expr l) d_env Require false false b_env nt
          (E_aux(E_vector_update_subrange(vec',i1',i2',e'),
                 (l,constrained_annot_efr  nt cs_loc sub_effects))) expect_t in
      (e',t,t_env,cs3@cs@cs_i1@cs_i2@cs_loc@cs_e,nob,(union_effects ef3 sub_effects))
    | E_vector_append(v1,v2) -> 
      let item_t,ord = match expect_t_actual.t with
        | Tapp("vector",[_;_;TA_ord o;TA_typ i]) -> i,o
        | Tapp("range",_) -> bit_t,new_o ()
        | Tapp("atom",_) -> bit_t, new_o ()
        | _ -> new_t (),new_o () in
      let base1,rise1 = new_n(), new_n() in
      let base2,rise2 = new_n(),new_n() in
      let (v1',t1',_,cs_1,_,ef_1) = 
        check_exp envs imp_param true true ret_t
          {t=Tapp("vector",[TA_nexp base1;TA_nexp rise1;TA_ord ord;TA_typ item_t])} v1 in
      let (v2',t2',_,cs_2,_,ef_2) = 
        check_exp envs imp_param true true ret_t
          {t=Tapp("vector",[TA_nexp base2;TA_nexp rise2;TA_ord ord;TA_typ item_t])} v2 in
      let result_rise = mk_add rise1 rise2 in
      let result_base = match ord.order with
        | Odec -> mk_sub result_rise n_one
        | _ -> n_zero in
      let ti =  {t=Tapp("vector",[TA_nexp result_base;TA_nexp result_rise;TA_ord ord; TA_typ item_t])} in
      let sub_effects = union_effects ef_1 ef_2 in
      let (t,cs_c,ef_c,e') = 
        type_coerce (Expr l) d_env Require false true b_env ti 
          (E_aux(E_vector_append(v1',v2'),(l,simple_annot_efr ti sub_effects))) expect_t in
      (e',t,t_env,cs_1@cs_2,nob,(union_effects ef_c sub_effects))
    | E_list(es) ->
      let item_t = match expect_t_actual.t with
        | Tapp("list",[TA_typ i]) -> i
        | _ -> new_t() in
      let es,cs,effect,item_t = 
        (List.fold_left (fun (es,cs,effect,_) (e,t,_,c,_,ef) -> (e::es),(c@cs),union_effects ef effect,t) 
           ([],[],pure_e,item_t) (List.map (check_exp envs imp_param true true ret_t item_t) es) ) in
      let t = {t = Tapp("list",[TA_typ item_t])} in
      let t',cs',ef',e' = type_coerce (Expr l) d_env Require false false b_env t 
        (E_aux(E_list es,(l,simple_annot_efr t effect))) expect_t in
      (e',t',t_env,cs@cs',nob,union_effects ef' effect)
    | E_cons(i, ls) ->
      let item_t = match expect_t_actual.t with
        | Tapp("list",[TA_typ i]) -> i
        | _ -> new_t() in
      let lt = {t=Tapp("list",[TA_typ item_t])} in
      let (ls',t',_,cs,_,ef) = check_exp envs imp_param true true ret_t lt ls in
      let (i', ti, _,cs_i,_,ef_i) = check_exp envs imp_param true true ret_t item_t i in
      let sub_effects = union_effects ef ef_i in
      let (t',cs',ef',e') = 
        type_coerce (Expr l) d_env Require false false b_env lt
          (E_aux(E_cons(i',ls'),(l,simple_annot_efr lt sub_effects))) expect_t in
      (e',t',t_env,cs@cs'@cs_i,nob,union_effects ef' sub_effects)
    | E_record(FES_aux(FES_Fexps(fexps,_),l')) -> 
      let u,_ = get_abbrev d_env expect_t in
      let u_actual = match u.t with | Tabbrev(_, u) -> u | _ -> u in
      let field_walker r subst_env bounds tag n =
        (fun (FE_aux(FE_Fexp(id,exp),(l,annot))) (fexps,cons,ef') ->
          let i = id_to_string id in
          match lookup_field_type i r with
            | None -> 
              typ_error l ("Expected a struct of type " ^ n ^ ", which should not have a field " ^ i)
            | Some(ft) ->
              let ft = typ_subst subst_env false ft in
              let (e,t',_,c,_,ef) = check_exp envs imp_param true true ret_t ft exp in
              (FE_aux(FE_Fexp(id,e),(l,Base(([],t'),tag,c,ef,ef,bounds)))::fexps,cons@c,union_effects ef ef')) in  
      (match u_actual.t with
        | Tid(n) | Tapp(n,_)->
          (match lookup_record_typ n d_env.rec_env with 
            | Some(((i,Record,(Base((params,t),tag,cs,eft,_,bounds)),fields) as r)) -> 
              let (ts,cs,eft,subst_env) = subst params false false t cs eft in
              if (List.length fexps = List.length fields) 
              then let fexps,cons,ef =
                     List.fold_right (field_walker r subst_env bounds tag n) fexps ([],[],pure_e) in
                   let e = E_aux(E_record(FES_aux(FES_Fexps(fexps,false),l')),(l,simple_annot_efr u ef)) in
                   let (t',cs',ef',e') = type_coerce (Expr l) d_env Guarantee false false b_env ts e expect_t in
                   (e',t',t_env,cs@cons@cs',nob,union_effects ef ef')
              else typ_error l ("Expected a struct of type " ^ n ^ ", which should have " ^
                                string_of_int (List.length fields) ^ " fields")
            | Some(i,Register,tannot,fields) -> typ_error l ("Expected a value with register type, found a struct")
            | _ -> typ_error l ("Expected a value of type " ^ n ^ " but found a struct"))           
        | Tuvar _ ->
          let field_names = List.map (fun (FE_aux(FE_Fexp(id,exp),(l,annot))) -> id_to_string id) fexps in
          (match lookup_record_fields field_names d_env.rec_env with
            | Some(((i,Record,(Base((params,t),tag,cs,eft,_,bounds)),fields) as r)) ->
              let (ts,cs,eft,subst_env) = subst params false false t cs eft in
              let fexps,cons,ef = List.fold_right (field_walker r subst_env bounds tag i) fexps ([],[],pure_e) in 
              let e = E_aux(E_record(FES_aux(FES_Fexps(fexps,false),l')),(l,simple_annot_efr ts ef)) in
              let (t',cs',ef',e') = type_coerce (Expr l) d_env Guarantee false false b_env ts e expect_t in
              (e',t',t_env,cs@cons@cs',nob,union_effects ef ef')
            | Some(i,Register,tannot,fields) -> typ_error l "Expected a value with register type, found a struct"
            | _ -> typ_error l "No struct type matches the set of fields given")
        | _ -> typ_error l ("Expected an expression of type " ^ t_to_string expect_t ^ " but found a struct"))
    | E_record_update(exp,FES_aux(FES_Fexps(fexps,_),l')) -> 
      let (e',t',_,c,_,ef) = check_exp envs imp_param true true ret_t expect_t exp in
      let field_walker r subst_env bounds tag i =
        (fun (FE_aux(FE_Fexp(id,exp),(l,annot))) (fexps,cons,ef') ->
           let fi = id_to_string id in
           match lookup_field_type fi r with
           | None -> typ_error l ("Expected a struct with type " ^ i ^ ", which does not have a field " ^ fi)
           | Some ft ->
             let ft = typ_subst subst_env false ft in
             let (e,t',_,c,_,ef) = check_exp envs imp_param true true ret_t ft exp in
             (FE_aux(FE_Fexp(id,e),(l,Base(([],t'),tag,c,pure_e,ef,bounds)))::fexps,cons@c,union_effects ef ef')) in
      (match t'.t with
        | Tid i | Tabbrev(_, {t=Tid i}) | Tapp(i,_) ->
          (match lookup_record_typ i d_env.rec_env with
           | Some((i,Register,tannot,fields)) ->
             typ_error l "Expected a struct for this update, instead found a register"
           | Some(((i,Record,(Base((params,t),tag,cs,eft,_,bounds)),fields) as r)) ->
              if (List.length fexps <= List.length fields) 
              then 
                let (ts,cs,eft,subst_env) = subst params false false t cs eft in
                let fexps,cons,ef = List.fold_right (field_walker r subst_env bounds tag i) fexps ([],[],pure_e) in
                let e = E_aux(E_record_update(e',FES_aux(FES_Fexps(fexps,false),l')), (l,simple_annot_efr ts ef)) in
                let (t',cs',ef',e') = type_coerce (Expr l) d_env Guarantee false false b_env ts e expect_t in
                (e',t',t_env,cs@cons@cs',nob,union_effects ef ef')
              else typ_error l ("Expected fields from struct " ^ i ^ ", given more fields than struct includes")
            | _ -> 
              typ_error l ("Expected a struct or register, instead found an expression with type " ^ i))
        | Tuvar _ ->
          let field_names = List.map (fun (FE_aux(FE_Fexp(id,exp),(l,annot))) -> id_to_string id) fexps in
          (match lookup_possible_records field_names d_env.rec_env with
            | [] -> typ_error l "No struct matches the set of fields given for this struct update"
            | [(((i,Record,(Base((params,t),tag,cs,eft,_,bounds)),fields) as r))] ->
              let (ts,cs,eft,subst_env) = subst params false false t cs eft in
              let fexps,cons,ef = List.fold_right (field_walker r subst_env bounds tag i) fexps ([],[],pure_e) in
              let e =  E_aux(E_record_update(e',FES_aux(FES_Fexps(fexps,false),l')), (l,simple_annot_efr ts ef)) in
              let (t',cs',ef',e') = type_coerce (Expr l) d_env Guarantee false false b_env ts e expect_t in
              (e',t',t_env,cs@cons@cs',nob,union_effects ef ef')
            | [(i,Register,tannot,fields)] -> typ_error l "Expected a value with register type, found a struct"
            | records -> typ_error l "Multiple structs contain this set of fields, try adding a cast")
        | _ -> typ_error l ("Expected a struct to update but found an expression of type " ^ t_to_string expect_t))
    | E_field(exp,id) ->
      let (e',t',env_sub,c_sub,bounds,ef_sub) = check_exp envs imp_param true true ret_t (new_t()) exp in
      let fi = id_to_string id in
      (match t'.t with
      | Tabbrev({t=Tid i}, _) | Tabbrev({t=Tapp(i,_)},_) | Tid i | Tapp(i,_) ->
          (match lookup_record_typ i d_env.rec_env with
            | Some(((i,rec_kind,(Base((params,t),tag,cs,eft,_,bounds)),fields) as r)) ->
              let (ts,cs,eft,subst_env) = subst params false false t cs eft in
              (match lookup_field_type fi r with
                | None -> typ_error l ("Type " ^ i ^ " does not have a field " ^ fi)
                | Some t ->
                  let ft = typ_subst subst_env false t in
                  let (_,cs_sub') = type_consistent (Expr l) d_env Guarantee true ts t' in
                  let (e',t',_,c_sub,_,ef_sub),ef_update =
                    match rec_kind with
                      | Register ->
                        (check_exp envs imp_param true true ret_t (into_register_typ t') exp,
                         add_effect (BE_aux(BE_rreg, l)) pure_e)
                      | Record -> ((e',t',env_sub,c_sub,bounds,ef_sub), pure_e) in
                  let (et',c',ef',acc) = 
                    type_coerce (Expr l) d_env Require false true b_env ft 
                      (E_aux(E_field(e',id),
                             (l,Base(([],ft),
                                     tag,cs,union_effects eft ef_update,union_effects ef_sub ef_update,bounds))))
                      expect_t in
                  (acc,et',t_env,cs@c'@c_sub@cs_sub',nob,union_effects ef' (union_effects ef_update ef_sub)))
            | _ -> 
              typ_error l ("Expected a struct or register, instead found an expression with type " ^ i))
      | Tuvar _ ->
        (match lookup_possible_records [fi] d_env.rec_env with
         | [] -> typ_error l ("No struct or register has a field " ^ fi)
         | [(((i,rec_kind,(Base((params,t),tag,cs,eft,_,bounds)),fields) as r))] ->
           let (ts,cs,eft,subst_env) = subst params false false t cs eft in
           (match lookup_field_type fi r with
            | None -> 
              raise
                (Reporting_basic.err_unreachable l "lookup_possible_records returned a record without the field")
            | Some t ->
              let ft = typ_subst subst_env false t in
              let (_,cs_sub') = type_consistent (Expr l) d_env Guarantee false ts t' in
              let (e',t',_,c_sub,_,ef_sub),ef_update =
                match rec_kind with
                  | Register ->
                    (check_exp envs imp_param true true ret_t (into_register_typ t') exp,
                     add_effect (BE_aux(BE_rreg, l)) pure_e)
                  | Record -> ((e',t',env_sub,c_sub,bounds,ef_sub), pure_e) in
              let (et',c',ef',acc) = 
                type_coerce (Expr l) d_env Require false false b_env ft 
                  (E_aux(E_field(e',id),
                         (l,Base(([],ft),tag,
                                 cs,union_effects eft ef_update,union_effects ef_sub ef_update,bounds)))) expect_t in
              (acc,et',t_env,cs@c'@c_sub@cs_sub',nob,union_effects ef' (union_effects ef_update ef_sub)))
         | records ->
           typ_error l ("Multiple structs or registers contain field " ^ fi ^ ", try adding a cast to disambiguate"))
      | _ -> typ_error l ("Expected a struct or register but found an expression of type " ^ t_to_string t'))
    | E_case(exp,pexps) ->
      let (e',t',_,cs,_,ef) = check_exp envs imp_param true true ret_t (new_t()) exp in
      (*let _ = Printf.eprintf "Type of pattern after expression check %s\n" (t_to_string t') in*)
      let t' = 
        match t'.t with
          | Tapp("register",[TA_typ t]) -> t
          | _ -> t' in
      (*let _ = Printf.eprintf "Type of pattern after register check %s\n" (t_to_string t') in*)
      let (pexps',t,cs',ef') = 
        check_cases envs imp_param ret_t t' expect_t (if (List.length pexps) = 1 then Solo else Switch) pexps in
      let effects = union_effects ef ef' in
      (E_aux(E_case(e',pexps'),(l,simple_annot_efr t effects)),t,
       t_env,cs@[BranchCons(Expr l, None, cs')],nob,effects)
    | E_let(lbind,body) -> 
      let (lb',t_env',cs,b_env',ef) = (check_lbind envs imp_param false (Some ret_t) Emp_local lbind) in
      let new_env = 
        (Env(d_env,Envmap.union_merge (tannot_merge (Expr l) d_env false)
               t_env t_env', merge_bounds b_env' b_env,tp_env)) 
      in
      let (e,t,_,cs',_,ef') = check_exp new_env imp_param true true ret_t expect_t body in
      let effects = union_effects ef ef' in
      (E_aux(E_let(lb',e),(l,simple_annot_efr t effects)),t,t_env,cs@cs',nob,effects)
    | E_assign(lexp,exp) ->
      let (lexp',t',_,t_env',tag,cs,b_env',efl,efr) = check_lexp envs imp_param ret_t true lexp in
      let t' = match t'.t with | Tapp("reg",[TA_typ t]) | Tapp("register",[TA_typ t])
                               | Tabbrev(_,{t=Tapp("register",[TA_typ t])}) -> t
                               | _ -> t' in
      let (exp',t'',_,cs',_,efr') = check_exp envs imp_param true true ret_t t' exp in
      let (t',c') = type_consistent (Expr l) d_env Require false unit_t expect_t in
      let effects = union_effects efl (union_effects efr efr') in
      (E_aux(E_assign(lexp',exp'),(l,(Base(([],unit_t),tag,[],efl,effects,nob)))),
       unit_t,t_env',cs@cs'@c',b_env',effects)
    | E_exit e ->
      let (e',t',_,_,_,_) = check_exp envs imp_param true true ret_t (new_t ()) e in
      let efs = add_effect (BE_aux(BE_escape, l)) pure_e in
      (E_aux (E_exit e',(l,(simple_annot_efr expect_t efs))),expect_t,t_env,[],nob,efs)
    | E_return e ->
      let (e', t'',_,cs,_,efr) = check_exp envs imp_param true true ret_t ret_t e in
      let ers = add_effect (BE_aux (BE_lret,l)) pure_e in
      (E_aux (E_return e', (l, (simple_annot_efr ret_t ers))), ret_t, t_env,cs,nob,union_effects efr ers)
    | E_sizeof nexp ->
      let n = anexp_to_nexp envs nexp in
      let n_subst = subst_n_with_env tp_env n in
      let n_typ = mk_atom n_subst in
      let nannot = bounds_annot n_typ b_env in
      let e = E_aux (E_sizeof_internal (l, nannot), (l,nannot)) in      
      let t',cs,ef,e' = type_coerce (Expr l) d_env Require false false b_env n_typ e expect_t in
      (e',t',t_env,cs,nob,ef)
    | E_assert(cond,msg) ->
      let (cond',t',_,_,_,_) = check_exp envs imp_param true true ret_t bit_t cond in
      let (msg',mt',_,_,_,_) = check_exp envs imp_param true true ret_t {t= Tapp("option",[TA_typ string_t])} msg in
      let (t',c') = type_consistent (Expr l) d_env Require false unit_t expect_t in
      (E_aux (E_assert(cond',msg'), (l, (simple_annot expect_t))), expect_t,t_env,c',nob,pure_e)
    | E_comment s ->
      (E_aux (E_comment s, (l, simple_annot unit_t)), expect_t,t_env,[],nob,pure_e)
    | E_comment_struc e ->
      (E_aux (E_comment_struc e, (l, simple_annot unit_t)), expect_t,t_env,[],nob,pure_e)
    | E_internal_cast _ | E_internal_exp _ | E_internal_exp_user _ | E_internal_let _
    | E_internal_plet _ | E_internal_return _ | E_sizeof_internal _ -> 
      raise (Reporting_basic.err_unreachable l "Internal expression passed back into type checker")

and recheck_for_register envs imp_param widen_num widen_vec ret_t expect_t exp = 
  match check_exp envs imp_param widen_num widen_vec ret_t expect_t exp with
  | exp',t',_,cs,_,ef ->
    match exp' with
    | E_aux(_, (l, Base(_, _, _, leff, ceff, _))) ->
      if has_rreg_effect ceff
      then try let (exp',t',_,cs,_,ef) =
                 check_exp envs imp_param widen_num widen_vec ret_t (into_register_typ t') exp in
          (exp',t',cs,ef),(add_effect (BE_aux(BE_rreg,l)) pure_e),External None
        with | _ -> (exp',t',cs,ef),pure_e, Emp_local
      else (exp',t',cs,ef),pure_e, Emp_local
    | _ -> (exp',t',cs,ef),pure_e, Emp_local

and check_block envs imp_param ret_t expect_t exps:((tannot exp) list * tannot * nexp_range list * t * effect) =
  let Env(d_env,t_env,b_env,tp_env) = envs in
  match exps with
    | [] -> ([],NoTyp,[],unit_t,pure_e)
    | [e] -> 
      let (E_aux(e',(l,annot)),t,envs,sc,_,ef) = check_exp envs imp_param true true ret_t expect_t e in
      ([E_aux(e',(l,annot))],annot,sc,t,ef)
    | e::exps -> 
      let (e',t',t_env',sc,b_env',ef') = check_exp envs imp_param true true ret_t unit_t e in
      let (exps',annot',sc',t,ef) = 
        check_block (Env(d_env,
                         Envmap.union_merge (tannot_merge (Expr Parse_ast.Unknown) d_env false) t_env t_env',
                         merge_bounds b_env' b_env, tp_env)) imp_param ret_t expect_t exps in
      let annot' = match annot' with
        | Base(pt,tag,cs,efl,efr,bounds) -> Base(pt,tag,cs,efl,union_effects efr ef',bounds)
        | _ -> annot' in
      ((e'::exps'),annot',sc@sc',t,union_effects ef ef')

and check_cases envs imp_param ret_t check_t expect_t kind pexps
  : ((tannot pexp) list * typ * nexp_range list * effect) =
  let (Env(d_env,t_env,b_env,tp_env)) = envs in
  match pexps with
    | [] -> raise (Reporting_basic.err_unreachable Parse_ast.Unknown "switch with no cases found")
    | [(Pat_aux(Pat_exp(pat,exp),(l,annot)))] ->
      let pat',env,cs_p,bounds,u = check_pattern envs Emp_local check_t pat in
      let e,t,_,cs_e,_,ef = 
        check_exp (Env(d_env,
                       Envmap.union_merge (tannot_merge (Expr l) d_env true) t_env env,
                       merge_bounds b_env bounds, tp_env)) imp_param true true ret_t expect_t exp in
      let cs = [CondCons(Expr l,kind,None, cs_p, cs_e)] in
      [Pat_aux(Pat_exp(pat',e),(l,cons_efs_annot t cs pure_e ef))],t,cs,ef
    | ((Pat_aux(Pat_exp(pat,exp),(l,annot)))::pexps) ->
      let pat',env,cs_p,bounds,u = check_pattern envs Emp_local check_t pat in
      let (e,t,_,cs_e,_,ef) = 
        check_exp (Env(d_env,
                       Envmap.union_merge (tannot_merge (Expr l) d_env true) t_env env,
                       merge_bounds b_env bounds, tp_env)) imp_param true true ret_t expect_t exp in
      let cs = CondCons(Expr l,kind,None,cs_p,cs_e) in
      let (pes,tl,csl,efl) = check_cases envs imp_param ret_t check_t expect_t kind pexps in      
      ((Pat_aux(Pat_exp(pat',e),(l,cons_efs_annot t [cs] pure_e ef)))::pes,tl,cs::csl,union_effects efl ef)

and check_lexp envs imp_param ret_t is_top (LEXP_aux(lexp,(l,annot))) 
    : (tannot lexp * typ * bool * tannot emap * tag * nexp_range list * bounds_env * effect * effect ) =
  let (Env(d_env,t_env,b_env,tp_env)) = envs in
  match lexp with
    | LEXP_id id -> 
      let i = id_to_string id in
      (match Envmap.apply t_env i with
       | Some(Base((parms,t),Default,_,_,_,_)) ->
         let t = {t=Tapp("reg",[TA_typ t])} in
         let bounds = extract_bounds d_env i t in
         let tannot = (Base(([],t),Emp_intro,[],pure_e,pure_e,bounds)) in
         (LEXP_aux(lexp,(l,tannot)),t,false,Envmap.from_list [i,tannot],Emp_intro,[],bounds,pure_e,pure_e)
       | Some(Base(([],t),Alias alias_inf,_,_,_,_)) ->
         let ef = {effect = Eset[BE_aux(BE_wreg,l)]} in
         (match Envmap.apply d_env.alias_env i with
          | Some(OneReg(reg, (Base(([],t'),_,_,_,_,_)))) ->
            (LEXP_aux(lexp,(l,(Base(([],t'),Alias alias_inf,[],ef,ef,nob)))), t, false,
             Envmap.empty, External (Some reg),[],nob,ef,ef)
          | Some(TwoReg(reg1,reg2, (Base(([],t'),_,_,_,_,_)))) ->
            let u = match t.t with
              | Tapp("register", [TA_typ u]) -> u 
              | _ -> raise (Reporting_basic.err_unreachable l "TwoReg didn't contain a register type") in
            (LEXP_aux(lexp,(l,Base(([],t'),Alias alias_inf,[],ef,ef,nob))),
             u, false, Envmap.empty, External None,[],nob,ef,ef)
          | _ -> assert false)
       | Some(Base((parms,t),tag,cs,_,_,b)) ->
          let t,cs,ef,_ = 
            match tag with | External _ | Emp_global -> subst parms false false t cs pure_e
                           | _ -> t,cs,{effect = Eset[BE_aux(BE_lset,l)]},Envmap.empty
          in
          let t,cs' = get_abbrev d_env t in
          let t_actual = match t.t with | Tabbrev(i,t) -> t | _ -> t in
          let cs_o = cs@cs' in
          (*let _ = Printf.eprintf "Assigning to %s, t is %s\n" i (t_to_string t_actual) in*)
          (match t_actual.t,is_top with
           | Tapp("register",[TA_typ u]),true ->
             let ef = {effect=Eset[BE_aux(BE_wreg,l)]} in
             (LEXP_aux(lexp,(l,(Base(([],t),External (Some i),cs_o,ef,pure_e,nob)))),u,false,
              Envmap.empty,External (Some i),[],nob,ef,ef)
           | Tapp("register",[TA_typ u]),false ->
             (LEXP_aux(lexp,(l,(Base(([],t), Emp_global, cs_o, pure_e,pure_e,nob)))), t,false,
              Envmap.empty, Emp_global, [],nob,pure_e,pure_e)
           | Tapp("reg",[TA_typ u]),_ ->
             (LEXP_aux(lexp,(l,(Base(([],t),Emp_set,cs_o,ef,ef,b)))),u,false,Envmap.empty,Emp_set,[],nob,ef,ef)
           | Tapp("vector",_),false ->
             (LEXP_aux(lexp,(l,(Base(([],t),tag,cs_o,ef,ef,b)))),t,true,Envmap.empty,Emp_set,[],nob,ef,ef)
           | (Tfn _ ,_) ->
             (match tag with 
              | External _ | Spec | Emp_global -> 
                let u = new_t() in
                let t = {t = Tapp("reg",[TA_typ u])} in
                let bounds = extract_bounds d_env i t in
                let tannot = (Base(([],t),Emp_intro,[],pure_e,pure_e,bounds)) in
                (LEXP_aux(lexp,(l,tannot)),u,false,Envmap.from_list [i,tannot],Emp_intro,[],bounds,pure_e,pure_e)
              | _ -> 
                typ_error l ("Cannot assign to " ^ i ^" with type " ^ t_to_string t ^ 
                             ". Assignment must be to registers or non-parameter, non-let-bound local variables."))
           | _,_ ->
             if is_top
             then 
               typ_error l ("Cannot assign to " ^ i ^" with type " ^ t_to_string t ^ 
                            ". Assignment must be to registers or non-parameter, non-let-bound local variables.")
             else 
               (LEXP_aux(lexp,(l,constrained_annot t cs_o)),t,true,Envmap.empty,Emp_local,[],nob,pure_e,pure_e))
        | _ -> 
          let u = new_t() in
          let t = {t=Tapp("reg",[TA_typ u])} in
          let bounds = extract_bounds d_env i u in
          let tannot = (Base(([],t),Emp_intro,[],pure_e,pure_e,bounds)) in
          (LEXP_aux(lexp,(l,tannot)),u,false,Envmap.from_list [i,tannot],Emp_intro,[],bounds,pure_e,pure_e))
    | LEXP_memory(id,exps) -> 
      let i = id_to_string id in
      (match Envmap.apply t_env i with
        | Some(Base((parms,t),tag,cs,ef,_,_)) ->
          let t,cs,ef,_ = subst parms false false t cs ef in
          (match t.t with
            | Tfn(apps,out,_,ef') ->
              (match ef'.effect with
                | Eset effects ->
                  let mem_write = List.exists (fun (BE_aux(b,_)) ->
                      match b with | BE_wmem -> true | _ -> false) effects in
                  let memv_write = List.exists (fun (BE_aux(b,_)) ->
                      match b with |BE_wmv -> true | _ -> false) effects in
                  let reg_write = List.exists (fun (BE_aux(b,_)) ->
                      match b with | BE_wreg -> true | _ -> false) effects in
                  if  (mem_write || memv_write || reg_write)
                  then
                    let app,cs_a = get_abbrev d_env apps in
                    let out,cs_o = get_abbrev d_env out in
                    let cs_call = cs@cs_o@cs_a in
                    (match app.t with
                      | Ttup ts | Tabbrev(_,{t=Ttup ts}) ->
                        let (args,item_t) = ((fun ts -> (List.rev (List.tl ts), List.hd ts)) (List.rev ts)) in
                        let args_t = {t = Ttup args} in
                        let (es, cs_es, ef_es) = 
                          match args,exps with
                            | [],[] -> ([],[],pure_e)
                            | [],[e] -> let (e',_,_,cs_e,_,ef_e) = check_exp envs imp_param true true ret_t unit_t e
                              in ([e'],cs_e,ef_e)
                            | [],es -> typ_error l ("Expected no arguments for assignment function " ^ i)
                            | args,[] -> 
                              typ_error l ("Expected arguments with types " ^ (t_to_string args_t) ^
                                           "for assignment function " ^ i)
                            | args,es -> 
                              (match check_exp envs imp_param true true ret_t args_t
                                       (E_aux (E_tuple exps,(l,NoTyp))) with
                              | (E_aux(E_tuple es,(l',tannot)),_,_,cs_e,_,ef_e) -> (es,cs_e,ef_e)
                              | _ -> 
                                raise (Reporting_basic.err_unreachable l 
                                         "Gave check_exp a tuple, didn't get a tuple back"))
                        in
                        let ef_all = union_effects ef' ef_es in
                        (LEXP_aux(LEXP_memory(id,es),(l,Base(([],out),tag,cs_call,ef',ef_all,nob))),
                         item_t,false,Envmap.empty,tag,cs_call@cs_es,nob,ef',ef_all)
                      | _ -> 
                        let e = match exps with
                          | [] -> E_aux(E_lit(L_aux(L_unit,l)),(l,NoTyp))
                          | [(E_aux(E_lit(L_aux(L_unit,_)),(_,NoTyp)) as e)] -> e
                          | es -> typ_error l ("Expected no arguments for assignment function " ^ i) in
                        let (e,_,_,cs_e,_,ef_e) = check_exp envs imp_param true true ret_t apps e in
                        let ef_all = union_effects ef ef_e in
                        (LEXP_aux(LEXP_memory(id,[e]),(l,Base(([],out),tag,cs_call,ef,ef_all,nob))),
                         app,false,Envmap.empty,tag,cs_call@cs_e,nob,ef,ef_all))
                  else typ_error l ("Assignments require functions with a wmem, wmv, or wreg effect")
                | _ -> typ_error l ("Assignments require functions with a wmem, wmv, or wreg effect"))
            | _ ->
              typ_error l ("Assignments require a function here, found " ^ i ^ " which has type " ^ (t_to_string t)))
        | _ -> typ_error l ("Unbound identifier " ^ i))
    | LEXP_cast(typ,id) -> 
      let i = id_to_string id in
      let ty = typ_to_t envs false false typ in
      let ty = typ_subst tp_env false ty in
      let new_bounds = extract_bounds d_env i ty in
      (match Envmap.apply t_env i with
        | Some(Base((parms,t),tag,cs,_,_,bounds)) ->
          let t,cs,ef,_ = 
            match tag with | External _ | Emp_global -> subst parms false false t cs pure_e
                           | _ -> t,cs,{effect=Eset[BE_aux(BE_lset,l)]},Envmap.empty
          in
          let t,cs' = get_abbrev d_env t in
          let t_actual = match t.t with | Tabbrev(_,t) -> t | _ -> t in
          let bs = merge_bounds bounds new_bounds in
          (match t_actual.t,is_top with
            | Tapp("register",[TA_typ u]),true ->
              let t',cs = type_consistent (Expr l) d_env Require false ty u in
              let ef = {effect=Eset[BE_aux(BE_wreg,l)]} in
              (LEXP_aux(lexp,(l,(Base(([],t),External (Some i),cs,ef,pure_e,nob)))),ty,false,
               Envmap.empty,External (Some i),[],nob,ef,ef)
            | Tapp("register",[TA_typ u]),false ->
              (LEXP_aux(lexp,(l,(Base(([],t), Emp_global, cs', pure_e,pure_e,nob)))), t,false,
               Envmap.empty, Emp_global, [],nob,pure_e,pure_e)              
            | Tapp("reg",[TA_typ u]),_ ->
              let t',cs = type_consistent (Expr l) d_env Require false ty u in
              (LEXP_aux(lexp,(l,(Base(([],t),Emp_set,cs,ef,pure_e,bs)))),ty,false,
               Envmap.empty,Emp_set,[],bs,ef,ef)
            | Tapp("vector",_),false ->
              (LEXP_aux(lexp,(l,(Base(([],t),tag,cs,ef,pure_e,bs)))),ty,true,Envmap.empty,Emp_set,[],bs,ef,ef)
            | Tuvar _,_ ->
              let u' = {t=Tapp("reg",[TA_typ ty])} in
              equate_t t u';
              (LEXP_aux(lexp,(l,(Base((([],u'),Emp_set,cs,ef,pure_e,bs))))),
               ty,false,Envmap.empty,Emp_set,[],bs,ef,ef)
            | (Tfn _ ,_) ->
              (match tag with 
               | External _ | Spec | Emp_global ->
                 let u' = {t=Tapp("reg",[TA_typ ty])} in
                  let tannot = (Base(([],u'),Emp_intro,[],pure_e,pure_e,new_bounds)) in
                  (LEXP_aux(lexp,(l,tannot)),u',
                   false,Envmap.from_list [i,tannot],Emp_intro,[],new_bounds,pure_e,pure_e)
                | _ -> 
                  typ_error l ("Cannot assign to " ^ i ^ " with type " ^ t_to_string t)) 
            | _,_ -> 
              if is_top
              then typ_error l 
                ("Cannot assign to " ^ i ^ " with type " ^ t_to_string t ^
                    ". May only assign to registers, and non-paremeter, non-let bound local variables")
              else 
                (* TODO, make sure this is a record *)
                (LEXP_aux(lexp,(l,(Base(([],t),Emp_local,cs,pure_e,pure_e,nob)))),
                 ty,false,Envmap.empty,Emp_local,[],nob,pure_e,pure_e))
        | _ -> 
          let t = {t=Tapp("reg",[TA_typ ty])} in
          let tannot = (Base(([],t),Emp_intro,[],pure_e,pure_e,new_bounds)) in
          (LEXP_aux(lexp,(l,tannot)),ty,false,Envmap.from_list [i,tannot],Emp_intro,[],new_bounds,pure_e,pure_e))
    | LEXP_tup tuples ->
      if is_top
      then
        if tuples = []
        then typ_error l "Attempt to set an empty tuple, which is not allowed"
        else
          let tuple_checks = List.map (check_lexp envs imp_param ret_t true) tuples in
          let tuple_vs = List.map (fun (le,_,_,_,_,_,_,_,_) -> le) tuple_checks in
          let tuple_typs = List.map (fun (_,le_t,_,_,_,_,_,_,_) -> le_t) tuple_checks in
          let tuple_tags = List.map (fun (_,_,_,_,tag,_,_,_,_) -> tag) tuple_checks in
          let env = List.fold_right (fun (_,_,_,env,_,_,_,_,_) envf -> Envmap.union env envf)
              tuple_checks Envmap.empty in
          let cs = List.fold_right (fun (_,_,_,_,_,cs,_,_,_) csf -> cs @csf) tuple_checks [] in
          let bounds = List.fold_right (fun (_,_,_,_,_,_,bs,_,_) bf -> merge_bounds bs bf) tuple_checks nob in
          let efr = List.fold_right (fun (_,_,_,_,_,_,_,_,efr) efrf -> union_effects efr efrf) tuple_checks pure_e in
          let ty = mk_tup tuple_typs in
          let tag = Tuple_assign tuple_tags in
          let tannot = (Base(([],ty),tag,[],pure_e,efr,bounds)) in
          (LEXP_aux (LEXP_tup tuple_vs, (l,tannot)), ty,false,env, tag,cs,bounds,pure_e,efr)
      else typ_error l "Tuples in assignments may only be at the top level or within other tuples"
    | LEXP_vector(vec,acc) -> 
      let (vec',vec_t,reg_required,env,tag,csi,bounds,efl,efr) = check_lexp envs imp_param ret_t false vec in
      let vec_t,cs' = get_abbrev d_env vec_t in
      let vec_actual,writing_reg_bit = match vec_t.t with
        | Tapp("register",[TA_typ {t=Tabbrev(_,t)}]) | Tapp("register",[TA_typ t])
        | Tabbrev(_,{t=Tapp("register",[TA_typ t])}) -> t,true
        | Tabbrev(_,t) -> t,false | _ -> vec_t,false in
      (match vec_actual.t with
       | Tapp("vector",[TA_nexp base;TA_nexp rise;TA_ord ord;TA_typ item_t]) ->
         let acc_n = new_n () in
         let acc_t,cs_t = match ord.order with
           | Oinc -> mk_atom acc_n, [LtEq(Specc l, Require, base, acc_n);
                                     LtEq(Specc l, Require, acc_n, (mk_sub (mk_add base rise) n_one))]
           | Odec -> mk_atom acc_n, [GtEq(Specc l, Require, base, acc_n);
                                     GtEq(Specc l, Require, acc_n, (mk_sub (mk_add base n_one) rise))] 
            | _ -> typ_error l ("Assignment to one vector element requires a non-polymorphic order")
          in
         let (e,acc_t',_,cs',_,ef_e) = check_exp envs imp_param false false ret_t acc_t acc in
         let item_t_act,_ = get_abbrev d_env item_t in
         let item_t,add_reg_write,reg_still_required = 
           match item_t_act.t with
             | Tapp("register",[TA_typ t]) | Tabbrev(_,{t=Tapp("register",[TA_typ t])}) -> t,true,false
             | Tapp("reg",[TA_typ t]) -> t,false,false
             | _ -> item_t,false,not(writing_reg_bit) in
         let efl,tag = if add_reg_write || writing_reg_bit then (add_effect (BE_aux(BE_wreg,l)) efl,External None)
           else match tag with | External _ -> (efl,Emp_local) | _ ->  (efl,tag) in
         let efr = union_effects efl (union_effects efr ef_e) in
         if is_top && reg_still_required && reg_required && not(writing_reg_bit)
         then typ_error l "Assignment expected a register or non-parameter non-letbound identifier to mutate"
         else
           (LEXP_aux(LEXP_vector(vec',e),(l,Base(([],item_t_act),tag,csi,efl,efr,nob))),
            item_t_act,reg_required && reg_still_required,
            env,tag,csi@cs'@cs_t,bounds,efl,efr)
       | Tuvar _ -> 
         typ_error l "Assignment expected a vector with a known order, try adding an annotation."
       | _ -> typ_error l ("Assignment expected vector, found assignment to type " ^ (t_to_string vec_t))) 
    | LEXP_vector_range(vec,e1,e2)-> 
      let (vec',vec_t,reg_required,env,tag,csi,bounds,efl,efr) = check_lexp envs imp_param ret_t false vec in
      let vec_t,cs = get_abbrev d_env vec_t in
      let vec_actual,writing_reg_bits = match vec_t.t with
        | Tapp("register",[TA_typ {t=Tabbrev(_,t)}]) | Tapp("register",[TA_typ t])
        | Tabbrev(_,{t=Tapp("register",[TA_typ t])}) -> t,true
        | Tabbrev(_,t) -> t,false | _ -> vec_t,false in
      let vec_actual,add_reg_write,reg_still_required,cs = 
        match vec_actual.t,is_top with
          | Tapp("register",[TA_typ t]),true ->
            (match get_abbrev d_env t with | {t=Tabbrev(_,t)},cs' | t,cs' -> t,true,false,cs@cs')
          | Tapp("register",[TA_typ t]),false -> vec_actual,false,false,cs
          | Tapp("reg",[TA_typ t]),_ ->
            (match get_abbrev d_env t with | {t=Tabbrev(_,t)},cs' | t,cs' -> t,false,false,cs@cs')
          | _ -> vec_actual,false,true,cs in
      (match vec_actual.t with
       | Tapp("vector",[TA_nexp base;TA_nexp rise;TA_ord ord;TA_typ t])
       | Tapp("register", [TA_typ {t= Tapp("vector",[TA_nexp base;TA_nexp rise;TA_ord ord;TA_typ t])}]) ->
          let size_e1,size_e2 = new_n(),new_n() in
          let e1_t = {t=Tapp("atom",[TA_nexp size_e1])} in
          let e2_t = {t=Tapp("atom",[TA_nexp size_e2])} in
          let (e1',e1_t',_,cs1,_,ef_e) = check_exp envs imp_param false false ret_t e1_t e1 in
          let (e2',e2_t',_,cs2,_,ef_e') = check_exp envs imp_param false false ret_t e2_t e2 in
          let len = new_n() in
          let needs_reg = match t.t with
            | Tapp("reg",_) -> false
            | Tapp("register",_) -> false
            | _ -> true in
          let cs_t,res_t = match ord.order with
            | Oinc ->  ([LtEq((Expr l),Require,base,size_e1);
                         LtEq((Expr l),Require,size_e1, size_e2);
                         LtEq((Expr l),Require,size_e2, rise);
                         Eq((Expr l),len, mk_add (mk_sub size_e2 size_e1) n_one)],
                        if is_top
                        then {t=Tapp("vector",[TA_nexp size_e1;TA_nexp len;TA_ord ord;TA_typ t])}
                        else vec_actual)
            | Odec -> ([GtEq((Expr l),Require,base,size_e1);
                        GtEq((Expr l),Require,size_e1,size_e2);
                        GtEq((Expr l),Require,size_e2,mk_sub base rise);                         
                        Eq((Expr l),len, mk_add (mk_sub size_e1 size_e2) n_one)],
                       if is_top
                       then {t=Tapp("vector",[TA_nexp size_e1;TA_nexp len;TA_ord ord; TA_typ t])}
                       else vec_actual)
            | _ -> typ_error l ("Assignment to a range of vector elements requires either inc or dec order")
          in
          let efl,tag =
            if add_reg_write || writing_reg_bits
            then (add_effect (BE_aux(BE_wreg,l)) efl,External None)
            else match tag with | External _ -> (efl,Emp_local) | _ ->  (efl,tag) in
          let cs = cs_t@cs@cs1@cs2 in
          let ef = union_effects efl (union_effects efr (union_effects ef_e ef_e')) in
          if is_top && reg_required && reg_still_required && needs_reg && not(writing_reg_bits)  
          then typ_error l "Assignment requires a register or a non-parameter, non-letbound local identifier"
          else (LEXP_aux(LEXP_vector_range(vec',e1',e2'),(l,Base(([],res_t),tag,cs,efl,ef,nob))),
                res_t,reg_required&&reg_still_required && needs_reg,env,tag,cs,bounds,efl,ef)
       | Tuvar _ ->
         typ_error l
           "Assignement to a range of items requires a vector with a known order, try adding an annotation."
        | _ -> typ_error l ("Assignment expected vector, found assignment to type " ^ (t_to_string vec_t))) 
    | LEXP_field(vec,id)-> 
      let (vec',item_t,reg_required,env,tag,csi,bounds,efl,efr) = check_lexp envs imp_param ret_t false vec in
      let vec_t = match vec' with
        | LEXP_aux(_,(l',Base((parms,t),_,_,_,_,_))) -> t
        | _ -> item_t in
      let fi = id_to_string id in
      (match vec_t.t with
        | Tid i | Tabbrev({t=Tid i},_) | Tabbrev({t=Tapp(i,_)},_) | Tapp(i,_)->
          (match lookup_record_typ i d_env.rec_env with
            | Some(((i,rec_kind,(Base((params,t),tag,cs,eft,_,bounds)),fields) as r)) ->
              let (ts,cs,eft,subst_env) = subst params false false t cs eft in
              (match lookup_field_type fi r with
                | None -> typ_error l ("Type " ^ i ^ " does not have a field " ^ fi)
                | Some t ->
                  let eft = if rec_kind = Register then add_effect (BE_aux(BE_wreg, l)) eft else eft in
                  let efr = union_effects eft efr in
                  let ft = typ_subst subst_env false t in
                  let (_,cs_sub') = type_consistent (Expr l) d_env Guarantee false ts vec_t in
                  (LEXP_aux(LEXP_field(vec',id),(l,(Base(([],ft),tag,csi@cs,eft,efr,nob)))),
                   ft,false,env,tag,csi@cs@cs_sub',bounds,eft,efr))
            | _ -> 
              typ_error l
                ("Expected a register or struct for this update, instead found an expression with type " ^ i))
        | _ -> typ_error l ("Expected a register binding here, found " ^ (t_to_string item_t)))

and check_lbind envs imp_param is_top_level opt_ret_t emp_tag (LB_aux(lbind,(l,annot)))
  : tannot letbind * tannot emap * nexp_range list * bounds_env * effect =
  let Env(d_env,t_env,b_env,tp_env) = envs in
  match lbind with
  | LB_val_explicit(typ,pat,e) -> 
    let tan = typschm_to_tannot envs false false typ emp_tag in
    (match tan with
    | Base((params,t),tag,cs,ef,_,b) ->
      let t,cs,ef,tp_env' = subst params false true t cs ef in
      let envs' = (Env(d_env,t_env,b_env,Envmap.union tp_env tp_env')) in
      let (pat',env,cs1,bounds,u) = check_pattern envs' emp_tag t pat in
      let ret_t = match opt_ret_t with Some t -> t | None -> t in
      let (e,t,_,cs2,_,ef2) = check_exp envs' imp_param true true ret_t t e in
      let (cs,map) = if is_top_level then resolve_constraints (cs@cs1@cs2) else (cs@cs1@cs2,None) in
      let ef = union_effects ef ef2 in
      (*let _ = Printf.eprintf "checking tannot in let1\n" in*)
      let tannot =
        if is_top_level 
        then check_tannot l (Base((params,t),tag,cs,ef,pure_e,
                                  match map with | None -> bounds | Some m -> add_map_to_bounds m bounds))
            None cs ef (*in top level, must be pure_e*) 
        else (Base ((params,t),tag,cs,pure_e,ef,bounds))
      in
      (*let _ = Printf.eprintf "done checking tannot in let1\n" in*)
      (LB_aux (LB_val_explicit(typ,pat',e),(l,tannot)),env,cs,merge_bounds b_env bounds,ef)
    | NoTyp | Overload _ -> raise (Reporting_basic.err_unreachable l "typschm_to_tannot failed to produce a Base"))
  | LB_val_implicit(pat,e) -> 
    let (pat',env,cs1,bounds,u) = check_pattern envs emp_tag (new_t ()) pat in
    let ret_t = match opt_ret_t with Some t -> t | None -> u in
    let (e,t',_,cs2,_,ef) = check_exp envs imp_param true true ret_t u e in
    let (cs,map) = if is_top_level then resolve_constraints (cs1@cs2) else (cs1@cs2),None in
    (*let _ = Printf.eprintf "checking tannot in let2\n" in*)
    let tannot = 
      if is_top_level
      then check_tannot l (Base(([],t'),emp_tag,cs,ef,pure_e,
                                match map with | None -> bounds | Some m -> add_map_to_bounds m bounds))
          None cs ef (* see above *)
      else (Base (([],t'),emp_tag,cs,pure_e,ef,merge_bounds bounds b_env))
    in
    (*let _ = Printf.eprintf "done checking tannot in let2\n" in*)
    (LB_aux (LB_val_implicit(pat',e),(l,tannot)), env,cs,merge_bounds bounds b_env,ef)

let check_record_typ envs (id: string) (typq : typquant) (fields : (Ast.typ * id) list)
  : (tannot * (string * typ) list) = 
  let (params,typarms,constraints) = typq_to_params envs typq in
  let ty = match typarms with | [] -> {t = Tid id} | parms -> {t = Tapp(id,parms)} in
  let tyannot = Base((params,ty),Emp_global,constraints,pure_e,pure_e,nob) in
  let fields' = List.map (fun (ty,i)->(id_to_string i),(typ_to_t envs false false ty)) fields in
  (tyannot, fields')

let check_variant_typ envs (id: string) typq arms = 
  let (Env(d_env,t_env,b_env,tp_env)) = envs in
  let (params,typarms,constraints) = typq_to_params envs typq in
  let num_arms = List.length arms in
  let ty = match params with
    | [] -> {t=Tid id} 
    | params -> {t = Tapp(id, typarms) }in
  let tyannot = Base((params,ty),Constructor num_arms,constraints,pure_e,pure_e,nob) in
  let arm_t input = Base((params,{t=Tfn(input,ty,IP_none,pure_e)}),Constructor num_arms,constraints,pure_e,pure_e,nob) in
  let arms' = List.map 
      (fun (Tu_aux(tu,l')) -> 
         match tu with 
         | Tu_id i -> ((id_to_string i),(arm_t unit_t))
         | Tu_ty_id(typ,i)-> ((id_to_string i),(arm_t (typ_to_t envs false false typ))))
      arms in
  let t_env = List.fold_right (fun (id,tann) t_env -> Envmap.insert t_env (id,tann)) arms' t_env in
  tyannot, t_env

let check_enum_type envs (id: string) ids =
  let (Env(d_env,t_env,b_env,tp_env)) = envs in
  let ids' = List.map id_to_string ids in
  let max = (List.length ids') -1 in
  let ty = Base (([],{t = Tid id }),Enum max,[],pure_e,pure_e,nob) in
  let t_env = List.fold_right (fun id t_env -> Envmap.insert t_env (id,ty)) ids' t_env in
  let enum_env = Envmap.insert d_env.enum_env (id,ids') in
  ty, t_env, enum_env

let check_register_type envs l (id: string) base top ranges =
  let (Env(d_env,t_env,b_env,tp_env)) = envs in
  let basei = normalize_nexp(anexp_to_nexp envs base) in
  let topi = normalize_nexp(anexp_to_nexp envs top) in
  match basei.nexp,topi.nexp with
  | Nconst b, Nconst t -> 
    if (le_big_int b t) then (
      let ty = {t = Tapp("vector",[TA_nexp basei; TA_nexp (mk_c(add_big_int (sub_big_int t b) (big_int_of_int 1))); 
                                   TA_ord({order = Oinc}); TA_typ({t = Tid "bit"});])} in
      let rec range_to_type_inc (BF_aux(idx,l)) = 
        (match idx with
         | BF_single i ->
           if (le_big_int b (big_int_of_int i)) && (le_big_int (big_int_of_int i) t)
           then {t = Tid "bit"}, i, 1
           else typ_error l 
               ("register type declaration " ^ id ^
                " contains a field specification outside of the declared register size")
         | BF_range(i1,i2) -> 
           if i1<i2 
           then 
             if (le_big_int b (big_int_of_int i1)) && (le_big_int (big_int_of_int i2) t) 
             then let size = i2 - i1 + 1 in
               ({t=Tapp("vector",[TA_nexp (mk_c_int i1); TA_nexp (mk_c_int size);
                                  TA_ord({order=Oinc}); TA_typ {t=Tid "bit"}])}, i1, size)
             else typ_error l ("register type declaration " ^ id 
                               ^ " contains a field specification outside of the declared register size")
           else typ_error l ("register type declaration " ^ id ^ " is not consistently increasing")
         | BF_concat(bf1, bf2) ->
           (match (range_to_type_inc bf1, range_to_type_inc bf2) with
            | ({t = Tid "bit"}, start, size1),({t= Tid "bit"}, start2, size2) 
            | (({t = Tid "bit"}, start, size1), ({t= Tapp("vector", _)}, start2, size2)) 
            | (({t=Tapp("vector", _)}, start, size1), ({t=Tid "bit"}, start2, size2))
            | (({t=Tapp("vector",_)}, start, size1), ({t=Tapp("vector",_)}, start2, size2)) ->
              if start < start2
              then let size = size1 + size2 in
                ({t=Tapp("vector", [TA_nexp (mk_c_int start); TA_nexp (mk_c_int size);
                                    TA_ord({order = Oinc}); TA_typ {t=Tid"bit"}])}, start, size)
              else typ_error l ("register type declaration " ^ id ^ " is not consistently increasing")
            | _ -> raise (Reporting_basic.err_unreachable l "range_to_type returned something odd")))
      in                
      let franges = 
        List.map 
          (fun (bf,id) ->
             let (bf_t, _, _) = range_to_type_inc bf in ((id_to_string id),bf_t))
          ranges 
      in
      let tannot = into_register d_env (Base(([],ty),External None,[],pure_e,pure_e,nob)) in
      tannot, franges)
    else (
      let ty = {t = Tapp("vector",[TA_nexp basei; TA_nexp (mk_c(add_big_int (sub_big_int b t) one)); 
                                   TA_ord({order = Odec}); TA_typ({t = Tid "bit"});])} in
      let rec range_to_type_dec (BF_aux(idx,l)) = 
        (match idx with
         | BF_single i ->
           if (ge_big_int b (big_int_of_int i)) && (ge_big_int (big_int_of_int i) t)
           then {t = Tid "bit"}, i, 1
           else typ_error l 
               ("register type declaration " ^ id ^
                " contains a field specification outside of the declared register size")
         | BF_range(i1,i2) -> 
           if i1>i2 
           then 
             if (ge_big_int b (big_int_of_int i1)) && (ge_big_int (big_int_of_int i2) t) 
             then let size = (i1 - i2) + 1 in
               ({t=Tapp("vector",[TA_nexp (mk_c_int i1); TA_nexp (mk_c_int size);
                                  TA_ord({order=Odec}); TA_typ {t=Tid "bit"}])}, i1, size)
             else typ_error l ("register type declaration " ^ id 
                               ^ " contains a field specification outside of the declared register size")
           else typ_error l ("register type declaration " ^ id ^ " is not consistently decreasing")
         | BF_concat(bf1, bf2) ->
           (match (range_to_type_dec bf1, range_to_type_dec bf2) with
            | ({t = Tid "bit"}, start, size1),({t= Tid "bit"}, start2, size2) 
            | (({t = Tid "bit"}, start, size1), ({t= Tapp("vector", _)}, start2, size2)) 
            | (({t=Tapp("vector", _)}, start, size1), ({t=Tid "bit"}, start2, size2))
            | (({t=Tapp("vector",_)}, start, size1), ({t=Tapp("vector",_)}, start2, size2)) ->
              if start > start2
              then let size = size1 + size2 in
                ({t=Tapp("vector", [TA_nexp (mk_c_int start); TA_nexp (mk_c_int size);
                                    TA_ord({order = Oinc}); TA_typ {t=Tid"bit"}])}, start, size)
              else typ_error l ("register type declaration " ^ id ^ " is not consistently decreasing")
            | _ -> raise (Reporting_basic.err_unreachable l "range_to_type has returned something odd")))
      in
      let franges = 
        List.map 
          (fun (bf,id) -> let (bf_t, _, _) = range_to_type_dec bf in (id_to_string id, bf_t))
          ranges 
      in
      let tannot = into_register d_env (Base(([],ty),External None,[],pure_e,pure_e,nob)) in
      tannot, franges)
  | _,_ -> raise (Reporting_basic.err_unreachable l "Nexps in register declaration do not evaluate to constants")

(*val check_type_def : envs -> (tannot type_def) -> (tannot type_def) envs_out*)
let check_type_def envs (TD_aux(td,(l,annot))) =
  let (Env(d_env,t_env,b_env,tp_env)) = envs in
  match td with
    | TD_abbrev(id,nmscm,typschm) -> 
      let tan = typschm_to_tannot envs false false typschm Emp_global in
      (TD_aux(td,(l,tan)),
       Env( { d_env with abbrevs = Envmap.insert d_env.abbrevs ((id_to_string id),tan)},t_env,b_env,tp_env))
    | TD_record(id,nmscm,typq,fields,_) -> 
      let id' = id_to_string id in
      let (tyannot, fields') = check_record_typ envs id' typq fields in
      (TD_aux(td,(l,tyannot)),
       Env({d_env with rec_env = (id',Record,tyannot,fields')::d_env.rec_env},t_env,b_env,tp_env))
    | TD_variant(id,nmscm,typq,arms,_) ->
      let id' = id_to_string id in
      let tyannot, t_env = check_variant_typ envs id' typq arms in
      (TD_aux(td,(l,tyannot)),(Env (d_env,t_env,b_env,tp_env)))
    | TD_enum(id,nmscm,ids,_) -> 
      let id' = id_to_string id in
      let ty,t_env,enum_env = check_enum_type envs id' ids in
      (TD_aux(td,(l,ty)),Env({d_env with enum_env = enum_env;},t_env,b_env,tp_env))
    | TD_register(id,base,top,ranges) -> 
      let id' = id_to_string id in
      let (tannot, franges) = check_register_type envs l id' base top ranges in
      (TD_aux(td,(l,tannot)),
       Env({d_env with rec_env = ((id',Register,tannot,franges)::d_env.rec_env);
                       abbrevs = Envmap.insert d_env.abbrevs (id',tannot)},t_env,b_env,tp_env))

(*val check_kind_def : envs -> (tannot kind_def) -> (tannot kind_def) envs_out*)
let check_kind_def envs (KD_aux(kd,(l,annot))) =
  let (Env(d_env,t_env,b_env,tp_env)) = envs in
  match kd with
  | KD_nabbrev(kind,id,nmscm,n) ->
    let id' = id_to_string id in
    let n = normalize_nexp (anexp_to_nexp envs n) in
    (KD_aux(kd,(l,annot)),
     Env( { d_env with nabbrevs = Envmap.insert d_env.nabbrevs (id', (mk_nid id' n))},t_env,b_env,tp_env))
  | KD_abbrev(kind,id,nmscm,typschm) -> 
    let tan = typschm_to_tannot envs false false typschm Emp_global in
    (KD_aux(kd,(l,tan)),
     Env( { d_env with abbrevs = Envmap.insert d_env.abbrevs ((id_to_string id),tan)},t_env,b_env,tp_env))
  | KD_record(kind,id,nmscm,typq,fields,_) -> 
    let id' = id_to_string id in
    let (tyannot, fields') = check_record_typ envs id' typq fields in
    (KD_aux(kd,(l,tyannot)),Env({d_env with rec_env = (id',Record,tyannot,fields')::d_env.rec_env},t_env,b_env,tp_env))
  | KD_variant(kind,id,nmscm,typq,arms,_) ->
    let id' = id_to_string id in
    let tyannot, t_env = check_variant_typ envs id' typq arms in
    (KD_aux(kd,(l,tyannot)),(Env (d_env,t_env,b_env,tp_env)))
  | KD_enum(kind,id,nmscm,ids,_) -> 
    let id' = id_to_string id in
    let ty,t_env,enum_env = check_enum_type envs id' ids in
    (KD_aux(kd,(l,ty)),Env({d_env with enum_env = enum_env;},t_env,b_env,tp_env))
  | KD_register(kind,id,base,top,ranges) -> 
    let id' = id_to_string id in
    let (tannot, franges) = check_register_type envs l id' base top ranges in
    (KD_aux(kd,(l,tannot)),
     Env({d_env with rec_env = ((id',Register,tannot,franges)::d_env.rec_env);
                     abbrevs = Envmap.insert d_env.abbrevs (id',tannot)},t_env,b_env,tp_env))

let check_val_spec envs (VS_aux(vs,(l,annot))) = 
  let (Env(d_env,t_env,b_env,tp_env)) = envs in
  match vs with
    | VS_val_spec(typs,id) -> 
      let tannot = typschm_to_tannot envs true true typs Spec in
      (VS_aux(vs,(l,tannot)),
       (*Should maybe add to bounds here*)
       Env(d_env,(Envmap.insert t_env (id_to_string id,tannot)),b_env,tp_env))
    | VS_extern_no_rename(typs,id) ->
      let tannot = typschm_to_tannot envs true true typs (External None) in
      (VS_aux(vs,(l,tannot)),
       Env(d_env,(Envmap.insert t_env (id_to_string id,tannot)),b_env,tp_env))
    | VS_extern_spec(typs,id,s) ->
      let tannot = typschm_to_tannot envs true true typs (External (Some s)) in
      (VS_aux(vs,(l,tannot)),
       Env(d_env,(Envmap.insert t_env (id_to_string id,tannot)), b_env,tp_env))

let check_default envs (DT_aux(ds,l)) =
  let (Env(d_env,t_env,b_env,tp_env)) = envs in
  match ds with
    | DT_kind _ -> ((DT_aux(ds,l)),envs)
    | DT_order ord -> (DT_aux(ds,l), Env({d_env with default_o = (aorder_to_ord ord)},t_env,b_env,tp_env))
    | DT_typ(typs,id) ->
      let tannot = typschm_to_tannot envs false false typs Default in
      (DT_aux(ds,l),
       Env(d_env,(Envmap.insert t_env (id_to_string id,tannot)),b_env,tp_env))

let check_fundef envs (FD_aux(FD_function(recopt,tannotopt,effectopt,funcls),(l,annot))) =
  (*let _ = Printf.eprintf "checking fundef\n" in*)
  let Env(d_env,t_env,b_env,tp_env) = envs in
  let _ = reset_fresh () in
  let is_rec = match recopt with
              | Rec_aux(Rec_nonrec,_) -> false
              | Rec_aux(Rec_rec,_) -> true in
  let id = match (List.fold_right 
                    (fun (FCL_aux((FCL_Funcl(id,pat,exp)),(l,annot))) id' ->
                      match id' with
                        | Some(id') -> if id' = id_to_string id then Some(id') 
                          else typ_error l ("Function declaration expects all definitions to have the same name, " 
                                            ^ id_to_string id ^ " differs from other definitions of " ^ id')
                        | None -> Some(id_to_string id)) funcls None) with
    | Some id -> id 
    | None -> raise (Reporting_basic.err_unreachable l "funcl list might be empty") in
  let in_env = Envmap.apply t_env id in 
  let (typ_params,has_spec) = match in_env with
    | Some(Base( (params,u),Spec,constraints,eft,_,_)) -> params,true
    | _ -> [],false in
  let ret_t,param_t,tannot,t_param_env = match tannotopt with
    | Typ_annot_opt_aux(Typ_annot_opt_some(typq,typ),l') ->
      let (ids,_,constraints) = typq_to_params envs typq in
      let t = typ_to_t envs false false typ in
      (*TODO add check that ids == typ_params when has_spec*)
      let t,constraints,_,t_param_env =
        subst (if has_spec then typ_params else ids) true true t constraints pure_e in
      let p_t = new_t () in
      let ef = new_e () in
      t,p_t,Base((ids,{t=Tfn(p_t,t,IP_none,ef)}),Emp_global,constraints,ef,pure_e,nob),t_param_env in
  let cond_kind = if (List.length funcls) = 1 then Solo else Switch in
  let check t_env tp_env imp_param =
    List.split
      (List.map (fun (FCL_aux((FCL_Funcl(id,pat,exp)),(l,_))) ->
        (*let _ = Printf.eprintf "checking function %s : %s -> %s\n" 
          (id_to_string id) (t_to_string param_t) (t_to_string ret_t) in*)
        let (pat',t_env',cs_p,b_env',t') = check_pattern (Env(d_env,t_env,b_env,tp_env)) Emp_local param_t pat in
        let _, _ = type_consistent (Patt l) d_env Require false param_t t' in
        let exp',_,_,cs_e,_,ef = 
          check_exp (Env(d_env,Envmap.union_merge (tannot_merge (Expr l) d_env true) t_env t_env', 
                         merge_bounds b_env b_env',tp_env)) imp_param true true ret_t ret_t exp in
        (*let _ = Printf.eprintf "checked function %s : %s -> %s\n" 
          (id_to_string id) (t_to_string param_t) (t_to_string ret_t) in
          let _ = Printf.eprintf "constraints were pattern: %s\n expression: %s\n" 
          (constraints_to_string cs_p) (constraints_to_string cs_e) in*)
        let cs = CondCons(Fun l,cond_kind,None,cs_p,cs_e) in
        (FCL_aux((FCL_Funcl(id,pat',exp')),(l,(Base(([],ret_t),Emp_global,[cs],ef,pure_e,nob)))),(cs,ef))) funcls) in
  let check_pattern_after_constraints (FCL_aux ((FCL_Funcl (_, pat, _)), _)) =
    check_pattern_after_constraint_res (Env(d_env,t_env,b_env,tp_env)) false param_t pat in
  let update_pattern var (FCL_aux ((FCL_Funcl(id,(P_aux(pat,t)),exp)),annot)) =
    let pat' = match pat with
      | P_lit (L_aux (L_unit,l')) -> P_aux(P_id (Id_aux (Id var, l')), t)
      | P_tup pats -> P_aux(P_tup ((P_aux (P_id (Id_aux (Id var, l)), t))::pats), t)
      | _ ->  P_aux(P_tup [(P_aux (P_id (Id_aux (Id var,l)), t));(P_aux(pat,t))], t)
    in (FCL_aux ((FCL_Funcl(id,pat',exp)),annot))
  in
  match (in_env,tannot) with
    | Some(Base( (params,u),Spec,constraints,eft,_,_)), Base( (p',t),_,c',eft',_,_) ->
      (*let _ = Printf.eprintf "Function %s is in env\n" id in*)
      let u,constraints,eft,t_param_env = subst_with_env t_param_env true u constraints eft in
      let _,cs_decs = type_consistent (Specc l) d_env Require false t u in
      (*let _ = Printf.eprintf "valspec consistent with type for %s, %s ~< %s with %s deriveds and %s stated\n" 
        id (t_to_string t) (t_to_string u) (constraints_to_string cs_decs) 
        (constraints_to_string (constraints@c')) in*)
      let imp_param = match u.t with 
        | Tfn(_,_,IP_user n,_) -> Some n
        | _ -> None in
      let (t_env,orig_env) = if is_rec then (t_env,t_env) else (Envmap.remove t_env id,t_env) in
      let funcls,cs_ef = check t_env t_param_env imp_param in
      let cses,ef = ((fun (cses,efses) -> 
        cses,(List.fold_right union_effects efses pure_e)) (List.split cs_ef)) in
      let cs = if List.length funcls = 1 then cses else [BranchCons(Fun l,None, cses)] in
      let cs',map = resolve_constraints (cs@cs_decs@constraints@c') in
      let tannot =
        check_tannot l (match map with | None -> tannot | Some m -> add_map_tannot m tannot) imp_param cs' ef in
      (*let _ = Printf.eprintf "remaining constraints are: %s\n" (constraints_to_string cs') in
        let _ = Printf.eprintf "check_tannot ok for %s val type %s derived type %s \n" 
        id (t_to_string u) (t_to_string t) in*)
      let _ = List.map check_pattern_after_constraints funcls in
      let funcls = match imp_param with
        | Some {nexp = Nvar i} -> List.map (update_pattern i) funcls
        | _ -> funcls
      in
      (*let _ = Printf.eprintf "done funcheck case 1 of %s\n%!" id in*)
      (FD_aux(FD_function(recopt,tannotopt,effectopt,funcls),(l,tannot))),
      Env(d_env,orig_env (*Envmap.insert t_env (id,tannot)*),b_env,tp_env)
    | _ , _->
      (*let _ = Printf.eprintf "checking %s, not in env\n%!" id in
      let t_env = if is_rec then Envmap.insert t_env (id,tannot) else t_env in*)
      let funcls,cs_ef = check t_env t_param_env None in
      let cses,ef =
        ((fun (cses,efses) -> (cses,(List.fold_right union_effects efses pure_e))) (List.split cs_ef)) in
      let cs = if List.length funcls = 1 then cses else [BranchCons(Fun l, None, cses)] in
      (*let _ = Printf.eprintf "unresolved constraints are %s\n%!" (constraints_to_string cs) in*)
      let (cs',map) = resolve_constraints cs in
      (*let _ = Printf.eprintf "checking tannot for %s 2  remaining constraints are %s\n" 
          id (constraints_to_string cs') in*)
      let tannot = check_tannot l
                                (match map with | None -> tannot | Some m -> add_map_tannot m tannot)
                                None cs' ef in
      let _ = List.map check_pattern_after_constraints funcls in
      (*let _ = Printf.eprintf "done funcheck case2\n" in*)
      (FD_aux(FD_function(recopt,tannotopt,effectopt,funcls),(l,tannot))),
      Env(d_env,(if is_rec then t_env else Envmap.insert t_env (id,tannot)),b_env,tp_env)

(*TODO Only works for inc vectors, need to add support for dec*)
let check_alias_spec envs alias (AL_aux(al,(l,annot))) e_typ =
  let (Env(d_env,t_env,b_env,tp_env)) = envs in
  let check_reg (RI_aux ((RI_id (Id_aux(_,l) as id)), _)) : (string * tannot reg_id * typ * typ) =
    let i = id_to_string id in
    (match Envmap.apply t_env i with
      | Some(Base(([],t), External (Some j), [], _,_,_)) ->
        let t,_ = get_abbrev d_env t in
        let t_actual,t_id = match t.t with 
          | Tabbrev(i,t) -> t,i
          | _ -> t,t in
        (match t_actual.t with 
          | Tapp("register",[TA_typ t']) -> 
            if i = j then (i,(RI_aux (RI_id id, (l,Base(([],t),External (Some j), [], pure_e,pure_e,nob)))),t_id,t')
            else assert false
          | _ -> typ_error l 
            ("register alias " ^ alias ^ " to " ^ i ^ " expected a register, found " ^ (t_to_string t)))
      | _ -> typ_error l ("register alias " ^ alias ^ " to " ^ i ^ " exepcted a register.")) in
  match al with
    | AL_subreg(reg_a,subreg) -> 
      let (reg,reg_a,reg_t,t) = check_reg reg_a in 
      (match reg_t.t with
        | Tid i ->
          (match lookup_record_typ i d_env.rec_env with
            | None -> typ_error l ("Expected a register with bit fields, given " ^ i)
            | Some(((i,rec_kind,tannot,fields) as r)) ->
              let fi = id_to_string subreg in
              (match lookup_field_type fi r with
                | None -> typ_error l ("Type " ^ i ^ " does not have a field " ^ fi)
                | Some et ->
                  let tannot = Base(([],et),Alias (Alias_field(reg,fi)),[],pure_e,pure_e,nob) in
                  let d_env = {d_env with alias_env = Envmap.insert (d_env.alias_env) (alias, (OneReg(reg,tannot)))} in
                  (AL_aux(AL_subreg(reg_a,subreg),(l,tannot)),tannot,d_env)))
        | _ -> typ_error l ("Expected a register with fields, given " ^ (t_to_string reg_t)))
    | AL_bit(reg_a,bit) -> 
      let (reg,reg_a,reg_t,t) = check_reg reg_a in
      let (E_aux(bit,(le,eannot)),_,_,_,_,_) = check_exp envs None true true (new_t ()) (new_t ()) bit in
      (match t.t with
        | Tapp("vector",[TA_nexp base;TA_nexp len;TA_ord order;TA_typ item_t]) ->
          (match (base.nexp,len.nexp,order.order, bit) with
            | (Nconst i,Nconst j,Oinc, E_lit (L_aux((L_num k), ll))) ->
              if (int_of_big_int i) <= k && ((int_of_big_int i) + (int_of_big_int j)) >= k 
              then let tannot = Base(([],item_t),Alias (Alias_extract(reg, k,k)),[],pure_e,pure_e,nob) in
                   let d_env = 
                     {d_env with alias_env = Envmap.insert (d_env.alias_env) (alias, (OneReg(reg,tannot)))} in
                   (AL_aux(AL_bit(reg_a,(E_aux(bit,(le,eannot)))), (l,tannot)), tannot,d_env)
              else typ_error ll ("Alias bit lookup must be in the range of the vector in the register")
            | _ -> typ_error l ("Alias bit lookup must have a constant index"))
        | _ -> typ_error l ("Alias bit lookup must refer to a register with type vector, found " ^ (t_to_string t)))
    | AL_slice(reg_a,sl1,sl2) -> 
      let (reg,reg_a,reg_t,t) = check_reg reg_a in 
      let (E_aux(sl1,(le1,eannot1)),_,_,_,_,_) = check_exp envs None true true (new_t ()) (new_t ()) sl1 in
      let (E_aux(sl2,(le2,eannot2)),_,_,_,_,_) = check_exp envs None true true (new_t ()) (new_t ()) sl2 in
      (match t.t with
        | Tapp("vector",[TA_nexp base;TA_nexp len;TA_ord order;TA_typ item_t]) ->
          (match (base.nexp,len.nexp,order.order, sl1,sl2) with
            | (Nconst i,Nconst j,Oinc, E_lit (L_aux((L_num k), ll)),E_lit (L_aux((L_num k2), ll2))) ->
              if (int_of_big_int i) <= k && ((int_of_big_int i) + (int_of_big_int j)) >= k2 && k < k2 
              then let t = {t = Tapp("vector",[TA_nexp (int_to_nexp k);TA_nexp (int_to_nexp ((k2-k) +1));
                                              TA_ord order; TA_typ item_t])} in 
                   let tannot = Base(([],t),Alias (Alias_extract(reg, k, k2)),[],pure_e,pure_e,nob) in
                   let d_env = 
                     {d_env with alias_env = Envmap.insert (d_env.alias_env) (alias, (OneReg(reg,tannot)))} in
                   (AL_aux(AL_slice(reg_a,(E_aux(sl1,(le1,eannot1))),(E_aux(sl2,(le2,eannot2)))),
                           (l,tannot)), tannot,d_env)
              else typ_error ll ("Alias slices must be in the range of the vector in the register")
            | _ -> typ_error l ("Alias slices must have constant slices"))
        | _ -> typ_error l ("Alias slices must point to a register with a vector type: found " ^ (t_to_string t)))
    | AL_concat(reg1_a,reg2_a) -> 
      let (reg1,reg1_a,reg_t,t1) = check_reg reg1_a in
      let (reg2,reg2_a,reg_t,t2) = check_reg reg2_a in
      (match (t1.t,t2.t) with
        | (Tapp("vector",[TA_nexp b1;TA_nexp r; TA_ord {order = Oinc}; TA_typ item_t]),
           Tapp("vector",[TA_nexp _ ;TA_nexp r2; TA_ord {order = Oinc}; TA_typ item_t2])) ->
          let _ = type_consistent (Specc l) d_env Guarantee false item_t item_t2 in
          let t = {t= Tapp("register",
                           [TA_typ {t= Tapp("vector",[TA_nexp b1; TA_nexp (mk_add r r2);
                                                      TA_ord {order = Oinc}; TA_typ item_t])}])} in
          let tannot = Base(([],t),Alias (Alias_pair(reg1,reg2)),[],pure_e,pure_e,nob) in
          let d_env = {d_env with alias_env = Envmap.insert (d_env.alias_env) (alias, TwoReg(reg1,reg2,tannot))} in
          (AL_aux (AL_concat(reg1_a,reg2_a), (l,tannot)), tannot, d_env)
        | _ -> typ_error l 
          ("Alias concatentaion must connect two registers with vector type, found " ^ t_to_string t1 ^ " and " ^ t_to_string t2))

(*val check_def : envs -> tannot def -> (tannot def) envs_out*)
let check_def envs def = 
  let (Env(d_env,t_env,b_env,tp_env)) = envs in
  match def with
  | DEF_kind kdef ->
    (*let _ = Printf.eprintf "checking kind def\n" in*)
    let kd,envs = check_kind_def envs kdef in
    (*let _ = Printf.eprintf "checked kind def\n" in*)
    (DEF_kind kd,envs)
  | DEF_type tdef ->
    (*let _ = Printf.eprintf "checking type def\n" in*)
    let td,envs = check_type_def envs tdef in
    (*let _ = Printf.eprintf "checked type def\n" in*)
    (DEF_type td,envs)
  | DEF_fundef fdef -> 
    (*let _ = Printf.eprintf "checking fun def\n" in*)
    let fd,envs = check_fundef envs fdef in
    (*let _ = Printf.eprintf "checked fun def\n" in*)
    (DEF_fundef fd,envs)
  | DEF_val letdef -> 
    (*let _ = Printf.eprintf "checking letdef\n" in*)
    let (letbind,t_env_let,_,b_env_let,eft) = check_lbind envs None true None Emp_global letdef in
    (*let _ = Printf.eprintf "checked letdef\n" in*)
    (DEF_val letbind,Env(d_env,Envmap.union t_env t_env_let, merge_bounds b_env b_env_let, tp_env))
  | DEF_spec spec -> 
    (*let _ = Printf.eprintf "checking spec\n" in*)
    let vs,envs = check_val_spec envs spec in
    (*let _ = Printf.eprintf "checked spec\n" in*)
    (DEF_spec vs, envs)
  | DEF_default default -> let ds,envs = check_default envs default in
                           (DEF_default ds,envs)
  | DEF_reg_dec(DEC_aux(DEC_reg(typ,id), (l,annot))) -> 
    (*let _ = Printf.eprintf "checking reg dec\n" in *)
    let t = (typ_to_t envs false false typ) in
    let i = id_to_string id in
    let tannot = into_register d_env (Base(([],t),External (Some i),[],pure_e,pure_e,nob)) in
   (* let _ = Printf.eprintf "done checking reg dec\n" in*)
    (DEF_reg_dec(DEC_aux(DEC_reg(typ,id),(l,tannot))),(Env(d_env,Envmap.insert t_env (i,tannot),b_env, tp_env)))
  | DEF_reg_dec(DEC_aux(DEC_alias(id,aspec), (l,annot))) -> 
    (*let _ = Printf.eprintf "checking reg dec b\n" in*)
    let i = id_to_string id in
    let (aspec,tannot,d_env) = check_alias_spec envs i aspec None in
    (*let _ = Printf.eprintf "done checking reg dec b\n" in *)
    (DEF_reg_dec(DEC_aux(DEC_alias(id,aspec),(l,tannot))),(Env(d_env, Envmap.insert t_env (i,tannot),b_env,tp_env)))
  | DEF_reg_dec(DEC_aux(DEC_typ_alias(typ,id,aspec),(l,tannot))) ->
    (*let _ = Printf.eprintf "checking reg dec c\n" in*)
    let i = id_to_string id in
    let t = typ_to_t envs false false typ in
    let (aspec,tannot,d_env) = check_alias_spec envs i aspec (Some t) in
    (*let _ = Printf.eprintf "done checking reg dec c\n" in*)
    (DEF_reg_dec(DEC_aux(DEC_typ_alias(typ,id,aspec),(l,tannot))),(Env(d_env,Envmap.insert t_env (i,tannot),b_env,tp_env)))
  | DEF_scattered _ -> raise (Reporting_basic.err_unreachable Parse_ast.Unknown "Scattered given to type checker")
  | _ -> def,envs (*Else a comment, so skip but keep*)


(*val check : envs ->  tannot defs -> tannot defs*)
let rec check envs (Defs defs) = 
 match defs with
   | [] -> (Defs []),envs
   | def::defs -> let (def, envs) = check_def envs def in
                  let (Defs defs, envs) = check envs (Defs defs) in
                  (Defs (def::defs)), envs
