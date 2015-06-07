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
  | Base((_,t),_,_,_,_) -> t
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
    | (id,Register,fmaps)::rec_env -> fields_to_rec fields rec_env
    | (id,Record,fmaps)::rec_env ->
      if (List.length fields) = (List.length fmaps) then
	match field_equivs fields fmaps with
	  | Some(ftyps) -> Some(id,ftyps)
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

let rec typ_to_t imp_ok fun_ok (Typ_aux(typ,l)) =
  let trans t = typ_to_t false false t in 
  match typ with
    | Typ_id i -> {t = Tid (id_to_string i)}
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
		  {t = Tfn (trans new_ty1, trans ty2, IP_user (anexp_to_nexp ne), aeffect_to_effect e)}
		| _ -> typ_error l "Declaring an implicit parameter requires a Nat specification")
	    | None -> typ_error l "A function type with an implicit parameter must declare the implicit first")
	  else typ_error l "This function has one (or more) implicit parameter(s) not permitted here"
	else {t = Tfn (trans ty1,trans ty2,IP_none,aeffect_to_effect e)}
      else typ_error l "Function types are only permitted at the top level."
    | Typ_tup(tys) -> {t = Ttup (List.map trans tys) }
    | Typ_app(i,args) -> {t = Tapp (id_to_string i,List.map typ_arg_to_targ args) }
    | Typ_wild -> new_t ()
and typ_arg_to_targ (Typ_arg_aux(ta,l)) = 
  match ta with
    | Typ_arg_nexp n -> TA_nexp (anexp_to_nexp n)
    | Typ_arg_typ t -> TA_typ (typ_to_t false false t)
    | Typ_arg_order o -> TA_ord (aorder_to_ord o)
    | Typ_arg_effect e -> TA_eft (aeffect_to_effect e)
and anexp_to_nexp ((Nexp_aux(n,l)) : Ast.nexp) : nexp =
  match n with
    | Nexp_var (Kid_aux((Var i),l')) -> {nexp = Nvar i}
    | Nexp_constant i -> {nexp=Nconst (big_int_of_int i)}
    | Nexp_times(n1,n2) -> {nexp=Nmult(anexp_to_nexp n1,anexp_to_nexp n2)}
    | Nexp_sum(n1,n2) -> {nexp=Nadd(anexp_to_nexp n1,anexp_to_nexp n2)}
    | Nexp_minus(n1,n2) -> {nexp=Nsub(anexp_to_nexp n1,anexp_to_nexp n2)}
    | Nexp_exp n -> {nexp=N2n(anexp_to_nexp n,None)}
    | Nexp_neg n -> {nexp=Nneg(anexp_to_nexp n)}
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
                    | K_Nat  -> TA_nexp { nexp = Nvar i}                      
                    | K_Ord  -> TA_ord { order = Ovar i}
                    | K_Efct -> TA_eft { effect = Evar i} in
                  ((i,k)::ids,targ::typarms,cs)
		| None -> raise (Reporting_basic.err_unreachable l'' "Unkinded id without default after initial check"))
	    | KOpt_kind(kind,Kid_aux((Var i),l'')) -> 
              let k = kind_to_k kind in
              let targ = match k.k with
                | K_Typ  -> TA_typ {t = Tvar i}
                | K_Nat  -> TA_nexp { nexp = Nvar i}                      
                | K_Ord  -> TA_ord { order = Ovar i}
                | K_Efct -> TA_eft { effect = Evar i} in
              ((i,k)::ids,targ::typarms,cs))
	| QI_const(NC_aux(nconst,l')) -> 
	  (*TODO: somehow the requirement vs best guarantee needs to be derived from user or context*)
	  (match nconst with
	    | NC_fixed(n1,n2) -> (ids,typarms,Eq(Specc l',anexp_to_nexp n1,anexp_to_nexp n2)::cs)
	    | NC_bounded_ge(n1,n2) -> (ids,typarms,GtEq(Specc l',Guarantee,anexp_to_nexp n1,anexp_to_nexp n2)::cs)
	    | NC_bounded_le(n1,n2) -> (ids,typarms,LtEq(Specc l',Guarantee,anexp_to_nexp n1,anexp_to_nexp n2)::cs)
	    | NC_nat_set_bounded(Kid_aux((Var i),l''), bounds) -> (ids,typarms,In(Specc l',i,bounds)::cs)))

let typq_to_params envs (TypQ_aux(tq,l)) =
  match tq with
    | TypQ_tq(qis) -> quants_to_consts envs qis
    | TypQ_no_forall -> [],[],[]

let typschm_to_tannot envs imp_parm_ok fun_ok ((TypSchm_aux(typschm,l)):typschm) (tag : tag) : tannot = 
  match typschm with
    | TypSchm_ts(tq,typ) -> 
      let t = typ_to_t imp_parm_ok fun_ok typ in
      let (ids,_,constraints) = typq_to_params envs tq in
      Base((ids,t),tag,constraints,pure_e,nob)

let into_register d_env (t : tannot) : tannot =
  match t with
    | Base((ids,ty),tag,constraints,eft,bindings) -> 
      let ty',_ =  get_abbrev d_env ty in
      (match ty'.t with 
	| Tapp("register",_)-> t
        | Tabbrev(ti,{t=Tapp("register",_)}) -> Base((ids,ty'),tag,constraints,eft,bindings)
	| _ -> Base((ids, {t= Tapp("register",[TA_typ ty'])}),tag,constraints,eft,bindings))
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
			       [TA_nexp{nexp = Nconst (big_int_of_int i)}])},lit
	      | _ -> {t = Tapp("atom",
			       [TA_nexp{nexp = Nconst (big_int_of_int i)}])},lit)
	  | L_hex s -> 
	    let size = big_int_of_int ((String.length s) * 4) in
	    let is_inc = match d_env.default_o.order with | Oinc -> true | _ -> false in
	    {t = Tapp("vector",
		      [TA_nexp (if is_inc then {nexp = Nconst zero} else {nexp = Nconst (sub_big_int size one)});
		       TA_nexp {nexp = Nconst size};
		       TA_ord d_env.default_o; TA_typ{t=Tid "bit"}])},lit
	  | L_bin s -> 
	    let size = big_int_of_int (String.length s) in
	    let is_inc = match d_env.default_o.order with | Oinc -> true | _ -> false in
	    {t = Tapp("vector",
		      [TA_nexp(if is_inc then {nexp = Nconst zero} else {nexp = Nconst (sub_big_int size one)});
		       TA_nexp{nexp = Nconst size};
		       TA_ord d_env.default_o;TA_typ{t = Tid"bit"}])},lit
	  | L_string s -> {t = Tid "string"},lit
	  | L_undef -> typ_error l' "Cannot pattern match on undefined") in
(*      let _ = Printf.printf "checking pattern literal. expected type is %s. t is %s\n" (t_to_string expect_t) (t_to_string t) in*)
      let t',cs' = type_consistent (Patt l) d_env Require true t expect_t in
      let cs_l = cs@cs' in
      (P_aux(P_lit(L_aux(lit,l')),(l,cons_tag_annot t emp_tag cs_l)),Envmap.empty,cs_l,nob,t)
    | P_wild -> 
      (P_aux(p,(l,cons_tag_annot expect_t emp_tag cs)),Envmap.empty,cs,nob,expect_t)
    | P_as(pat,id) ->
      let v = id_to_string id in
      let (pat',env,constraints,bounds,t) = check_pattern envs emp_tag expect_t pat in
      let bounds = extract_bounds d_env v t in
      let tannot = Base(([],t),emp_tag,cs,pure_e,bounds) in
      (P_aux(P_as(pat',id),(l,tannot)),Envmap.insert env (v,tannot),cs@constraints,bounds,t)
    | P_typ(typ,pat) -> 
      let t = typ_to_t false false typ in
      let t = typ_subst tp_env false t in
      let (pat',env,constraints,bounds,u) = check_pattern envs emp_tag t pat in
      let t,cs_consistent = type_consistent (Patt l) d_env Guarantee false t expect_t in
      (P_aux(P_typ(typ,pat'),(l,tag_annot t emp_tag)),env,cs@constraints@cs_consistent,bounds,t)
    | P_id id -> 
      let i = id_to_string id in
      let default_bounds = extract_bounds d_env i expect_t in
      let default = let id_annot = Base(([],expect_t),emp_tag,cs,pure_e,default_bounds) in
		    let pat_annot = match is_enum_typ d_env expect_t with
		      | None -> id_annot
		      | Some n -> Base(([],expect_t), Enum n, cs,pure_e,default_bounds) in
		    (P_aux(p,(l,pat_annot)),Envmap.from_list [(i,id_annot)],cs,default_bounds,expect_t) in
      (match Envmap.apply t_env i with
	| Some(Base((params,t),Constructor,cs,ef,bounds)) ->
	  let t,cs,ef,_ = subst params false t cs ef in
          (match t.t with
            | Tfn({t = Tid "unit"},t',IP_none,ef) -> 
	      if conforms_to_t d_env false false t' expect_t 
	      then
		let tp,cp = type_consistent (Expr l) d_env Guarantee false t' expect_t in
		(P_aux(P_app(id,[]),(l,tag_annot t Constructor)),Envmap.empty,cs@cp,bounds,tp)
	      else default
            | Tfn(t1,t',IP_none,e) -> 
	      if conforms_to_t d_env false false t' expect_t
	      then typ_error l ("Constructor " ^ i ^ " expects arguments of type " ^ (t_to_string t) ^ ", found none")
	      else default
            | _ -> raise (Reporting_basic.err_unreachable l "Constructor tannot does not have function type"))
	| Some(Base((params,t),Enum max,cs,ef,bounds)) ->
	  let t,cs,ef,_ = subst params false t cs ef in
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
	| Some(Base((params,t),Constructor,constraints,eft,bounds)) -> 
          let t,dec_cs,_,_ = subst params false t constraints eft in
	  (match t.t with
	    | Tid id -> if pats = [] 
	      then let t',ret_cs = type_consistent (Patt l) d_env Guarantee false t expect_t in
		   (P_aux(p,(l,cons_tag_annot t' Constructor dec_cs)), Envmap.empty,dec_cs@ret_cs,nob,t')
	      else typ_error l ("Constructor " ^ i ^ " does not expect arguments")
	    | Tfn(t1,t2,IP_none,ef) ->
	      let t',ret_cs = type_consistent (Patt l) d_env Guarantee false t2 expect_t in
              (match pats with
              | [] -> let _ = type_consistent (Patt l) d_env Guarantee false unit_t t1 in
                      (P_aux(P_app(id,[]),(l,cons_tag_annot t' Constructor dec_cs)),
		       Envmap.empty,dec_cs@ret_cs,nob,t')
              | [p] -> let (p',env,p_cs,bounds,u) = check_pattern envs emp_tag t1 p in
                       (P_aux(P_app(id,[p']),
			      (l,cons_tag_annot t' Constructor dec_cs)),env,dec_cs@p_cs@ret_cs,bounds,t')
              | pats -> let (pats',env,p_cs,bounds,u) = 
                          match check_pattern envs emp_tag t1 (P_aux(P_tup(pats),(l,annot))) with
                          | ((P_aux(P_tup(pats'),_)),env,constraints,bounds,u) -> (pats',env,constraints,bounds,u)
                          | _ -> assert false in
	                (P_aux(P_app(id,pats'),
			       (l,cons_tag_annot t' Constructor dec_cs)),env,dec_cs@p_cs@ret_cs,bounds,t'))
	    | _ -> typ_error l ("Identifier " ^ i ^ " must be a union constructor"))
	| Some(Base((params,t),tag,constraints,eft,bounds)) -> 
	  typ_error l ("Identifier " ^ i ^ " used in pattern is not a union constructor"))
    | P_record(fpats,_) -> 
      (match (fields_to_rec fpats d_env.rec_env) with
	| None -> typ_error l ("No struct exists with the listed fields")
	| Some(id,typ_pats) ->
	  let pat_checks = 
	    List.map (fun (tan,id,l,pat) -> 
	      let (Base((vs,t),tag,cs,eft,bounds)) = tan in
	      let t,cs,_,_ = subst vs false t cs eft in
	      let (pat,env,constraints,new_bounds,u) = check_pattern envs emp_tag t pat in
	      let pat = FP_aux(FP_Fpat(id,pat),(l,Base(([],t),tag,cs,pure_e,bounds))) in
	      (pat,env,cs@constraints,merge_bounds bounds new_bounds)) typ_pats in
	  let pats' = List.map (fun (a,_,_,_) -> a) pat_checks in
	  (*Need to check for variable duplication here*)
	  let env = List.fold_right (fun (_,env,_,_) env' -> Envmap.union env env') pat_checks Envmap.empty in
	  let constraints = (List.fold_right (fun (_,_,cs,_) cons -> cs@cons) pat_checks [])@cs in
	  let bounds = List.fold_right (fun (_,_,_,bounds) b_env -> merge_bounds bounds b_env) pat_checks nob in
	  let t = {t=Tid id} in
          let t',cs' = type_consistent (Patt l) d_env Guarantee false t expect_t in
	  (P_aux((P_record(pats',false)),(l,cons_tag_annot t' emp_tag (cs@cs'))),env,constraints@cs',bounds,t'))
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
      let (u,cs) = List.fold_right (fun u (t,cs) -> let t',cs = type_consistent (Patt l) d_env Require true u t in t',cs) ts (item_t,[]) in
      let len = List.length ts in
      let t = 
        match (ord.order,d_env.default_o.order) with
        | (Oinc,_) | (Ovar _, Oinc) | (Ouvar _,Oinc) -> 
          {t = Tapp("vector",[TA_nexp n_zero;
                              TA_nexp {nexp= Nconst (big_int_of_int len)};
                              TA_ord{order=Oinc};
                              TA_typ u])}
        | (Odec,_) | (Ovar _, Odec) | (Ouvar _,Odec) -> 
          {t= Tapp("vector", [TA_nexp {nexp = Nconst (if len = 0 then zero else (big_int_of_int (len -1)))};
                              TA_nexp {nexp = Nconst (big_int_of_int len)};
                              TA_ord{order=Odec};
                              TA_typ u;])}
        | _ -> raise (Reporting_basic.err_unreachable l "Default order not set") in
      (*TODO Should gather the constraints here, with regard to the expected base and rise, and potentially reset them above*)
      (P_aux(P_vector(pats'),(l,cons_tag_annot t emp_tag cs)), env,cs@constraints,bounds,t) 
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
	then [LtEq(co, Require, base, {nexp = Nconst (big_int_of_int fst)});
	      GtEq(co,Require, rise, {nexp = Nconst (big_int_of_int (lst-fst))});]@cs
	else [GtEq(co, Require, base, {nexp = Nconst (big_int_of_int fst)});
	      LtEq(co,Require, rise, { nexp = Nconst (big_int_of_int (fst -lst))});]@cs in
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
	    | Tapp("vector",[(TA_nexp b);(TA_nexp r);(TA_ord o);(TA_typ u)]) -> {nexp = Nadd(r,rn)}
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

let simp_exp e l t = E_aux(e,(l,simple_annot t))
      
let rec check_exp envs (imp_param:nexp option) (expect_t:t) (E_aux(e,(l,annot)):tannot exp): (tannot exp * t * tannot emap * nexp_range list * bounds_env * effect) =
  let Env(d_env,t_env,b_env,tp_env) = envs in
  let expect_t,_ = get_abbrev d_env expect_t in
  let rebuild annot = E_aux(e,(l,annot)) in
  match e with
    | E_block exps -> 
      let (exps',annot',sc,t,ef) = check_block envs imp_param expect_t exps in
      (E_aux(E_block(exps'),(l,annot')),t,Envmap.empty,sc,nob,ef)
    | E_nondet exps ->
      let (ces, sc, ef)  = 
	List.fold_right (fun e (es,sc,ef) -> let (e,_,_,sc',_,ef') = (check_exp envs imp_param unit_t e) in
					     (e::es,sc@sc',union_effects ef ef')) exps ([],[],pure_e) in
      let _,cs = type_consistent (Expr l) d_env Require false unit_t expect_t in
      (E_aux (E_nondet ces,(l,cons_ef_annot unit_t sc ef)),unit_t,t_env,sc,nob,ef)
    | E_id id -> 
      let i = id_to_string id in
      (match Envmap.apply t_env i with
      | Some(Base((params,t),Constructor,cs,ef,bounds)) ->
	let t,cs,ef,_ = subst params false t cs ef in
        (match t.t with
        | Tfn({t = Tid "unit"},t',IP_none,ef) -> 
          let t',cs',ef',e' = type_coerce (Expr l) d_env Require false false b_env t' 
	    (rebuild (Base(([],{t=Tfn(unit_t,t',IP_none,ef)}),Constructor,cs,ef,bounds))) expect_t in
          (e',t',t_env,cs@cs',nob,union_effects ef ef')
        | Tfn(t1,t',IP_none,e) -> 
          typ_error l ("Constructor " ^ i ^ " expects arguments of type " ^ (t_to_string t) ^ ", found none")
        | _ -> raise (Reporting_basic.err_unreachable l "Constructor tannot does not have function type"))
      | Some(Base((params,t),(Enum max),cs,ef,bounds)) ->
        let t',cs,_,_ = subst params false t cs ef in
        let t',cs',ef',e' = 
	  type_coerce (Expr l) d_env Require false false b_env t' (rebuild (cons_tag_annot t' (Enum max) cs)) expect_t in
        (e',t',t_env,cs@cs',nob,ef')
      | Some(Base(tp,Default,cs,ef,_)) | Some(Base(tp,Spec,cs,ef,_)) ->
        typ_error l ("Identifier " ^ i ^ " must be defined, not just specified, before use")
      | Some(Base((params,t),tag,cs,ef,bounds)) ->
	let ((t,cs,ef,_),is_alias) = 
	  match tag with | Emp_global | External _ -> (subst params false t cs ef),false 
	    | Alias -> (t,cs, add_effect (BE_aux(BE_rreg, Parse_ast.Unknown)) ef, Envmap.empty),true 
	    | _ -> (t,cs,ef,Envmap.empty),false 
	in
        let t,cs' = get_abbrev d_env t in
        let cs = cs@cs' in
        let t_actual,expect_actual = match t.t,expect_t.t with
          | Tabbrev(_,t),Tabbrev(_,e) -> t,e
          | Tabbrev(_,t),_ -> t,expect_t 
          | _,Tabbrev(_,e) -> t,e
          | _,_ -> t,expect_t in
	(*let _ = Printf.printf "On general id check, expect_t %s, t %s, tactual %s, expect_actual %s\n" (t_to_string expect_t) (t_to_string t) (t_to_string t_actual) (t_to_string expect_actual) in*)
        (match t_actual.t,expect_actual.t with 
        | Tfn _,_ -> typ_error l ("Identifier " ^ (id_to_string id) ^ " is bound to a function and cannot be used as a value")
        | Tapp("register",[TA_typ(t')]),Tapp("register",[TA_typ(expect_t')]) -> 
          let tannot = Base(([],t),Emp_global,cs,ef,bounds) in
	  let t',cs' = type_consistent (Expr l) d_env Require false t' expect_t' in
          (rebuild tannot,t,t_env,cs@cs',bounds,ef)
        | Tapp("register",[TA_typ(t')]),Tuvar _ ->
	  let ef' = add_effect (BE_aux(BE_rreg,l)) ef in
          let tannot = Base(([],t),(if is_alias then Alias else External (Some i)),cs,ef',bounds) in
          let t',cs',_,e' = type_coerce (Expr l) d_env Require false false b_env t' (rebuild tannot) expect_actual in
          (e',t,t_env,cs@cs',bounds,ef')
        | Tapp("register",[TA_typ(t')]),_ ->
	  let ef' = add_effect (BE_aux(BE_rreg,l)) ef in
          let tannot = Base(([],t),(if is_alias then Alias else External (Some i)),cs,ef',bounds) in
          let t',cs',_,e' = type_coerce (Expr l) d_env Require false false b_env t' (rebuild tannot) expect_actual in
          (e',t',t_env,cs@cs',bounds,ef')
        | Tapp("reg",[TA_typ(t')]),_ ->
          let tannot = cons_bs_annot t cs bounds in
          let t',cs',_,e' = type_coerce (Expr l) d_env Require false false b_env t' (rebuild tannot) expect_actual in
          (e',t',t_env,cs@cs',bounds,pure_e)
        | _ -> 
          let t',cs',ef',e' = 
	    type_coerce (Expr l) d_env Require false false b_env t (rebuild (Base(([],t),tag,cs,pure_e,bounds))) expect_t in
          (e',t',t_env,cs@cs',bounds,union_effects ef ef')
        )
      | Some NoTyp | Some Overload _ | None -> typ_error l ("Identifier " ^ (id_to_string id) ^ " is unbound"))
    | E_lit (L_aux(lit,l')) ->
      let e,cs,effect = (match lit with
        | L_unit  -> (rebuild (simple_annot unit_t)),[],pure_e
	| L_zero  -> 
          (match expect_t.t with
          | Tid "bool" -> simp_exp (E_lit(L_aux(L_zero,l'))) l bool_t,[],pure_e
          | _ -> simp_exp e l bit_t,[],pure_e)
	| L_one   -> 
          (match expect_t.t with
          | Tid "bool" -> simp_exp (E_lit(L_aux(L_one,l'))) l bool_t,[],pure_e
          | _ -> simp_exp e l bit_t,[],pure_e)
	| L_true  -> simp_exp e l bool_t,[],pure_e
	| L_false -> simp_exp e l bool_t,[],pure_e
	| L_num i -> 
	  (*let _ = Printf.eprintf "expected type of number literal %i is %s\n" i (t_to_string expect_t) in*)
          (match expect_t.t with
          | Tid "bit" | Toptions({t=Tid"bit"},_) -> 
            if i = 0 then simp_exp (E_lit(L_aux(L_zero,l'))) l bit_t,[],pure_e
	    else if i = 1 then simp_exp (E_lit(L_aux(L_one,l'))) l bit_t,[],pure_e
	    else typ_error l ("Expected a bit, found " ^ string_of_int i)
          | Tid "bool" | Toptions({t=Tid"bool"},_)->
            if i = 0 then simp_exp (E_lit(L_aux(L_zero,l'))) l bit_t,[],pure_e
            else if i = 1 then simp_exp (E_lit(L_aux(L_one,l'))) l bit_t ,[],pure_e
            else typ_error l ("Expected bool or a bit, found " ^ string_of_int i)
          | Tapp ("vector",[TA_nexp base;TA_nexp rise;TA_ord o;(TA_typ {t=Tid "bit"})]) ->
            let n = {nexp = Nconst (big_int_of_int i) } in
            let t = {t=Tapp("atom", [TA_nexp n;])} in
            let cs = [LtEq(Expr l,Guarantee,n,mk_sub {nexp = N2n(rise,None)} n_one)] in
            let f = match o.order with | Oinc -> "to_vec_inc" | Odec -> "to_vec_dec" | _ -> "to_vec_inc" in
	    (*let _ = Printf.eprintf "adding a call to to_vec_*: bounds are %s\n" (bounds_to_string b_env) in*)
	    let internal_tannot = (l,(cons_bs_annot {t = Tapp("implicit",[TA_nexp rise])} [] b_env)) in
	    let tannot = (l,cons_tag_annot expect_t (External (Some f)) cs) in
            E_aux(E_app((Id_aux((Id f),l)),
			[(E_aux (E_internal_exp(internal_tannot), tannot));simp_exp e l t]),tannot),cs,pure_e
          | _ -> simp_exp e l {t = Tapp("atom", [TA_nexp{nexp = Nconst (big_int_of_int i)}])},[],pure_e)
	| L_hex s -> simp_exp e l {t = Tapp("vector",
			                    [TA_nexp{nexp = Nconst zero};
				             TA_nexp{nexp = Nconst (big_int_of_int ((String.length s)*4))};
				             TA_ord d_env.default_o;TA_typ{t = Tid "bit"}])},[],pure_e
	| L_bin s -> simp_exp e l {t = Tapp("vector",
			                    [TA_nexp{nexp = Nconst zero};
				             TA_nexp{nexp = Nconst (big_int_of_int (String.length s))};
				             TA_ord d_env.default_o ;TA_typ{t = Tid"bit"}])},[],pure_e
	| L_string s -> simp_exp e l {t = Tid "string"},[],pure_e
	| L_undef -> 
	  let ef = {effect=Eset[BE_aux(BE_undef,l)]} in
          (match expect_t.t with
            | Tapp ("vector",[TA_nexp base;TA_nexp {nexp=Nconst rise};TA_ord o;(TA_typ {t=Tid "bit"})]) 
	    | Tapp ("register",[TA_typ {t=Tapp ("vector",[TA_nexp base;TA_nexp {nexp=Nconst rise};
							  TA_ord o;(TA_typ {t=Tid "bit"})])}])->
              let f = match o.order with | Oinc -> "to_vec_inc" | Odec -> "to_vec_dec" | _ -> "to_vec_inc" (*Change to follow a default?*) in
	      let tannot = (l,Base(([],expect_t),External (Some f),[],ef,b_env)) in
              E_aux(E_app((Id_aux((Id f),l)),
			  [(E_aux (E_internal_exp(tannot), tannot));simp_exp e l bit_t]),tannot),[],ef
            | _ -> simp_exp e l (new_t ()),[],ef)) in
      let t',cs',_,e' = type_coerce (Expr l) d_env Require false true b_env (get_e_typ e) e expect_t in
      (e',t',t_env,cs@cs',nob,effect)
    | E_cast(typ,e) ->
      let cast_t = typ_to_t false false typ in
      let cast_t,cs_a = get_abbrev d_env cast_t in
      let cast_t = typ_subst tp_env false cast_t in
      let ct = {t = Toptions(cast_t,None)} in
      let (e',u,t_env,cs,bounds,ef) = check_exp envs imp_param ct e in
      (*let _ = Printf.eprintf "Type checking cast: cast_t is %s constraints after checking e are %s\n" (t_to_string cast_t) (constraints_to_string cs) in*)
      let t',cs2,ef',e' = type_coerce (Expr l) d_env Require true false b_env u e' cast_t in
      (*let _ = Printf.eprintf "Type checking cast: after first coerce with u at %s, and final t' %s is and constraints are %s\n" (t_to_string u) (t_to_string t') (constraints_to_string cs2) in*)
      let t',cs3,ef'',e'' = type_coerce (Expr l) d_env Guarantee false false b_env cast_t e' expect_t in 
      (*let _ = Printf.eprintf "Type checking cast: after second coerce expect_t is %s, t' %s is and constraints are %s\n" (t_to_string expect_t) (t_to_string t') (constraints_to_string cs3) in*)
      (e'',t',t_env,cs_a@cs@cs2@cs3,bounds,union_effects ef' (union_effects ef'' ef))
    | E_app(id,parms) -> 
      let i = id_to_string id in
      let check_parms p_typ parms = (match parms with
        | [] | [(E_aux (E_lit (L_aux (L_unit,_)),_))] 
	  -> let (_,cs') = type_consistent (Expr l) d_env Require false unit_t p_typ in [],unit_t,cs',pure_e 
        | [parm] -> let (parm',arg_t,t_env,cs',_,ef_p) = check_exp envs imp_param p_typ parm in [parm'],arg_t,cs',ef_p
        | parms -> 
          (match check_exp envs imp_param p_typ (E_aux (E_tuple parms,(l,NoTyp))) with
          | ((E_aux(E_tuple parms',tannot')),arg_t,t_env,cs',_,ef_p) -> parms',arg_t,cs',ef_p
          | _ -> raise (Reporting_basic.err_unreachable l "check_exp, given a tuple and a tuple type, didn't return a tuple"))) 
      in
      let coerce_parms arg_t parms expect_arg_t =
	(match parms with
	| [] | [(E_aux (E_lit (L_aux(L_unit, _)), _))] -> [],pure_e,[]
	| [parm] -> 
	  let _,cs,ef,parm' = 
	    type_coerce (Expr l) d_env Guarantee false false b_env arg_t parm expect_arg_t in [parm'],ef,cs
	| parms ->
          (match 
	   type_coerce (Expr l) d_env Guarantee false false b_env arg_t (E_aux (E_tuple parms,(l,NoTyp))) expect_arg_t
	   with
          | (_,cs,ef,(E_aux(E_tuple parms',tannot'))) -> (parms',ef,cs)
          | _ -> raise (Reporting_basic.err_unreachable l "type coerce given tuple and tuple type returned non-tuple"))) 
      in
      let check_result ret imp tag cs ef parms =    
	match (imp,imp_param) with
	  | (IP_length n ,None) | (IP_user n,None) | (IP_start n,None) ->
	    (*let _ = Printf.eprintf "implicit length or var required, no imp_param %s\n!" (n_to_string n) in*)
	    let internal_exp = 
	      let implicit = {t= Tapp("implicit",[TA_nexp n])} in
	      let annot_i = Base(([],implicit),Emp_local,[],pure_e,b_env) in
	      E_aux(E_internal_exp((l,annot_i)),(l,simple_annot nat_t)) in
            type_coerce (Expr l) d_env Require false false b_env ret 
	      (E_aux (E_app(id, internal_exp::parms),(l,(Base(([],ret),tag,cs,ef,nob))))) expect_t
	  | (IP_length n ,Some ne) | (IP_user n,Some ne) | (IP_start n,Some ne) ->
	    (*let _ = Printf.eprintf "implicit length or var required %s with imp_param %s\n" (n_to_string n) (n_to_string ne) in
	    let _ = Printf.eprintf "and expected type is %s and return type is %s\n" (t_to_string expect_t) (t_to_string ret) in*)
	    let internal_exp = 
	      let implicit_user = {t = Tapp("implicit",[TA_nexp ne])} in
	      let implicit = {t= Tapp("implicit",[TA_nexp n])} in
	      let annot_iu = Base(([],implicit_user),Emp_local,[],pure_e,b_env)in
	      let annot_i = Base(([],implicit),Emp_local,[],pure_e,b_env) in
	      E_aux (E_internal_exp_user((l, annot_iu),(l,annot_i)), (l,simple_annot nat_t))
	    in
	    type_coerce (Expr l) d_env Require false false b_env ret 
	      (E_aux (E_app(id,internal_exp::parms),(l,(Base(([],ret),tag,cs,ef,nob))))) expect_t
          | (IP_none,_) -> 
	    (*let _ = Printf.printf "no implicit length or var required\n" in*)
            type_coerce (Expr l) d_env Require false false b_env ret 
	      (E_aux (E_app(id, parms),(l,(Base(([],ret),tag,cs,ef,nob))))) expect_t
      in
      (match Envmap.apply t_env i with
      | Some(Base(tp,Enum _,_,_,_)) ->
        typ_error l ("Expected function with name " ^ i ^ " but found an enumeration identifier")
      | Some(Base(tp,Default,_,_,_)) ->
        typ_error l ("Function " ^ i ^ " must be specified, not just declared as a default, before use")
      | Some(Base((params,t),tag,cs,ef,bounds)) ->
	(*let _ = Printf.eprintf "Going to check a function call %s with unsubstituted types %s and constraints %s \n" i (t_to_string t) (constraints_to_string cs) in*)
        let t,cs,ef,_ = subst params false t cs ef in
        (match t.t with
        | Tfn(arg,ret,imp,ef') ->
	  (*let _ = Printf.eprintf "Checking funcation call of %s\n" i in
	  let _ = Printf.eprintf "Substituted types and constraints are %s and %s\n" (t_to_string t) (constraints_to_string cs) in*)
          let parms,arg_t,cs_p,ef_p = check_parms arg parms in
	  (*let _ = Printf.eprintf "Checked parms of %s\n" i in*)
          let (ret_t,cs_r,ef_r,e') = check_result ret imp tag cs ef' parms in
	  (*let _ = Printf.eprintf "Checked result of %s and constraints are %s\n" i (constraints_to_string cs_r) in*)
          (e',ret_t,t_env,cs@cs_p@cs_r, bounds,union_effects ef' (union_effects ef_p ef_r))
        | _ -> typ_error l ("Expected a function or constructor, found identifier " ^ i ^ " bound to type " ^ (t_to_string t)))
      | Some(Overload(Base((params,t),tag,cs,ef,_),overload_return,variants)) ->
	let t_p,cs_p,ef_p,_ = subst params false t cs ef in
	let args,arg_t,arg_cs,arg_ef = 
	  (match t_p.t with
	  | Tfn(arg,ret,_,ef') -> check_parms arg parms 
	  | _ -> 
	    typ_error l ("Expected a function or constructor, found identifier " ^ i
			 ^ " bound to type " ^ (t_to_string t))) in
	(match (select_overload_variant d_env true overload_return variants arg_t) with
	  | [] -> typ_error l 
	    ("No function found with name " ^ i ^ " that expects parameters " ^ (t_to_string arg_t))
	  | [Base((params,t),tag,cs,ef,bounds)] ->
	    (match t.t with
	      | Tfn(arg,ret,imp,ef') ->
		let args',arg_ef',arg_cs' = coerce_parms arg_t args arg in
		let (ret_t,cs_r,ef_r,e') = check_result ret imp tag cs ef' args' in
		(e',ret_t,t_env,cs_p@arg_cs@arg_cs'@cs_r,nob,
		 union_effects ef_r (union_effects ef_p (union_effects (union_effects arg_ef' arg_ef) ef')))
	      | _ -> raise (Reporting_basic.err_unreachable l "Overloaded variant not a function"))
	  | variants' ->
	    (match select_overload_variant d_env false true variants' expect_t with
	      | [] ->
		typ_error l ("No function found with name " ^ i ^ ", expecting parameters " ^ (t_to_string arg_t) ^ " and returning " ^ (t_to_string expect_t))
	      | [Base((params,t),tag,cs,ef,bounds)] ->
		(match t.t with
		  |Tfn(arg,ret,imp,ef') ->
		    let args',arg_ef',arg_cs' = coerce_parms arg_t args arg in 
		    let (ret_t,cs_r,ef_r,e') = check_result ret imp tag cs ef' args' in
		    (e',ret_t,t_env,cs_p@arg_cs@arg_cs'@cs_r,nob,
		     union_effects ef_r (union_effects ef_p (union_effects (union_effects arg_ef arg_ef') ef')))
	         | _ -> raise (Reporting_basic.err_unreachable l "Overloaded variant not a function"))
	      | _ -> 
                typ_error l ("More than one definition of " ^ i ^ " found with type " ^ (t_to_string arg_t) ^ " -> " ^ (t_to_string expect_t) ^ ". A cast may be required")))
      | _ -> typ_error l ("Unbound function " ^ i))
    | E_app_infix(lft,op,rht) -> 
      let i = id_to_string op in
      let check_parms arg_t lft rht =
        match check_exp envs imp_param arg_t (E_aux(E_tuple [lft;rht],(l,NoTyp))) with
        | ((E_aux(E_tuple [lft';rht'],_)),arg_t,_,cs',_,ef') -> (lft',rht',arg_t,cs',ef')
        | _ -> 
	  raise (Reporting_basic.err_unreachable l "check exp given tuple and tuple type and returned non-tuple") 
      in
      let check_result ret imp tag cs ef lft rht =
        match imp with
	  (*| IP_length _ ->  
            let internal_exp =  match expect_t.t,ret.t with 
              | Tapp("vector",_),_ -> 
		E_aux (E_internal_exp (l,simple_annot expect_t), (l, simple_annot nat_t))
              | _,Tapp("vector",_) -> 
		E_aux (E_internal_exp (l,simple_annot ret), (l,simple_annot nat_t))
              | _ -> typ_error l (i ^ " expected either the return type or the expected type to be a vector") in
            type_coerce (Expr l) d_env false false ret (E_aux (E_app(op, [internal_exp;lft;rht]),(l,(Base(([],ret),tag,cs,ef,nob))))) expect_t*)
          | IP_none -> 
            type_coerce (Expr l) d_env Require false false b_env ret 
	      (E_aux (E_app_infix(lft,op,rht),(l,(Base(([],ret),tag,cs,ef,nob))))) expect_t 
      in
      (match Envmap.apply t_env i with
      | Some(Base(tp,Enum _,cs,ef,b)) -> 
	typ_error l ("Expected function with name " ^ i ^ " but found an enumeration identifier")
      | Some(Base(tp,Default,cs,ef,b)) -> 
	typ_error l ("Function " ^ i ^ " must be defined, not just declared as default, before use")
      | Some(Base((params,t),tag,cs,ef,b)) ->
        let t,cs,ef,_ = subst params false t cs ef in
        (match t.t with
        | Tfn(arg,ret,imp,ef) -> 
          let (lft',rht',arg_t,cs_p,ef_p) = check_parms arg lft rht in
          let ret_t,cs_r',ef_r,e' = check_result ret imp tag cs ef lft' rht' in
          (e',ret_t,t_env,cs@cs_p@cs_r',nob,union_effects ef (union_effects ef_p ef_r))
        | _ -> 
	  typ_error l ("Expected a function, found identifier " ^ i ^ " bound to type " ^ (t_to_string t)))
      | Some(Overload(Base((params,t),tag,cs,ef,_),overload_return,variants)) ->
	let t_p,cs_p,ef_p,_ = subst params false t cs ef in
	let lft',rht',arg_t,arg_cs,arg_ef =  
	  (match t_p.t with
	  | Tfn(arg,ret,_,ef') -> check_parms arg lft rht
	  | _ -> typ_error l ("Expected a function, found identifier " ^ i ^ " bound to type " ^ (t_to_string t))) in
        (*let _ = Printf.eprintf "Looking for overloaded function %s, generic type is %s, arg_t is %s\n" i (t_to_string t_p) (t_to_string arg_t) in*)
	(match (select_overload_variant d_env true overload_return variants arg_t) with
	| [] -> 
	  typ_error l ("No function found with name " ^ i ^
			  " that expects parameters " ^ (t_to_string arg_t))
	| [Base((params,t),tag,cs,ef,b)] ->
          (*let _ = Printf.eprintf "Selected an overloaded function for %s,
	    variant with function type %s for actual type %s\n" i (t_to_string t) (t_to_string arg_t) in*)
	  (match t.t with
	  | Tfn(arg,ret,imp,ef') ->
            (match arg.t,arg_t.t with
            | Ttup([tlft;trght]),Ttup([tlft_t;trght_t]) ->
	      let (lft',rht',arg_t,cs_p,ef_p) = check_parms arg lft rht in
              (*let (_,cs_lft,ef_lft,lft') = type_coerce (Expr l) d_env false tlft_t lft' tlft in
		let (_,cs_rght,ef_rght,rht') = type_coerce (Expr l) d_env false trght_t rht' trght in*)
	      let (ret_t,cs_r,ef_r,e') = check_result ret imp tag cs ef lft' rht' in
	      (e',ret_t,t_env,cs_p@arg_cs@cs@cs_r,nob,
	       union_effects ef_r (union_effects ef_p (union_effects arg_ef ef')))
            |_ -> raise (Reporting_basic.err_unreachable l "function no longer has tuple type"))
	  | _ -> raise (Reporting_basic.err_unreachable l "overload variant does not have function"))
	| variants ->
	  (*let _ = Printf.eprintf "Number of variants found before looking at return value %i\n%!" (List.length variants) in*)
	  (match (select_overload_variant d_env false true variants expect_t) with
	    | [] -> 
	      typ_error l ("No matching function found with name " ^ i ^ " that expects parameters " ^
			      (t_to_string arg_t) ^ " returning " ^ (t_to_string expect_t))
	    | [Base((params,t),tag,cs,ef,b)] -> 
              (*let _ = Printf.eprintf "Selected an overloaded function for %s,
	    variant with function type %s for actual type %s\n" i (t_to_string t) (t_to_string arg_t) in*)
	      (match t.t with
		| Tfn(arg,ret,imp,ef') ->
		  (match arg.t,arg_t.t with
		    | Ttup([tlft;trght]),Ttup([tlft_t;trght_t]) ->
		      let (lft',rht',arg_t,cs_p,ef_p) = check_parms arg lft rht in
		      let (ret_t,cs_r,ef_r,e') = check_result ret imp tag cs ef lft' rht' in
		      (e',ret_t,t_env,cs_p@arg_cs@cs@cs_r,nob,
		       union_effects ef_r (union_effects ef_p (union_effects arg_ef ef')))
		    |_ -> raise (Reporting_basic.err_unreachable l "function no longer has tuple type"))
		| _ -> raise (Reporting_basic.err_unreachable l "overload variant does not have function"))
	    | _ -> 
              typ_error l ("More than one variant of " ^ i ^ " found with type " ^ (t_to_string arg_t) ^ " -> " ^ (t_to_string expect_t) ^ ". A cast may be required")))
      | _ -> typ_error l ("Unbound infix function " ^ i))
    | E_tuple(exps) ->
      (match expect_t.t with
      | Ttup ts ->
        let tl = List.length ts in
        let el = List.length exps in
        if tl = el then
          let exps,typs,consts,effect = 
            List.fold_right2 
	      (fun e t (exps,typs,consts,effect) -> 
		let (e',t',_,c,_,ef) = check_exp envs imp_param t e in ((e'::exps),(t'::typs),c@consts,union_effects ef effect))
              exps ts ([],[],[],pure_e) in
          let t = {t = Ttup typs} in
          (E_aux(E_tuple(exps),(l,simple_annot t)),t,t_env,consts,nob,effect)
        else typ_error l ("Expected a tuple with length " ^ (string_of_int tl) ^ " found one of length " ^ (string_of_int el))
      | _ ->
        let exps,typs,consts,effect = 
          List.fold_right 
	    (fun e (exps,typs,consts,effect) -> 
	      let (e',t,_,c,_,ef) = check_exp envs imp_param (new_t ()) e in
	      ((e'::exps),(t::typs),c@consts,union_effects ef effect))
	    exps ([],[],[],pure_e) in
        let t = { t=Ttup typs } in
        let t',cs',ef',e' = 
	  type_coerce (Expr l) d_env Guarantee false false b_env
	    t (E_aux(E_tuple(exps),(l,simple_annot t))) expect_t in
        (e',t',t_env,consts@cs',nob,union_effects ef' effect))
    | E_if(cond,then_,else_) ->
      let (cond',_,_,c1,_,ef1) = check_exp envs imp_param bit_t cond in
      (match expect_t.t with
      | Tuvar _ -> 
        let then',then_t,then_env,then_c,then_bs,then_ef = check_exp envs imp_param (new_t ()) then_ in
        let else',else_t,else_env,else_c,else_bs,else_ef = check_exp envs imp_param (new_t ()) else_ in
	(*TOTHINK Possibly I should first consistency check else and then, with Guarantee, then check against expect_t with Require*)
        let then_t',then_c' = type_consistent (Expr l) d_env Require true then_t expect_t in
        let else_t',else_c' = type_consistent (Expr l) d_env Require true else_t expect_t  in
        let t_cs = CondCons((Expr l),c1,then_c@then_c') in
        let e_cs = CondCons((Expr l),[],else_c@else_c') in
        (E_aux(E_if(cond',then',else'),(l,simple_annot expect_t)),
         expect_t,Envmap.intersect_merge (tannot_merge (Expr l) d_env true) then_env else_env,[t_cs;e_cs],
	 merge_bounds then_bs else_bs, (*TODO Should be an intersecting merge*)
         union_effects ef1 (union_effects then_ef else_ef))
      | _ ->
        let then',then_t,then_env,then_c,then_bs,then_ef = check_exp envs imp_param expect_t then_ in
        let else',else_t,else_env,else_c,else_bs,else_ef = check_exp envs imp_param expect_t else_ in
        let t_cs = CondCons((Expr l),c1,then_c) in
        let e_cs = CondCons((Expr l),[],else_c) in
        (E_aux(E_if(cond',then',else'),(l,simple_annot expect_t)),
         expect_t,Envmap.intersect_merge (tannot_merge (Expr l) d_env true) then_env else_env,[t_cs;e_cs],
	 merge_bounds then_bs else_bs,
         union_effects ef1 (union_effects then_ef else_ef)))
    | E_for(id,from,to_,step,order,block) -> 
      (*TOTHINK Instead of making up new ns here, perhaps I should instead make sure they conform to range without coercion as these nu variables might be floating*)
      let fb,fr,tb,tr,sb,sr = new_n(),new_n(),new_n(),new_n(),new_n(),new_n() in
      let ft,tt,st = {t=Tapp("range",[TA_nexp fb;TA_nexp fr])},
	{t=Tapp("range",[TA_nexp tb;TA_nexp tr])},{t=Tapp("range",[TA_nexp sb;TA_nexp sr])} in     
      let from',from_t,_,from_c,_,from_ef = check_exp envs imp_param ft from in
      let to_',to_t,_,to_c,_,to_ef = check_exp envs imp_param tt to_ in
      let step',step_t,_,step_c,_,step_ef = check_exp envs imp_param st step in
      let new_annot,local_cs = 
	match (aorder_to_ord order).order with
	  | Oinc ->
	    (simple_annot {t=Tapp("range",[TA_nexp fb;TA_nexp tr])},
	     [LtEq((Expr l),Guarantee ,fr,tr);LtEq((Expr l),Guarantee,fb,tb)])
	  | Odec ->
	    (simple_annot {t=Tapp("range",[TA_nexp tb; TA_nexp fr])},
	     [GtEq((Expr l),Guarantee,fr,tr);GtEq((Expr l),Guarantee,fb,tb)])
	  | _ -> (typ_error l "Order specification in a foreach loop must be either inc or dec, not polymorphic")
      in 
      (*TODO Might want to extend bounds here for the introduced variable*)
      let (block',b_t,_,b_c,_,b_ef)=
	check_exp (Env(d_env,Envmap.insert t_env (id_to_string id,new_annot),b_env,tp_env)) imp_param expect_t block
      in
      (E_aux(E_for(id,from',to_',step',order,block'),(l,constrained_annot b_t local_cs)),expect_t,Envmap.empty,
       b_c@from_c@to_c@step_c@local_cs,nob,(union_effects b_ef (union_effects step_ef (union_effects to_ef from_ef))))
    | E_vector(es) ->
      let item_t,ord = match expect_t.t with
        | Tapp("vector",[base;rise;TA_ord ord;TA_typ item_t]) -> item_t,ord
        | _ -> new_t (),d_env.default_o in
      let es,cs,effect = (List.fold_right 
			    (fun (e,_,_,c,_,ef) (es,cs,effect) -> (e::es),(c@cs),union_effects ef effect)
			    (List.map (check_exp envs imp_param item_t) es) ([],[],pure_e)) in
      let len = List.length es in
      let t = match ord.order,d_env.default_o.order with
        | (Oinc,_) | (Ouvar _,Oinc) | (Ovar _,Oinc) -> 
          {t = Tapp("vector", [TA_nexp n_zero; TA_nexp {nexp = Nconst (big_int_of_int len)};
                               TA_ord {order = Oinc}; TA_typ item_t])}
        | (Odec,_) | (Ouvar _,Odec) | (Ovar _,Odec) -> 
          {t = Tapp("vector",[TA_nexp {nexp=Nconst (big_int_of_int (len-1))};
                              TA_nexp {nexp=Nconst (big_int_of_int len)};
                              TA_ord {order= Odec}; TA_typ item_t])} in
      let t',cs',ef',e' = type_coerce (Expr l) d_env Guarantee false false b_env t 
	(E_aux(E_vector es,(l,simple_annot t))) expect_t in
      (e',t',t_env,cs@cs',nob,union_effects effect ef')
    | E_vector_indexed(eis,(Def_val_aux(default,(ld,annot)))) ->
      let item_t,base_n,rise_n = match expect_t.t with
        | Tapp("vector",[TA_nexp base;TA_nexp rise;ord;TA_typ item_t]) -> item_t,base,rise
        | _ -> new_t (),new_n (), new_n () in
      let first,last = fst (List.hd eis), fst (List.hd (List.rev eis)) in
      let is_increasing = first <= last in
      let es,cs,effect,contains_skip,_ = (List.fold_right 
			      (fun ((i,e),c,ef) (es,cs,effect,skips,prev) -> 
				(*let _ = Printf.printf "Checking increasing %b %i %i\n" is_increasing prev i in*)
                                let (esn, csn, efn) = (((i,e)::es), (c@cs), union_effects ef effect) in
				if (is_increasing && prev > i)
				then (esn,csn,efn,(((prev-i) > 1) || skips),i)
                                else if prev < i 
                                then (esn,csn,efn,(((i-prev) > 1) || skips),i)
                                else if i = prev
                                then (typ_error l ("Indexed vector contains a duplicate definition of index " ^ (string_of_int i)))
                                else (typ_error l ("Indexed vector is not consistently " ^ (if is_increasing then "increasing" else "decreasing"))))
			      (List.map (fun (i,e) -> let (e,_,_,cs,_,eft) = (check_exp envs imp_param item_t e) in ((i,e),cs,eft))
				 eis) ([],[],pure_e,false,(if is_increasing then (last+1) else (last-1)))) in
      let (default',fully_enumerate,cs_d,ef_d) = match (default,contains_skip) with
	| (Def_val_empty,false) -> (Def_val_aux(Def_val_empty,(ld,simple_annot item_t)),true,[],pure_e)
        | (Def_val_empty,true)  -> 
          let ef = add_effect (BE_aux(BE_unspec,l)) pure_e in
	  let (de,_,_,_,_,ef_d) = check_exp envs imp_param item_t (E_aux(E_lit (L_aux(L_undef,l)), (l,NoTyp))) in
          (Def_val_aux(Def_val_dec de, (l, cons_ef_annot item_t [] ef)),false,[],ef)
	| (Def_val_dec e,_) -> let (de,t,_,cs_d,_,ef_d) = (check_exp envs imp_param item_t e) in
			       (*Check that ef_d doesn't write to memory or registers? *)
			       (Def_val_aux(Def_val_dec de,(ld,cons_ef_annot item_t cs_d ef_d)),false,cs_d,ef_d) in
      let (base_bound,length_bound,cs_bounds) = 
	if fully_enumerate
	then ({nexp=Nconst (big_int_of_int first)},{nexp = Nconst (big_int_of_int (List.length eis))},[])
	else (base_n,rise_n,[LtEq(Expr l,Require, base_n,{nexp = Nconst (big_int_of_int first)});
			     GtEq(Expr l,Require, rise_n,{nexp = Nconst (big_int_of_int (List.length eis))})]) 
      in	     
      let t = {t = Tapp("vector",
			[TA_nexp(base_bound);TA_nexp length_bound;
			 TA_ord({order= if is_increasing then Oinc else Odec});TA_typ item_t])} in
      let t',cs',ef',e' = type_coerce (Expr l) d_env Require false false b_env t 
	                          (E_aux (E_vector_indexed(es,default'),(l,simple_annot t))) expect_t in
      (e',t',t_env,cs@cs_d@cs_bounds@cs',nob,union_effects ef_d (union_effects ef' effect))
    | E_vector_access(vec,i) ->
      let base,len,ord = new_n(),new_n(),new_o() in
      let item_t = new_t () in
      let min,max = new_n(),new_n() in
      let vt = {t= Tapp("vector",[TA_nexp base;TA_nexp len;TA_ord ord; TA_typ item_t])} in
      let (vec',t',_,cs,_,ef) = check_exp envs imp_param vt vec in
      let it = {t= Tapp("range",[TA_nexp min;TA_nexp max])} in
      let (i',ti',_,cs_i,_,ef_i) = check_exp envs imp_param it i in
      let ord,item_t = match t'.t with
        | Tabbrev(_,{t=Tapp("vector",[_;_;TA_ord ord;TA_typ t])}) | Tapp("vector",[_;_;TA_ord ord;TA_typ t]) -> ord,t
        | _ -> ord,item_t in
      let oinc_max_access = mk_sub (mk_add base len) n_one in
      let odec_min_access = mk_sub base len in
      let cs_loc = 
	match (ord.order,d_env.default_o.order) with
	  | (Oinc,_) ->
	    [LtEq((Expr l),Require,base,min); 
	     LtEq((Expr l),Require, max,oinc_max_access); LtEq((Expr l),Require, min,oinc_max_access)] 
	  | (Odec,_) -> 
	    [GtEq((Expr l),Require,base,min); LtEq((Expr l),Require,min,odec_min_access); LtEq((Expr l),Require,max,odec_min_access)]
	  | (_,Oinc) -> 
	    [LtEq((Expr l),Require,base,min); 
	     LtEq((Expr l),Require, max,oinc_max_access); LtEq((Expr l),Require, min,oinc_max_access)] 
	  | (_,Odec) ->
	    [GtEq((Expr l),Require,base,min); LtEq((Expr l),Require,min,odec_min_access); LtEq((Expr l),Require,max,odec_min_access)]
	  | _ -> typ_error l "A vector must be either increasing or decreasing to access a single element"
      in 
      (*let _ = Printf.eprintf "Type checking vector access. item_t is %s and expect_t is %s\n" (t_to_string item_t) (t_to_string expect_t) in*)
      let t',cs',ef',e'=type_coerce (Expr l) d_env Require false false b_env item_t 
	(E_aux(E_vector_access(vec',i'),(l,simple_annot item_t))) expect_t in
      (e',t',t_env,cs_loc@cs_i@cs@cs',nob,union_effects ef (union_effects ef' ef_i))
    | E_vector_subrange(vec,i1,i2) ->
      let base,rise,ord = new_n(),new_n(),new_o() in
      let new_base,new_rise = new_n(),new_n() in
      let n1,min1,max1 = new_n(), new_n(),new_n() in
      let n2,min2,max2 = new_n(), new_n(),new_n() in
      let base_e,rise_e,ord_e,item_t = match expect_t.t with
	| Tapp("vector",[TA_nexp base_n;TA_nexp rise_n; TA_ord ord_n; TA_typ item_t]) -> base_n,rise_n,ord_n,item_t
	| _ -> new_n(),new_n(),new_o(),new_t() in
      let vt = {t=Tapp("vector",[TA_nexp base;TA_nexp rise;TA_ord ord;TA_typ item_t])} in
      let (vec',t',_,cs,_,ef) = check_exp envs imp_param vt vec in
      let i1t = {t=Tapp("atom",[TA_nexp n1])} in
      let (i1', ti1, _,cs_i1,_,ef_i1) = check_exp envs imp_param i1t i1 in
      let i2t = {t=Tapp("atom",[TA_nexp n2])} in
      let (i2', ti2, _,cs_i2,_,ef_i2) = check_exp envs imp_param i2t i2 in
      let cs_loc =
	match (ord.order,d_env.default_o.order) with
	  | (Oinc,_) -> 
	    [Eq((Expr l), new_base, n1);
	     Eq((Expr l), new_rise, mk_sub n2 n1);
	     LtEq((Expr l),Require, min1, n1); LtEq((Expr l),Require, n1,max1);
	     LtEq((Expr l),Require, min2, n2); LtEq((Expr l),Require, n2,max2);
	     LtEq((Expr l),Require,base,n1); 
	     LtEq((Expr l),Require,base,max1); 
	     LtEq((Expr l),Require,n2,mk_add base rise);
	     LtEq((Expr l),Require,max2,mk_add base rise);]
	  | (Odec,_) ->
	    [Eq((Expr l), new_base, n1);
	     Eq((Expr l), new_rise, mk_add (mk_sub n1 n2) n_one);
	     LtEq((Expr l), Require, min1, n1); LtEq((Expr l),Require, n1,max1);
	     LtEq((Expr l), Require, min2, n2); LtEq((Expr l),Require, n2,max2);
	     GtEq((Expr l),Require,base,n1); 
	     GtEq((Expr l),Require,base,max1); 
	     LtEq((Expr l),Require,n2,mk_add (mk_sub base rise) n_one);
	     LtEq((Expr l),Require,max2,mk_add (mk_sub base rise) n_one);]	     
	  | (_,Oinc) ->
	    [Eq((Expr l), new_base, n1);
	     Eq((Expr l), new_rise, mk_sub n2 n1);
	     LtEq((Expr l),Require, min1, n1); LtEq((Expr l),Require, n1,max1);
	     LtEq((Expr l),Require, min2, n2); LtEq((Expr l),Require, n2,max2);
	     LtEq((Expr l),Require,base,n1); 
	     LtEq((Expr l),Require,base,max1); 
	     LtEq((Expr l),Require,n2,mk_add base rise);
	     LtEq((Expr l),Require,max2,mk_add base rise);]
	  | (_,Odec) -> 
	    [Eq((Expr l), new_base, n1);
	     Eq((Expr l), new_rise, mk_add (mk_sub n1 n2) n_one);
	     LtEq((Expr l), Require, min1, n1); LtEq((Expr l),Require, n1,max1);
	     LtEq((Expr l), Require, min2, n2); LtEq((Expr l),Require, n2,max2);
	     GtEq((Expr l),Require,base,n1); 
	     GtEq((Expr l),Require,base,max1); 
	     LtEq((Expr l),Require,n2,mk_add (mk_sub base rise) n_one);
	     LtEq((Expr l),Require,max2,mk_add (mk_sub base rise) n_one);]	     
	  | _ -> typ_error l "A vector must be either increasing or decreasing to access a slice" in
      let nt = {t=Tapp("vector",[TA_nexp new_base;TA_nexp new_rise; TA_ord ord;TA_typ item_t])} in
      let (t,cs3,ef3,e') = 
	type_coerce (Expr l) d_env Require false false b_env nt 
	  (E_aux(E_vector_subrange(vec',i1',i2'),(l,constrained_annot nt cs_loc))) expect_t in
      (e',t,t_env,cs3@cs@cs_i1@cs_i2@cs_loc,nob,(union_effects ef (union_effects ef3 (union_effects ef_i1 ef_i2))))
    | E_vector_update(vec,i,e) ->
      let base,rise,ord = new_n(),new_n(),new_o() in
      let min,m_rise = new_n(),new_n() in
      let item_t = match expect_t.t with
	| Tapp("vector",[TA_nexp base_n;TA_nexp rise_n; TA_ord ord_n; TA_typ item_t]) -> item_t
	| _ -> new_t() in
      let vt = {t=Tapp("vector",[TA_nexp base;TA_nexp rise;TA_ord ord;TA_typ item_t])} in
      let (vec',t',_,cs,_,ef) = check_exp envs imp_param vt vec in
      let it = {t=Tapp("range",[TA_nexp min;TA_nexp m_rise])} in
      let (i', ti, _,cs_i,_,ef_i) = check_exp envs imp_param it i in
      let (e', te, _,cs_e,_,ef_e) = check_exp envs imp_param item_t e in
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
      let (t,cs3,ef3,e') = 
	type_coerce (Expr l) d_env Require false false b_env nt 
	  (E_aux(E_vector_update(vec',i',e'),(l,constrained_annot nt cs_loc))) expect_t in
      (e',t,t_env,cs3@cs@cs_i@cs_e@cs_loc,nob,(union_effects ef (union_effects ef3 (union_effects ef_i ef_e))))
    | E_vector_update_subrange(vec,i1,i2,e) ->
      let base,rise,ord = new_n(),new_n(),new_o() in
      let min1,m_rise1 = new_n(),new_n() in
      let min2,m_rise2 = new_n(),new_n() in
      let item_t = match expect_t.t with
	| Tapp("vector",[TA_nexp base_n;TA_nexp rise_n; TA_ord ord_n; TA_typ item_t]) -> item_t
	| _ -> new_t() in
      let vt = {t=Tapp("vector",[TA_nexp base;TA_nexp rise;TA_ord ord;TA_typ item_t])} in
      let (vec',t',_,cs,_,ef) = check_exp envs imp_param vt vec in
      let i1t = {t=Tapp("range",[TA_nexp min1;TA_nexp m_rise1])} in
      let (i1', ti1, _,cs_i1,_,ef_i1) = check_exp envs imp_param i1t i1 in
      let i2t = {t=Tapp("range",[TA_nexp min2;TA_nexp m_rise2])} in
      let (i2', ti2, _,cs_i2,_,ef_i2) = check_exp envs imp_param i2t i2 in
      let (e',item_t',_,cs_e,_,ef_e) =
	try check_exp envs imp_param item_t e with
	  | _ ->
	    let (base_e,rise_e) = new_n(),new_n() in
	    let (e',ti',env_e,cs_e,bs_e,ef_e) = 
	      check_exp envs imp_param {t=Tapp("vector",[TA_nexp base_e;TA_nexp rise_e;TA_ord ord;TA_typ item_t])} e 
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
      let (t,cs3,ef3,e') = 
       type_coerce (Expr l) d_env Require false false b_env nt (E_aux(E_vector_update_subrange(vec',i1',i2',e'),(l,constrained_annot  nt cs_loc))) expect_t in
      (e',t,t_env,cs3@cs@cs_i1@cs_i2@cs_loc@cs_e,nob,(union_effects ef (union_effects ef3 (union_effects ef_i1 (union_effects ef_i2 ef_e)))))
    | E_vector_append(v1,v2) -> 
      let item_t,ord = match expect_t.t with
        | Tapp("vector",[_;_;TA_ord o;TA_typ i]) -> i,o
        | Tapp("range",_) -> bit_t,new_o ()
        | _ -> new_t (),new_o () in
      let base1,rise1 = new_n(), new_n() in
      let base2,rise2 = new_n(),new_n() in
      let (v1',t1',_,cs_1,_,ef_1) = 
	check_exp envs imp_param {t=Tapp("vector",[TA_nexp base1;TA_nexp rise1;TA_ord ord;TA_typ item_t])} v1 in
      let (v2',t2',_,cs_2,_,ef_2) = 
	check_exp envs imp_param {t=Tapp("vector",[TA_nexp base2;TA_nexp rise2;TA_ord ord;TA_typ item_t])} v2 in
      let ti =  {t=Tapp("vector",[TA_nexp base1;TA_nexp {nexp = Nadd(rise1,rise2)};TA_ord ord; TA_typ item_t])} in
      let cs_loc = match ord.order with
        | Odec -> [GtEq((Expr l),Require,base1,mk_add rise1 rise2)]
        | _ -> [] in
      let (t,cs_c,ef_c,e') = 
        type_coerce (Expr l) d_env Require false false b_env ti 
	  (E_aux(E_vector_append(v1',v2'),(l,constrained_annot ti cs_loc))) expect_t in
      (e',t,t_env,cs_loc@cs_1@cs_2,nob,(union_effects ef_c (union_effects ef_1 ef_2)))
    | E_list(es) ->
      let item_t = match expect_t.t with
	| Tapp("list",[TA_typ i]) -> i
	| _ -> new_t() in
      let es,cs,effect = 
	(List.fold_right (fun (e,_,_,c,_,ef) (es,cs,effect) -> (e::es),(c@cs),union_effects ef effect) 
	   (List.map (check_exp envs imp_param item_t) es) ([],[],pure_e)) in
      let t = {t = Tapp("list",[TA_typ item_t])} in
      let t',cs',ef',e' = type_coerce (Expr l) d_env Require false false b_env t 
	(E_aux(E_list es,(l,simple_annot t))) expect_t in
      (e',t',t_env,cs@cs',nob,union_effects ef' effect)
    | E_cons(ls,i) ->
      let item_t = match expect_t.t with
	| Tapp("list",[TA_typ i]) -> i
	| _ -> new_t() in
      let lt = {t=Tapp("list",[TA_typ item_t])} in
      let (ls',t',_,cs,_,ef) = check_exp envs imp_param lt ls in
      let (i', ti, _,cs_i,_,ef_i) = check_exp envs imp_param item_t i in
      let (t',cs',ef',e') = 
	type_coerce (Expr l) d_env Require false false b_env lt (E_aux(E_cons(ls',i'),(l,simple_annot lt))) expect_t in
      (e',t',t_env,cs@cs'@cs_i,nob,union_effects ef' (union_effects ef ef_i))
    | E_record(FES_aux(FES_Fexps(fexps,_),l')) -> 
      let u,_ = get_abbrev d_env expect_t in
      let u_actual = match u.t with | Tabbrev(_, u) -> u | _ -> u in
      (match u_actual.t with
	| Tid(n) ->
	  (match lookup_record_typ n d_env.rec_env with 
	    | None -> typ_error l ("Expected a value of type " ^ n ^ " but found a struct")
	    | Some(((i,Record,fields) as r)) -> 
	      if (List.length fexps = List.length fields) 
	      then let fexps,cons,ef =
		     List.fold_right 
		       (fun (FE_aux(FE_Fexp(id,exp),(l,annot))) (fexps,cons,ef') ->
			 let i = id_to_string id in
			 match lookup_field_type i r with
			   | NoTyp -> 
			     typ_error l ("Expected a struct of type " ^ n ^ ", which should not have a field " ^ i)
                           | Overload _ ->  raise (Reporting_basic.err_unreachable l "Field given overload tannot")
			   | Base((params,et),tag,cs,ef,bounds) ->
			     let et,cs,_,_ = subst params false et cs ef in
			     let (e,t',_,c,_,ef) = check_exp envs imp_param et exp in
			     (FE_aux(FE_Fexp(id,e),(l,Base(([],t'),tag,cs@c,ef,bounds)))::fexps,cons@cs@c,union_effects ef ef'))
		       fexps ([],[],pure_e) in
		   E_aux(E_record(FES_aux(FES_Fexps(fexps,false),l')),(l,simple_annot u)),expect_t,t_env,cons,nob,ef
	      else typ_error l ("Expected a struct of type " ^ n ^ ", which should have " ^ string_of_int (List.length fields) ^ " fields")
	    | Some(i,Register,fields) -> typ_error l ("Expected a value with register type, found a struct"))
	| Tuvar _ ->
	  let field_names = List.map (fun (FE_aux(FE_Fexp(id,exp),(l,annot))) -> id_to_string id) fexps in
	  (match lookup_record_fields field_names d_env.rec_env with
	    | None -> typ_error l "No struct type matches the set of fields given"
	    | Some(((i,Record,fields) as r)) ->
	      let fexps,cons,ef =
		List.fold_right 
		  (fun (FE_aux(FE_Fexp(id,exp),(l,annot))) (fexps,cons,ef') ->
		    let i = id_to_string id in
		    match lookup_field_type i r with
		      | NoTyp -> raise (Reporting_basic.err_unreachable l "field_match didn't have a full match")
                      | Overload _ -> raise (Reporting_basic.err_unreachable l "Record given overload annot")
		      | Base((params,et),tag,cs,ef,binding) ->
			let et,cs,_,_ = subst params false et cs ef in
			let (e,t',_,c,_,ef) = check_exp envs imp_param et exp in
			(FE_aux(FE_Fexp(id,e),(l,Base(([],t'),tag,cs@c,ef,binding)))::fexps,cons@cs@c,union_effects ef ef'))
		  fexps ([],[],pure_e) in
	      expect_t.t <- Tid i; (*TODO THis should use equate_t !!*)
	      E_aux(E_record(FES_aux(FES_Fexps(fexps,false),l')),(l,simple_annot expect_t)),expect_t,t_env,cons,nob,ef
	    | Some(i,Register,fields) -> typ_error l "Expected a value with register type, found a struct")
	| _ -> typ_error l ("Expected an expression of type " ^ t_to_string expect_t ^ " but found a struct"))
    | E_record_update(exp,FES_aux(FES_Fexps(fexps,_),l')) -> 
      let (e',t',_,c,_,ef) = check_exp envs imp_param expect_t exp in
      (match t'.t with
	| Tid i | Tabbrev(_, {t=Tid i}) ->
	  (match lookup_record_typ i d_env.rec_env with
	    | None -> typ_error l ("Expected a struct for this update, instead found an expression with type " ^ i)
	    | Some((i,Register,fields)) ->
	      typ_error l "Expected a struct for this update, instead found a register"
	    | Some(((i,Record,fields) as r)) ->
	      if (List.length fexps <= List.length fields) 
	      then let fexps,cons,ef =
		     List.fold_right 
		       (fun (FE_aux(FE_Fexp(id,exp),(l,annot))) (fexps,cons,ef') ->
			 let fi = id_to_string id in
			 match lookup_field_type fi r with
			   | NoTyp -> 
			     typ_error l ("Expected a struct with type " ^ i ^ ", which does not have a field " ^ fi)
                           | Overload _ -> raise (Reporting_basic.err_unreachable l "Record given overload annot")
			   | Base((params,et),tag,cs,ef,bounds) ->
			     let et,cs,_,_ = subst params false et cs ef in
			     let (e,t',_,c,_,ef) = check_exp envs imp_param et exp in
			     (FE_aux(FE_Fexp(id,e),(l,Base(([],t'),tag,cs@c,ef,bounds)))::fexps,cons@cs@c,union_effects ef ef'))
		       fexps ([],[],pure_e) in
		   E_aux(E_record_update(e',FES_aux(FES_Fexps(fexps,false),l')), (l,simple_annot expect_t)),expect_t,t_env,cons,nob,ef
	      else typ_error l ("Expected fields from struct " ^ i ^ ", given more fields than struct includes"))
	| Tuvar _ ->
	  let field_names = List.map (fun (FE_aux(FE_Fexp(id,exp),(l,annot))) -> id_to_string id) fexps in
	  (match lookup_possible_records field_names d_env.rec_env with
	    | [] -> typ_error l "No struct matches the set of fields given for this struct update"
	    | [(((i,Record,fields) as r))] ->
	      let fexps,cons,ef =
		List.fold_right 
		  (fun (FE_aux(FE_Fexp(id,exp),(l,annot))) (fexps,cons,ef') ->
		    let i = id_to_string id in
		    match lookup_field_type i r with
		      | NoTyp -> raise (Reporting_basic.err_unreachable l "field_match didn't have a full match")
                      | Overload _ -> raise (Reporting_basic.err_unreachable l "Record given overload annot")
		      | Base((params,et),tag,cs,ef,bounds) ->
			let et,cs,_,_ = subst params false et cs ef in
			let (e,t',_,c,_,ef) = check_exp envs imp_param et exp in
			(FE_aux(FE_Fexp(id,e),(l,Base(([],t'),tag,cs@c,ef,bounds)))::fexps,cons@cs@c,union_effects ef ef'))
		  fexps ([],[],pure_e) in
	      expect_t.t <- Tid i; (*Should be equate_t*)
	      E_aux(E_record_update(e',FES_aux(FES_Fexps(fexps,false),l')), (l,simple_annot expect_t)),expect_t,t_env,cons,nob,ef
	    | [(i,Register,fields)] -> typ_error l "Expected a value with register type, found a struct"
	    | records -> typ_error l "Multiple structs contain this set of fields, try adding a cast to disambiguate")
	| _ -> typ_error l ("Expected a struct to update but found an expression of type " ^ t_to_string expect_t))
    | E_field(exp,id) ->
      let (e',t',_,c_sub,_,ef_sub) = check_exp envs imp_param (new_t()) exp in
      (match t'.t with
      | Tabbrev({t=Tid i}, t2) ->
	  (match lookup_record_typ i d_env.rec_env with
	    | None -> 
	      typ_error l ("Expected a struct or register for this access, instead found an expression with type " ^ i)
	    | Some(((i,rec_kind,fields) as r)) ->
	      let fi = id_to_string id in
	      (match lookup_field_type fi r with
		| NoTyp -> 
		  typ_error l ("Type " ^ i ^ " does not have a field " ^ fi)
                | Overload _ ->  raise (Reporting_basic.err_unreachable l "Record given overload annot")
		| Base((params,et),tag,cs,ef,bounds) ->
		  let et,cs,ef,_ = subst params false et cs ef in
		  let (et',c',ef',acc) = 
		    type_coerce (Expr l) d_env Require false false b_env et 
		      (E_aux(E_field(e',id),(l,Base(([],et),tag,cs,ef,bounds)))) expect_t in
		  (acc,et',t_env,cs@c'@c_sub,nob,union_effects ef' ef_sub)))
      | Tid i ->
	  (match lookup_record_typ i d_env.rec_env with
	    | None -> 
	      typ_error l ("Expected a struct or register for this access, instead found an expression with type " ^ i)
	    | Some(((i,rec_kind,fields) as r)) ->
	      let fi = id_to_string id in
	      (match lookup_field_type fi r with
		| NoTyp -> 
		  typ_error l ("Type " ^ i ^ " does not have a field " ^ fi)
                | Overload _ -> raise (Reporting_basic.err_unreachable l "Record given overload annot")
		| Base((params,et),tag,cs,ef,bounds) ->
		  let et,cs,ef,_ = subst params false et cs ef in
		  let (et',c',ef',acc) =
		    type_coerce (Expr l) d_env Require false false b_env et 
		      (E_aux(E_field(e',id),(l,Base(([],et),tag,cs,ef,bounds)))) expect_t in
		  (acc,et',t_env,cs@c'@c_sub,nob,union_effects ef' ef_sub)))
	| Tuvar _ ->
	  let fi = id_to_string id in
	  (match lookup_possible_records [fi] d_env.rec_env with
	    | [] -> typ_error l ("No struct has a field " ^ fi)
	    | [(((i,rkind,fields) as r))] ->
	      let fi = id_to_string id in
	      (match lookup_field_type fi r with
		| NoTyp -> 
		  raise (Reporting_basic.err_unreachable l "lookup_possible_records returned a record that didn't include the field")
                | Overload _ -> raise (Reporting_basic.err_unreachable l "Record given overload annot")
		| Base((params,et),tag,cs,ef,bounds) ->
		  let et,cs,ef,_ = subst params false et cs ef in
		  let (et',c',ef',acc) = 
		    type_coerce (Expr l) d_env Guarantee false false b_env et 
		      (E_aux(E_field(e',id),
			     (l,Base(([],et),tag,cs,ef,bounds)))) expect_t in
                  equate_t t' {t=Tid i};
		  (acc,et',t_env,cs@c'@c_sub,nob,union_effects ef' ef_sub))
	    | records -> typ_error l ("Multiple structs contain field " ^ fi ^ ", try adding a cast to disambiguate"))
	| _ -> typ_error l ("Expected a struct or register for access but found an expression of type " ^ t_to_string t'))
    | E_case(exp,pexps) ->
      (*let check_t = new_t() in*)
      let (e',t',_,cs,_,ef) = check_exp envs imp_param (new_t()) exp in
      (*let _ = Printf.eprintf "Type of pattern after expression check %s\n" (t_to_string t') in*)
      let t' = 
	match t'.t with
	  | Tapp("register",[TA_typ t]) -> t
	  | _ -> t' in
      (*let _ = Printf.eprintf "Type of pattern after register check %s\n" (t_to_string t') in*)
      let (pexps',t,cs',ef') = check_cases envs imp_param t' expect_t pexps in
      (E_aux(E_case(e',pexps'),(l,simple_annot t)),t,t_env,cs@cs',nob,union_effects ef ef')
    | E_let(lbind,body) -> 
      let (lb',t_env',cs,b_env',ef) = (check_lbind envs imp_param false Emp_local lbind) in
      let new_env = 
	(Env(d_env,Envmap.union_merge (tannot_merge (Expr l) d_env false) t_env t_env', merge_bounds b_env' b_env,tp_env)) 
      in
      let (e,t,_,cs',_,ef') = check_exp new_env imp_param expect_t body in
      (E_aux(E_let(lb',e),(l,simple_annot t)),t,t_env,cs@cs',nob,union_effects ef ef')
    | E_assign(lexp,exp) ->
      let (lexp',t',_,t_env',tag,cs,b_env',ef) = check_lexp envs imp_param true lexp in
      let (exp',t'',_,cs',_,ef') = check_exp envs imp_param t' exp in
      let (t',c') = type_consistent (Expr l) d_env Require false unit_t expect_t in
      (*let _ = Printf.eprintf "Constraints for E_assign %s\n" (constraints_to_string (cs@cs'@c')) in*)
      (E_aux(E_assign(lexp',exp'),(l,(Base(([],unit_t),tag,[],ef,nob)))),unit_t,t_env',cs@cs'@c',b_env',union_effects ef ef')
    | E_exit e ->
      let (e',t',_,_,_,_) = check_exp envs imp_param (new_t ()) e in
      (E_aux (E_exit e',(l,(simple_annot expect_t))),expect_t,t_env,[],nob,pure_e)
    | E_internal_cast _ | E_internal_exp _ -> raise (Reporting_basic.err_unreachable l "Internal expression passed back into type checker")
		    
and check_block envs imp_param expect_t exps:((tannot exp) list * tannot * nexp_range list * t * effect) =
  let Env(d_env,t_env,b_env,tp_env) = envs in
  match exps with
    | [] -> ([],NoTyp,[],unit_t,pure_e)
    | [e] -> 
      let (E_aux(e',(l,annot)),t,envs,sc,_,ef) = check_exp envs imp_param expect_t e in
      ([E_aux(e',(l,annot))],annot,sc,t,ef)
    | e::exps -> 
      let (e',t',t_env',sc,b_env',ef') = check_exp envs imp_param unit_t e in
      let (exps',annot',sc',t,ef) = 
        check_block (Env(d_env,
			 Envmap.union_merge (tannot_merge (Expr Parse_ast.Unknown) d_env false) t_env t_env',
			 merge_bounds b_env' b_env, tp_env)) imp_param expect_t exps in
      ((e'::exps'),annot',sc@sc',t,union_effects ef ef')

and check_cases envs imp_param check_t expect_t pexps : ((tannot pexp) list * typ * nexp_range list * effect) =
  let (Env(d_env,t_env,b_env,tp_env)) = envs in
  match pexps with
    | [] -> raise (Reporting_basic.err_unreachable Parse_ast.Unknown "switch with no cases found")
    | [(Pat_aux(Pat_exp(pat,exp),(l,annot)))] ->
      let pat',env,cs_p,bounds,u = check_pattern envs Emp_local check_t pat in
      let e,t,_,cs_e,_,ef = 
	check_exp (Env(d_env,
		       Envmap.union_merge (tannot_merge (Expr l) d_env true) t_env env,
		       merge_bounds b_env bounds, tp_env)) imp_param expect_t exp in
      let cs = [CondCons(Expr l, cs_p, cs_e)] in
      [Pat_aux(Pat_exp(pat',e),(l,cons_ef_annot t cs ef))],t,cs,ef
    | ((Pat_aux(Pat_exp(pat,exp),(l,annot)))::pexps) ->
      let pat',env,cs_p,bounds,u = check_pattern envs Emp_local check_t pat in
      let (e,t,_,cs_e,_,ef) = 
	check_exp (Env(d_env,
		       Envmap.union_merge (tannot_merge (Expr l) d_env true) t_env env,
		       merge_bounds b_env bounds, tp_env)) imp_param expect_t exp in
      let cs = CondCons(Expr l,cs_p,cs_e) in
      let (pes,tl,csl,efl) = check_cases envs imp_param check_t expect_t pexps in      
      ((Pat_aux(Pat_exp(pat',e),(l,cons_ef_annot t [cs] ef)))::pes,tl,cs::csl,union_effects efl ef)

and check_lexp envs imp_param is_top (LEXP_aux(lexp,(l,annot))) 
    : (tannot lexp * typ * bool * tannot emap * tag * nexp_range list * bounds_env * effect ) =
  let (Env(d_env,t_env,b_env,tp_env)) = envs in
  match lexp with
    | LEXP_id id -> 
      let i = id_to_string id in
      (match Envmap.apply t_env i with
	(*TODO Should change this to use the default as the expected type*)
	| Some(Base((parms,t),Default,_,_,_)) ->
	  typ_error l ("Identifier " ^ i ^ " cannot be assigned when only a default specification exists")
        | Some(Base(([],t),Alias,_,_,_)) ->
	  let ef = {effect = Eset[BE_aux(BE_wreg,l)]} in
          (match Envmap.apply d_env.alias_env i with
            | Some(OneReg(reg, (Base(([],t'),_,_,_,_)))) ->
              (LEXP_aux(lexp,(l,(Base(([],t'),Alias,[],ef,nob)))), t, false, Envmap.empty, External (Some reg),[],nob,ef)
            | Some(TwoReg(reg1,reg2, (Base(([],t'),_,_,_,_)))) ->
	      let u = match t.t with
		| Tapp("register", [TA_typ u]) -> u in
              (LEXP_aux(lexp,(l,Base(([],t'),Alias,[],ef,nob))), u, false, Envmap.empty, External None,[],nob,ef)
            | _ -> assert false)
	| Some(Base((parms,t),tag,cs,_,b)) ->
	  let t,cs,_,_ = 
	    match tag with | External _ | Emp_global -> subst parms false t cs pure_e | _ -> t,cs,pure_e,Envmap.empty
	  in
	  let t,cs' = get_abbrev d_env t in
          let t_actual = match t.t with | Tabbrev(i,t) -> t | _ -> t in
	  let cs_o = cs@cs' in
          (*let _ = Printf.eprintf "Assigning to %s, t is %s\n" i (t_to_string t_actual) in*)
	  (match t_actual.t,is_top with
	    | Tapp("register",[TA_typ u]),_ ->
	      let ef = {effect=Eset[BE_aux(BE_wreg,l)]} in
	      (LEXP_aux(lexp,(l,(Base(([],t),External (Some i),cs_o,ef,nob)))),u,false,
	       Envmap.empty,External (Some i),[],nob,ef)
	    | Tapp("reg",[TA_typ u]),_ ->
	      (LEXP_aux(lexp,(l,(Base(([],t),Emp_local,cs_o,pure_e,b)))),u,false,
	       Envmap.empty,Emp_local,[],nob,pure_e)
	    | Tapp("vector",_),false ->
	      (LEXP_aux(lexp,(l,(Base(([],t),tag,cs_o,pure_e,b)))),t,true,Envmap.empty,Emp_local,[],nob,pure_e)
	    | (Tfn _ ,_) ->
	      (match tag with 
		| External _ | Spec | Emp_global -> 
		  let u = new_t() in
		  let t = {t = Tapp("reg",[TA_typ u])} in
		  let bounds = extract_bounds d_env i t in
		  let tannot = (Base(([],t),Emp_local,[],pure_e,bounds)) in
		  (LEXP_aux(lexp,(l,tannot)),u,false,Envmap.from_list [i,tannot],Emp_local,[],bounds,pure_e)
		| _ -> 
		  typ_error l ("Cannot assign to " ^ i ^" with type " ^ t_to_string t ^ 
				  ". Assignment must be to registers or non-parameter, non-let-bound local variables."))
	    | _,_ -> 
	      if is_top
	      then 
		typ_error l ("Cannot assign to " ^ i ^" with type " ^ t_to_string t ^ 
				". Assignment must be to registers or non-parameter, non-let-bound local variables.")
	      else 
		(LEXP_aux(lexp,(l,constrained_annot t cs_o)),t,true,Envmap.empty,Emp_local,[],nob,pure_e))
	| _ -> 
	  let u = new_t() in
	  let t = {t=Tapp("reg",[TA_typ u])} in
	  let bounds = extract_bounds d_env i u in
	  let tannot = (Base(([],t),Emp_local,[],pure_e,bounds)) in
	  (LEXP_aux(lexp,(l,tannot)),u,false,Envmap.from_list [i,tannot],Emp_local,[],bounds,pure_e))
    | LEXP_memory(id,exps) -> 
      let i = id_to_string id in
      (match Envmap.apply t_env i with
	| Some(Base((parms,t),tag,cs,ef,_)) ->
	  let is_external = match tag with | External any -> true | _ -> false in
	  let t,cs,ef,_ = subst parms false t cs ef in
	  (match t.t with
	    | Tfn(apps,out,_,ef') ->
	      (match ef'.effect with
		| Eset effects ->
                  let mem_write = List.exists (fun (BE_aux(b,_)) -> match b with | BE_wmem -> true | _ -> false) effects in
                  let reg_write = List.exists (fun (BE_aux(b,_)) -> match b with | BE_wreg -> true | _ -> false) effects in
		  if  (mem_write || reg_write)
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
			    | [],[e] -> let (e',_,_,cs_e,_,ef_e) = check_exp envs imp_param unit_t e in ([e'],cs_e,ef_e)
			    | [],es -> typ_error l ("Expected no arguments for assignment function " ^ i)
			    | args,[] -> 
			      typ_error l ("Expected arguments with types " ^ (t_to_string args_t) ^
					   "for assignment function " ^ i)
			    | args,es -> 
			      (match check_exp envs imp_param args_t (E_aux (E_tuple exps,(l,NoTyp))) with
				| (E_aux(E_tuple es,(l',tannot)),_,_,cs_e,_,ef_e) -> (es,cs_e,ef_e)
				| _ -> 
				  raise (Reporting_basic.err_unreachable l 
					   "Gave check_exp a tuple, didn't get a tuple back"))
			in
			let ef_all = union_effects ef' ef_es in
			(LEXP_aux(LEXP_memory(id,es),(l,Base(([],out),tag,cs_call,ef',nob))),
			 item_t,false,Envmap.empty,tag,cs_call@cs_es,nob,ef_all)
		      | _ -> 
			let e = match exps with
			  | [] -> E_aux(E_lit(L_aux(L_unit,l)),(l,NoTyp))
			  | [(E_aux(E_lit(L_aux(L_unit,_)),(_,NoTyp)) as e)] -> e
			  | es -> typ_error l ("Expected no arguments for assignment function " ^ i) in
			let (e,_,_,cs_e,_,ef_e) = check_exp envs imp_param apps e in
			let ef_all = union_effects ef ef_e in
			(LEXP_aux(LEXP_memory(id,[e]),(l,Base(([],out),tag,cs_call,ef,nob))),
			 app,false,Envmap.empty,tag,cs_call@cs_e,nob,ef_all))
		  else typ_error l ("Assignments require functions with a wmem or wreg effect")
		| _ -> typ_error l ("Assignments require functions with a wmem or wreg effect"))
	    | _ -> typ_error l ("Assignments require a function here, found " ^ i ^ " which has type " ^ (t_to_string t)))
	| _ -> typ_error l ("Unbound identifier " ^ i))
    | LEXP_cast(typ,id) -> 
      let i = id_to_string id in
      let ty = typ_to_t false false typ in
      let ty = typ_subst tp_env false ty in
      let new_bounds = extract_bounds d_env i ty in
      (match Envmap.apply t_env i with
	| Some(Base((parms,t),tag,cs,_,bounds)) ->
	  let t,cs,_,_ = 
	    match tag with | External _ | Emp_global -> subst parms false t cs pure_e | _ -> t,cs,pure_e,Envmap.empty
	  in
	  let t,cs' = get_abbrev d_env t in
          let t_actual = match t.t with | Tabbrev(_,t) -> t | _ -> t in
	  let bs = merge_bounds bounds new_bounds in
	  (match t_actual.t,is_top with
	    | Tapp("register",[TA_typ u]),_ ->
	      let t',cs = type_consistent (Expr l) d_env Require false ty u in
	      let ef = {effect=Eset[BE_aux(BE_wreg,l)]} in
	      (LEXP_aux(lexp,(l,(Base(([],t),External (Some i),cs,ef,nob)))),ty,false,
	       Envmap.empty,External (Some i),[],nob,ef)
	    | Tapp("reg",[TA_typ u]),_ ->
	      let t',cs = type_consistent (Expr l) d_env Require false ty u in
	      (LEXP_aux(lexp,(l,(Base(([],t),Emp_local,cs,pure_e,bs)))),ty,false,
	       Envmap.empty,Emp_local,[],bs,pure_e)
	    | Tapp("vector",_),false ->
	      (LEXP_aux(lexp,(l,(Base(([],t),Emp_local,cs,pure_e,bs)))),ty,true,Envmap.empty,Emp_local,[],bs,pure_e)
	    | Tuvar _,_ ->
	      let u' = {t=Tapp("reg",[TA_typ ty])} in
	      equate_t t u';
	      (LEXP_aux(lexp,(l,(Base((([],u'),Emp_local,cs,pure_e,bs))))),ty,false,Envmap.empty,Emp_local,[],bs,pure_e)
	    | (Tfn _ ,_) ->
	      (match tag with 
		| External _ | Spec | Emp_global -> 
		  let tannot = (Base(([],ty),Emp_local,[],pure_e,new_bounds)) in
		  (LEXP_aux(lexp,(l,tannot)),ty,false,Envmap.from_list [i,tannot],Emp_local,[],new_bounds,pure_e)
		| _ -> 
		  typ_error l ("Cannot assign to " ^ i ^ " with type " ^ t_to_string t)) 
	    | _,_ -> 
	      if is_top
	      then typ_error l 
		("Cannot assign to " ^ i ^ " with type " ^ t_to_string t ^
		    ". May only assign to registers, and non-paremeter, non-let bound local variables")
	      else 
		(* TODO, make sure this is a record *)
		(LEXP_aux(lexp,(l,(Base(([],t),Emp_local,cs,pure_e,nob)))),ty,false,Envmap.empty,Emp_local,[],nob,pure_e))
	| _ -> 
	  let t = {t=Tapp("reg",[TA_typ ty])} in
	  let tannot = (Base(([],t),Emp_local,[],pure_e,new_bounds)) in
	  (LEXP_aux(lexp,(l,tannot)),ty,false,Envmap.from_list [i,tannot],Emp_local,[],new_bounds,pure_e))
    | LEXP_vector(vec,acc) -> 
      let (vec',vec_t,reg_required,env,tag,csi,bounds,ef) = check_lexp envs imp_param false vec in
      let vec_t,cs' = get_abbrev d_env vec_t in
      let vec_actual = match vec_t.t with | Tabbrev(_,t) -> t | _ -> vec_t in
      (match vec_actual.t with
	| Tapp("vector",[TA_nexp base;TA_nexp rise;TA_ord ord;TA_typ item_t]) ->
	  let acc_t = match ord.order with
	    | Oinc -> {t = Tapp("range",[TA_nexp base;TA_nexp (mk_sub (mk_add base rise) n_one)])} 
	    | Odec -> {t = Tapp("range",[TA_nexp (mk_sub rise (mk_add base n_one)); TA_nexp base])}
	    | _ -> typ_error l ("Assignment to one vector element requires a non-polymorphic order")
	  in
	  let (e,acc_t',_,cs',_,ef_e) = check_exp envs imp_param acc_t acc in
	  let item_t,add_reg_write,reg_still_required = 
	    match item_t.t with
	      | Tapp("register",[TA_typ t]) | Tabbrev(_,{t=Tapp("register",[TA_typ t])}) -> t,true,false
	      | Tapp("reg",[TA_typ t]) -> t,false,false
	      | _ -> item_t,false,true in
	  let ef = if add_reg_write then add_effect (BE_aux(BE_wreg,l)) ef else ef in
	  if is_top && reg_still_required && reg_required
	  then typ_error l "Assignment expected a register or non-parameter non-letbound identifier to mutate"
	  else
	    (LEXP_aux(LEXP_vector(vec',e),(l,Base(([],item_t),tag,csi,ef,nob))),item_t,reg_required && reg_still_required,
	     env,tag,csi@cs',bounds,union_effects ef ef_e)
	| Tuvar _ -> 
	  typ_error l "Assignment expected a vector with a known order, try adding an annotation."
	| _ -> typ_error l ("Assignment expected vector, found assignment to type " ^ (t_to_string vec_t))) 
    | LEXP_vector_range(vec,e1,e2)-> 
      let (vec',item_t,reg_required,env,tag,csi,bounds,ef) = check_lexp envs imp_param false vec in
      let item_t,cs = get_abbrev d_env item_t in
      let item_actual = match item_t.t with | Tabbrev(_,t) -> t | _ -> item_t in
      let item_actual,add_reg_write,reg_still_required,cs = 
	match item_actual.t with
	  | Tapp("register",[TA_typ t]) ->
	    (match get_abbrev d_env t with | {t=Tabbrev(_,t)},cs' | t,cs' -> t,true,false,cs@cs')
	  | Tapp("reg",[TA_typ t]) ->
	    (match get_abbrev d_env t with | {t=Tabbrev(_,t)},cs' | t,cs' -> t,false,false,cs@cs')
	  | _ -> item_actual,false,true,cs in
      (match item_actual.t with
	| Tapp("vector",[TA_nexp base;TA_nexp rise;TA_ord ord;TA_typ t]) ->
	  let base_e1,range_e1,base_e2,range_e2 = new_n(),new_n(),new_n(),new_n() in
	  let base_t = {t=Tapp("range",[TA_nexp base_e1;TA_nexp range_e1])} in
	  let range_t = {t=Tapp("range",[TA_nexp base_e2;TA_nexp range_e2])} in
	  let (e1',base_t',_,cs1,_,ef_e) = check_exp envs imp_param base_t e1 in
	  let (e2',range_t',_,cs2,_,ef_e') = check_exp envs imp_param range_t e2 in
	  let base_e1,range_e1,base_e2,range_e2 = match base_t'.t,range_t'.t with
	    | (Tapp("range",[TA_nexp base_e1;TA_nexp range_e1]),
	       Tapp("range",[TA_nexp base_e2;TA_nexp range_e2])) -> base_e1,range_e1,base_e2,range_e2
	    | _ -> base_e1,range_e1,base_e2,range_e2 in
          let len = new_n() in
	  let needs_reg = match t.t with
	    | Tapp("reg",_) -> false
	    | Tapp("register",_) -> false
	    | _ -> true in
	  let cs_t,res_t = match ord.order with
	    | Oinc ->  ([LtEq((Expr l),Require,base,base_e1);
			 LtEq((Expr l),Require,mk_add base_e1 range_e1, mk_add base_e2 range_e2);
			 LtEq((Expr l),Require,mk_add base_e1 range_e2, mk_add base rise);
                         LtEq((Expr l),Require,len, mk_sub (mk_add (mk_add base_e2 range_e2) n_one) 
			                                   (mk_add base_e1 range_e1))],
			{t=Tapp("vector",[TA_nexp base_e1;TA_nexp len;TA_ord ord;TA_typ t])})
	    | Odec -> ([GtEq((Expr l),Require,base,base_e1);
			GtEq((Expr l),Require,mk_add base_e1 range_e1,mk_add base_e2 range_e2);
			GtEq((Expr l),Require,mk_add base_e1 range_e2,mk_sub base rise);                         
                        LtEq((Expr l),Require,len, mk_sub (mk_add (mk_add base_e2 range_e2) n_one)
			                                  (mk_add base_e1 range_e1));],
                       {t=Tapp("vector",[TA_nexp {nexp=Nadd(base_e1,range_e1)};TA_nexp len;TA_ord ord; TA_typ t])})
	    | _ -> typ_error l ("Assignment to a range of vector elements requires either inc or dec order")
	  in
	  let cs = cs_t@cs@cs1@cs2 in
	  let ef = union_effects ef (union_effects ef_e ef_e') in
	  if is_top && reg_required && reg_still_required && needs_reg 
	  then typ_error l "Assignment requires a register or a non-parameter, non-letbound local identifier"
	  else (LEXP_aux(LEXP_vector_range(vec',e1',e2'),(l,Base(([],item_t),tag,cs,ef,nob))),res_t,reg_required&&reg_still_required && needs_reg
		,env,tag,cs,bounds,ef)
	| Tuvar _ -> typ_error l "Assignement to a range of elements requires a vector with a known order, try adding an annotation."
	| _ -> typ_error l ("Assignment expected vector, found assignment to type " ^ (t_to_string item_t))) 
    | LEXP_field(vec,id)-> 
      let (vec',item_t,reg_required,env,tag,csi,bounds,ef) = check_lexp envs imp_param false vec in
      let vec_t = match vec' with
        | LEXP_aux(_,(l',Base((parms,t),_,_,_,_))) -> t
        | _ -> item_t in
      (match vec_t.t with
	| Tid i | Tabbrev({t=Tid i},_) ->
	  (match lookup_record_typ i d_env.rec_env with
	    | None -> 
	      typ_error l ("Expected a register or struct for this update, instead found an expression with type " ^ i)
            | Some(((i,rec_kind,fields) as r)) ->
	      let fi = id_to_string id in
	      (match lookup_field_type fi r with
		| NoTyp -> 
		  typ_error l ("Type " ^ i ^ " does not have a field " ^ fi)
                | Overload _ -> raise (Reporting_basic.err_unreachable l "Record given overload annot")
		| Base((params,et),_,cs,_,_) ->
		  let et,cs,ef,_ = subst params false et cs ef in
		  (LEXP_aux(LEXP_field(vec',id),(l,(Base(([],et),tag,csi@cs,ef,nob)))),et,false,env,tag,csi@cs,bounds,ef)))
	| _ -> typ_error l ("Expected a register binding here, found " ^ (t_to_string item_t)))

and check_lbind envs imp_param is_top_level emp_tag (LB_aux(lbind,(l,annot))) : tannot letbind * tannot emap * nexp_range list * bounds_env * effect =
  let Env(d_env,t_env,b_env,tp_env) = envs in
  match lbind with
  | LB_val_explicit(typ,pat,e) -> 
    let tan = typschm_to_tannot envs false false typ emp_tag in
    (match tan with
    | Base((params,t),tag,cs,ef,b) ->
      let t,cs,ef,tp_env' = subst params false t cs ef in
      let envs' = (Env(d_env,t_env,b_env,Envmap.union tp_env tp_env')) in
      let (pat',env,cs1,bounds,u) = check_pattern envs' emp_tag t pat in
      let (e,t,_,cs2,_,ef2) = check_exp envs' imp_param t e in
      let cs = if is_top_level then resolve_constraints cs@cs1@cs2 else cs@cs1@cs2 in
      let ef = union_effects ef ef2 in
      (*let _ = Printf.eprintf "checking tannot in let1\n" in*)
      let tannot = if is_top_level 
	then check_tannot l (Base((params,t),tag,cs,ef,bounds)) None cs ef (*in top level, must be pure_e*) 
	else (Base ((params,t),tag,cs,ef,bounds))
      in
      (*let _ = Printf.eprintf "done checking tannot in let1\n" in*)
      (LB_aux (LB_val_explicit(typ,pat',e),(l,tannot)),env,cs,merge_bounds b_env bounds,ef)
    | NoTyp | Overload _ -> raise (Reporting_basic.err_unreachable l "typschm_to_tannot failed to produce a Base"))
  | LB_val_implicit(pat,e) -> 
    let t = new_t () in
    let (pat',env,cs1,bounds,u) = check_pattern envs emp_tag (new_t ()) pat in
    let (e,t',_,cs2,_,ef) = check_exp envs imp_param u e in
    let cs = if is_top_level then resolve_constraints cs1@cs2 else cs1@cs2 in
    (*let _ = Printf.eprintf "checking tannot in let2\n" in*)
    let tannot = 
      if is_top_level then check_tannot l (Base(([],t'),emp_tag,cs,ef,bounds)) None cs ef (* see above *)
      else (Base (([],t'),emp_tag,cs,ef,merge_bounds bounds b_env))
    in
    (*let _ = Printf.eprintf "done checking tannot in let2\n" in*)
    (LB_aux (LB_val_implicit(pat',e),(l,tannot)), env,cs,merge_bounds bounds b_env,ef)

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
      let (params,typarms,constraints) = typq_to_params envs typq in
      let ty = match typarms with | [] -> {t = Tid id'} | parms -> {t = Tapp(id',parms)} in
      let tyannot = Base((params,ty),Emp_global,constraints,pure_e,nob) in
      (*TODO This should create some bindings*)
      let fields' = List.map 
	(fun (ty,i)->(id_to_string i),Base((params,(typ_to_t false false ty)),Emp_global,constraints,pure_e,nob)) fields in
      (TD_aux(td,(l,tyannot)),Env({d_env with rec_env = (id',Record,fields')::d_env.rec_env},t_env,b_env,tp_env))
    | TD_variant(id,nmscm,typq,arms,_) ->
      let id' = id_to_string id in
      let (params,typarms,constraints) = typq_to_params envs typq in
      let ty = match params with
        | [] -> {t=Tid id'} 
        | params -> {t = Tapp(id', typarms) }in
      let tyannot = Base((params,ty),Constructor,constraints,pure_e,nob) in
      let arm_t input = Base((params,{t=Tfn(input,ty,IP_none,pure_e)}),Constructor,constraints,pure_e,nob) in
      let arms' = List.map 
	(fun (Tu_aux(tu,l')) -> 
	  match tu with 
	    | Tu_id i -> ((id_to_string i),(arm_t unit_t))
	    | Tu_ty_id(typ,i)-> ((id_to_string i),(arm_t (typ_to_t false false typ))))
	arms in
      let t_env = List.fold_right (fun (id,tann) t_env -> Envmap.insert t_env (id,tann)) arms' t_env in
      (TD_aux(td,(l,tyannot)),(Env (d_env,t_env,b_env,tp_env)))
    | TD_enum(id,nmscm,ids,_) -> 
      let id' = id_to_string id in
      let ids' = List.map id_to_string ids in
      let max = (List.length ids') -1 in
      let ty = Base (([],{t = Tid id' }),Enum max,[],pure_e,nob) in
      let t_env = List.fold_right (fun id t_env -> Envmap.insert t_env (id,ty)) ids' t_env in
      let enum_env = Envmap.insert d_env.enum_env (id',ids') in
      (TD_aux(td,(l,ty)),Env({d_env with enum_env = enum_env;},t_env,b_env,tp_env))
    | TD_register(id,base,top,ranges) -> 
      let id' = id_to_string id in
      let basei = normalize_nexp(anexp_to_nexp base) in
      let topi = normalize_nexp(anexp_to_nexp top) in
      match basei.nexp,topi.nexp with
	| Nconst b, Nconst t -> 
	  if (le_big_int b t) then (
	    let ty = {t = Tapp("vector",[TA_nexp basei; TA_nexp{nexp=Nconst(add_big_int (sub_big_int t b) (big_int_of_int 1))}; 
					 TA_ord({order = Oinc}); TA_typ({t = Tid "bit"});])} in
	    let franges = 
	      List.map 
		(fun ((BF_aux(idx,l)),id) ->
		  ((id_to_string id),
		   Base(([],
			match idx with
			  | BF_single i -> 
			    if (le_big_int b (big_int_of_int i)) && (le_big_int (big_int_of_int i) t) 
			    then {t = Tid "bit"}
			    else typ_error l ("register type declaration " ^ id' ^ " contains a field specification outside of the declared register size")
			  | BF_range(i1,i2) -> 
			    if i1<i2 
			    then if (le_big_int b (big_int_of_int i1)) && (le_big_int (big_int_of_int i2) t) 
			      then {t=Tapp("vector",[TA_nexp {nexp=Nconst (big_int_of_int i1)};
                                                     TA_nexp {nexp=Nconst (big_int_of_int ((i2 - i1) +1))}; TA_ord({order=Oinc}); TA_typ {t=Tid "bit"}])}
			      else typ_error l ("register type declaration " ^ id' ^ " contains a field specification outside of the declared register size")
			    else typ_error l ("register type declaration " ^ id' ^ " is not consistently increasing")
			  | BF_concat _ -> assert false (* TODO: This implies that the variable refers to a concatenation of the different ranges specified; so now I need to implement it thusly*)),Emp_global,[],pure_e,nob)))
		ranges 
	    in
	    let tannot = into_register d_env (Base(([],ty),Emp_global,[],pure_e,nob)) in
	    (TD_aux(td,(l,tannot)),
	     Env({d_env with rec_env = ((id',Register,franges)::d_env.rec_env);
	       abbrevs = Envmap.insert d_env.abbrevs (id',tannot)},t_env,b_env,tp_env)))
	  else (
	    let ty = {t = Tapp("vector",[TA_nexp basei; TA_nexp{nexp=Nconst(add_big_int (sub_big_int b t) one)}; 
					 TA_ord({order = Odec}); TA_typ({t = Tid "bit"});])} in
	    let franges = 
	      List.map 
		(fun ((BF_aux(idx,l)),id) ->
		  ((id_to_string id),
		   Base(([],
			 match idx with
			   | BF_single i -> 
			     if (ge_big_int b (big_int_of_int i)) && (ge_big_int (big_int_of_int i) t) 
			     then {t = Tid "bit"}
			     else typ_error l ("register type declaration " ^ id' ^ " contains a field specification outside of the declared register size")
			   | BF_range(i1,i2) -> 
			     if i1>i2 
			     then if (ge_big_int b (big_int_of_int i1)) && (ge_big_int (big_int_of_int i2) t) 
			       then {t = Tapp("vector",[TA_nexp {nexp=Nconst (big_int_of_int i1)};
							TA_nexp {nexp=Nconst (big_int_of_int ((i1 - i2) + 1))};
							TA_ord({order = Odec}); TA_typ({t = Tid "bit"})])}
			       else typ_error l ("register type declaration " ^ id' ^ " contains a field specification outside of the declared register size")
			     else typ_error l ("register type declaration " ^ id' ^ " is not consistently decreasing")
			   | BF_concat _ -> assert false (* What is this supposed to imply again?*)),
			Emp_global,[],pure_e,nob)))
		ranges 
	    in
	    let tannot = into_register d_env (Base(([],ty),Emp_global,[],pure_e,nob)) in
	    (TD_aux(td,(l,tannot)),
	     Env({d_env with rec_env = (id',Register,franges)::d_env.rec_env;
	       abbrevs = Envmap.insert d_env.abbrevs (id',tannot)},t_env,b_env,tp_env)))
	| _,_ -> raise (Reporting_basic.err_unreachable l "Nexps in register declaration do not evaluate to constants")

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
  (*let _ = Printf.printf "checking fundef\n" in*)
  let Env(d_env,t_env,b_env,tp_env) = envs in
  let _ = reset_fresh () in
  let is_rec = match recopt with
              | Rec_aux(Rec_nonrec,_) -> false
	      | Rec_aux(Rec_rec,_) -> true in
  let Some(id) = List.fold_right 
    (fun (FCL_aux((FCL_Funcl(id,pat,exp)),(l,annot))) id' ->
      match id' with
	| Some(id') -> if id' = id_to_string id then Some(id') 
	  else typ_error l ("Function declaration expects all definitions to have the same name, " 
			    ^ id_to_string id ^ " differs from other definitions of " ^ id')
	| None -> Some(id_to_string id)) funcls None in
  let in_env = Envmap.apply t_env id in 
  let typ_params = match in_env with
    | Some(Base( (params,u),Spec,constraints,eft,_)) -> params
    | _ -> [] in
  let ret_t,param_t,tannot,t_param_env = match tannotopt with
    | Typ_annot_opt_aux(Typ_annot_opt_some(typq,typ),l') ->
      let (ids,_,constraints) = typq_to_params envs typq in
      let t = typ_to_t false false typ in
      let t,constraints,_,t_param_env = subst (if ids=[] then typ_params else ids) true t constraints pure_e in
      let p_t = new_t () in
      let ef = new_e () in
      t,p_t,Base((ids,{t=Tfn(p_t,t,IP_none,ef)}),Emp_global,constraints,ef,nob),t_param_env in
  let check t_env tp_env imp_param =
    List.split
      (List.map (fun (FCL_aux((FCL_Funcl(id,pat,exp)),(l,_))) ->
	(*let _ = Printf.eprintf "checking function %s : %s -> %s\n" (id_to_string id) (t_to_string param_t) (t_to_string ret_t) in*)
	let (pat',t_env',cs_p,b_env',t') = check_pattern (Env(d_env,t_env,b_env,tp_env)) Emp_local param_t pat in
	let t', _ = type_consistent (Patt l) d_env Require false param_t t' in
	let exp',_,_,cs_e,_,ef = 
	  check_exp (Env(d_env,Envmap.union_merge (tannot_merge (Expr l) d_env true) t_env t_env', 
			 merge_bounds b_env b_env',tp_env)) imp_param ret_t exp in
	(*let _ = Printf.eprintf "checked function %s : %s -> %s\n" (id_to_string id) (t_to_string param_t) (t_to_string ret_t) in
	let _ = Printf.eprintf "constraints were %s\n" (constraints_to_string (cs_p@cs_e)) in*)
	let cs = [CondCons(Fun l,cs_p,cs_e)] in
	(FCL_aux((FCL_Funcl(id,pat',exp')),(l,(Base(([],ret_t),Emp_global,cs,ef,nob)))),(cs,ef))) funcls) in
  let update_pattern var (FCL_aux ((FCL_Funcl(id,(P_aux(pat,t)),exp)),annot)) = 
    let pat' = match pat with
      | P_lit (L_aux (L_unit,l')) -> P_aux(P_id (Id_aux (Id var, l')), t)
      | P_tup pats -> P_aux(P_tup ((P_aux (P_id (Id_aux (Id var, l)), t))::pats), t)
      | _ ->  P_aux(P_tup [(P_aux (P_id (Id_aux (Id var,l)), t));(P_aux(pat,t))], t)
    in (FCL_aux ((FCL_Funcl(id,pat',exp)),annot))
  in
  match (in_env,tannot) with
    | Some(Base( (params,u),Spec,constraints,eft,_)), Base( (p',t),_,c',eft',_) ->
      (*let _ = Printf.eprintf "Function %s is in env\n" id in*)
      let u,constraints,eft,t_param_env_spec = subst params true u constraints eft in
      let t_param_cs = type_param_consistent l t_param_env_spec t_param_env in
      let _,cs_decs = type_consistent (Specc l) d_env Require false t u in
      (*let _ = Printf.eprintf "valspec consistent with declared type for %s, %s ~< %s with %s derived constraints and %s stated and %s from environment consistency\n" id (t_to_string t) (t_to_string u) (constraints_to_string cs_decs) (constraints_to_string (constraints@c')) (constraints_to_string t_param_cs) in*)
      let imp_param = match u.t with 
	| Tfn(_,_,IP_user n,_) -> Some n
	| _ -> None in
      let t_env = if is_rec then t_env else Envmap.remove t_env id in
      let funcls,cs_ef = check t_env t_param_env_spec imp_param in
      let cs,ef = ((fun (cses,efses) -> 
	(List.concat cses),(List.fold_right union_effects efses pure_e)) (List.split cs_ef)) in
      let cs' = resolve_constraints (cs@cs_decs@constraints@c'@t_param_cs) in
      (*let _ = Printf.eprintf "remaining constraints are: %s\n" (constraints_to_string cs') in*)
      let tannot = check_tannot l tannot imp_param cs' ef in
     (*let _ = Printf.eprintf "check_tannot ok for %s val type %s derived type %s \n" id (t_to_string u) (t_to_string t) in*)
      let funcls = match imp_param with
	| Some {nexp = Nvar i} -> List.map (update_pattern i) funcls 
	| _ -> funcls
      in
      (*let _ = Printf.eprintf "done funcheck case 1\n" in*)
      (FD_aux(FD_function(recopt,tannotopt,effectopt,funcls),(l,tannot))),
      Env(d_env,Envmap.insert t_env (id,tannot),b_env,tp_env)
    | _ , _-> 
      let t_env = if is_rec then Envmap.insert t_env (id,tannot) else t_env in
      let funcls,cs_ef = check t_env t_param_env None in
      let cs,ef = ((fun (cses,efses) -> (List.concat cses),(List.fold_right union_effects efses pure_e)) (List.split cs_ef)) in
      let cs' = resolve_constraints cs in
      (*let _ = Printf.eprintf "checking tannot for %s 2  remaining constraints are %s\n" id (constraints_to_string cs') in*)
      let tannot = check_tannot l tannot None cs' ef in
      (*let _ = Printf.eprintf "done funcheck case2\n" in*)
      (FD_aux(FD_function(recopt,tannotopt,effectopt,funcls),(l,tannot))),
      Env(d_env,(if is_rec then t_env else Envmap.insert t_env (id,tannot)),b_env,tp_env)

(*TODO Only works for inc vectors, need to add support for dec*)
let check_alias_spec envs alias (AL_aux(al,(l,annot))) e_typ =
  let (Env(d_env,t_env,b_env,tp_env)) = envs in
  let check_reg (RI_aux ((RI_id (Id_aux(_,l) as id)), _)) : (string * tannot reg_id * typ * typ) =
    let i = id_to_string id in
    (match Envmap.apply t_env i with
      | Some(Base(([],t), External (Some j), [], _,_)) ->
	let t,_ = get_abbrev d_env t in
        let t_actual,t_id = match t.t with 
          | Tabbrev(i,t) -> t,i
          | _ -> t,t in
	(match t_actual.t with 
	  | Tapp("register",[TA_typ t']) -> 
	    if i = j then (i,(RI_aux (RI_id id, (l,Base(([],t),External (Some j), [], pure_e,nob)))),t_id,t')
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
	    | Some(((i,rec_kind,fields) as r)) ->
	      let fi = id_to_string subreg in
	      (match lookup_field_type fi r with
		| NoTyp -> typ_error l ("Type " ^ i ^ " does not have a field " ^ fi)
                | Overload _ ->  raise (Reporting_basic.err_unreachable l "Record given overload annot")
		| Base(([],et),tag,cs,ef,b) ->
		  let tannot = Base(([],et),Alias,[],pure_e,nob) in
		  let d_env = {d_env with alias_env = Envmap.insert (d_env.alias_env) (alias, (OneReg(reg,tannot)))} in
		  (AL_aux(AL_subreg(reg_a,subreg),(l,tannot)),tannot,d_env)))
	| _ -> let _ = Printf.printf "%s\n" (t_to_string reg_t) in assert false)
    | AL_bit(reg_a,bit) -> 
      let (reg,reg_a,reg_t,t) = check_reg reg_a in
      let (E_aux(bit,(le,eannot)),_,_,_,_,_) = check_exp envs None (new_t ()) bit in
      (match t.t with
	| Tapp("vector",[TA_nexp base;TA_nexp len;TA_ord order;TA_typ item_t]) ->
	  match (base.nexp,len.nexp,order.order, bit) with
	    | (Nconst i,Nconst j,Oinc, E_lit (L_aux((L_num k), ll))) ->
	      if (int_of_big_int i) <= k && ((int_of_big_int i) + (int_of_big_int j)) >= k 
	      then let tannot = Base(([],item_t),Alias,[],pure_e,nob) in
		   let d_env = 
		     {d_env with alias_env = Envmap.insert (d_env.alias_env) (alias, (OneReg(reg,tannot)))} in
		   (AL_aux(AL_bit(reg_a,(E_aux(bit,(le,eannot)))), (l,tannot)), tannot,d_env)
	      else typ_error ll ("Alias bit lookup must be in the range of the vector in the register")
	    | _ -> assert false)
    | AL_slice(reg_a,sl1,sl2) -> 
      let (reg,reg_a,reg_t,t) = check_reg reg_a in 
      let (E_aux(sl1,(le1,eannot1)),_,_,_,_,_) = check_exp envs None (new_t ()) sl1 in
      let (E_aux(sl2,(le2,eannot2)),_,_,_,_,_) = check_exp envs None (new_t ()) sl2 in
      (match t.t with
	| Tapp("vector",[TA_nexp base;TA_nexp len;TA_ord order;TA_typ item_t]) ->
	  match (base.nexp,len.nexp,order.order, sl1,sl2) with
	    | (Nconst i,Nconst j,Oinc, E_lit (L_aux((L_num k), ll)),E_lit (L_aux((L_num k2), ll2))) ->
	      if (int_of_big_int i) <= k && ((int_of_big_int i) + (int_of_big_int j)) >= k2 && k < k2 
	      then let t = {t = Tapp("vector",[TA_nexp (int_to_nexp k);TA_nexp (int_to_nexp ((k2-k) +1));
					      TA_ord order; TA_typ item_t])} in 
		   let tannot = Base(([],t),Alias,[],pure_e,nob) in
		   let d_env = 
		     {d_env with alias_env = Envmap.insert (d_env.alias_env) (alias, (OneReg(reg,tannot)))} in
		   (AL_aux(AL_slice(reg_a,(E_aux(sl1,(le1,eannot1))),(E_aux(sl2,(le2,eannot2)))),
			   (l,tannot)), tannot,d_env)
	      else typ_error ll ("Alias slices must be in the range of the vector in the register")
	    | _ -> assert false)
    | AL_concat(reg1_a,reg2_a) -> 
      let (reg1,reg1_a,reg_t,t1) = check_reg reg1_a in
      let (reg2,reg2_a,reg_t,t2) = check_reg reg2_a in
      (match (t1.t,t2.t) with
	| (Tapp("vector",[TA_nexp b1;TA_nexp r; TA_ord {order = Oinc}; TA_typ item_t]),
	   Tapp("vector",[TA_nexp _ ;TA_nexp r2; TA_ord {order = Oinc}; TA_typ item_t2])) ->
	  let _ = type_consistent (Specc l) d_env Guarantee false item_t item_t2 in
	  let t = {t= Tapp("register",[TA_typ {t= Tapp("vector",[TA_nexp b1; TA_nexp {nexp = Nadd(r,r2)}; TA_ord {order = Oinc}; TA_typ item_t])}])} in
	  let tannot = Base(([],t),Alias,[],pure_e,nob) in
	  let d_env = {d_env with alias_env = Envmap.insert (d_env.alias_env) (alias, TwoReg(reg1,reg2,tannot))} in
	  (AL_aux (AL_concat(reg1_a,reg2_a), (l,tannot)), tannot, d_env))

(*val check_def : envs -> tannot def -> (tannot def) envs_out*)
let check_def envs def = 
  let (Env(d_env,t_env,b_env,tp_env)) = envs in
  match def with
  | DEF_type tdef ->
    (*let _ = Printf.printf "checking type def\n" in*)
    let td,envs = check_type_def envs tdef in
    (*let _ = Printf.printf "checked type def\n" in*)
    (DEF_type td,envs)
  | DEF_fundef fdef -> 
    (*let _ = Printf.printf "checking fun def\n" in*)
    let fd,envs = check_fundef envs fdef in
    (*let _ = Printf.printf "checked fun def\n" in*)
    (DEF_fundef fd,envs)
  | DEF_val letdef -> 
    (*let _ = Printf.eprintf "checking letdef\n" in*)
    let (letbind,t_env_let,_,b_env_let,eft) = check_lbind envs None true Emp_global letdef in
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
    let t = (typ_to_t false false typ) in
    let i = id_to_string id in
    let tannot = into_register d_env (Base(([],t),External (Some i),[],pure_e,nob)) in
    (*let _ = Printf.eprintf "done checking reg dec\n" in*)
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
    let t = typ_to_t false false typ in
    let (aspec,tannot,d_env) = check_alias_spec envs i aspec (Some t) in
    (*let _ = Printf.eprintf "done checking reg dec c\n" in*)
    (DEF_reg_dec(DEC_aux(DEC_typ_alias(typ,id,aspec),(l,tannot))),(Env(d_env,Envmap.insert t_env (i,tannot),b_env,tp_env)))
  | DEF_scattered _ -> raise (Reporting_basic.err_unreachable Parse_ast.Unknown "Scattered given to type checker")


(*val check : envs ->  tannot defs -> tannot defs*)
let rec check envs (Defs defs) = 
 match defs with
   | [] -> (Defs [])
   | def::defs -> let (def, envs) = check_def envs def in
		  let (Defs defs) = check envs (Defs defs) in
		  (Defs (def::defs))
