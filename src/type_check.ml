open Ast
open Type_internal
type kind = Type_internal.kind
type typ = Type_internal.t
type 'a exp = 'a Ast.exp
type 'a emap = 'a Envmap.t

type envs = Env of def_envs * tannot emap
type 'a envs_out = 'a * envs

let id_to_string (Id_aux(id,l)) =
  match id with
    | Id(s) -> s
    | DeIid(s) -> s

let typ_error l msg  =
  raise (Reporting_basic.err_typ 
           l
           (msg ))

let resolve_constraints a = a
let resolve_params a = a

let rec field_equivs fields fmaps = 
  match fields with
    | [] -> Some []
    | (FP_aux(FP_Fpat(id,pat),(l,annot)))::fields -> 
      if (List.mem_assoc (id_to_string id) fmaps)
      then match (field_equivs fields fmaps) with
	| None -> None
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

(*No checks necessary, unlike conversion in initial_check*)
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

let rec typ_to_t (Typ_aux(typ,l)) =
  match typ with
    | Typ_id i -> {t = Tid (id_to_string i)}
    | Typ_var (Kid_aux((Var i),l')) -> {t = Tvar i}
    | Typ_fn (ty1,ty2,e) -> {t = Tfn (typ_to_t ty1,typ_to_t ty2,aeffect_to_effect e)}
    | Typ_tup(tys) -> {t = Ttup (List.map typ_to_t tys) }
    | Typ_app(i,args) -> {t = Tapp (id_to_string i,List.map typ_arg_to_targ args) }
and typ_arg_to_targ (Typ_arg_aux(ta,l)) = 
  match ta with
    | Typ_arg_nexp n -> TA_nexp (anexp_to_nexp n)
    | Typ_arg_typ t -> TA_typ (typ_to_t t)
    | Typ_arg_order o -> TA_ord (aorder_to_ord o)
    | Typ_arg_effect e -> TA_eft (aeffect_to_effect e)
and anexp_to_nexp ((Nexp_aux(n,l)) : Ast.nexp) : nexp =
  match n with
    | Nexp_var (Kid_aux((Var i),l')) -> {nexp = Nvar i}
    | Nexp_constant i -> {nexp=Nconst i}
    | Nexp_times(n1,n2) -> {nexp=Nmult(anexp_to_nexp n1,anexp_to_nexp n2)}
    | Nexp_sum(n1,n2) -> {nexp=Nadd(anexp_to_nexp n1,anexp_to_nexp n2)}
    | Nexp_exp n -> {nexp=N2n(anexp_to_nexp n)}
and aeffect_to_effect ((Effect_aux(e,l)) : Ast.effect) : effect = 
  match e with
    | Effect_var (Kid_aux((Var i),l')) -> {effect = Evar i}
    | Effect_set effects -> {effect = Eset effects}
and aorder_to_ord (Ord_aux(o,l) : Ast.order) = 
  match o with
    | Ord_var (Kid_aux((Var i),l')) -> {order = Ovar i}
    | Ord_inc -> {order = Oinc}
    | Ord_dec -> {order = Odec}

let rec eval_to_nexp_const n =
  match n.nexp with
    | Nconst i -> n
    | Nmult(n1,n2) ->
      (match (eval_to_nexp_const n1).nexp,(eval_to_nexp_const n2).nexp with
	| Nconst i1, Nconst i2 -> {nexp=Nconst (i1*i2)}
	| _,_ -> raise (Reporting_basic.err_unreachable Parse_ast.Unknown "Var found in eval_to_nexp_const"))
    | Nadd(n1,n2) ->
      (match (eval_to_nexp_const n1).nexp,(eval_to_nexp_const n2).nexp with
	| Nconst i1, Nconst i2 -> {nexp=Nconst (i1+i2)}
	| _,_ -> raise (Reporting_basic.err_unreachable Parse_ast.Unknown "Var found in eval_to_nexp_const"))
    | Nneg n1 ->
      (match (eval_to_nexp_const n1).nexp with
	| Nconst i -> {nexp = Nconst(- i)}
	| _ -> raise (Reporting_basic.err_unreachable Parse_ast.Unknown "Var found in eval_to_nexp_const"))
    | N2n n1 ->
      (match (eval_to_nexp_const n1).nexp with
	| Nconst i ->
	  let rec two_pow = function
	    | 0 -> 1;
	    | n -> 2* (two_pow n-1) in
	  {nexp = Nconst(two_pow i)}
	| _ -> raise (Reporting_basic.err_unreachable Parse_ast.Unknown "Var found in eval_to_nexp_const"))
    | Nvar _ | Nuvar _ -> raise (Reporting_basic.err_unreachable Parse_ast.Unknown "Var found in eval_to_nexp_const")


let rec quants_to_consts (Env (d_env,t_env)) qis : (t_params * nexp_range list) =
  match qis with 
    | [] -> [],[]
    | (QI_aux(qi,l))::qis ->
      let (ids,cs) = quants_to_consts (Env (d_env,t_env)) qis in
      (match qi with
	| QI_id(KOpt_aux(ki,l')) -> 
	  (match ki with 
	    | KOpt_none (Kid_aux((Var i),l'')) -> 
	      (match Envmap.apply d_env.k_env i with
		| Some k -> ((i,k)::ids,cs)
		| None -> raise (Reporting_basic.err_unreachable l'' "Unkinded id without default after initial check"))
	    | KOpt_kind(kind,Kid_aux((Var i),l'')) -> ((i,kind_to_k kind)::ids,cs))
	| QI_const(NC_aux(nconst,l')) -> 
	  (match nconst with
	    | NC_fixed(n1,n2) -> (ids,Eq(l',anexp_to_nexp n1,anexp_to_nexp n2)::cs)
	    | NC_bounded_ge(n1,n2) -> (ids,GtEq(l',anexp_to_nexp n1,anexp_to_nexp n2)::cs)
	    | NC_bounded_le(n1,n2) -> (ids,LtEq(l',anexp_to_nexp n1,anexp_to_nexp n2)::cs)
	    | NC_nat_set_bounded(Kid_aux((Var i),l''), bounds) -> (ids,In(l',i,bounds)::cs)))


let typq_to_params envs (TypQ_aux(tq,l)) =
  match tq with
    | TypQ_tq(qis) -> quants_to_consts envs qis
    | TypQ_no_forall -> [],[]

let typschm_to_tannot envs ((TypSchm_aux(typschm,l)):typschm) (tag : tag) : tannot = 
  match typschm with
    | TypSchm_ts(tq,typ) -> 
      let t = typ_to_t typ in
      let (ids,constraints) = typq_to_params envs tq in
      Some((ids,t),tag,constraints)

let into_register (t : tannot) : tannot =
  match t with
    | Some((ids,ty),tag,constraints) -> 
      (match ty.t with 
	| Tapp("register",_)-> t
	| _ -> Some((ids, {t= Tapp("register",[TA_typ ty])}),tag,constraints))
    | None -> None

let rec check_pattern envs (P_aux(p,(l,annot))) : ((tannot pat) * (tannot emap) * nexp_range list * t)  =
  let (Env(d_env,t_env)) = envs in
  match p with
    | P_lit (L_aux(lit,l')) ->
      let t =
	(match lit with
	  | L_unit  -> {t = Tid "unit"} 
	  | L_zero  -> {t = Tid "bit"}
	  | L_one   -> {t = Tid "bit"}
	  | L_true  -> {t = Tid "bool"}
	  | L_false -> {t = Tid "bool"}
	  | L_num i -> {t = Tapp("enum",
				 [TA_nexp{nexp = Nconst i};TA_nexp{nexp= Nconst 0};])}
	  | L_hex s -> {t = Tapp("vector",
				 [TA_nexp{nexp = Nconst 0};TA_nexp{nexp = Nconst ((String.length s)*4)};
				  TA_ord{order = Oinc};TA_typ{t = Tid "bit"}])}
	  | L_bin s -> {t = Tapp("vector",
				 [TA_nexp{nexp = Nconst 0};TA_nexp{nexp = Nconst(String.length s)};
				  TA_ord{order = Oinc};TA_typ{t = Tid"bit"}])}
	  | L_string s -> {t = Tid "string"}
	  | L_undef -> typ_error l' "Cannot pattern match on undefined") in
      (P_aux(p,(l,Some(([],t),Emp,[]))),Envmap.empty,[],t)
    | P_wild -> 
      let t = new_t () in
      (P_aux(p,(l,Some(([],t),Emp,[]))),Envmap.empty,[],t)
    | P_as(pat,id) ->
      let (pat',env,constraints,t) = check_pattern envs pat in
      let tannot = Some(([],t),Emp,constraints) in
      (P_aux(p,(l,tannot)),Envmap.insert env (id_to_string id,tannot),constraints,t)
    | P_typ(typ,pat) -> 
      let t = typ_to_t typ in
      let (pat',env,constraints,u) = check_pattern envs pat in
      let (t',constraint') = type_consistent l d_env u t in
      (P_aux(P_typ(typ,pat'),(l,Some(([],t'),Emp,constraint'@constraints))),env,constraints@constraint',t)
    | P_id id -> 
      let t = new_t () in
      let tannot = Some(([],t),Emp,[]) in
      (P_aux(p,(l,tannot)),Envmap.insert (Envmap.empty) (id_to_string id,tannot),[],t)
    | P_app(id,pats) -> 
      let i = id_to_string id in
      (match Envmap.apply t_env i with
	| None | Some None -> typ_error l ("Constructor " ^ i ^ " in pattern is undefined")
	| Some(Some((params,t),Constructor,constraints)) -> 
          let t,constraints = subst params t constraints in
	  (match t.t with
	    | Tid id -> if pats = [] then 
		(P_aux(p,(l,Some((params,t),Constructor,constraints))),Envmap.empty,constraints,t)
	      else typ_error l ("Constructor " ^ i ^ " does not expect arguments")
	    | Tfn(t1,t2,ef) ->
              (match pats with
              | [] -> let t' = type_consistent l d_env unit_t t1 in
                      (P_aux(P_app(id,[]),(l,Some((params,t2),Constructor,constraints))),Envmap.empty,constraints,t2)
              | [p] -> let (p',env,constraints,u) = check_pattern envs p in
                       let (t',constraint') = type_consistent l d_env u t1 in
                           (P_aux(P_app(id,[p']),(l,Some((params,t2),Constructor,constraint'@constraints))),env,constraints@constraint',t2)
              | pats -> let ((P_aux(P_tup(pats'),_)),env,constraints,u) = 
		          check_pattern envs (P_aux(P_tup(pats),(l,annot))) in
	                let (t',constraint') = type_consistent l d_env u t1 in
	                (P_aux(P_app(id,pats'),(l,Some((params,t2),Constructor,constraint'@constraints))),env,constraints,t2))
	    | _ -> typ_error l ("Identifier " ^ i ^ " is not bound to a constructor"))
	| Some(Some((params,t),tag,constraints)) -> typ_error l ("Identifier " ^ i ^ " used in pattern is not a constructor"))
    | P_record(fpats,_) -> 
      (match (fields_to_rec fpats d_env.rec_env) with
	| None -> typ_error l ("No record exists with the listed fields")
	| Some(id,typ_pats) ->
	  let pat_checks = 
	    List.map (fun (tan,id,l,pat) -> 
	      let (pat,env,constraints,u) = check_pattern envs pat in
	      let (Some((vs,t),tag,cs)) = tan in
	      let (t',cs') = type_consistent l d_env u t in 
	      let pat = FP_aux(FP_Fpat(id,pat),(l,Some((vs,t'),tag,cs@cs'@constraints))) in
	      (pat,env,cs@cs'@constraints)) typ_pats in
	  let pats' = List.map (fun (a,b,c) -> a) pat_checks in
	  (*Need to check for variable duplication here*)
	  let env = List.fold_right (fun (_,env,_) env' -> Envmap.union env env') pat_checks Envmap.empty in
	  let constraints = List.fold_right (fun (_,_,cs) cons -> cs@cons) pat_checks [] in
	  let t = {t=Tid id} in
	  (P_aux((P_record(pats',false)),(l,Some(([],t),Emp,constraints))),env,constraints,t))
    | P_vector pats -> 
      let (pats',ts,t_envs,constraints) = 
	List.fold_right 
	  (fun pat (pats,ts,t_envs,constraints) -> 
	    let (pat',t_env,cons,t) = check_pattern envs pat in 
	    ((pat'::pats),(t::ts),(t_env::t_envs),(cons@constraints)))
	  pats ([],[],[],[]) in
      let env = List.fold_right (fun e env -> Envmap.union e env) t_envs Envmap.empty in (*Need to check for non-duplication of variables*)
      let (u,cs) = List.fold_right (fun u (t,cs) -> let t',cs = type_consistent l d_env u t in t',cs) ts ((new_t ()),[]) in
      let t = {t = Tapp("vector",[(TA_nexp {nexp= Nconst 0});(TA_nexp {nexp= Nconst (List.length ts)});(TA_ord{order=Oinc});(TA_typ u)])} in
      (P_aux(P_vector(pats'),(l,Some(([],t),Emp,cs@constraints))), env,cs@constraints,t)
    | P_vector_indexed(ipats) -> 
      let (is,pats) = List.split ipats in
      let (fst,lst) = (List.hd is),(List.hd (List.rev is)) in
      let inc_or_dec = 
	if fst < lst then
	  (let is_increasing = List.fold_left 
	     (fun i1 i2 -> if i1 < i2 then i2 
	       else typ_error l "Indexed vector access was inconsistently increasing") fst (List.tl is) in
	   true)
	else if lst < fst then
	  (let is_decreasing = List.fold_left
	     (fun i1 i2 -> if i1 > i2 then i2
	       else typ_error l "Indexed vector access was inconsistently decreasing") fst (List.tl is) in
	   false)
	else typ_error l "Indexed vector cannot be determined as either increasing or decreasing" in
      let base,rise = new_n (), new_n () in
      let (pats',ts,t_envs,constraints) = 
	List.fold_right 
	  (fun (i,pat) (pats,ts,t_envs,constraints) -> 
	    let (pat',env,cons,t) = check_pattern envs pat in 
	    (((i,pat')::pats),(t::ts),(env::t_envs),(cons@constraints)))
	  ipats ([],[],[],[]) in
      let env = List.fold_right (fun e env -> Envmap.union e env) t_envs Envmap.empty in (*Need to check for non-duplication of variables*)
      let (u,cs) = List.fold_right (fun u (t,cs) -> type_consistent l d_env u t) ts (new_t (),[]) in
      let t = {t = Tapp("vector",[(TA_nexp base);(TA_nexp rise);
				  (TA_ord{order=(if inc_or_dec then Oinc else Odec)});(TA_typ u)])} in
      let cs = if inc_or_dec 
	then [LtEq(l, base, {nexp = Nconst fst});
	      GtEq(l,rise, {nexp = Nconst (lst-fst)});]@cs
	else [GtEq(l,base, {nexp = Nconst fst});
	      LtEq(l,rise, { nexp = Nconst (fst -lst)});]@cs in
      (P_aux(P_vector_indexed(pats'),(l,Some(([],t),Emp,constraints))), env,constraints@cs,t)
    | P_tup(pats) -> 
      let (pats',ts,t_envs,constraints) = 
	List.fold_right 
	  (fun pat (pats,ts,t_envs,constraints) -> 
	    let (pat',env,cons,t) = check_pattern envs pat in 
	    ((pat'::pats),(t::ts),(env::t_envs),cons@constraints))
	  pats ([],[],[],[]) in
      let env = List.fold_right (fun e env -> Envmap.union e env) t_envs Envmap.empty in (*Need to check for non-duplication of variables*)
      let t = {t = Ttup ts} in
      (P_aux(P_tup(pats'),(l,Some(([],t),Emp,constraints))), env,constraints,t)
    | P_vector_concat pats -> 
      let (pats',ts,envs,constraints) = 
	List.fold_right 
	  (fun pat (pats,ts,t_envs,constraints) -> 
	    let (pat',env,cons,t) = check_pattern envs pat in 
	    (pat'::pats,t::ts,env::t_envs,cons@constraints))
	  pats ([],[],[],[]) in
      let env = List.fold_right (fun e env -> Envmap.union e env) envs Envmap.empty in (*Need to check for non-duplication of variables*)
      let t_init = new_t () in
      let or_init = new_o () in
      let ts = List.map 
	(fun t->let ti= { t = Tapp("vector",[TA_nexp(new_n ());TA_nexp(new_n ());TA_ord(or_init);TA_typ t_init])} in
	 type_consistent l d_env t ti) ts in
      let ts,cs = List.split ts in
      let base,rise = new_n (),new_n () in
      let t = {t = Tapp("vector",[(TA_nexp base);(TA_nexp rise);(TA_ord or_init);(TA_typ t_init)])} in
      let base_c,r1 = match (List.hd ts).t with
	| Tapp("vector",[(TA_nexp b);(TA_nexp r);(TA_ord o);(TA_typ u)]) -> b,r
	| _ -> assert false (*turn to unreachable*) in
      let range_c = List.fold_right 
	(fun t rn ->
	  match t.t with
	    | Tapp("vector",[(TA_nexp b);(TA_nexp r);(TA_ord o);(TA_typ u)]) -> {nexp = Nadd(r,rn)}
	    | _ -> assert false (*turn to unreachable*) ) (List.tl ts) r1 in
      let cs = [Eq(l,base,base_c);Eq(l,rise,range_c)]@(List.flatten cs) in
      (P_aux(P_vector_concat(pats'),(l,Some(([],t),Emp,constraints@cs))), env,constraints@cs,t)
    | P_list(pats) -> 
      let (pats',ts,envs,constraints) = 
	List.fold_right 
	  (fun pat (pats,ts,t_envs,constraints) -> 
	    let (pat',env,cons,t) = check_pattern envs pat in 
	    (pat'::pats,t::ts,env::t_envs,cons@constraints))
	  pats ([],[],[],[]) in
      let env = List.fold_right (fun e env -> Envmap.union e env) envs Envmap.empty in (*Need to check for non-duplication of variables*)
      let u,cs = List.fold_right (fun u (t,cs) -> let t',cs' = type_consistent l d_env u t in t',cs@cs') ts (new_t (),[]) in
      let t = {t = Tapp("list",[TA_typ u])} in
      (P_aux(P_list(pats'),(l,Some(([],t),Emp,constraints@cs))), env,constraints@cs,t)
      
let rec check_exp envs expect_t (E_aux(e,(l,annot)) : tannot exp) : (tannot exp * t * tannot emap * nexp_range list) =
  let Env(d_env,t_env) = envs in
  let rebuild annot = E_aux(e,(l,annot)) in
  match e with
    | E_block(exps) -> 
      let (exps',annot',t_env',sc,t) = check_block t_env envs expect_t exps in
      (E_aux(E_block(exps'),(l,annot')),t, t_env',sc)
    | E_id(id) -> 
      let i = id_to_string id in
      (match Envmap.apply t_env i with
      | Some(Some((params,t),Constructor,cs)) ->
        (match t.t with
        | Tfn({t = Tid "unit"},t',ef) -> 
          let t',cs = subst params t' cs in
          let t',cs',e' = type_coerce l d_env t' (rebuild (Some((params,{t=Tfn(unit_t,t',ef)}),Constructor,cs))) expect_t in
          (e',t',t_env,cs@cs')
        | Tfn(t1,t',e) -> 
          typ_error l ("Constructor " ^ i ^ " expects arguments of type INSERT TYPE PRINTER HERE, found none")
        | _ -> raise (Reporting_basic.err_unreachable l "Constructor tannot does not have function type"))
      | Some(Some((params,t),Enum,cs)) ->
        let t',cs = subst params t cs in
        let t',cs',e' = type_coerce l d_env t' (rebuild (Some((params,t'),Enum,cs))) expect_t in
        (e',t',t_env,cs@cs')
      | Some(Some(tp,Default,cs)) | Some(Some(tp,Spec,cs)) ->
        typ_error l ("Identifier " ^ i ^ " must be defined, not just specified, before use")
      | Some(Some((params,t),tag,cs)) ->
        (match t.t,expect_t.t with 
        | Tfn _,_ -> typ_error l ("Identifier " ^ (id_to_string id) ^ " is bound to a function and cannot be used as a value")
        | Tapp("register",[TA_typ(t')]),Tapp("register",[TA_typ(expect_t')]) -> 
          let tannot = Some((params,t),External,cs) in
          let t',cs = subst params t' cs in
          let t',cs',e' = type_coerce l d_env t' (rebuild tannot) expect_t' in
          (e',t',t_env,cs@cs')
        | Tapp("register",[TA_typ(t')]),_ ->
          let tannot = Some((params,t),External,cs) in
          let t',cs = subst params t' cs in
          let t',cs',e' = type_coerce l d_env t' (rebuild tannot) expect_t in
          (e',t',t_env,cs@cs')
        | Tapp("reg",[TA_typ(t)]),_ ->
          let tannot = Some((params,t),Emp,cs) in
          let t',cs',e' = type_coerce l d_env t (rebuild tannot) expect_t in
          (e',t',t_env,cs@cs')
        | _ -> 
          let t',cs',e' = type_coerce l d_env t (rebuild (Some((params,t),tag,cs))) expect_t in
          (e',t',t_env,cs@cs')
        )
      | Some None | None -> (* Turned off until lexp is type checked. TURN ME BACK ON:: typ_error l ("Identifier " ^ (id_to_string id) ^ " is unbound")*) (rebuild None,expect_t,t_env,[]))
    | E_lit (L_aux(lit,l')) ->
      let t,lit' = (match lit with
        | L_unit  -> unit_t,lit
	| L_zero  -> bit_t,lit
	| L_one   -> bit_t,lit
	| L_true  -> bool_t,lit
	| L_false -> bool_t,lit
	| L_num i -> 
          (match expect_t.t with
          | Tid "bit" -> 
            if i = 0 then bit_t,L_zero
	    else 
	      if i = 1 then bit_t,L_one
	      else typ_error l "Expected bit,found a number that cannot be used as a bit"
          | _ -> {t = Tapp("enum",
			   [TA_nexp{nexp = Nconst i};TA_nexp{nexp= Nconst 0};])},lit)
	| L_hex s -> {t = Tapp("vector",
			       [TA_nexp{nexp = Nconst 0};
				TA_nexp{nexp = Nconst ((String.length s)*4)};
				TA_ord{order = Oinc};TA_typ{t = Tid "bit"}])},lit
	| L_bin s -> {t = Tapp("vector",
			       [TA_nexp{nexp = Nconst 0};
				TA_nexp{nexp = Nconst(String.length s)};
				TA_ord{order = Oinc};TA_typ{t = Tid"bit"}])},lit
	| L_string s -> {t = Tid "string"},lit
	| L_undef -> new_t (),lit) in
      let t',cs',e' = 
	type_coerce l d_env t (E_aux(E_lit(L_aux(lit',l')),(l,(Some(([],t),Emp,[]))))) expect_t in
      (e',t',t_env,cs')
    | E_cast(typ,e) ->
      let t = typ_to_t typ in
      let t',cs = type_consistent l d_env t expect_t in
      let (e',u,t_env,cs') = check_exp envs t' e in
      (e',t',t_env,cs@cs')
        
    | E_app(id,parms) -> 
      (*TODO add a tuple arg to store the function effects in, for eventual checking*)
      let i = id_to_string id in
      (match Envmap.apply t_env i with
      | Some(Some(tp,Enum,cs)) ->
        typ_error l ("Expected function with name " ^ i ^ " but found an enumeration identifier")
      | Some(Some(tp,Default,cs)) ->
        typ_error l ("Function " ^ i ^ " must be defined, not just declared as a default, before use")
      | Some(Some((params,t),tag,cs)) ->
        let t,cs = subst params t cs in
        (match t.t with
        | Tfn(arg,ret,ef) ->
          (match parms with
          | [] -> 
            let (p',cs') = type_consistent l d_env unit_t arg in
            let (ret_t,cs_r,e') = type_coerce l d_env ret (rebuild (Some(([],unit_t),tag,cs@cs'))) expect_t in
            (e',ret_t,t_env,cs@cs'@cs_r)
          | [parm] ->
            let (parm',arg_t,t_env,cs') = check_exp envs arg parm in
            let (ret_t,cs_r',e') = type_coerce l d_env ret (E_aux(E_app(id,[parm']),(l,(Some(([],ret),tag,cs))))) expect_t in
            (e',ret_t,t_env,cs@cs'@cs_r')
          | parms -> 
            let ((E_aux(E_tuple parms',tannot')),arg_t,t_env,cs') = check_exp envs arg (E_aux(E_tuple parms,(l,None))) in
            let (ret_t,cs_r',e') = type_coerce l d_env ret (E_aux(E_app(id, parms'),(l,(Some(([],ret),tag,cs))))) expect_t in
            (e',ret_t,t_env,cs@cs'@cs_r'))
        | _ -> typ_error l ("Expected a function or constructor, found identifier " ^ i ^ " bound to type " ^ (t_to_string t)))
      | _ -> typ_error l ("Unbound function " ^ i)) 
    | E_app_infix(lft,op,rht) -> 
      let i = id_to_string op in
      (match Envmap.apply t_env i with
      | Some(Some(tp,Enum,cs)) ->
        typ_error l ("Expected function with name " ^ i ^ " but found an enumeration identifier")
      | Some(Some(tp,Default,cs)) ->
        typ_error l ("Function " ^ i ^ " must be defined, not just declared as a default, before use")
      | Some(Some((params,t),tag,cs)) ->
        let t,cs = subst params t cs in
        (match t.t with
        | Tfn(arg,ret,ef) -> 
          let (E_aux(E_tuple [lft';rht'],tannot'),arg_t,t_env,cs') = check_exp envs arg (E_aux(E_tuple [lft;rht],(l,None))) in
          let ret_t,cs_r',e' = type_coerce l d_env ret (E_aux(E_app_infix(lft',op,rht'),(l,(Some(([],ret),tag,cs))))) expect_t in
          (e',ret_t,t_env,cs@cs'@cs_r')
        | _ -> typ_error l ("Expected a function or constructor, found identifier " ^ i ^ " bound to type " ^ (t_to_string t)))
      | _ -> typ_error l ("Unbound infix function " ^ i))
    | E_tuple(exps) ->
      (match expect_t.t with
      | Ttup ts ->
        let tl = List.length ts in
        let el = List.length exps in
        if tl = el then
          let exps,typs,consts = 
            List.fold_right2 (fun e t (exps,typs,consts) -> let (e',t',_,c) = check_exp envs t e in ((e'::exps),(t'::typs),c@consts))
              exps ts ([],[],[]) in
          let t = {t = Ttup typs} in
          (E_aux(E_tuple(exps),(l,Some(([],t),Emp,consts))),t,t_env,consts)
        else typ_error l ("Expected a tuple with length " ^ (string_of_int tl) ^ " found one of length " ^ (string_of_int el))
      | _ ->
        let exps,typs,consts = 
          List.fold_right (fun e (exps,typs,consts) -> let (e',t,_,c) = check_exp envs (new_t ()) e in ((e'::exps),(t::typs),c@consts)) exps ([],[],[]) in
        let t = { t=Ttup typs } in
        let t',cs',e' = type_coerce l d_env t (E_aux(E_tuple(exps),(l,Some(([],t),Emp,consts)))) expect_t in
        (e',t',t_env,consts@cs'))
    | E_if(cond,then_,else_) ->
      let (cond',_,_,c1) = check_exp envs bool_t cond in
      let then',then_t,then_env,then_c = check_exp envs expect_t then_ in
      let else',else_t,else_env,else_c = check_exp envs expect_t else_ in
      (E_aux(E_if(cond',then',else'),(l,Some(([],expect_t),Emp,c1@then_c@else_c))),expect_t,Envmap.intersect then_env else_env,then_c@else_c@c1)
    | E_for(id,from,to_,step,block) -> 
      (E_aux(e,(l,annot)),expect_t,t_env,[]) (*TODO*)
    | E_vector(es) ->
      let item_t = match expect_t.t with
        | Tapp("vector",[base;rise;ord;TA_typ item_t]) -> item_t
          (* TODO: Consider whether an enum should be looked for here*)
        | _ -> new_t () in
      let es,cs = (List.fold_right (fun (e,_,_,c) (es,cs) -> (e::es),(c@cs)) (List.map (check_exp envs item_t) es) ([],[])) in
      let t = {t = Tapp("vector",[TA_nexp({nexp=Nconst 0});TA_nexp({nexp=Nconst (List.length es)});TA_ord({order=Oinc});TA_typ item_t])} in
      let t',cs',e' = type_coerce l d_env t (E_aux(E_vector es,(l,Some(([],t),Emp,cs)))) expect_t in
      (e',t',t_env,cs@cs')
    | E_let(lbind,body) -> 
      let (lb',t_env',cs) = (check_lbind envs lbind) in
      let (e,t,_,cs') = check_exp (Env(d_env,Envmap.union t_env t_env')) expect_t body in
      (E_aux(E_let(lb',e),(l,Some(([],t),Emp,cs@cs'))),t,t_env,cs@cs')
    | _ -> (E_aux(e,(l,annot)),expect_t,t_env,[])
		    
and check_block orig_envs envs expect_t exps : ((tannot exp) list * tannot * tannot emap * nexp_range list * t) =
  let Env(d_env,t_env) = envs in
  match exps with
    | [] -> ([],None,orig_envs,[],unit_t)
    | [e] -> let (E_aux(e',(l,annot)),t,envs,sc) = check_exp envs expect_t e in
	     ([E_aux(e',(l,annot))],annot,orig_envs,sc,t)
    | e::exps -> let (e',t',t_env,sc) = check_exp envs unit_t e in
		 let (exps',annot',orig_envs,sc',t) = check_block orig_envs (Env(d_env,t_env)) expect_t exps in
		 ((e'::exps'),annot',orig_envs,sc@sc',t)

and check_lbind envs (LB_aux(lbind,(l,annot))) : tannot letbind * tannot emap * nexp_range list =
  let Env(d_env,t_env) = envs in
  match lbind with
  | LB_val_explicit(typ,pat,e) -> 
    let tan = typschm_to_tannot envs typ Emp in
    (match tan with
    | Some((params,t),tag,cs) ->
      let t,cs = subst params t cs in
      let (pat',env,cs1,u) = check_pattern envs pat in
      let t',cs' = type_consistent l d_env u t in
      let (e,t,_,cs2) = check_exp envs t' e in
      let cs = resolve_constraints cs@cs1@cs'@cs2 in
      let tannot = resolve_params(Some((params,t),tag,cs)) in
      (LB_aux (LB_val_explicit(typ,pat',e),(l,tannot)),env,cs)
    | None -> raise (Reporting_basic.err_unreachable l "typschm_to_tannot failed to produce a Some"))
  | LB_val_implicit(pat,e) -> 
    let t = new_t () in
    let (pat',env,cs1,u) = check_pattern envs pat in
    let (e,t',_,cs2) = check_exp envs u e in
    let cs = resolve_constraints cs1@cs2 in
    let tannot = resolve_params(Some(([],t'),Emp,cs)) in
    (LB_aux (LB_val_implicit(pat',e),(l,tannot)), env,cs)

(*val check_type_def : envs -> (tannot type_def) -> (tannot type_def) envs_out*)
let check_type_def envs (TD_aux(td,(l,annot))) =
  let (Env(d_env,t_env)) = envs in
  match td with
    | TD_abbrev(id,nmscm,typschm) -> 
      let tan = typschm_to_tannot envs typschm Emp in
      (TD_aux(td,(l,tan)),
       Env( { d_env with abbrevs = Envmap.insert d_env.abbrevs ((id_to_string id),tan)},t_env))
    | TD_record(id,nmscm,typq,fields,_) -> 
      let id' = id_to_string id in
      let (params,constraints) = typq_to_params envs typq in
      let tyannot = Some((params,{t=Tid id'}),Emp,constraints) in
      let fields' = List.map 
	(fun (ty,i)->(id_to_string i),Some((params,(typ_to_t ty)),Emp,constraints)) fields in
      (TD_aux(td,(l,tyannot)),Env({d_env with rec_env = (id',Record,fields')::d_env.rec_env},t_env))
    | TD_variant(id,nmscm,typq,arms,_) ->
      let id' = id_to_string id in
      let (params,constraints) = typq_to_params envs typq in
      let ty = {t=Tid id'} in
      let tyannot = Some((params,ty),Constructor,constraints) in
      let arm_t input = Some((params,{t=Tfn(input,ty,{effect=Eset []})}),Constructor,constraints) in
      let arms' = List.map 
	(fun (Tu_aux(tu,l')) -> 
	  match tu with 
	    | Tu_id i -> ((id_to_string i),(arm_t unit_t))
	    | Tu_ty_id(typ,i)-> ((id_to_string i),(arm_t (typ_to_t typ))))
	arms in
      let t_env = List.fold_right (fun (id,tann) t_env -> Envmap.insert t_env (id,tann)) arms' t_env in
      (TD_aux(td,(l,tyannot)),(Env (d_env,t_env)))
    | TD_enum(id,nmscm,ids,_) -> 
      let id' = id_to_string id in
      let ids' = List.map id_to_string ids in
      let ty = Some (([],{t = Tid id' }),Enum,[]) in
      let t_env = List.fold_right (fun id t_env -> Envmap.insert t_env (id,ty)) ids' t_env in
      let enum_env = Envmap.insert d_env.enum_env (id',ids') in
      (TD_aux(td,(l,ty)),Env({d_env with enum_env = enum_env;},t_env))
    | TD_register(id,base,top,ranges) -> 
      let id' = id_to_string id in
      let basei = eval_to_nexp_const(anexp_to_nexp base) in
      let topi = eval_to_nexp_const(anexp_to_nexp top) in
      match basei.nexp,topi.nexp with
	| Nconst b, Nconst t -> 
	  if b <= t then (
	    let ty = {t = Tapp("vector",[TA_nexp basei; TA_nexp{nexp=Nconst(t-b)}; 
					 TA_ord({order = Oinc}); TA_typ({t = Tid "bit"});])} in
	    let franges = 
	      List.map 
		(fun ((BF_aux(idx,l)),id) ->
		  let (base,climb) =
		    match idx with
		      | BF_single i -> 
			if b <= i && i <= t 
			then {nexp=Nconst i},{nexp=Nconst 0}
			else typ_error l ("register type declaration " ^ id' ^ " contains a field specification outside of the declared register size")
		      | BF_range(i1,i2) -> 
			if i1<i2 
			then if b<=i1 && i2<=t 
			  then {nexp=Nconst i1},{nexp=Nconst (i2 - i1)}
			  else typ_error l ("register type declaration " ^ id' ^ " contains a field specification outside of the declared register size")
			else typ_error l ("register type declaration " ^ id' ^ " is not consistently increasing")
		      | BF_concat _ -> assert false (* What is this supposed to imply again?*) in
		  ((id_to_string id),
		   Some(([],{t=Tapp("vector",[TA_nexp base;TA_nexp climb;TA_ord({order=Oinc});TA_typ({t= Tid "bit"})])}),Emp,[])))
		ranges 
	    in
	    let tannot = into_register (Some(([],ty),Emp,[])) in
	    (TD_aux(td,(l,tannot)),
	     Env({d_env with rec_env = ((id',Register,franges)::d_env.rec_env);
	       abbrevs = Envmap.insert d_env.abbrevs (id',tannot)},t_env)))
	  else (
	    let ty = {t = Tapp("vector",[TA_nexp basei; TA_nexp{nexp=Nconst(b-t)}; 
					 TA_ord({order = Odec}); TA_typ({t = Tid "bit"});])} in
	    let franges = 
	      List.map 
		(fun ((BF_aux(idx,l)),id) ->
		  let (base,climb) =
		    match idx with
		      | BF_single i -> 
			if b >= i && i >= t 
			then {nexp=Nconst i},{nexp=Nconst 0}
			else typ_error l ("register type declaration " ^ id' ^ " contains a field specification outside of the declared register size")
		      | BF_range(i1,i2) -> 
			if i1>i2 
			then if b>=i1 && i2>=t 
			  then {nexp=Nconst i1},{nexp=Nconst (i1 - i2)}
			  else typ_error l ("register type declaration " ^ id' ^ " contains a field specification outside of the declared register size")
			else typ_error l ("register type declaration " ^ id' ^ " is not consistently decreasing")
		      | BF_concat _ -> assert false (* What is this supposed to imply again?*) in
		  ((id_to_string id),
		   Some(([],{t=Tapp("vector",[TA_nexp base;TA_nexp climb;TA_ord({order=Odec});TA_typ({t= Tid "bit"})])}),Emp,[])))
		ranges 
	    in
	    let tannot = into_register (Some(([],ty),Emp,[])) in
	    (TD_aux(td,(l,tannot)),
	     Env({d_env with rec_env = (id',Register,franges)::d_env.rec_env;
	       abbrevs = Envmap.insert d_env.abbrevs (id',tannot)},t_env)))

let check_val_spec envs (VS_aux(vs,(l,annot))) = 
  let (Env(d_env,t_env)) = envs in
  match vs with
    | VS_val_spec(typs,id) -> 
      let tannot = typschm_to_tannot envs typs Spec in
      (VS_aux(vs,(l,tannot)),
       Env(d_env,(Envmap.insert t_env (id_to_string id,tannot))))
    | VS_extern_no_rename(typs,id) ->
      let tannot = typschm_to_tannot envs typs External in
      (VS_aux(vs,(l,tannot)),
       Env(d_env,(Envmap.insert t_env (id_to_string id,tannot))))
    | VS_extern_spec(typs,id,s) ->
      let tannot = typschm_to_tannot envs typs External in
      (VS_aux(vs,(l,tannot)),
       Env(d_env,(Envmap.insert t_env (id_to_string id,tannot))))

let check_default envs (DT_aux(ds,(l,annot))) =
  let (Env(d_env,t_env)) = envs in
  match ds with
    | DT_kind _ -> ((DT_aux(ds,(l,annot))),envs)
    | DT_typ(typs,id) ->
      let tannot = typschm_to_tannot envs typs Default in
      (DT_aux(ds,(l,tannot)),
       Env(d_env,(Envmap.insert t_env (id_to_string id,tannot))))

let check_fundef envs (FD_aux(FD_function(recopt,tannotopt,effectopt,funcls),(l,annot))) =
  let Env(d_env,t_env) = envs in
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
  let ret_t,param_t,tannot = match tannotopt with
    | Typ_annot_opt_aux(Typ_annot_opt_some(typq,typ),(l',annot')) ->
      let (ids,constraints) = typq_to_params envs typq in
      let t = typ_to_t typ in
      let p_t = new_t () in
      let ef = new_e () in
      t,p_t,Some((ids,{t=Tfn(p_t,t,ef)}),Emp,constraints) in
  let check t_env =
    List.split
      (List.map (fun (FCL_aux((FCL_Funcl(id,pat,exp)),(l,annot))) ->
	let (pat',t_env',constraints',t') = check_pattern (Env(d_env,t_env)) pat in
	let u,cs = type_consistent l d_env t' param_t in
	let exp,_,_,constraints = check_exp (Env(d_env,Envmap.union t_env t_env')) ret_t exp in
	(FCL_aux((FCL_Funcl(id,pat',exp)),(l,tannot)),constraints'@cs@constraints)) funcls) in
  match (in_env,tannot) with
    | Some(Some( (params,u),Spec,constraints)), Some( (p',t),Emp,c') ->
      let u,constraints = subst params u constraints in
      let t,c' = subst p' t c' in
      let t',cs = type_consistent l d_env t u in
      let t_env = if is_rec then t_env else Envmap.remove t_env id in
      let funcls,cs = check t_env in
      let cs' = resolve_constraints cs in
      let tannot = resolve_params tannot in
      (FD_aux(FD_function(recopt,tannotopt,effectopt,funcls),(l,tannot))),
      Env(d_env,Envmap.insert t_env (id,tannot))
    | _ , _-> 
      let t_env = if is_rec then Envmap.insert t_env (id,tannot) else t_env in
      let funcles,cs = check t_env in
      let cs' = resolve_constraints cs in
      let tannot = resolve_params tannot in
      (FD_aux(FD_function(recopt,tannotopt,effectopt,funcls),(l,tannot))),
      Env(d_env,(if is_rec then t_env else Envmap.insert t_env (id,tannot)))

(*val check_def : envs -> tannot def -> (tannot def) envs_out*)
let check_def envs (DEF_aux(def,(l,annot))) = 
  let (Env(d_env,t_env)) = envs in
  match def with
    | DEF_type tdef -> let td,envs = check_type_def envs tdef in
		       (DEF_aux((DEF_type td),(l,annot)),envs)
    | DEF_fundef fdef -> let fd,envs = check_fundef envs fdef in
			 (DEF_aux(DEF_fundef(fd),(l,annot)),envs)
    | DEF_val letdef -> let (letbind,t_env_let,_) = check_lbind envs letdef in
                        (DEF_aux(DEF_val letbind,(l,annot)),Env(d_env,Envmap.union t_env_let t_env))
    | DEF_spec spec -> let vs,envs = check_val_spec envs spec in
		       (DEF_aux(DEF_spec(vs),(l,annot)),envs)
    | DEF_default default -> let ds,envs = check_default envs default in
			     (DEF_aux((DEF_default(ds)),(l,annot)),envs)
    | DEF_reg_dec(typ,id) -> 
      let t = (typ_to_t typ) in
      let tannot = into_register (Some(([],t),External,[])) in 
      (DEF_aux(def,(l,tannot)),(Env(d_env,Envmap.insert t_env ((id_to_string id),tannot))))


(*val check : envs ->  tannot defs -> tannot defs*)
let rec check envs (Defs defs) = 
 match defs with
   | [] -> (Defs [])
   | def::defs -> let (def, envs) = check_def envs def in
		  let (Defs defs) = check envs (Defs defs) in
		  (Defs (def::defs))
