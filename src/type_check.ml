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
      Some((ids,t),tag,constraints,pure_e)

let into_register d_env (t : tannot) : tannot =
  match t with
    | Some((ids,ty),tag,constraints,eft) -> 
      let ty',_,_ =  get_abbrev d_env ty in
      (match ty'.t with 
	| Tapp("register",_)-> t
        | Tabbrev(ti,{t=Tapp("register",_)}) -> Some((ids,ty'),tag,constraints,eft)
	| _ -> Some((ids, {t= Tapp("register",[TA_typ ty'])}),tag,constraints,eft))
    | None -> None

let rec check_pattern envs emp_tag expect_t (P_aux(p,(l,annot))) : ((tannot pat) * (tannot emap) * nexp_range list * t)  =
  let (Env(d_env,t_env)) = envs in
  match p with
    | P_lit (L_aux(lit,l')) ->
      let t,lit =
	(match lit with
	  | L_unit  -> unit_t,lit 
	  | L_zero  -> bit_t,lit
	  | L_one   -> bit_t,lit
	  | L_true  -> bool_t,lit
	  | L_false -> bool_t,lit
	  | L_num i -> 
	    (match expect_t.t with
	      | Tid "bit" -> 
		if i = 0 then bit_t,L_zero 
		else if i = 1 then bit_t,L_one
		else {t = Tapp("range",
			       [TA_nexp{nexp = Nconst i};TA_nexp{nexp= Nconst 0};])},lit
	      | _ -> {t = Tapp("range",
			       [TA_nexp{nexp = Nconst i};TA_nexp{nexp= Nconst 0};])},lit)
	  | L_hex s -> {t = Tapp("vector",
				 [TA_nexp{nexp = Nconst 0};TA_nexp{nexp = Nconst ((String.length s)*4)};
				  TA_ord{order = Oinc};TA_typ{t = Tid "bit"}])},lit
	  | L_bin s -> {t = Tapp("vector",
				 [TA_nexp{nexp = Nconst 0};TA_nexp{nexp = Nconst(String.length s)};
				  TA_ord{order = Oinc};TA_typ{t = Tid"bit"}])},lit
	  | L_string s -> {t = Tid "string"},lit
	  | L_undef -> typ_error l' "Cannot pattern match on undefined") in
      let t',cs = type_consistent l d_env t expect_t in
      (P_aux(P_lit(L_aux(lit,l')),(l,Some(([],t),Emp_local,cs,pure_e))),Envmap.empty,[],t)
    | P_wild -> 
      (P_aux(p,(l,Some(([],expect_t),Emp_local,[],pure_e))),Envmap.empty,[],expect_t)
    | P_as(pat,id) ->
      let (pat',env,constraints,t) = check_pattern envs emp_tag expect_t pat in
      let tannot = Some(([],t),emp_tag,[],pure_e) in
      (P_aux(P_as(pat',id),(l,tannot)),Envmap.insert env (id_to_string id,tannot),constraints,t)
    | P_typ(typ,pat) -> 
      let t = typ_to_t typ in
      let (pat',env,constraints,u) = check_pattern envs emp_tag t pat in
      let (t',constraint') = type_consistent l d_env u t in (*TODO: This should be a no-op now, should check*)
      (P_aux(P_typ(typ,pat'),(l,Some(([],t'),Emp_local,[],pure_e))),env,constraints@constraint',t)
    | P_id id -> 
      let tannot = Some(([],expect_t),emp_tag,[],pure_e) in
      (P_aux(p,(l,tannot)),Envmap.from_list [(id_to_string id,tannot)],[],expect_t)
    | P_app(id,pats) -> 
      let i = id_to_string id in
      (match Envmap.apply t_env i with
	| None | Some None -> typ_error l ("Constructor " ^ i ^ " in pattern is undefined")
	| Some(Some((params,t),Constructor,constraints,eft)) -> 
          let t,constraints,_ = subst params t constraints eft in
	  (match t.t with
	    | Tid id -> if pats = [] then
                let t',constraints' = type_consistent l d_env t expect_t in
		(P_aux(p,(l,Some(([],t'),Constructor,constraints,pure_e))),Envmap.empty,constraints@constraints',t')
	      else typ_error l ("Constructor " ^ i ^ " does not expect arguments")
	    | Tfn(t1,t2,ef) ->
              (match pats with
              | [] -> let _ = type_consistent l d_env unit_t t1 in
                      let t',constraints' = type_consistent l d_env t2 expect_t in
                      (P_aux(P_app(id,[]),(l,Some(([],t'),Constructor,constraints,pure_e))),Envmap.empty,constraints@constraints',t')
              | [p] -> let (p',env,constraints,u) = check_pattern envs emp_tag t1 p in
                       let (t1',constraint') = type_consistent l d_env u t1 in (*TODO This should be a no-op now, should check *)
                       let t',constraints' = type_consistent l d_env t2 expect_t in
                       (P_aux(P_app(id,[p']),(l,Some(([],t'),Constructor,constraints,pure_e))),env,constraints@constraint'@constraints',t')
              | pats -> let ((P_aux(P_tup(pats'),_)),env,constraints,u) = 
		          check_pattern envs emp_tag t1 (P_aux(P_tup(pats),(l,annot))) in
	                let (t1',constraint') = type_consistent l d_env u t1 in (*TODO This should be a no-op now, should check *)
                        let t',constraints' = type_consistent l d_env t2 expect_t in
	                (P_aux(P_app(id,pats'),(l,Some(([],t'),Constructor,constraints,pure_e))),env,constraint'@constraints@constraints',t'))
	    | _ -> typ_error l ("Identifier " ^ i ^ " is not bound to a constructor"))
	| Some(Some((params,t),tag,constraints,eft)) -> typ_error l ("Identifier " ^ i ^ " used in pattern is not a constructor"))
    | P_record(fpats,_) -> 
      (match (fields_to_rec fpats d_env.rec_env) with
	| None -> typ_error l ("No struct exists with the listed fields")
	| Some(id,typ_pats) ->
	  let pat_checks = 
	    List.map (fun (tan,id,l,pat) -> 
	      let (Some((vs,t),tag,cs,eft)) = tan in
	      let t,cs,_ = subst vs t cs eft in
	      let (pat,env,constraints,u) = check_pattern envs emp_tag t pat in
	      let (t',cs') = type_consistent l d_env u t in 
	      let pat = FP_aux(FP_Fpat(id,pat),(l,Some(([],t'),tag,cs@cs',pure_e))) in
	      (pat,env,cs@cs'@constraints)) typ_pats in
	  let pats' = List.map (fun (a,b,c) -> a) pat_checks in
	  (*Need to check for variable duplication here*)
	  let env = List.fold_right (fun (_,env,_) env' -> Envmap.union env env') pat_checks Envmap.empty in
	  let constraints = List.fold_right (fun (_,_,cs) cons -> cs@cons) pat_checks [] in
	  let t = {t=Tid id} in
          let t',cs' = type_consistent l d_env t expect_t in
	  (P_aux((P_record(pats',false)),(l,Some(([],t'),Emp_local,constraints@cs',pure_e))),env,constraints@cs',t'))
    | P_vector pats -> 
      let item_t = match expect_t.t with (*TODO check for abbrev, throw error if not a vector or tuvar*)
	| Tapp("vector",[b;r;o;TA_typ i]) -> i
	| _ -> new_t () in
      let (pats',ts,t_envs,constraints) = 
	List.fold_right 
	  (fun pat (pats,ts,t_envs,constraints) -> 
	    let (pat',t_env,cons,t) = check_pattern envs emp_tag item_t pat in 
	    ((pat'::pats),(t::ts),(t_env::t_envs),(cons@constraints)))
	  pats ([],[],[],[]) in
      let env = List.fold_right (fun e env -> Envmap.union e env) t_envs Envmap.empty in (*Need to check for non-duplication of variables*)
      let (u,cs) = List.fold_right (fun u (t,cs) -> let t',cs = type_consistent l d_env u t in t',cs) ts (item_t,[]) in
      let t = {t = Tapp("vector",[(TA_nexp {nexp= Nconst 0});(TA_nexp {nexp= Nconst (List.length ts)});(TA_ord{order=Oinc});(TA_typ u)])} in
      (P_aux(P_vector(pats'),(l,Some(([],t),Emp_local,cs,pure_e))), env,cs@constraints,t)
    | P_vector_indexed(ipats) -> 
      let item_t = match expect_t.t with
	| Tapp("vector",[b;r;o;TA_typ i]) -> i
	| _ -> new_t () in
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
	    let (pat',env,cons,t) = check_pattern envs emp_tag item_t pat in 
	    (((i,pat')::pats),(t::ts),(env::t_envs),(cons@constraints)))
	  ipats ([],[],[],[]) in
      let env = List.fold_right (fun e env -> Envmap.union e env) t_envs Envmap.empty in (*Need to check for non-duplication of variables*)
      let (u,cs) = List.fold_right (fun u (t,cs) -> type_consistent l d_env u t) ts (item_t,[]) in
      let t = {t = Tapp("vector",[(TA_nexp base);(TA_nexp rise);
				  (TA_ord{order=(if inc_or_dec then Oinc else Odec)});(TA_typ u)])} in
      let cs = if inc_or_dec 
	then [LtEq(l, base, {nexp = Nconst fst});
	      GtEq(l,rise, {nexp = Nconst (lst-fst)});]@cs
	else [GtEq(l,base, {nexp = Nconst fst});
	      LtEq(l,rise, { nexp = Nconst (fst -lst)});]@cs in
      (P_aux(P_vector_indexed(pats'),(l,Some(([],t),Emp_local,cs,pure_e))), env,constraints@cs,t)
    | P_tup(pats) -> 
      let item_ts = match expect_t.t with
	| Ttup ts ->
	  if (List.length ts) = (List.length pats) 
	  then ts
	  else typ_error l ("Expected a pattern with a tuple with " ^ (string_of_int (List.length ts)) ^ " elements")
	| _ -> List.map (fun _ -> new_t ()) pats in
      let (pats',ts,t_envs,constraints) = 
	List.fold_right 
	  (fun (pat,t) (pats,ts,t_envs,constraints) -> 
	    let (pat',env,cons,t) = check_pattern envs emp_tag t pat in 
	    ((pat'::pats),(t::ts),(env::t_envs),cons@constraints))
	  (List.combine pats item_ts) ([],[],[],[]) in
      let env = List.fold_right (fun e env -> Envmap.union e env) t_envs Envmap.empty in (*Need to check for non-duplication of variables*)
      let t = {t = Ttup ts} in
      (P_aux(P_tup(pats'),(l,Some(([],t),Emp_local,[],pure_e))), env,constraints,t)
    | P_vector_concat pats -> 
      let (pats',ts,envs,constraints) = 
	List.fold_right 
	  (fun pat (pats,ts,t_envs,constraints) -> 
	    let (pat',env,cons,t) = check_pattern envs emp_tag expect_t pat in 
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
	| _ -> raise (Reporting_basic.err_unreachable l "vector concat pattern impossibility") in
      let range_c = List.fold_right 
	(fun t rn ->
	  match t.t with
	    | Tapp("vector",[(TA_nexp b);(TA_nexp r);(TA_ord o);(TA_typ u)]) -> {nexp = Nadd(r,rn)}
	    | _ -> raise (Reporting_basic.err_unreachable l "vector concat pattern impossibility") ) (List.tl ts) r1 in
      let cs = [Eq(l,base,base_c);Eq(l,rise,range_c)]@(List.flatten cs) in
      (P_aux(P_vector_concat(pats'),(l,Some(([],t),Emp_local,cs,pure_e))), env,constraints@cs,t)
    | P_list(pats) -> 
      let item_t = match expect_t.t with
	| Tapp("list",[TA_typ i]) -> i
	| _ -> new_t () in
      let (pats',ts,envs,constraints) = 
	List.fold_right 
	  (fun pat (pats,ts,t_envs,constraints) -> 
	    let (pat',env,cons,t) = check_pattern envs emp_tag item_t pat in 
	    (pat'::pats,t::ts,env::t_envs,cons@constraints))
	  pats ([],[],[],[]) in
      let env = List.fold_right (fun e env -> Envmap.union e env) envs Envmap.empty in (*Need to check for non-duplication of variables*)
      let u,cs = List.fold_right (fun u (t,cs) -> let t',cs' = type_consistent l d_env u t in t',cs@cs') ts (item_t,[]) in
      let t = {t = Tapp("list",[TA_typ u])} in
      (P_aux(P_list(pats'),(l,Some(([],t),Emp_local,cs,pure_e))), env,constraints@cs,t)
      
let rec check_exp envs expect_t (E_aux(e,(l,annot)) : tannot exp) : (tannot exp * t * tannot emap * nexp_range list * effect) =
  let Env(d_env,t_env) = envs in
  let rebuild annot = E_aux(e,(l,annot)) in
  match e with
    | E_block(exps) -> 
      let (exps',annot',t_env',sc,t,ef) = check_block t_env envs expect_t exps in
      (E_aux(E_block(exps'),(l,annot')),t, t_env',sc,ef)
    | E_id(id) -> 
      let i = id_to_string id in
      (match Envmap.apply t_env i with
      | Some(Some((params,t),Constructor,cs,ef)) ->
	let t,cs,ef = subst params t cs ef in
        (match t.t with
        | Tfn({t = Tid "unit"},t',ef) -> 
          let t',cs',e' = type_coerce l d_env t' (rebuild (Some(([],{t=Tfn(unit_t,t',ef)}),Constructor,cs,ef))) expect_t in
          (e',t',t_env,cs@cs',ef)
        | Tfn(t1,t',e) -> 
          typ_error l ("Constructor " ^ i ^ " expects arguments of type " ^ (t_to_string t) ^ ", found none")
        | _ -> raise (Reporting_basic.err_unreachable l "Constructor tannot does not have function type"))
      | Some(Some((params,t),Enum,cs,ef)) ->
        let t',cs,_ = subst params t cs ef in
        let t',cs',e' = type_coerce l d_env t' (rebuild (Some(([],t'),Enum,cs,pure_e))) expect_t in
        (e',t',t_env,cs@cs',pure_e)
      | Some(Some(tp,Default,cs,ef)) | Some(Some(tp,Spec,cs,ef)) ->
        typ_error l ("Identifier " ^ i ^ " must be defined, not just specified, before use")
      | Some(Some((params,t),tag,cs,ef)) ->
	let t,cs,ef = match tag with | Emp_global | External _ -> subst params t cs ef | _ -> t,cs,ef in
        let t,cs',ef' = get_abbrev d_env t in
        let cs,ef = cs@cs',union_effects ef ef' in
        let t_actual,expect_actual = match t.t,expect_t.t with
          | Tabbrev(_,t),Tabbrev(_,e) -> t,e
          | Tabbrev(_,t),_ -> t,expect_t 
          | _,Tabbrev(_,e) -> t,e
          | _,_ -> t,expect_t in
        (match t_actual.t,expect_actual.t with 
        | Tfn _,_ -> typ_error l ("Identifier " ^ (id_to_string id) ^ " is bound to a function and cannot be used as a value")
        | Tapp("register",[TA_typ(t')]),Tapp("register",[TA_typ(expect_t')]) -> 
          let tannot = Some(([],t),Emp_local,cs,ef) in
          let t',cs',e' = type_coerce l d_env t' (rebuild tannot) expect_t' in
          (e',t,t_env,cs@cs',ef)
        | Tapp("register",[TA_typ(t')]),Tuvar _ ->
	  let ef' = add_effect (BE_aux(BE_rreg,l)) ef in
          let tannot = Some(([],t),External (Some i),cs,ef') in
          let t',cs',e' = type_coerce l d_env t' (rebuild tannot) expect_actual in
          (e',t,t_env,cs@cs',ef)
        | Tapp("register",[TA_typ(t')]),_ ->
	  let ef' = add_effect (BE_aux(BE_rreg,l)) ef in
          let tannot = Some(([],t),External (Some i),cs,ef') in
          let t',cs',e' = type_coerce l d_env t' (rebuild tannot) expect_actual in
          (e',t',t_env,cs@cs',ef)
        | Tapp("reg",[TA_typ(t')]),_ ->
          let tannot = Some(([],t),Emp_local,cs,pure_e) in
          let t',cs',e' = type_coerce l d_env t' (rebuild tannot) expect_actual in
          (e',t',t_env,cs@cs',pure_e)
        | _ -> 
          let t',cs',e' = type_coerce l d_env t (rebuild (Some(([],t),tag,cs,pure_e))) expect_t in
          (e',t,t_env,cs@cs',pure_e)
        )
      | Some None | None -> typ_error l ("Identifier " ^ (id_to_string id) ^ " is unbound"))
    | E_lit (L_aux(lit,l')) ->
      let t,lit',effect = (match lit with
        | L_unit  -> unit_t,lit,pure_e
	| L_zero  -> 
          (match expect_t.t with
          | Tid "bool" -> bool_t,L_false,pure_e
          | _ -> bit_t,lit,pure_e)
	| L_one   -> 
          (match expect_t.t with
          | Tid "bool" -> bool_t,L_true,pure_e
          | _ -> bit_t,lit,pure_e)
	| L_true  -> bool_t,lit,pure_e
	| L_false -> bool_t,lit,pure_e
	| L_num i -> 
          (match expect_t.t with
          | Tid "bit" -> 
            if i = 0 then bit_t,L_zero,pure_e
	    else 
	      if i = 1 then bit_t,L_one,pure_e
	      else typ_error l "Expected bit, found a number that cannot be used as a bit"
          | Tid "bool" ->
            if i = 0 then bool_t, L_false,pure_e
            else 
              if i = 1 then bool_t,L_true,pure_e
              else typ_error l "Expected bool, found a number that cannot be used as a bit and converted to bool"
          | _ -> {t = Tapp("range",
			   [TA_nexp{nexp = Nconst i};TA_nexp{nexp= Nconst 0};])},lit,pure_e)
	| L_hex s -> {t = Tapp("vector",
			       [TA_nexp{nexp = Nconst 0};
				TA_nexp{nexp = Nconst ((String.length s)*4)};
				TA_ord{order = Oinc};TA_typ{t = Tid "bit"}])},lit,pure_e
	| L_bin s -> {t = Tapp("vector",
			       [TA_nexp{nexp = Nconst 0};
				TA_nexp{nexp = Nconst(String.length s)};
				TA_ord{order = Oinc};TA_typ{t = Tid"bit"}])},lit,pure_e
	| L_string s -> {t = Tid "string"},lit,pure_e
	| L_undef -> new_t (),lit,{effect=Eset[BE_aux(BE_undef,l)]}) in
      let t',cs',e' = 
	type_coerce l d_env t (E_aux(E_lit(L_aux(lit',l')),(l,(Some(([],t),Emp_local,[],effect))))) expect_t in
      (e',t',t_env,cs',effect)
    | E_cast(typ,e) ->
      let t = typ_to_t typ in
      let t',cs = type_consistent l d_env t expect_t in
      let (e',u,t_env,cs',ef) = check_exp envs t' e in
      (e',t',t_env,cs@cs',ef)        
    | E_app(id,parms) -> 
      let i = id_to_string id in
      (match Envmap.apply t_env i with
      | Some(Some(tp,Enum,cs,ef)) ->
        typ_error l ("Expected function with name " ^ i ^ " but found an enumeration identifier")
      | Some(Some(tp,Default,cs,ef)) ->
        typ_error l ("Function " ^ i ^ " must be defined, not just declared as a default, before use")
      | Some(Some((params,t),tag,cs,ef)) ->
        let t,cs,ef = subst params t cs ef in
        (match t.t with
        | Tfn(arg,ret,ef') ->
          (match parms with
          | [] -> 
            let (p',cs') = type_consistent l d_env unit_t arg in
            let (ret_t,cs_r,e') = type_coerce l d_env ret (rebuild (Some(([],ret),tag,cs@cs',ef))) expect_t in
            (e',ret_t,t_env,cs@cs'@cs_r,ef)
          | [parm] ->
            let (parm',arg_t,t_env,cs',ef_p) = check_exp envs arg parm in
            let (ret_t,cs_r',e') = type_coerce l d_env ret (E_aux(E_app(id,[parm']),(l,(Some(([],ret),tag,cs,ef'))))) expect_t in
            (e',ret_t,t_env,cs@cs'@cs_r',union_effects ef_p ef')
          | parms -> 
            let ((E_aux(E_tuple parms',tannot')),arg_t,t_env,cs',ef_p) = check_exp envs arg (E_aux(E_tuple parms,(l,None))) in
            let (ret_t,cs_r',e') = type_coerce l d_env ret (E_aux(E_app(id, parms'),(l,(Some(([],ret),tag,cs,ef'))))) expect_t in
            (e',ret_t,t_env,cs@cs'@cs_r',union_effects ef_p ef'))
        | _ -> typ_error l ("Expected a function or constructor, found identifier " ^ i ^ " bound to type " ^ (t_to_string t)))
      | _ -> typ_error l ("Unbound function " ^ i)) 
    | E_app_infix(lft,op,rht) -> 
      let i = id_to_string op in
      (match Envmap.apply t_env i with
      | Some(Some(tp,Enum,cs,ef)) ->
        typ_error l ("Expected function with name " ^ i ^ " but found an enumeration identifier")
      | Some(Some(tp,Default,cs,ef)) ->
        typ_error l ("Function " ^ i ^ " must be defined, not just declared as a default, before use")
      | Some(Some((params,t),tag,cs,ef)) ->
        let t,cs,ef = subst params t cs ef in
        (match t.t with
        | Tfn(arg,ret,ef) -> 
          let (E_aux(E_tuple [lft';rht'],tannot'),arg_t,t_env,cs',ef') = check_exp envs arg (E_aux(E_tuple [lft;rht],(l,None))) in
          let ret_t,cs_r',e' = type_coerce l d_env ret (E_aux(E_app_infix(lft',op,rht'),(l,(Some(([],ret),tag,cs,ef))))) expect_t in
          (e',ret_t,t_env,cs@cs'@cs_r',union_effects ef ef')
        | _ -> typ_error l ("Expected a function or constructor, found identifier " ^ i ^ " bound to type " ^ (t_to_string t)))
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
		let (e',t',_,c,ef) = check_exp envs t e in ((e'::exps),(t'::typs),c@consts,union_effects ef effect))
              exps ts ([],[],[],pure_e) in
          let t = {t = Ttup typs} in
          (E_aux(E_tuple(exps),(l,Some(([],t),Emp_local,[],pure_e))),t,t_env,consts,effect)
        else typ_error l ("Expected a tuple with length " ^ (string_of_int tl) ^ " found one of length " ^ (string_of_int el))
      | _ ->
        let exps,typs,consts,effect = 
          List.fold_right 
	    (fun e (exps,typs,consts,effect) -> 
	      let (e',t,_,c,ef) = check_exp envs (new_t ()) e in ((e'::exps),(t::typs),c@consts,union_effects ef effect))
	    exps ([],[],[],pure_e) in
        let t = { t=Ttup typs } in
        let t',cs',e' = type_coerce l d_env t (E_aux(E_tuple(exps),(l,Some(([],t),Emp_local,[],pure_e)))) expect_t in
        (e',t',t_env,consts@cs',effect))
    | E_if(cond,then_,else_) ->
      let (cond',_,_,c1,ef1) = check_exp envs bool_t cond in
      let then',then_t,then_env,then_c,then_ef = check_exp envs expect_t then_ in
      let else',else_t,else_env,else_c,else_ef = check_exp envs expect_t else_ in
      (E_aux(E_if(cond',then',else'),(l,Some(([],expect_t),Emp_local,[],pure_e))),
       expect_t,Envmap.intersect_merge (tannot_merge l d_env) then_env else_env,then_c@else_c@c1,
       union_effects ef1 (union_effects then_ef else_ef))
    | E_for(id,from,to_,step,order,block) -> 
      let fb,fr,tb,tr,sb,sr = new_n(),new_n(),new_n(),new_n(),new_n(),new_n() in
      let ft,tt,st = {t=Tapp("range",[TA_nexp fb;TA_nexp fr])},
	{t=Tapp("range",[TA_nexp tb;TA_nexp tr])},{t=Tapp("range",[TA_nexp sb;TA_nexp sr])} in     
      let from',from_t,_,from_c,from_ef = check_exp envs ft from in
      let to_',to_t,_,to_c,to_ef = check_exp envs tt to_ in
      let step',step_t,_,step_c,step_ef = check_exp envs st step in
      let new_annot,local_cs = 
	match (aorder_to_ord order).order with
	  | Oinc ->
	    (Some(([],{t=Tapp("range",[TA_nexp fb;TA_nexp {nexp=Nadd(tb,tr)}])}),Emp_local,[],pure_e),
	     [LtEq(l,{nexp=Nadd(fb,fr)},{nexp=Nadd(tb,tr)});LtEq(l,fb,tb)])
	  | Odec ->
	    (Some(([],{t=Tapp("range",[TA_nexp tb; TA_nexp {nexp=Nadd(fb,fr)}])}),Emp_local,[],pure_e),
	     [GtEq(l,{nexp=Nadd(fb,fr)},{nexp=Nadd(tb,tr)});GtEq(l,fb,tb)])
	  | _ -> (typ_error l "Order specification in a foreach loop must be either inc or dec, not polymorphic")
      in
      let (block',b_t,_,b_c,b_ef) = check_exp (Env(d_env,Envmap.insert t_env (id_to_string id,new_annot))) expect_t block in
      (E_aux(E_for(id,from',to_',step',order,block'),(l,Some(([],b_t),Emp_local,local_cs,pure_e))),expect_t,Envmap.empty,
       b_c@from_c@to_c@step_c@local_cs,(union_effects b_ef (union_effects step_ef (union_effects to_ef from_ef))))
    | E_vector(es) ->
      let item_t = match expect_t.t with
        | Tapp("vector",[base;rise;ord;TA_typ item_t]) -> item_t
          (* TODO: Consider whether an range should be looked for here*)
        | _ -> new_t () in
      let es,cs,effect = (List.fold_right 
			    (fun (e,_,_,c,ef) (es,cs,effect) -> (e::es),(c@cs),union_effects ef effect)
			    (List.map (check_exp envs item_t) es) ([],[],pure_e)) in
      let t = {t = Tapp("vector",[TA_nexp({nexp=Nconst 0});TA_nexp({nexp=Nconst (List.length es)});TA_ord({order=Oinc});TA_typ item_t])} in
      let t',cs',e' = type_coerce l d_env t (E_aux(E_vector es,(l,Some(([],t),Emp_local,[],pure_e)))) expect_t in
      (e',t',t_env,cs@cs',effect)
    | E_vector_indexed eis ->
      let item_t = match expect_t.t with
        | Tapp("vector",[base;rise;ord;TA_typ item_t]) -> item_t
          (* TODO: Consider whether an range should be looked for here*)
        | _ -> new_t () in
      let first,last = fst (List.hd eis), fst (List.hd (List.rev eis)) in
      let is_increasing = first <= last in
      let es,cs,effect,_ = (List.fold_right 
			      (fun ((i,e),c,ef) (es,cs,effect,prev) -> 
				if is_increasing 
				then if prev <= i then (((i,e)::es),(c@cs),union_effects ef effect,i) 
				  else (typ_error l "Indexed vector is not consistently increasing")
				else if i <= prev then (((i,e)::es),(c@cs),union_effects ef effect,i) 
				else (typ_error l "Indexed vector is not consistently decreasing"))
			      (List.map (fun (i,e) -> let (e,_,_,cs,eft) = (check_exp envs item_t e) in ((i,e),cs,eft))
				 eis) ([],[],pure_e,first)) in
      let t = {t = Tapp("vector",[TA_nexp({nexp=Nconst first});TA_nexp({nexp=Nconst (List.length eis)});
				  TA_ord({order= if is_increasing then Oinc else Odec});TA_typ item_t])} in
      let t',cs',e' = type_coerce l d_env t (E_aux(E_vector_indexed es,(l,Some(([],t),Emp_local,[],pure_e)))) expect_t in
      (e',t',t_env,cs@cs',effect)
    | E_vector_access(vec,i) ->
      let base,rise,ord = new_n(),new_n(),new_o() in
      let min,m_rise = new_n(),new_n() in
      let item_t = new_t () in
      let vt = {t= Tapp("vector",[TA_nexp base;TA_nexp rise;TA_ord ord; TA_typ item_t])} in
      let (vec',t',_,cs,ef) = check_exp envs vt vec in
      let it = {t= Tapp("range",[TA_nexp min;TA_nexp m_rise])} in
      let (i',ti',_,cs_i,ef_i) = check_exp envs it i in
      let cs_loc = 
	match ord.order with
	  | Oinc ->
	    [LtEq(l,base,min); LtEq(l,{nexp=Nadd(min,m_rise)},{nexp=Nadd(base,rise)})] 
	  | Odec -> 
	    [GtEq(l,base,min); LtEq(l,{nexp=Nadd(min,m_rise)},{nexp=Nadd(base,{nexp=Nneg rise})})]
	  | _ -> typ_error l "A vector must be either increasing or decreasing to access a single element"
      in 
      let t',cs',e'=type_coerce l d_env item_t (E_aux(E_vector_access(vec',i'),(l,Some(([],item_t),Emp_local,[],pure_e)))) expect_t in
      (e',t',t_env,cs_loc@cs_i@cs@cs',union_effects ef ef_i)
    | E_vector_subrange(vec,i1,i2) ->
      let base,rise,ord = new_n(),new_n(),new_o() in
      let min1,m_rise1 = new_n(),new_n() in
      let min2,m_rise2 = new_n(),new_n() in
      let base_n,rise_n,ord_n,item_t = match expect_t.t with
	| Tapp("vector",[TA_nexp base_n;TA_nexp rise_n; TA_ord ord_n; TA_typ item_t]) -> base_n,rise_n,ord_n,item_t
	| _ -> new_n(),new_n(),new_o(),new_t() in
      let vt = {t=Tapp("vector",[TA_nexp base;TA_nexp rise;TA_ord ord;TA_typ item_t])} in
      let (vec',t',_,cs,ef) = check_exp envs vt vec in
      let i1t = {t=Tapp("range",[TA_nexp min1;TA_nexp m_rise1])} in
      let (i1', ti1, _,cs_i1,ef_i1) = check_exp envs i1t i1 in
      let i2t = {t=Tapp("range",[TA_nexp min2;TA_nexp m_rise2])} in
      let (i2', ti2, _,cs_i2,ef_i2) = check_exp envs i2t i2 in
      let cs_loc =
	match ord.order with
	  | Oinc -> 
	    [LtEq(l,base,min1); LtEq(l,{nexp=Nadd(min1,m_rise1)},{nexp=Nadd(min2,m_rise2)}); 
	     LtEq(l,{nexp=Nadd(min2,m_rise2)},{nexp=Nadd(base,rise)});
	     LtEq(l,min1,base_n); LtEq(l,base_n,{nexp=Nadd(min1,m_rise1)});
	     LtEq(l,rise_n,{nexp=Nadd(min2,m_rise2)})]
	  | Odec ->
	    [GtEq(l,base,{nexp=Nadd(min1,m_rise1)}); GtEq(l,{nexp=Nadd(min1,m_rise1)},{nexp=Nadd(min2,m_rise2)});
	     GtEq(l,{nexp=Nadd(min2,m_rise2)},{nexp=Nadd(base,{nexp=Nneg rise})});
	     GtEq(l,min1,base_n); GtEq(l,base_n,{nexp=Nadd(min1,m_rise1)});
	     GtEq(l,rise_n,{nexp=Nadd(min2,m_rise2)})]
	  | _ -> typ_error l "A vector must be either increasing or decreasing to access a slice" in
      let nt = {t=Tapp("vector",[TA_nexp base_n;TA_nexp rise_n; TA_ord ord;TA_typ item_t])} in
      let (t,cs3,e') = 
	type_coerce l d_env nt (E_aux(E_vector_subrange(vec',i1',i2'),(l,Some(([],nt),Emp_local,cs_loc,pure_e)))) expect_t in
      (e',t,t_env,cs3@cs@cs_i1@cs_i2@cs_loc,(union_effects ef (union_effects ef_i1 ef_i2)))
    | E_vector_update(vec,i,e) ->
      let base,rise,ord = new_n(),new_n(),new_o() in
      let min,m_rise = new_n(),new_n() in
      let item_t = match expect_t.t with
	| Tapp("vector",[TA_nexp base_n;TA_nexp rise_n; TA_ord ord_n; TA_typ item_t]) -> item_t
	| _ -> new_t() in
      let vt = {t=Tapp("vector",[TA_nexp base;TA_nexp rise;TA_ord ord;TA_typ item_t])} in
      let (vec',t',_,cs,ef) = check_exp envs vt vec in
      let it = {t=Tapp("range",[TA_nexp min;TA_nexp m_rise])} in
      let (i', ti, _,cs_i,ef_i) = check_exp envs it i in
      let (e', te, _,cs_e,ef_e) = check_exp envs item_t e in
      let cs_loc = 
	match ord.order with
	  | Oinc ->
	    [LtEq(l,base,min); LtEq(l,{nexp=Nadd(min,m_rise)},{nexp=Nadd(base,rise)})] 
	  | Odec -> 
	    [GtEq(l,base,min); LtEq(l,{nexp=Nadd(min,m_rise)},{nexp=Nadd(base,{nexp=Nneg rise})})]
	  | _ -> typ_error l "A vector must be either increasing or decreasing to change a single element"
      in      
      let nt = {t=Tapp("vector",[TA_nexp base;TA_nexp rise; TA_ord ord;TA_typ item_t])} in
      let (t,cs3,e') = 
	type_coerce l d_env nt (E_aux(E_vector_update(vec',i',e'),(l,Some(([],nt),Emp_local,cs_loc,pure_e)))) expect_t in
      (e',t,t_env,cs3@cs@cs_i@cs_e@cs_loc,(union_effects ef (union_effects ef_i ef_e)))
    | E_vector_update_subrange(vec,i1,i2,e) ->
      let base,rise,ord = new_n(),new_n(),new_o() in
      let min1,m_rise1 = new_n(),new_n() in
      let min2,m_rise2 = new_n(),new_n() in
      let item_t = match expect_t.t with
	| Tapp("vector",[TA_nexp base_n;TA_nexp rise_n; TA_ord ord_n; TA_typ item_t]) -> item_t
	| _ -> new_t() in
      let vt = {t=Tapp("vector",[TA_nexp base;TA_nexp rise;TA_ord ord;TA_typ item_t])} in
      let (vec',t',_,cs,ef) = check_exp envs vt vec in
      let i1t = {t=Tapp("range",[TA_nexp min1;TA_nexp m_rise1])} in
      let (i1', ti1, _,cs_i1,ef_i1) = check_exp envs i1t i1 in
      let i2t = {t=Tapp("range",[TA_nexp min2;TA_nexp m_rise2])} in
      let (i2', ti2, _,cs_i2,ef_i2) = check_exp envs i2t i2 in
      let (e',item_t',_,cs_e,ef_e) =
	try check_exp envs item_t e with
	  | _ ->
	    let (base_e,rise_e) = new_n(),new_n() in
	    let (e',ti',env_e,cs_e,ef_e) = 
	      check_exp envs {t=Tapp("vector",[TA_nexp base_e;TA_nexp rise_e;TA_ord ord;TA_typ item_t])} e in
	    let cs_add = [Eq(l,base_e,min1);LtEq(l,rise,m_rise2)] in
	    (e',ti',env_e,cs_e@cs_add,ef_e) in	     
      let cs_loc =
	match ord.order with
	  | Oinc -> 
	    [LtEq(l,base,min1); LtEq(l,{nexp=Nadd(min1,m_rise1)},{nexp=Nadd(min2,m_rise2)}); 
	     LtEq(l,{nexp=Nadd(min2,m_rise2)},{nexp=Nadd(base,rise)});]
	  | Odec ->
	    [GtEq(l,base,{nexp=Nadd(min1,m_rise1)}); GtEq(l,{nexp=Nadd(min1,m_rise1)},{nexp=Nadd(min2,m_rise2)});
	     GtEq(l,{nexp=Nadd(min2,m_rise2)},{nexp=Nadd(base,{nexp=Nneg rise})});]
	  | _ -> typ_error l "A vector must be either increasing or decreasing to modify a slice" in
      let nt = {t=Tapp("vector",[TA_nexp base;TA_nexp rise; TA_ord ord;TA_typ item_t])} in
      let (t,cs3,e') = 
       type_coerce l d_env nt (E_aux(E_vector_update_subrange(vec',i1',i2',e'),(l,Some(([],nt),Emp_local,cs_loc,pure_e)))) expect_t in
      (e',t,t_env,cs3@cs@cs_i1@cs_i2@cs_loc@cs_e,(union_effects ef (union_effects ef_i1 (union_effects ef_i2 ef_e))))
    | E_list(es) ->
      let item_t = match expect_t.t with
	| Tapp("list",[TA_typ i]) -> i
	| _ -> new_t() in
      let es,cs,effect = 
	(List.fold_right (fun (e,_,_,c,ef) (es,cs,effect) -> (e::es),(c@cs),union_effects ef effect) 
	   (List.map (check_exp envs item_t) es) ([],[],pure_e)) in
      let t = {t = Tapp("list",[TA_typ item_t])} in
      let t',cs',e' = type_coerce l d_env t (E_aux(E_list es,(l,Some(([],t),Emp_local,[],pure_e)))) expect_t in
      (e',t',t_env,cs@cs',effect)
    | E_cons(ls,i) ->
      let item_t = match expect_t.t with
	| Tapp("list",[TA_typ i]) -> i
	| _ -> new_t() in
      let lt = {t=Tapp("list",[TA_typ item_t])} in
      let (ls',t',_,cs,ef) = check_exp envs lt ls in
      let (i', ti, _,cs_i,ef_i) = check_exp envs item_t i in
      let (t',cs',e') = type_coerce l d_env lt (E_aux(E_cons(ls',i'),(l,Some(([],lt),Emp_local,[],pure_e)))) expect_t in
      (e',t',t_env,cs@cs'@cs_i,(union_effects ef ef_i))
    | E_record(FES_aux(FES_Fexps(fexps,_),l')) -> 
      let u,_,_ = get_abbrev d_env expect_t in
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
			   | None -> 
			     typ_error l ("Expected a struct of type " ^ n ^ ", which should not have a field " ^ i)
			   | Some((params,et),tag,cs,ef) ->
			     let et,cs,_ = subst params et cs ef in
			     let (e,t',_,c,ef) = check_exp envs et exp in
			     (FE_aux(FE_Fexp(id,e),(l,Some(([],t'),tag,cs@c,ef)))::fexps,cons@cs@c,union_effects ef ef'))
		       fexps ([],[],pure_e) in
		   E_aux(E_record(FES_aux(FES_Fexps(fexps,false),l')),(l,Some(([],u),Emp_local,[],pure_e))),expect_t,t_env,cons,ef
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
		      | None -> raise (Reporting_basic.err_unreachable l "field_match didn't have a full match")
		      | Some((params,et),tag,cs,ef) ->
			let et,cs,_ = subst params et cs ef in
			let (e,t',_,c,ef) = check_exp envs et exp in
			(FE_aux(FE_Fexp(id,e),(l,Some(([],t'),tag,cs@c,ef)))::fexps,cons@cs@c,union_effects ef ef'))
		  fexps ([],[],pure_e) in
	      expect_t.t <- Tid i;
	      E_aux(E_record(FES_aux(FES_Fexps(fexps,false),l')),(l,Some(([],expect_t),Emp_local,[],pure_e))),expect_t,t_env,cons,ef
	    | Some(i,Register,fields) -> typ_error l "Expected a value with register type, found a struct")
	| _ -> typ_error l ("Expected an expression of type " ^ t_to_string expect_t ^ " but found a struct"))
    | E_record_update(exp,FES_aux(FES_Fexps(fexps,_),l')) -> 
      let (e',t',_,c,ef) = check_exp envs expect_t exp in
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
			   | None -> 
			     typ_error l ("Expected a struct with type " ^ i ^ ", which does not have a field " ^ fi)
			   | Some((params,et),tag,cs,ef) ->
			     let et,cs,_ = subst params et cs ef in
			     let (e,t',_,c,ef) = check_exp envs et exp in
			     (FE_aux(FE_Fexp(id,e),(l,Some(([],t'),tag,cs@c,ef)))::fexps,cons@cs@c,union_effects ef ef'))
		       fexps ([],[],pure_e) in
		   E_aux(E_record_update(e',FES_aux(FES_Fexps(fexps,false),l')),
			 (l,Some(([],expect_t),Emp_local,[],pure_e))),expect_t,t_env,cons,ef
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
		      | None -> raise (Reporting_basic.err_unreachable l "field_match didn't have a full match")
		      | Some((params,et),tag,cs,ef) ->
			let et,cs,_ = subst params et cs ef in
			let (e,t',_,c,ef) = check_exp envs et exp in
			(FE_aux(FE_Fexp(id,e),(l,Some(([],t'),tag,cs@c,ef)))::fexps,cons@cs@c,union_effects ef ef'))
		  fexps ([],[],pure_e) in
	      expect_t.t <- Tid i;
	      E_aux(E_record_update(e',FES_aux(FES_Fexps(fexps,false),l')),
		    (l,Some(([],expect_t),Emp_local,[],pure_e))),expect_t,t_env,cons,ef
	    | [(i,Register,fields)] -> typ_error l "Expected a value with register type, found a struct"
	    | records -> typ_error l "Multiple structs contain this set of fields, try adding a cast to disambiguate")
	| _ -> typ_error l ("Expected a struct to update but found an expression of type " ^ t_to_string expect_t))
    | E_field(exp,id) ->
      let (e',t',_,c,ef) = check_exp envs (new_t()) exp in
      (match t'.t with
      | Tabbrev({t=Tid i}, t2) ->
	  (match lookup_record_typ i d_env.rec_env with
	    | None -> typ_error l ("Expected a struct or register for this access, instead found an expression with type " ^ i)
	    | Some(((i,rec_kind,fields) as r)) ->
	      let fi = id_to_string id in
	      (match lookup_field_type fi r with
		| None -> 
		  typ_error l ("Type " ^ i ^ " does not have a field " ^ fi)
		| Some((params,et),tag,cs,ef) ->
		  let et,cs,ef = subst params et cs ef in
		  let (et',c',acc) = type_coerce l d_env et (E_aux(E_field(e',id),(l,Some(([],et),tag,cs,ef)))) expect_t in
		  (acc,et',t_env,cs@c',ef)))        
      | Tid i ->
	  (match lookup_record_typ i d_env.rec_env with
	    | None -> typ_error l ("Expected a struct or register for this access, instead found an expression with type " ^ i)
	    | Some(((i,rec_kind,fields) as r)) ->
	      let fi = id_to_string id in
	      (match lookup_field_type fi r with
		| None -> 
		  typ_error l ("Type " ^ i ^ " does not have a field " ^ fi)
		| Some((params,et),tag,cs,ef) ->
		  let et,cs,ef = subst params et cs ef in
		  let (et',c',acc) = type_coerce l d_env et (E_aux(E_field(e',id),(l,Some(([],et),tag,cs,ef)))) expect_t in
		  (acc,et',t_env,cs@c',ef)))
	| Tuvar _ ->
	  let fi = id_to_string id in
	  (match lookup_possible_records [fi] d_env.rec_env with
	    | [] -> typ_error l ("No struct has a field " ^ fi)
	    | [(((i,rkind,fields) as r))] ->
	      let fi = id_to_string id in
	      (match lookup_field_type fi r with
		| None -> 
		  raise (Reporting_basic.err_unreachable l "lookup_possible_records returned a record that didn't include the field")
		| Some((params,et),tag,cs,ef) ->
		  let et,cs,ef = subst params et cs ef in
		  let (et',c',acc) = type_coerce l d_env et (E_aux(E_field(e',id),(l,Some(([],et),tag,cs,ef)))) expect_t in
		  t'.t <- Tid i;
		  (acc,et',t_env,cs@c',ef))
	    | records -> typ_error l ("Multiple structs contain field " ^ fi ^ ", try adding a cast to disambiguate"))
	| _ -> typ_error l ("Expected a struct or register for access but found an expression of type " ^ t_to_string t'))
    | E_case(exp,pexps) ->
      (*let check_t = new_t() in*)
      let (e',t',_,cs,ef) = check_exp envs (new_t()) exp in
      (*let _ = Printf.printf "Type of pattern after expression check %s\n" (t_to_string t') in*)
      let t' = 
	match t'.t with
	  | Tapp("register",[TA_typ t]) -> t
	  | _ -> t' in
      (*let _ = Printf.printf "Type of pattern after register check %s\n" (t_to_string t') in*)
      let (pexps',t,cs',ef') = check_cases envs t' expect_t pexps in
      (E_aux(E_case(e',pexps'),(l,Some(([],t),Emp_local,[],pure_e))),t,t_env,cs@cs',union_effects ef ef')
    | E_let(lbind,body) -> 
      let (lb',t_env',cs,ef) = (check_lbind envs Emp_local lbind) in
      let (e,t,_,cs',ef') = check_exp (Env(d_env,Envmap.union_merge (tannot_merge l d_env) t_env t_env')) expect_t body in
      (E_aux(E_let(lb',e),(l,Some(([],t),Emp_local,[],pure_e))),t,t_env,cs@cs',union_effects ef ef')
    | E_assign(lexp,exp) ->
      let (lexp',t',t_env',tag,cs,ef) = check_lexp envs true lexp in
      let (exp',t'',_,cs',ef') = check_exp envs t' exp in
      let (t',c') = type_consistent l d_env unit_t expect_t in
      (E_aux(E_assign(lexp',exp'),(l,(Some(([],unit_t),tag,[],ef)))),unit_t,t_env',cs@cs'@c',union_effects ef ef')
		    
and check_block orig_envs envs expect_t exps : ((tannot exp) list * tannot * tannot emap * nexp_range list * t * effect) =
  let Env(d_env,t_env) = envs in
  match exps with
    | [] -> ([],None,orig_envs,[],unit_t,pure_e)
    | [e] -> let (E_aux(e',(l,annot)),t,envs,sc,ef) = check_exp envs expect_t e in
	     ([E_aux(e',(l,annot))],annot,orig_envs,sc,t,ef)
    | e::exps -> let (e',t',t_env',sc,ef') = check_exp envs unit_t e in
		 let (exps',annot',orig_envs,sc',t,ef) = check_block orig_envs (Env(d_env,Envmap.union_merge (tannot_merge Parse_ast.Unknown d_env) t_env t_env')) expect_t exps in
		 ((e'::exps'),annot',orig_envs,sc@sc',t,union_effects ef ef')

and check_cases envs check_t expect_t pexps : ((tannot pexp) list * typ * nexp_range list * effect) =
  let (Env(d_env,t_env)) = envs in
  match pexps with
    | [] -> raise (Reporting_basic.err_unreachable Parse_ast.Unknown "switch with no cases found")
    | [(Pat_aux(Pat_exp(pat,exp),(l,annot)))] ->
      let pat',env,cs_p,u = check_pattern envs Emp_local (new_t ()) pat in
      let t',cs_p' = type_consistent l d_env u check_t in
      let (e,t,_,cs2,ef2) = check_exp (Env(d_env,Envmap.union_merge (tannot_merge l d_env) t_env env)) expect_t exp in
      [Pat_aux(Pat_exp(pat',e),(l,Some(([],t),Emp_local,cs_p@cs_p'@cs2,ef2)))],t,cs_p@cs_p'@cs2,ef2
    | ((Pat_aux(Pat_exp(pat,exp),(l,annot)))::pexps) ->
      let pat',env,cs_p,u = check_pattern envs Emp_local check_t pat in
      let t',cs_p' = type_consistent l d_env u check_t in
      let (e,t,_,cs2,ef2) = check_exp (Env(d_env,Envmap.union_merge (tannot_merge l d_env) t_env env)) expect_t exp in
      let (pes,t'',csl,efl) = check_cases envs check_t expect_t pexps in
      ((Pat_aux(Pat_exp(pat',e),(l,(Some(([],t''),Emp_local,(csl@cs_p@cs_p'@cs2),(union_effects efl ef2))))))::pes,
       t'',
       csl@cs_p@cs_p'@cs2,union_effects efl ef2)

and check_lexp envs is_top (LEXP_aux(lexp,(l,annot))) : (tannot lexp * typ * tannot emap * tag *nexp_range list *effect ) =
  let (Env(d_env,t_env)) = envs in
  match lexp with
    | LEXP_id id -> 
      let i = id_to_string id in
      (match Envmap.apply t_env i with
	| Some(Some((parms,t),Default,_,_)) ->
	  typ_error l ("Identifier " ^ i ^ " cannot be assigned when only a default specification exists")
	| Some(Some((parms,t),tag,cs,_)) ->
	  let t,cs,_ = match tag with | External _ | Emp_global -> subst parms t cs pure_e | _ -> t,cs,pure_e in
	  let t,cs',_ = get_abbrev d_env t in
          let t_actual = match t.t with 
            | Tabbrev(i,t) -> t
            | _ -> t in
	  (match t_actual.t,is_top with
	    | Tapp("register",[TA_typ u]),_ ->
	      let ef = {effect=Eset[BE_aux(BE_wreg,l)]} in
	      (LEXP_aux(lexp,(l,(Some(([],t),External (Some i),cs@cs',ef)))),u,Envmap.empty,External (Some i),[],ef)
	    | Tapp("reg",[TA_typ u]),_ ->
	      (LEXP_aux(lexp,(l,(Some(([],t),Emp_local,cs@cs',pure_e)))),u,Envmap.empty,Emp_local,[],pure_e)
	    | Tapp("vector",_),false ->
	      (LEXP_aux(lexp,(l,(Some(([],t),Emp_local,cs@cs',pure_e)))),t,Envmap.empty,Emp_local,[],pure_e)
	    | _,_ -> 
	      if is_top
	      then typ_error l 
		("Can only assign to identifiers with type register or reg, found identifier " ^ i ^ " with type " ^ t_to_string t)
	      else 
		(LEXP_aux(lexp,(l,(Some(([],t),Emp_local,cs@cs',pure_e)))),t,Envmap.empty,Emp_local,[],pure_e) (* TODO, make sure this is a record *))
	| _ -> 
	  let u = new_t() in
	  let t = {t=Tapp("reg",[TA_typ u])} in
	  let tannot = (Some(([],t),Emp_local,[],pure_e)) in
	  (LEXP_aux(lexp,(l,tannot)),u,Envmap.from_list [i,tannot],Emp_local,[],pure_e))
    | LEXP_memory(id,exps) -> 
      let i = id_to_string id in
      (match Envmap.apply t_env i with
	| Some(Some((parms,t),tag,cs,ef)) ->
	  let is_external = match tag with | External any -> true | _ -> false in
	  let t,cs,ef = subst parms t cs ef in
	  (match t.t with
	    | Tfn(apps,out,ef') ->
	      (match ef'.effect with
		| Eset effects ->
		  if List.exists (fun (BE_aux(b,_)) -> match b with | BE_wmem -> true | _ -> false) effects 
		  then
                    let app,cs_a,_ = get_abbrev d_env apps in
                    let out,cs_o,_ = get_abbrev d_env out in
                    (match app.t with
		      | Ttup ts | Tabbrev(_,{t=Ttup ts}) -> 
			let (E_aux(E_tuple es,(l',tannot)),t',_,cs',ef_e) = check_exp envs apps (E_aux(E_tuple exps,(l,None))) in
			let item_t = match out.t with
			  | Tid "unit" -> {t = Tapp("vector",[TA_nexp (new_n());TA_nexp (new_n()); TA_ord (new_o());TA_typ bit_t])}
			  | _ -> out in
			let ef = if is_external then add_effect (BE_aux(BE_wmem,l)) ef_e else union_effects ef ef_e in
			(LEXP_aux(LEXP_memory(id,es),(l,Some(([],unit_t),tag,cs@cs',ef))),item_t,Envmap.empty,tag,cs@cs',ef)
		      | app_t -> 
			let e = match exps with
			  | [] -> E_aux(E_lit(L_aux(L_unit,l)),(l,None))
			  | [e] -> e
			  | es -> typ_error l ("Expected only one argument for memory access of " ^ i) in
			let (e,t',_,cs',ef_e) = check_exp envs apps e in
			let item_t = match out.t with
			  | Tid "unit" -> {t = Tapp("vector",[TA_nexp (new_n());TA_nexp (new_n()); TA_ord (new_o());TA_typ bit_t])} 
			  | _ -> out in
			  let ef = if is_external then add_effect (BE_aux(BE_wmem,l)) ef_e else union_effects ef ef_e in
			  (LEXP_aux(LEXP_memory(id,[e]),(l,Some(([],unit_t),tag,cs@cs',ef))), item_t,Envmap.empty,tag,cs@cs',ef))
		  else typ_error l ("Memory assignments require functions with wmem effect")
		| _ -> typ_error l ("Memory assignments require functions with declared wmem effect"))
	    | _ -> typ_error l ("Memory assignments require functions, found " ^ i ^ " which has type " ^ (t_to_string t)))
	| _ -> typ_error l ("Unbound identifier " ^ i))
    | LEXP_cast(typ,id) -> 
      let i = id_to_string id in
      let ty = typ_to_t typ in
      (match Envmap.apply t_env i with
	| Some(Some((parms,t),Default,_,_)) ->
	  typ_error l ("Identifier " ^ i ^ " cannot be assigned when only a default specification exists")
	| Some(Some((parms,t),tag,cs,_)) ->
	  let t,cs,_ = match tag with | External _ | Emp_global -> subst parms t cs pure_e | _ -> t,cs,pure_e in
	  let t,cs',_ = get_abbrev d_env t in
          let t_actual = match t.t with | Tabbrev(_,t) -> t | _ -> t in
	  (match t_actual.t,is_top with
	    | Tapp("register",[TA_typ u]),_ ->
	      let t',cs = type_consistent l d_env ty u in
	      let ef = {effect=Eset[BE_aux(BE_wreg,l)]} in
	      (LEXP_aux(lexp,(l,(Some(([],t),External (Some i),cs,ef)))),ty,Envmap.empty,External (Some i),[],ef)
	    | Tapp("reg",[TA_typ u]),_ ->
	      let t',cs = type_consistent l d_env ty u in
	      (LEXP_aux(lexp,(l,(Some(([],t),Emp_local,cs,pure_e)))),ty,Envmap.empty,Emp_local,[],pure_e)
	    | Tapp("vector",_),false ->
	      (LEXP_aux(lexp,(l,(Some(([],t),Emp_local,cs,pure_e)))),ty,Envmap.empty,Emp_local,[],pure_e)
	    | Tuvar _,_ ->
	      let u' = {t=Tapp("reg",[TA_typ ty])} in
	      t.t <- u'.t;
	      (LEXP_aux(lexp,(l,(Some((([],u'),Emp_local,cs,pure_e))))),ty,Envmap.empty,Emp_local,[],pure_e)
	    | _,_ -> 
	      if is_top
	      then typ_error l 
		("Can only assign to identifiers with type register or reg, found identifier " ^ i ^ " with type " ^ t_to_string t)
	      else 
		(LEXP_aux(lexp,(l,(Some(([],t),Emp_local,cs,pure_e)))),ty,Envmap.empty,Emp_local,[],pure_e)) (* TODO, make sure this is a record *)
	| _ -> 
	  let t = {t=Tapp("reg",[TA_typ ty])} in
	  let tannot = (Some(([],t),Emp_local,[],pure_e)) in
	  (LEXP_aux(lexp,(l,tannot)),ty,Envmap.from_list [i,tannot],Emp_local,[],pure_e))
    | LEXP_vector(vec,acc) -> 
      let (vec',item_t,env,tag,csi,ef) = check_lexp envs false vec in
      let item_t,cs',_ = get_abbrev d_env item_t in
      let item_actual = match item_t.t with | Tabbrev(_,t) -> t | _ -> item_t in
      (match item_actual.t with
	| Tapp("vector",[TA_nexp base;TA_nexp rise;TA_ord ord;TA_typ t]) ->
	  let acc_t = match ord.order with
	    | Oinc -> {t = Tapp("range",[TA_nexp base;TA_nexp rise])} 
	    | Odec -> {t = Tapp("range",[TA_nexp {nexp = Nadd(base,{nexp=Nneg rise})};TA_nexp base])} 
	    | _ -> typ_error l ("Assignment to one vector element requires either inc or dec order")
	  in
	  let (e,t',_,cs',ef_e) = check_exp envs acc_t acc in
	  let t,add_reg_write = 
	    match t.t with
	      | Tapp("register",[TA_typ t]) | Tabbrev(_,{t=Tapp("register",[TA_typ t])}) -> t,true
	      | _ -> t,false in
	  let ef = if add_reg_write then add_effect (BE_aux(BE_wreg,l)) ef else ef in
	  (LEXP_aux(LEXP_vector(vec',e),(l,Some(([],t),tag,csi,ef))),t,env,tag,csi@cs',union_effects ef ef_e)
	| Tuvar _ -> typ_error l "Assignment to one position expected a vector with a known order, found a polymorphic value, try adding a cast"
	| _ -> typ_error l ("Assignment expected vector, found assignment to type " ^ (t_to_string item_t))) 
    | LEXP_vector_range(vec,e1,e2)-> 
      let (vec',item_t,env,tag,csi,ef) = check_lexp envs false vec in
      let item_t,cs,_ = get_abbrev d_env item_t in
      let item_actual = match item_t.t with | Tabbrev(_,t) -> t | _ -> item_t in
      let item_actual,add_reg_write,cs = 
	match item_actual.t with
	  | Tapp("register",[TA_typ t]) ->
	    (match get_abbrev d_env t with
	      | {t=Tabbrev(_,t)},cs',_ | t,cs',_ -> t,true,cs@cs')
	  | _ -> item_actual,false,cs in
      (match item_actual.t with
	| Tapp("vector",[TA_nexp base;TA_nexp rise;TA_ord ord;TA_typ t]) ->
	  let base_e1,range_e1,base_e2,range_e2 = new_n(),new_n(),new_n(),new_n() in
	  let base_t = {t=Tapp("range",[TA_nexp base_e1;TA_nexp range_e1])} in
	  let range_t = {t=Tapp("range",[TA_nexp base_e2;TA_nexp range_e2])} in
	  let cs_t,res_t = match ord.order with
	    | Oinc ->  ([LtEq(l,base,base_e1);
			 LtEq(l,{nexp=Nadd(base_e1,range_e1)},{nexp=Nadd(base_e2,range_e2)});
			 LtEq(l,{nexp=Nadd(base_e1,range_e2)},{nexp=Nadd(base,rise)})],
			{t=Tapp("vector",[TA_nexp base_e1;TA_nexp {nexp=Nadd(base_e2,range_e2)};TA_ord ord;TA_typ t])})
	    | Odec -> ([GtEq(l,base,base_e1);
			GtEq(l,{nexp=Nadd(base_e1,range_e1)},{nexp=Nadd(base_e2,range_e2)});
			GtEq(l,{nexp=Nadd(base_e1,range_e2)},{nexp=Nadd(base,{nexp=Nneg rise})})],
		       {t=Tapp("vector",[TA_nexp {nexp=Nadd(base_e1,range_e1)};
					 TA_nexp {nexp=Nadd({nexp=Nadd(base_e1,range_e1)},{nexp=Nneg{nexp=Nadd(base_e2,range_e2)}})};
					 TA_ord ord; TA_typ t])})
	    | _ -> typ_error l ("Assignment to a range of vector elements requires either inc or dec order")
	  in
	  let (e1',t',_,cs1,ef_e) = check_exp envs base_t e1 in
	  let (e2',t',_,cs2,ef_e') = check_exp envs range_t e2 in
	  let cs = cs_t@cs@cs1@cs2 in
	  let ef = union_effects ef (union_effects ef_e ef_e') in
	  (LEXP_aux(LEXP_vector_range(vec',e1',e2'),(l,Some(([],item_t),tag,cs,ef))),res_t,env,tag,cs,ef)
	| Tuvar _ -> typ_error l "Assignement to a range of elements requires a vector with a known order, found a polymorphic value, try addinga  cast"
	| _ -> typ_error l ("Assignment expected vector, found assignment to type " ^ (t_to_string item_t))) 
    | LEXP_field(vec,id)-> 
      let (vec',item_t,env,tag,csi,ef) = check_lexp envs false vec in
      let vec_t = match vec' with
        | LEXP_aux(_,(l',Some((parms,t),_,_,_))) -> t
        | _ -> item_t in
      (match vec_t.t with
	| Tid i | Tabbrev({t=Tid i},_) ->
	  (match lookup_record_typ i d_env.rec_env with
	    | None -> typ_error l ("Expected a register or struct for this update, instead found an expression with type " ^ i)
	    | Some(((i,rec_kind,fields) as r)) ->
	      let fi = id_to_string id in
	      (match lookup_field_type fi r with
		| None -> 
		  typ_error l ("Type " ^ i ^ " does not have a field " ^ fi)
		| Some((params,et),_,cs,_) ->
		  let et,cs,ef = subst params et cs ef in
		  (LEXP_aux(LEXP_field(vec',id),(l,(Some(([],vec_t),tag,csi@cs,ef)))),et,env,tag,csi@cs,ef)))
	| _ -> typ_error l ("Expected a register binding here, found " ^ (t_to_string item_t)))

and check_lbind envs emp_tag (LB_aux(lbind,(l,annot))) : tannot letbind * tannot emap * nexp_range list * effect =
  let Env(d_env,t_env) = envs in
  match lbind with
  | LB_val_explicit(typ,pat,e) -> 
    let tan = typschm_to_tannot envs typ emp_tag in
    (match tan with
    | Some((params,t),tag,cs,ef) ->
      let t,cs,ef = subst params t cs ef in
      let (pat',env,cs1,u) = check_pattern envs emp_tag t pat in
      let t',cs' = type_consistent l d_env u t in
      let (e,t,_,cs2,ef2) = check_exp envs t' e in
      let cs = resolve_constraints cs@cs1@cs'@cs2 in
      let tannot = check_tannot l (Some((params,t),tag,cs,ef)) cs ef (*in top level, must be pure_e*) in
      (LB_aux (LB_val_explicit(typ,pat',e),(l,tannot)),env,cs,ef)
    | None -> raise (Reporting_basic.err_unreachable l "typschm_to_tannot failed to produce a Some"))
  | LB_val_implicit(pat,e) -> 
    let t = new_t () in
    let (pat',env,cs1,u) = check_pattern envs emp_tag (new_t ()) pat in
    let (e,t',_,cs2,ef) = check_exp envs u e in
    let cs = resolve_constraints cs1@cs2 in
    let tannot = check_tannot l (Some(([],t'),emp_tag,cs,ef)) cs ef (* see above *) in
    (LB_aux (LB_val_implicit(pat',e),(l,tannot)), env,cs,ef)

(*val check_type_def : envs -> (tannot type_def) -> (tannot type_def) envs_out*)
let check_type_def envs (TD_aux(td,(l,annot))) =
  let (Env(d_env,t_env)) = envs in
  match td with
    | TD_abbrev(id,nmscm,typschm) -> 
      let tan = typschm_to_tannot envs typschm Emp_global in
      (TD_aux(td,(l,tan)),
       Env( { d_env with abbrevs = Envmap.insert d_env.abbrevs ((id_to_string id),tan)},t_env))
    | TD_record(id,nmscm,typq,fields,_) -> 
      let id' = id_to_string id in
      let (params,constraints) = typq_to_params envs typq in
      let tyannot = Some((params,{t=Tid id'}),Emp_global,constraints,pure_e) in
      let fields' = List.map 
	(fun (ty,i)->(id_to_string i),Some((params,(typ_to_t ty)),Emp_global,constraints,pure_e)) fields in
      (TD_aux(td,(l,tyannot)),Env({d_env with rec_env = (id',Record,fields')::d_env.rec_env},t_env))
    | TD_variant(id,nmscm,typq,arms,_) ->
      let id' = id_to_string id in
      let (params,constraints) = typq_to_params envs typq in
      let ty = {t=Tid id'} in
      let tyannot = Some((params,ty),Constructor,constraints,pure_e) in
      let arm_t input = Some((params,{t=Tfn(input,ty,pure_e)}),Constructor,constraints,pure_e) in
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
      let ty = Some (([],{t = Tid id' }),Enum,[],pure_e) in
      let t_env = List.fold_right (fun id t_env -> Envmap.insert t_env (id,ty)) ids' t_env in
      let enum_env = Envmap.insert d_env.enum_env (id',ids') in
      (TD_aux(td,(l,ty)),Env({d_env with enum_env = enum_env;},t_env))
    | TD_register(id,base,top,ranges) -> 
      let id' = id_to_string id in
      let basei = eval_nexp(anexp_to_nexp base) in
      let topi = eval_nexp(anexp_to_nexp top) in
      match basei.nexp,topi.nexp with
	| Nconst b, Nconst t -> 
	  if b <= t then (
	    let ty = {t = Tapp("vector",[TA_nexp basei; TA_nexp{nexp=Nconst(t-b+1)}; 
					 TA_ord({order = Oinc}); TA_typ({t = Tid "bit"});])} in
	    let franges = 
	      List.map 
		(fun ((BF_aux(idx,l)),id) ->
		  ((id_to_string id),
		   Some(([],
			match idx with
			  | BF_single i -> 
			    if b <= i && i <= t 
			    then {t = Tid "bit"}
			    else typ_error l ("register type declaration " ^ id' ^ " contains a field specification outside of the declared register size")
			  | BF_range(i1,i2) -> 
			    if i1<i2 
			    then if b<=i1 && i2<=t 
			      then {t=Tapp("vector",[TA_nexp {nexp=Nconst i1}; TA_nexp {nexp=Nconst ((i2 - i1) +1)}; TA_ord({order=Oinc}); TA_typ {t=Tid "bit"}])}
			      else typ_error l ("register type declaration " ^ id' ^ " contains a field specification outside of the declared register size")
			    else typ_error l ("register type declaration " ^ id' ^ " is not consistently increasing")
			  | BF_concat _ -> assert false (* What is this supposed to imply again?*)),Emp_global,[],pure_e)))
		ranges 
	    in
	    let tannot = into_register d_env (Some(([],ty),Emp_global,[],pure_e)) in
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
		   Some(([],{t=Tapp("vector",[TA_nexp base;TA_nexp climb;TA_ord({order=Odec});TA_typ({t= Tid "bit"})])}),Emp_global,[],pure_e)))
		ranges 
	    in
	    let tannot = into_register d_env (Some(([],ty),Emp_global,[],pure_e)) in
	    (TD_aux(td,(l,tannot)),
	     Env({d_env with rec_env = (id',Register,franges)::d_env.rec_env;
	       abbrevs = Envmap.insert d_env.abbrevs (id',tannot)},t_env)))
	| _,_ -> raise (Reporting_basic.err_unreachable l "Nexps in register declaration do not evaluate to constants")

let check_val_spec envs (VS_aux(vs,(l,annot))) = 
  let (Env(d_env,t_env)) = envs in
  match vs with
    | VS_val_spec(typs,id) -> 
      let tannot = typschm_to_tannot envs typs Spec in
      (VS_aux(vs,(l,tannot)),
       Env(d_env,(Envmap.insert t_env (id_to_string id,tannot))))
    | VS_extern_no_rename(typs,id) ->
      let tannot = typschm_to_tannot envs typs (External None) in
      (VS_aux(vs,(l,tannot)),
       Env(d_env,(Envmap.insert t_env (id_to_string id,tannot))))
    | VS_extern_spec(typs,id,s) ->
      let tannot = typschm_to_tannot envs typs (External (Some s)) in
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
    | Typ_annot_opt_aux(Typ_annot_opt_some(typq,typ),l') ->
      let (ids,constraints) = typq_to_params envs typq in
      let t = typ_to_t typ in
      let t,constraints,_ = subst ids t constraints pure_e in
      let p_t = new_t () in
      let ef = new_e () in
      t,p_t,Some((ids,{t=Tfn(p_t,t,ef)}),Emp_global,constraints,ef) in
  let check t_env =
    List.split
      (List.map (fun (FCL_aux((FCL_Funcl(id,pat,exp)),(l,annot))) ->
	let (pat',t_env',constraints',t') = check_pattern (Env(d_env,t_env)) Emp_local param_t pat in
        (*let _ = Printf.printf "about to check that %s and %s are consistent\n" (t_to_string t') (t_to_string param_t) in*)
	let u,cs = type_consistent l d_env t' param_t in
	let exp',_,_,constraints,ef = check_exp (Env(d_env,Envmap.union_merge (tannot_merge l d_env) t_env t_env')) ret_t exp in
        (*let _ = Printf.printf "checked function %s : %s -> %s\n" (id_to_string id) (t_to_string param_t) (t_to_string ret_t) in*) 
	(*let _ = (Pretty_print.pp_exp Format.std_formatter) exp' in*)
	(FCL_aux((FCL_Funcl(id,pat',exp')),(l,tannot)),((constraints'@cs@constraints),ef))) funcls) in
  match (in_env,tannot) with
    | Some(Some( (params,u),Spec,constraints,eft)), Some( (p',t),_,c',eft') ->
      (*let _ = Printf.printf "Function %s is in env\n" id in*)
      let u,constraints,eft = subst params u constraints eft in
      let t',cs = type_consistent l d_env t u in
      let t_env = if is_rec then t_env else Envmap.remove t_env id in
      let funcls,cs_ef = check t_env in
      let cs,ef = ((fun (cses,efses) -> (List.concat cses),(List.fold_right union_effects efses pure_e)) (List.split cs_ef)) in
      let cs' = resolve_constraints cs in
      let tannot = check_tannot l tannot cs' ef in
      (FD_aux(FD_function(recopt,tannotopt,effectopt,funcls),(l,tannot))),
      Env(d_env,Envmap.insert t_env (id,tannot))
    | _ , _-> 
      let t_env = if is_rec then Envmap.insert t_env (id,tannot) else t_env in
      let funcls,cs_ef = check t_env in
      let cs,ef = ((fun (cses,efses) -> (List.concat cses),(List.fold_right union_effects efses pure_e)) (List.split cs_ef)) in
      let cs' = resolve_constraints cs in
      let tannot = check_tannot l tannot cs' ef in
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
    | DEF_val letdef -> let (letbind,t_env_let,_,eft) = check_lbind envs Emp_global letdef in
                        (DEF_aux(DEF_val letbind,(l,annot)),Env(d_env,Envmap.union t_env t_env_let))
    | DEF_spec spec -> let vs,envs = check_val_spec envs spec in
		       (DEF_aux(DEF_spec(vs),(l,annot)),envs)
    | DEF_default default -> let ds,envs = check_default envs default in
			     (DEF_aux((DEF_default(ds)),(l,annot)),envs)
    | DEF_reg_dec(typ,id) -> 
      let t = (typ_to_t typ) in
      let i = id_to_string id in
      let tannot = into_register d_env (Some(([],t),External (Some i),[],pure_e)) in
      (DEF_aux(def,(l,tannot)),(Env(d_env,Envmap.insert t_env (i,tannot))))


(*val check : envs ->  tannot defs -> tannot defs*)
let rec check envs (Defs defs) = 
 match defs with
   | [] -> (Defs [])
   | def::defs -> let (def, envs) = check_def envs def in
		  let (Defs defs) = check envs (Defs defs) in
		  (Defs (def::defs))
