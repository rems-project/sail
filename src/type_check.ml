open Ast
open Type_internal
type kind = Type_internal.kind
type typ = Type_internal.t
type 'a emap = 'a Envmap.t

type rec_kind = Record | Register
type def_envs = { 
  k_env: kind emap; 
  abbrevs: tannot emap; 
  namesch : tannot emap; 
  enum_env : (string list) emap; 
  rec_env : (string * rec_kind * ((string * tannot) list)) list;
 }
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
    | Nvar _ -> raise (Reporting_basic.err_unreachable Parse_ast.Unknown "Var found in eval_to_nexp_const")


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
    | Some((ids,ty),tag,constraints) -> Some((ids, {t= Tapp("register",[TA_typ ty])}),tag,constraints)
    | None -> None

let rec check_exp envs expect_t (E_aux(e,annot)) =
  match e with
    | E_block(exps) -> 
      let (exps',annot',envs,sc) = check_block envs envs expect_t exps in
      (E_aux(E_block(exps'),annot'), envs,sc)
    | E_id(id) -> let (names,kinds,typs) = envs in
		  (match Envmap.apply typs (id_to_string id) with
		    | Some(typ) -> (E_aux(e,annot),envs,[])
		    | None -> (E_aux(e,annot),envs,[]))
		    
and check_block orig_envs envs expect_t exps =
  match exps with
    | [] -> ([],(Parse_ast.Unknown,None),orig_envs,[])
    | [e] -> let (E_aux(e',annot),envs,sc) = check_exp envs expect_t e in
	     ([E_aux(e',annot)],annot,orig_envs,sc)
    | e::exps -> let (e',envs,sc) = check_exp envs expect_t (*wrong*) e in
		 let (exps',annot',orig_envs,sc') = check_block orig_envs envs expect_t exps in
		 ((e'::exps'),annot',orig_envs,sc@sc')

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
	    | Tu_id i -> ((id_to_string i),(arm_t {t=Tid "unit"}))
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
      let tannot = typschm_to_tannot envs typs Emp in
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

(*val check_def : envs -> tannot def -> (tannot def) envs_out*)
let check_def envs (DEF_aux(def,(l,annot))) = 
  match def with
    | DEF_type tdef -> let td,envs = check_type_def envs tdef in
		       (DEF_aux((DEF_type td),(l,annot)),envs)
    | DEF_fundef fdef -> (DEF_aux(def,(l,annot)),envs)
    | DEF_val letdef -> (DEF_aux(def,(l,annot)),envs)
    | DEF_spec spec -> let vs,envs = check_val_spec envs spec in
		       (DEF_aux(DEF_spec(vs),(l,annot)),envs)
    | DEF_default default -> let ds,envs = check_default envs default in
			     (DEF_aux((DEF_default(ds)),(l,annot)),envs)
    | DEF_reg_dec(typ,id) -> 
      let t = (typ_to_t typ) in
      let (Env(d_env,t_env)) = envs in
      let tannot = into_register (Some(([],t),External,[])) in 
      (DEF_aux(def,(l,tannot)),(Env(d_env,Envmap.insert t_env ((id_to_string id),tannot))))


(*val check : envs ->  tannot defs -> tannot defs*)
let rec check envs (Defs defs) = 
 match defs with
   | [] -> (Defs [])
   | def::defs -> let (def, envs) = check_def envs def in
		  let (Defs defs) = check envs (Defs defs) in
		  (Defs (def::defs))
