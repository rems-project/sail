open Type_internal
open Ast

type kind = Type_internal.kind
type typ = Type_internal.t

(*Envs is a tuple of used names (currently unused), map from id to kind, default order for vector types and literal vectors *)
type envs = Nameset.t * kind Envmap.t * order 
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
  raise (Reporting_basic.err_typ 
           l
           (msg ^
              (match opt_id, opt_var, opt_kind with
              | Some(id),None,Some(kind) -> (id_to_string id) ^ " of " ^ (kind_to_string kind)
              | Some(id),None,None -> ": " ^ (id_to_string id)
              | None,Some(v),Some(kind) -> (var_to_string v) ^ " of " ^ (kind_to_string kind)
              | None,Some(v),None -> ": " ^ (var_to_string v)
              | None,None,Some(kind) -> " " ^ (kind_to_string kind)
              | _ -> "")))
                
let to_ast_id (Parse_ast.Id_aux(id,l)) =
    Id_aux( (match id with
             | Parse_ast.Id(x) -> Id(x)
             | Parse_ast.DeIid(x) -> DeIid(x)) , l)

let to_ast_var (Parse_ast.Kid_aux(Parse_ast.Var v,l)) = Kid_aux(Var v,l)

let to_ast_base_kind (Parse_ast.BK_aux(k,l')) =
  match k with
  | Parse_ast.BK_type -> BK_aux(BK_type,l'), { k = K_Typ}
  | Parse_ast.BK_nat -> BK_aux(BK_nat,l'), { k = K_Nat }
  | Parse_ast.BK_order -> BK_aux(BK_order,l'), { k = K_Ord }
  | Parse_ast.BK_effect -> BK_aux(BK_effect,l'), { k = K_Efct }

let to_ast_kind (k_env : kind Envmap.t) (Parse_ast.K_aux(Parse_ast.K_kind(klst),l)) : (Ast.kind * kind) =
  match klst with
  | [] -> raise (Reporting_basic.err_unreachable l "Kind with empty kindlist encountered")
  | [k] -> let k_ast,k_typ = to_ast_base_kind k in
           K_aux(K_kind([k_ast]),l), k_typ
  | ks -> let k_pairs = List.map to_ast_base_kind ks in
          let reverse_typs = List.rev (List.map snd k_pairs) in
          let ret,args = List.hd reverse_typs, List.rev (List.tl reverse_typs) in
          match ret.k with
          | K_Typ -> K_aux(K_kind(List.map fst k_pairs), l), { k = K_Lam(args,ret) }
          | _ -> typ_error l "Type constructor must have an -> kind ending in Type" None None None

let rec to_ast_typ (k_env : kind Envmap.t) (def_ord : order) (t: Parse_ast.atyp) : Ast.typ =
(*  let _ = Printf.eprintf "to_ast_typ\n" in*)
  match t with
  | Parse_ast.ATyp_aux(t,l) ->
    Typ_aux( (match t with 
              | Parse_ast.ATyp_id(id) -> 
                let id = to_ast_id id in
                let mk = Envmap.apply k_env (id_to_string id) in
                (match mk with
                | Some(k) -> (match k.k with
                              | K_Typ -> Typ_id id
                              | K_infer -> k.k <- K_Typ; Typ_id id
                              | _ -> typ_error l "Required an identifier with kind Type, encountered " (Some id) None (Some k))
                | None -> typ_error l "Encountered an unbound type identifier" (Some id) None None)
              | Parse_ast.ATyp_var(v) -> 
                let v = to_ast_var v in
                let mk = Envmap.apply k_env (var_to_string v) in
                (match mk with
                | Some(k) -> (match k.k with
                              | K_Typ -> Typ_var v
                              | K_infer -> k.k <- K_Typ; Typ_var v
                              | _ -> typ_error l "Required a variable with kind Type, encountered " None (Some v) (Some k))
                | None -> typ_error l "Encountered an unbound variable" None (Some v) None)
              | Parse_ast.ATyp_fn(arg,ret,efct) -> Typ_fn( (to_ast_typ k_env def_ord arg),
                                                           (to_ast_typ k_env def_ord ret),
                                                           (to_ast_effects k_env efct))
              | Parse_ast.ATyp_tup(typs) -> Typ_tup( List.map (to_ast_typ k_env def_ord) typs)
	      | Parse_ast.ATyp_app(Parse_ast.Id_aux(Parse_ast.Id "vector_sugar_tb",il), [ b; r; ord ; ti]) ->
		let make_r bot top =
		  match bot,top with
		    | Parse_ast.ATyp_aux(Parse_ast.ATyp_constant b,_),Parse_ast.ATyp_aux(Parse_ast.ATyp_constant t,l) ->
		      Parse_ast.ATyp_aux(Parse_ast.ATyp_constant ((t-b)+1),l)
		    | bot,(Parse_ast.ATyp_aux(_,l) as top) ->
		      Parse_ast.ATyp_aux((Parse_ast.ATyp_sum 
					    ((Parse_ast.ATyp_aux 
						(Parse_ast.ATyp_sum (top, 
								     Parse_ast.ATyp_aux(Parse_ast.ATyp_constant 1,Parse_ast.Unknown)), 
						 Parse_ast.Unknown)),
					  (Parse_ast.ATyp_aux ((Parse_ast.ATyp_neg bot),Parse_ast.Unknown)))), l) in
		let base = to_ast_nexp k_env b in
		let rise = match def_ord with
		  | Ord_aux(Ord_inc,dl) ->  to_ast_nexp k_env (make_r b r) 
		  | Ord_aux(Ord_dec,dl) ->  to_ast_nexp k_env (make_r r b) 
		  | _ -> raise (Reporting_basic.err_unreachable l "Default order not inc or dec") in
		Typ_app(Id_aux(Id "vector",il),
			[Typ_arg_aux (Typ_arg_nexp base,Parse_ast.Unknown);
			 Typ_arg_aux (Typ_arg_nexp rise,Parse_ast.Unknown);
			 Typ_arg_aux (Typ_arg_order def_ord,Parse_ast.Unknown);
			 Typ_arg_aux (Typ_arg_typ (to_ast_typ k_env def_ord ti), Parse_ast.Unknown);])
	      | Parse_ast.ATyp_app(Parse_ast.Id_aux(Parse_ast.Id "vector_sugar_r",il), [b;r;ord;ti]) ->
		let make_sub_one t =
		  match t with
		    | Parse_ast.ATyp_aux(Parse_ast.ATyp_constant t,_) -> Parse_ast.ATyp_aux(Parse_ast.ATyp_constant (t-1),l)
		    | t -> (Parse_ast.ATyp_aux 
			      (Parse_ast.ATyp_sum (t, Parse_ast.ATyp_aux(Parse_ast.ATyp_constant (-1),Parse_ast.Unknown)),
			       Parse_ast.Unknown)) in
		let (base,rise) = match def_ord with
		  | Ord_aux(Ord_inc,dl) -> (to_ast_nexp k_env b), (to_ast_nexp k_env r)
		  | Ord_aux(Ord_dec,dl) -> (to_ast_nexp k_env (make_sub_one r)), (to_ast_nexp k_env r)
		  | _ -> raise (Reporting_basic.err_unreachable l "Default order not inc or dec") in
		Typ_app(Id_aux(Id "vector",il),
			[Typ_arg_aux (Typ_arg_nexp base,Parse_ast.Unknown);
			 Typ_arg_aux (Typ_arg_nexp rise,Parse_ast.Unknown);
			 Typ_arg_aux (Typ_arg_order def_ord,Parse_ast.Unknown);
			 Typ_arg_aux (Typ_arg_typ (to_ast_typ k_env def_ord ti), Parse_ast.Unknown);])
              | Parse_ast.ATyp_app(pid,typs) ->
                  let id = to_ast_id pid in 
                  let k = Envmap.apply k_env (id_to_string id) in
                  (match k with 
                  | Some({k = K_Lam(args,t)}) -> 
		    if ((List.length args) = (List.length typs))
		      then
		      Typ_app(id,(List.map2 (fun k a -> (to_ast_typ_arg k_env def_ord k a)) args typs))
		    else typ_error l "Type constructor given incorrect number of arguments" (Some id) None None
                  | None -> typ_error l "Required a type constructor, encountered an unbound identifier" (Some id) None None
                  | _ -> typ_error l "Required a type constructor, encountered a base kind variable" (Some id) None None)
              | _ -> typ_error l "Required an item of kind Type, encountered an illegal form for this kind" None None None
    ), l)

and to_ast_nexp (k_env : kind Envmap.t) (n: Parse_ast.atyp) : Ast.nexp =
  (*let _ = Printf.eprintf "to_ast_nexp\n" in*)
  match n with
  | Parse_ast.ATyp_aux(t,l) ->
    (match t with
     | Parse_ast.ATyp_id(i) ->
       let i = to_ast_id i in
       let v = id_to_string i in
       let mk = Envmap.apply k_env v in
       (match mk with
        | Some(k) -> Nexp_aux((match k.k with
            | K_Nat -> Nexp_id i
            | K_infer -> k.k <- K_Nat; Nexp_id i
            | _ -> typ_error l "Required an identifier with kind Nat, encountered " (Some i) None (Some k)),l)
        | None -> typ_error l "Encountered an unbound variable" (Some i) None None)
     | Parse_ast.ATyp_var(v) ->                 
       let v = to_ast_var v in
       let mk = Envmap.apply k_env (var_to_string v) in
       (*let _ = 
         Envmap.iter (fun v' k -> Printf.eprintf "%s -> %s, %s =? %b\n"
         v' (kind_to_string k) (var_to_string v) ((var_to_string v) = v') ) k_env in *)
       (match mk with
        | Some(k) -> Nexp_aux((match k.k with
            | K_Nat -> Nexp_var v
            | K_infer -> k.k <- K_Nat; Nexp_var v
            | _ -> typ_error l "Required a variable with kind Nat, encountered " None (Some v) (Some k)),l)
        | None -> typ_error l "Encountered an unbound variable" None (Some v) None)
    | Parse_ast.ATyp_constant(i) -> Nexp_aux(Nexp_constant(i),l)
    | Parse_ast.ATyp_sum(t1,t2) ->
      let n1 = to_ast_nexp k_env t1 in
      let n2 = to_ast_nexp k_env t2 in
      Nexp_aux(Nexp_sum(n1,n2),l)
    | Parse_ast.ATyp_exp(t1) -> Nexp_aux(Nexp_exp(to_ast_nexp k_env t1),l)
    | Parse_ast.ATyp_neg(t1) -> Nexp_aux(Nexp_neg(to_ast_nexp k_env t1),l)
    | Parse_ast.ATyp_times(t1,t2) ->
      let n1 = to_ast_nexp k_env t1 in
      let n2 = to_ast_nexp k_env t2 in
      Nexp_aux(Nexp_times(n1,n2),l)
    | Parse_ast.ATyp_minus(t1,t2) ->
      let n1 = to_ast_nexp k_env t1 in
      let n2 = to_ast_nexp k_env t2 in
      Nexp_aux(Nexp_minus(n1,n2),l)
    | _ -> typ_error l "Requred an item of kind Nat, encountered an illegal form for this kind" None None None)
    
and to_ast_order (k_env : kind Envmap.t) (def_ord : order) (o: Parse_ast.atyp) : Ast.order =
  match o with
  | Parse_ast.ATyp_aux(t,l) ->
    (match t with
      | Parse_ast.ATyp_var(v) -> 
        let v = to_ast_var v in
        let mk = Envmap.apply k_env (var_to_string v) in
        (match mk with
          | Some(k) -> (match k.k with
              | K_Ord -> Ord_aux(Ord_var v, l)
              | K_infer -> k.k <- K_Ord; Ord_aux(Ord_var v,l)
              | _ -> typ_error l "Required a variable with kind Order, encountered " None (Some v) (Some k))
          | None -> typ_error l "Encountered an unbound variable" None (Some v) None)
      | Parse_ast.ATyp_inc -> Ord_aux(Ord_inc,l)
      | Parse_ast.ATyp_dec -> Ord_aux(Ord_dec,l)
      | Parse_ast.ATyp_default_ord -> def_ord
      | _ -> typ_error l "Requred an item of kind Order, encountered an illegal form for this kind" None None None
    )

and to_ast_effects (k_env : kind Envmap.t) (e : Parse_ast.atyp) : Ast.effect =
  match e with
  | Parse_ast.ATyp_aux(t,l) ->
    Effect_aux( (match t with
               | Parse_ast.ATyp_var(v) ->  
                let v = to_ast_var v in
                let mk = Envmap.apply k_env (var_to_string v) in
                (match mk with
                | Some(k) -> (match k.k with
                              | K_Efct -> Effect_var v
                              | K_infer -> k.k <- K_Efct; Effect_var v
                              | _ -> typ_error l "Required a variable with kind Effect, encountered " None (Some v) (Some k))
                | None -> typ_error l "Encountered an unbound variable" None (Some v) None)
               | Parse_ast.ATyp_set(effects) ->
                 Effect_set( List.map 
                             (fun efct -> match efct with
                             | Parse_ast.BE_aux(e,l) ->
                               BE_aux((match e with 
                               | Parse_ast.BE_barr   -> BE_barr
                               | Parse_ast.BE_rreg   -> BE_rreg
                               | Parse_ast.BE_wreg   -> BE_wreg
                               | Parse_ast.BE_rmem   -> BE_rmem
                               | Parse_ast.BE_wmem   -> BE_wmem
			       | Parse_ast.BE_wmv    -> BE_wmv
			       | Parse_ast.BE_eamem  -> BE_eamem
			       | Parse_ast.BE_depend -> BE_depend
                               | Parse_ast.BE_undef  -> BE_undef
                               | Parse_ast.BE_unspec -> BE_unspec
                               | Parse_ast.BE_nondet -> BE_nondet
                               | Parse_ast.BE_escape -> BE_escape),l))
                             effects)
               | _ -> typ_error l "Required an item of kind Effects, encountered an illegal form for this kind" None None None
    ), l)

and to_ast_typ_arg (k_env : kind Envmap.t) (def_ord : order) (kind : kind) (arg : Parse_ast.atyp) : Ast.typ_arg =
  let l = (match arg with Parse_ast.ATyp_aux(_,l) -> l) in
  Typ_arg_aux (  
    (match kind.k with 
    | K_Typ -> Typ_arg_typ (to_ast_typ k_env def_ord arg)
    | K_Nat  -> Typ_arg_nexp (to_ast_nexp k_env arg)
    | K_Ord -> Typ_arg_order (to_ast_order k_env def_ord arg)
    | K_Efct -> Typ_arg_effect (to_ast_effects k_env arg)
    | _ -> raise (Reporting_basic.err_unreachable l "To_ast_typ_arg received Lam kind or infer kind")),
    l)

let to_ast_nexp_constraint (k_env : kind Envmap.t) (c : Parse_ast.n_constraint) : n_constraint =
  match c with 
  | Parse_ast.NC_aux(nc,l) ->
    NC_aux( (match nc with
             | Parse_ast.NC_fixed(t1,t2) -> 
               let n1 = to_ast_nexp k_env t1 in
               let n2 = to_ast_nexp k_env t2 in
               NC_fixed(n1,n2)
             | Parse_ast.NC_bounded_ge(t1,t2) ->
               let n1 = to_ast_nexp k_env t1 in
               let n2 = to_ast_nexp k_env t2 in
               NC_bounded_ge(n1,n2)
             | Parse_ast.NC_bounded_le(t1,t2) ->
               let n1 = to_ast_nexp k_env t1 in
               let n2 = to_ast_nexp k_env t2 in
               NC_bounded_le(n1,n2)
             | Parse_ast.NC_nat_set_bounded(id,bounds) ->
               NC_nat_set_bounded(to_ast_var id, bounds)
    ), l)               

(* Transforms a typquant while building first the kind environment of declared variables, and also the kind environment in context *)
let to_ast_typquant (k_env: kind Envmap.t) (tq : Parse_ast.typquant) : typquant * kind Envmap.t * kind Envmap.t =
  let opt_kind_to_ast k_env local_names local_env (Parse_ast.KOpt_aux(ki,l)) =
    let v, key, kind, ktyp =
      match ki with
      | Parse_ast.KOpt_none(v) ->
	let v = to_ast_var v in
	let key = var_to_string v in
	let kind,ktyp = if (Envmap.in_dom key k_env) then None,(Envmap.apply k_env key) else None,(Some{ k = K_infer }) in
	v,key,kind, ktyp
      | Parse_ast.KOpt_kind(k,v) ->
	let v = to_ast_var v in
	let key = var_to_string v in
	let kind,ktyp = to_ast_kind k_env k in
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
  | Parse_ast.TypQ_aux(tqa,l) ->
    (match tqa with
    | Parse_ast.TypQ_no_forall -> TypQ_aux(TypQ_no_forall,l), k_env, Envmap.empty
    | Parse_ast.TypQ_tq(qlist) ->
      let rec to_ast_q_items k_env local_names local_env = function
	| [] -> [],k_env,local_env
	| q::qs -> (match q with
	            | Parse_ast.QI_aux(qi,l) ->
		      (match qi with
		      | Parse_ast.QI_const(n_const) -> 
			let c = QI_aux(QI_const(to_ast_nexp_constraint k_env n_const),l) in
			let qis,k_env,local_env = to_ast_q_items k_env local_names local_env qs in
			(c::qis),k_env,local_env
		      | Parse_ast.QI_id(kid) ->
			let kid,k_env,local_names,local_env = opt_kind_to_ast k_env local_names local_env kid in
			let c = QI_aux(QI_id(kid),l) in
			let qis,k_env,local_env = to_ast_q_items k_env local_names local_env qs in
			(c::qis),k_env,local_env))	
      in
      let lst,k_env,local_env = to_ast_q_items k_env Nameset.empty Envmap.empty qlist in
      TypQ_aux(TypQ_tq(lst),l), k_env, local_env)

let to_ast_typschm (k_env:kind Envmap.t) (def_ord:order) (tschm:Parse_ast.typschm) :Ast.typschm * kind Envmap.t * kind Envmap.t =
  match tschm with
  | Parse_ast.TypSchm_aux(ts,l) -> 
    (match ts with | Parse_ast.TypSchm_ts(tquant,t) ->
      let tq,k_env,local_env = to_ast_typquant k_env tquant in
      let typ = to_ast_typ k_env def_ord t in
      TypSchm_aux(TypSchm_ts(tq,typ),l),k_env,local_env)

let to_ast_lit (Parse_ast.L_aux(lit,l)) : lit = 
  L_aux(
    (match lit with
    | Parse_ast.L_unit -> L_unit
    | Parse_ast.L_zero -> L_zero
    | Parse_ast.L_one -> L_one
    | Parse_ast.L_true -> L_true
    | Parse_ast.L_false -> L_false
    | Parse_ast.L_undef -> L_undef
    | Parse_ast.L_num(i) -> L_num(i)
    | Parse_ast.L_hex(h) -> L_hex(h)
    | Parse_ast.L_bin(b) -> L_bin(b)
    | Parse_ast.L_string(s) -> L_string(s))
      ,l)

let rec to_ast_pat (k_env : kind Envmap.t) (def_ord : order) (Parse_ast.P_aux(pat,l) : Parse_ast.pat) : tannot pat = 
  P_aux(
    (match pat with 
    | Parse_ast.P_lit(lit) -> P_lit(to_ast_lit lit)
    | Parse_ast.P_wild -> P_wild
    | Parse_ast.P_as(pat,id) -> P_as(to_ast_pat k_env def_ord pat,to_ast_id id)
    | Parse_ast.P_typ(typ,pat) -> P_typ(to_ast_typ k_env def_ord typ,to_ast_pat k_env def_ord pat)
    | Parse_ast.P_id(id) -> P_id(to_ast_id id)
    | Parse_ast.P_app(id,pats) ->
      if pats = [] 
      then P_id (to_ast_id id)
      else P_app(to_ast_id id, List.map (to_ast_pat k_env def_ord) pats)
    | Parse_ast.P_record(fpats,_) -> 
      P_record(List.map 
                 (fun (Parse_ast.FP_aux(Parse_ast.FP_Fpat(id,fp),l)) -> 
		      FP_aux(FP_Fpat(to_ast_id id, to_ast_pat k_env def_ord fp),(l,NoTyp)))
                 fpats, false)
    | Parse_ast.P_vector(pats) -> P_vector(List.map (to_ast_pat k_env def_ord) pats)
    | Parse_ast.P_vector_indexed(ipats) -> P_vector_indexed(List.map (fun (i,pat) -> i,to_ast_pat k_env def_ord pat) ipats)
    | Parse_ast.P_vector_concat(pats) -> P_vector_concat(List.map (to_ast_pat k_env def_ord) pats)
    | Parse_ast.P_tup(pats) -> P_tup(List.map (to_ast_pat k_env def_ord) pats)
    | Parse_ast.P_list(pats) -> P_list(List.map (to_ast_pat k_env def_ord) pats)
    ), (l,NoTyp))


let rec to_ast_letbind (k_env : kind Envmap.t) (def_ord : order) (Parse_ast.LB_aux(lb,l) : Parse_ast.letbind) : tannot letbind =
  LB_aux(
    (match lb with
    | Parse_ast.LB_val_explicit(typschm,pat,exp) ->
      let typsch, k_env, _  = to_ast_typschm k_env def_ord typschm in
      LB_val_explicit(typsch,to_ast_pat k_env def_ord pat, to_ast_exp k_env def_ord exp)
    | Parse_ast.LB_val_implicit(pat,exp) ->
      LB_val_implicit(to_ast_pat k_env def_ord pat, to_ast_exp k_env def_ord exp)
    ), (l,NoTyp))

and to_ast_exp (k_env : kind Envmap.t) (def_ord : order) (Parse_ast.E_aux(exp,l) : Parse_ast.exp) : tannot exp = 
  E_aux(
    (match exp with
    | Parse_ast.E_block(exps) -> 
      (match to_ast_fexps false k_env def_ord exps with
      | Some(fexps) -> E_record(fexps)
      | None -> E_block(List.map (to_ast_exp k_env def_ord) exps))
    | Parse_ast.E_nondet(exps) -> E_nondet(List.map (to_ast_exp k_env def_ord) exps)
    | Parse_ast.E_id(id) -> E_id(to_ast_id id)
    | Parse_ast.E_lit(lit) -> E_lit(to_ast_lit lit)
    | Parse_ast.E_cast(typ,exp) -> E_cast(to_ast_typ k_env def_ord typ, to_ast_exp k_env def_ord exp)
    | Parse_ast.E_app(f,args) -> 
      (match List.map (to_ast_exp k_env def_ord) args with
	| [] -> E_app(to_ast_id f, [])
	| [E_aux(E_tuple(exps),_)] -> E_app(to_ast_id f, exps)
	| exps -> E_app(to_ast_id f, exps))
    | Parse_ast.E_app_infix(left,op,right) -> 
      E_app_infix(to_ast_exp k_env def_ord left, to_ast_id op, to_ast_exp k_env def_ord right)
    | Parse_ast.E_tuple(exps) -> E_tuple(List.map (to_ast_exp k_env def_ord) exps)
    | Parse_ast.E_if(e1,e2,e3) -> E_if(to_ast_exp k_env def_ord e1, to_ast_exp k_env def_ord e2, to_ast_exp k_env def_ord e3)
    | Parse_ast.E_for(id,e1,e2,e3,atyp,e4) -> 
      E_for(to_ast_id id,to_ast_exp k_env def_ord e1, to_ast_exp k_env def_ord e2,
	    to_ast_exp k_env def_ord e3,to_ast_order k_env def_ord atyp, to_ast_exp k_env def_ord e4)
    | Parse_ast.E_vector(exps) -> 
      (match to_ast_iexps false k_env def_ord exps with
	| Some([]) -> E_vector([])
	| Some(iexps) -> E_vector_indexed(iexps, 
					  Def_val_aux(Def_val_empty,(l,NoTyp)))
	| None -> E_vector(List.map (to_ast_exp k_env def_ord) exps))
    | Parse_ast.E_vector_indexed(iexps,Parse_ast.Def_val_aux(default,dl)) -> 
      (match to_ast_iexps true k_env def_ord iexps with
	| Some(iexps) -> E_vector_indexed (iexps, 
					   Def_val_aux((match default with
					     | Parse_ast.Def_val_empty -> Def_val_empty
					     | Parse_ast.Def_val_dec e -> Def_val_dec (to_ast_exp k_env def_ord e)),(dl,NoTyp)))
	| _ -> raise (Reporting_basic.err_unreachable l "to_ast_iexps didn't throw error"))
    | Parse_ast.E_vector_access(vexp,exp) -> E_vector_access(to_ast_exp k_env def_ord vexp, to_ast_exp k_env def_ord exp)
    | Parse_ast.E_vector_subrange(vex,exp1,exp2) -> 
      E_vector_subrange(to_ast_exp k_env def_ord vex, to_ast_exp k_env def_ord exp1, to_ast_exp k_env def_ord exp2)
    | Parse_ast.E_vector_update(vex,exp1,exp2) -> 
      E_vector_update(to_ast_exp k_env def_ord vex, to_ast_exp k_env def_ord exp1, to_ast_exp k_env def_ord exp2)
    | Parse_ast.E_vector_update_subrange(vex,e1,e2,e3) -> 
      E_vector_update_subrange(to_ast_exp k_env def_ord vex, to_ast_exp k_env def_ord e1, 
			       to_ast_exp k_env def_ord e2, to_ast_exp k_env def_ord e3)
    | Parse_ast.E_vector_append(e1,e2) -> E_vector_append(to_ast_exp k_env def_ord e1,to_ast_exp k_env def_ord e2)
    | Parse_ast.E_list(exps) -> E_list(List.map (to_ast_exp k_env def_ord) exps)
    | Parse_ast.E_cons(e1,e2) -> E_cons(to_ast_exp k_env def_ord e1, to_ast_exp k_env def_ord e2)
    | Parse_ast.E_record _ -> raise (Reporting_basic.err_unreachable l "parser generated an E_record")
    | Parse_ast.E_record_update(exp,fexps) -> 
      (match to_ast_fexps true k_env def_ord fexps with
      | Some(fexps) -> E_record_update(to_ast_exp k_env def_ord exp, fexps)
      | _ -> raise (Reporting_basic.err_unreachable l "to_ast_fexps with true returned none"))
    | Parse_ast.E_field(exp,id) -> E_field(to_ast_exp k_env def_ord exp, to_ast_id id)
    | Parse_ast.E_case(exp,pexps) -> E_case(to_ast_exp k_env def_ord exp, List.map (to_ast_case k_env def_ord) pexps)
    | Parse_ast.E_let(leb,exp) -> E_let(to_ast_letbind k_env def_ord leb, to_ast_exp k_env def_ord exp)
    | Parse_ast.E_assign(lexp,exp) -> E_assign(to_ast_lexp k_env def_ord lexp, to_ast_exp k_env def_ord exp)
    | Parse_ast.E_sizeof(nexp) -> E_sizeof(to_ast_nexp k_env nexp)
    | Parse_ast.E_exit exp -> E_exit(to_ast_exp k_env def_ord exp)
    | Parse_ast.E_assert(cond,msg) -> E_assert(to_ast_exp k_env def_ord cond, to_ast_exp k_env def_ord msg)
    ), (l,NoTyp))

and to_ast_lexp (k_env : kind Envmap.t) (def_ord : order) (Parse_ast.E_aux(exp,l) : Parse_ast.exp) : tannot lexp = 
  LEXP_aux(
    (match exp with
    | Parse_ast.E_id(id) -> LEXP_id(to_ast_id id)
    | Parse_ast.E_app((Parse_ast.Id_aux(f,l') as f'),args) -> 
      (match f with
      | Parse_ast.Id(id) -> 
	(match List.map (to_ast_exp k_env def_ord) args with
	  | [] -> LEXP_memory(to_ast_id f',[])
	  | [E_aux(E_tuple exps,_)] -> LEXP_memory(to_ast_id f',exps)
	  | args -> LEXP_memory(to_ast_id f', args))
      | _ -> typ_error l' "memory call on lefthand side of assignment must begin with an id" None None None)
    | Parse_ast.E_cast(typ,Parse_ast.E_aux(Parse_ast.E_id(id),l')) ->
      LEXP_cast(to_ast_typ k_env def_ord typ, to_ast_id id)
    | Parse_ast.E_vector_access(vexp,exp) -> LEXP_vector(to_ast_lexp k_env def_ord vexp, to_ast_exp k_env def_ord exp)
    | Parse_ast.E_vector_subrange(vexp,exp1,exp2) -> 
      LEXP_vector_range(to_ast_lexp k_env def_ord vexp, to_ast_exp k_env def_ord exp1, to_ast_exp k_env def_ord exp2)
    | Parse_ast.E_field(fexp,id) -> LEXP_field(to_ast_lexp k_env def_ord fexp, to_ast_id id)
    | _ -> typ_error l "Only identifiers, cast identifiers, vector accesses, vector slices, and fields can be on the lefthand side of an assignment" None None None)
      , (l,NoTyp))

and to_ast_case (k_env : kind Envmap.t) (def_ord : order) (Parse_ast.Pat_aux(pex,l) : Parse_ast.pexp) : tannot pexp =
  match pex with 
  | Parse_ast.Pat_exp(pat,exp) -> Pat_aux(Pat_exp(to_ast_pat k_env def_ord pat, to_ast_exp k_env def_ord exp),(l,NoTyp))

and to_ast_fexps (fail_on_error:bool) (k_env:kind Envmap.t) (def_ord:order) (exps : Parse_ast.exp list) : tannot fexps option =
  match exps with
  | [] -> Some(FES_aux(FES_Fexps([],false), (Parse_ast.Unknown,NoTyp)))
  | fexp::exps -> let maybe_fexp,maybe_error = to_ast_record_try k_env def_ord fexp in
                  (match maybe_fexp,maybe_error with
                  | Some(fexp),None -> 
                    (match (to_ast_fexps fail_on_error k_env def_ord exps) with
                    | Some(FES_aux(FES_Fexps(fexps,_),l)) -> Some(FES_aux(FES_Fexps(fexp::fexps,false),l))
                    | _  -> None)
                  | None,Some(l,msg) -> 
                    if fail_on_error
                    then typ_error l msg None None None
                    else None
                  | _ -> None)

and to_ast_record_try (k_env:kind Envmap.t) (def_ord:order) (Parse_ast.E_aux(exp,l):Parse_ast.exp): tannot fexp option * (l * string) option =
  match exp with
  | Parse_ast.E_app_infix(left,op,r) ->
    (match left, op with
    | Parse_ast.E_aux(Parse_ast.E_id(id),li), Parse_ast.Id_aux(Parse_ast.Id("="),leq) ->
      Some(FE_aux(FE_Fexp(to_ast_id id, to_ast_exp k_env def_ord r), (l,NoTyp))),None
    | Parse_ast.E_aux(_,li) , Parse_ast.Id_aux(Parse_ast.Id("="),leq) ->
      None,Some(li,"Expected an identifier to begin this field assignment")
    | Parse_ast.E_aux(Parse_ast.E_id(id),li), Parse_ast.Id_aux(_,leq) ->
      None,Some(leq,"Expected a field assignment to be identifier = expression")
    | Parse_ast.E_aux(_,li),Parse_ast.Id_aux(_,leq) ->
      None,Some(l,"Expected a field assignment to be identifier = expression"))
  | _ ->
    None,Some(l, "Expected a field assignment to be identifier = expression")

and to_ast_iexps (fail_on_error:bool) (k_env:kind Envmap.t) (def_ord:order) (exps:Parse_ast.exp list):(int * tannot exp) list option =
 match exps with
   | [] -> Some([])
   | iexp::exps -> (match to_iexp_try k_env def_ord iexp with
		     | Some(iexp),None ->
		       (match to_ast_iexps fail_on_error k_env def_ord exps with
			 | Some(iexps) -> Some(iexp::iexps)
			 | _ -> None)
		     | None,Some(l,msg) ->
		       if fail_on_error
		       then typ_error l msg None None None
		       else None
		     | _ -> None)
and to_iexp_try (k_env:kind Envmap.t) (def_ord:order) (Parse_ast.E_aux(exp,l): Parse_ast.exp): ((int * tannot exp) option * (l*string) option) =
  match exp with
    | Parse_ast.E_app_infix(left,op,r) ->
      (match left,op with
	| Parse_ast.E_aux(Parse_ast.E_lit(Parse_ast.L_aux (Parse_ast.L_num i,ll)),cl), Parse_ast.Id_aux(Parse_ast.Id("="),leq) ->
	  Some(i,to_ast_exp k_env def_ord r),None
	| Parse_ast.E_aux(_,li), Parse_ast.Id_aux (Parse_ast.Id("="),leq) ->
	  None,(Some(li,"Expected a constant number to begin this indexed vector assignemnt"))
	| Parse_ast.E_aux(_,cl), Parse_ast.Id_aux(_,leq) ->
	  None,(Some(leq,"Expected an indexed vector assignment constant = expression")))
    | _ -> None,(Some(l,"Expected an indexed vector assignment: constant = expression"))
      
let to_ast_default (names, k_env, default_order) (default : Parse_ast.default_typing_spec) : (tannot default_spec) envs_out =
  match default with
  | Parse_ast.DT_aux(df,l) ->
    (match df with 
    | Parse_ast.DT_kind(bk,v) ->
      let k,k_typ = to_ast_base_kind bk in
      let v = to_ast_var v in
      let key = var_to_string v in
      DT_aux(DT_kind(k,v),l),(names,(Envmap.insert k_env (key,k_typ)),default_order)
    | Parse_ast.DT_typ(typschm,id) ->
      let tps,_,_ = to_ast_typschm k_env default_order typschm in
      DT_aux(DT_typ(tps,to_ast_id id),l),(names,k_env,default_order)
    | Parse_ast.DT_order(bk,o) ->
      let k,k_typ = to_ast_base_kind bk in
      (match (k,o) with
	| (BK_aux(BK_order, _), Parse_ast.ATyp_aux(Parse_ast.ATyp_inc,lo)) ->
	  let default_order = Ord_aux(Ord_inc,lo) in
	  DT_aux(DT_order default_order,l),(names,k_env,default_order)
	| (BK_aux(BK_order, _), Parse_ast.ATyp_aux(Parse_ast.ATyp_dec,lo)) ->
	  let default_order = Ord_aux(Ord_dec,lo) in
	  DT_aux(DT_order default_order,l),(names,k_env,default_order)
	| _ -> typ_error l "Inc and Dec must have kind Order" None None None))

let to_ast_spec (names,k_env,default_order) (val_:Parse_ast.val_spec) : (tannot val_spec) envs_out =
  match val_ with
  | Parse_ast.VS_aux(vs,l) ->
    (match vs with
    | Parse_ast.VS_val_spec(ts,id) ->
      (*let _ = Printf.eprintf "to_ast_spec called for internal spec: for %s\n" (id_to_string (to_ast_id id)) in*)
      let typsch,_,_ = to_ast_typschm k_env default_order ts in
      VS_aux(VS_val_spec(typsch,to_ast_id id),(l,NoTyp)),(names,k_env,default_order)
    | Parse_ast.VS_extern_spec(ts,id,s) ->
      let typsch,_,_ = to_ast_typschm k_env default_order ts in
      VS_aux(VS_extern_spec(typsch,to_ast_id id,s),(l,NoTyp)),(names,k_env,default_order)
    | Parse_ast.VS_extern_no_rename(ts,id) ->
      let typsch,_,_ = to_ast_typschm k_env default_order ts in
       VS_aux(VS_extern_no_rename(typsch,to_ast_id id),(l,NoTyp)),(names,k_env,default_order))
    

let to_ast_namescm (Parse_ast.Name_sect_aux(ns,l)) = 
  Name_sect_aux(
    (match ns with
    | Parse_ast.Name_sect_none -> Name_sect_none
    | Parse_ast.Name_sect_some(s) -> Name_sect_some(s)
    ),l)

let rec to_ast_range (Parse_ast.BF_aux(r,l)) = (* TODO add check that ranges are sensible for some definition of sensible *)
  BF_aux(
    (match r with
    | Parse_ast.BF_single(i) -> BF_single(i)
    | Parse_ast.BF_range(i1,i2) -> BF_range(i1,i2)
    | Parse_ast.BF_concat(ir1,ir2) -> BF_concat( to_ast_range ir1, to_ast_range ir2)),
    l)

let to_ast_type_union k_env default_order (Parse_ast.Tu_aux(tu,l)) =
  match tu with
    | Parse_ast.Tu_ty_id(atyp,id) -> (Tu_aux(Tu_ty_id ((to_ast_typ k_env default_order atyp),(to_ast_id id)),l))
    | Parse_ast.Tu_id id -> (Tu_aux(Tu_id(to_ast_id id),l)) 

let to_ast_typedef (names,k_env,def_ord) (td:Parse_ast.type_def) : (tannot type_def) envs_out =
  match td with
  | Parse_ast.TD_aux(td,l) ->
  (match td with 
  | Parse_ast.TD_abbrev(id,name_scm_opt,typschm) ->
    let id = to_ast_id id in
    let key = id_to_string id in
    let typschm,k_env,_ = to_ast_typschm k_env def_ord typschm in
    let td_abrv = TD_aux(TD_abbrev(id,to_ast_namescm name_scm_opt,typschm),(l,NoTyp)) in
    let typ = (match typschm with 
      | TypSchm_aux(TypSchm_ts(tq,typ), _) ->
        begin match (typquant_to_quantkinds k_env tq) with
        | [] -> {k = K_Typ}
        | typs -> {k= K_Lam(typs,{k=K_Typ})}
        end) in
    td_abrv,(names,Envmap.insert k_env (key,typ),def_ord)
  | Parse_ast.TD_record(id,name_scm_opt,typq,fields,_) -> 
    let id = to_ast_id id in
    let key = id_to_string id in
    let typq,k_env,_ = to_ast_typquant k_env typq in
    let fields = List.map (fun (atyp,id) -> (to_ast_typ k_env def_ord atyp),(to_ast_id id)) fields in (* Add check that all arms have unique names locally *)
    let td_rec = TD_aux(TD_record(id,to_ast_namescm name_scm_opt,typq,fields,false),(l,NoTyp)) in
    let typ = (match (typquant_to_quantkinds k_env typq) with
      | [ ] -> {k = K_Typ}
      | typs -> {k = K_Lam(typs,{k=K_Typ})}) in
    td_rec, (names,Envmap.insert k_env (key,typ), def_ord)
  | Parse_ast.TD_variant(id,name_scm_opt,typq,arms,_) ->
    let id = to_ast_id id in
    let key = id_to_string id in
    let typq,k_env,_ = to_ast_typquant k_env typq in
    let arms = List.map (to_ast_type_union k_env def_ord) arms in (* Add check that all arms have unique names *)
    let td_var = TD_aux(TD_variant(id,to_ast_namescm name_scm_opt,typq,arms,false),(l,NoTyp)) in
    let typ = (match (typquant_to_quantkinds k_env typq) with
      | [ ] -> {k = K_Typ}
      | typs -> {k = K_Lam(typs,{k=K_Typ})}) in
    td_var, (names,Envmap.insert k_env (key,typ), def_ord)
  | Parse_ast.TD_enum(id,name_scm_opt,enums,_) -> 
    let id = to_ast_id id in
    let key = id_to_string id in
    let enums = List.map to_ast_id enums in
    let keys = List.map id_to_string enums in
    let td_enum = TD_aux(TD_enum(id,to_ast_namescm name_scm_opt,enums,false),(l,NoTyp)) in (* Add check that all enums have unique names *)
    let k_env = List.fold_right (fun k k_env -> Envmap.insert k_env (k,{k=K_Nat})) keys (Envmap.insert k_env (key,{k=K_Typ})) in
    td_enum, (names,k_env,def_ord)
  | Parse_ast.TD_register(id,t1,t2,ranges) -> 
    let id = to_ast_id id in
    let key = id_to_string id in
    let n1 = to_ast_nexp k_env t1 in
    let n2 = to_ast_nexp k_env t2 in
    let ranges = List.map (fun (range,id) -> (to_ast_range range),to_ast_id id) ranges in
    TD_aux(TD_register(id,n1,n2,ranges),(l,NoTyp)), (names,Envmap.insert k_env (key, {k=K_Typ}),def_ord))

let to_ast_kdef (names,k_env,def_ord) (td:Parse_ast.kind_def) : (tannot kind_def) envs_out =
  match td with
  | Parse_ast.KD_aux(td,l) ->
  (match td with 
  | Parse_ast.KD_abbrev(kind,id,name_scm_opt,typschm) ->
    let id = to_ast_id id in
    let key = id_to_string id in
    let (kind,k) = to_ast_kind k_env kind in
    (match k.k with
     | K_Typ | K_Lam _ ->
       let typschm,k_env,_ = to_ast_typschm k_env def_ord typschm in
       let kd_abrv = KD_aux(KD_abbrev(kind,id,to_ast_namescm name_scm_opt,typschm),(l,NoTyp)) in
       let typ = (match typschm with 
           | TypSchm_aux(TypSchm_ts(tq,typ), _) ->
             begin match (typquant_to_quantkinds k_env tq) with
               | [] -> {k = K_Typ}
               | typs -> {k= K_Lam(typs,{k=K_Typ})}
             end) in
       kd_abrv,(names,Envmap.insert k_env (key,typ),def_ord)
     | K_Nat ->
       let kd_nabrv = 
         (match typschm with
          | Parse_ast.TypSchm_aux(Parse_ast.TypSchm_ts(Parse_ast.TypQ_aux(tq,_),atyp),_) ->
            (match tq with
             | Parse_ast.TypQ_no_forall ->
               KD_aux(KD_nabbrev(kind,id,to_ast_namescm name_scm_opt, to_ast_nexp k_env atyp), (l,NoTyp))
             | _ -> typ_error l "Def with kind Nat cannot have universal quantification" None None None)) in
       kd_nabrv,(names,Envmap.insert k_env (key, k),def_ord)
     | _ -> assert false
    )
  | Parse_ast.KD_record(kind,id,name_scm_opt,typq,fields,_) -> 
    let id = to_ast_id id in
    let key = id_to_string id in
    let (kind,k) = to_ast_kind k_env kind in
    let typq,k_env,_ = to_ast_typquant k_env typq in
    let fields = List.map (fun (atyp,id) -> (to_ast_typ k_env def_ord atyp),(to_ast_id id)) fields in (* Add check that all arms have unique names locally *)
    let kd_rec = KD_aux(KD_record(kind,id,to_ast_namescm name_scm_opt,typq,fields,false),(l,NoTyp)) in
    let typ = (match (typquant_to_quantkinds k_env typq) with
      | [ ] -> {k = K_Typ}
      | typs -> {k = K_Lam(typs,{k=K_Typ})}) in
    kd_rec, (names,Envmap.insert k_env (key,typ), def_ord)
  | Parse_ast.KD_variant(kind,id,name_scm_opt,typq,arms,_) ->
    let id = to_ast_id id in
    let key = id_to_string id in
    let kind,k = to_ast_kind k_env kind in
    let typq,k_env,_ = to_ast_typquant k_env typq in
    let arms = List.map (to_ast_type_union k_env def_ord) arms in (* Add check that all arms have unique names *)
    let kd_var = KD_aux(KD_variant(kind,id,to_ast_namescm name_scm_opt,typq,arms,false),(l,NoTyp)) in
    let typ = (match (typquant_to_quantkinds k_env typq) with
      | [ ] -> {k = K_Typ}
      | typs -> {k = K_Lam(typs,{k=K_Typ})}) in
    kd_var, (names,Envmap.insert k_env (key,typ), def_ord)
  | Parse_ast.KD_enum(kind,id,name_scm_opt,enums,_) -> 
    let id = to_ast_id id in
    let key = id_to_string id in
    let kind,k = to_ast_kind k_env kind in
    let enums = List.map to_ast_id enums in
    let keys = List.map id_to_string enums in
    let kd_enum = KD_aux(KD_enum(kind,id,to_ast_namescm name_scm_opt,enums,false),(l,NoTyp)) in (* Add check that all enums have unique names *)
    let k_env = List.fold_right (fun k k_env -> Envmap.insert k_env (k,{k=K_Nat})) keys (Envmap.insert k_env (key,{k=K_Typ})) in
    kd_enum, (names,k_env,def_ord)
  | Parse_ast.KD_register(kind,id,t1,t2,ranges) -> 
    let id = to_ast_id id in
    let key = id_to_string id in
    let kind,k = to_ast_kind k_env kind in
    let n1 = to_ast_nexp k_env t1 in
    let n2 = to_ast_nexp k_env t2 in
    let ranges = List.map (fun (range,id) -> (to_ast_range range),to_ast_id id) ranges in
    KD_aux(KD_register(kind,id,n1,n2,ranges),(l,NoTyp)), (names,Envmap.insert k_env (key, {k=K_Typ}),def_ord))


let to_ast_rec (Parse_ast.Rec_aux(r,l): Parse_ast.rec_opt) : rec_opt =
  Rec_aux((match r with
  | Parse_ast.Rec_nonrec -> Rec_nonrec
  | Parse_ast.Rec_rec -> Rec_rec
  ),l)

let to_ast_tannot_opt (k_env:kind Envmap.t) (def_ord:order) (Parse_ast.Typ_annot_opt_aux(tp,l)):tannot_opt * kind Envmap.t * kind Envmap.t=
  match tp with
  | Parse_ast.Typ_annot_opt_none -> raise (Reporting_basic.err_unreachable l "Parser generated typ annot opt none")
  | Parse_ast.Typ_annot_opt_some(tq,typ) ->
    let typq,k_env,k_local = to_ast_typquant k_env tq in
    Typ_annot_opt_aux(Typ_annot_opt_some(typq,to_ast_typ k_env def_ord typ),l),k_env,k_local

let to_ast_effects_opt (k_env : kind Envmap.t) (Parse_ast.Effect_opt_aux(e,l)) : effect_opt =
  match e with
  | Parse_ast.Effect_opt_pure -> Effect_opt_aux(Effect_opt_pure,l)
  | Parse_ast.Effect_opt_effect(typ) -> Effect_opt_aux(Effect_opt_effect(to_ast_effects k_env typ),l)

let to_ast_funcl (names,k_env,def_ord) (Parse_ast.FCL_aux(fcl,l) : Parse_ast.funcl) : (tannot funcl) =
  (*let _ = Printf.eprintf "to_ast_funcl\n" in*)
  match fcl with
  | Parse_ast.FCL_Funcl(id,pat,exp) -> 
    FCL_aux(FCL_Funcl(to_ast_id id, to_ast_pat k_env def_ord pat, to_ast_exp k_env def_ord exp),(l,NoTyp))

let to_ast_fundef  (names,k_env,def_ord) (Parse_ast.FD_aux(fd,l):Parse_ast.fundef) : (tannot fundef) envs_out = 
  match fd with
  | Parse_ast.FD_function(rec_opt,tannot_opt,effects_opt,funcls) -> 
    (*let _ = Printf.eprintf "to_ast_fundef\n" in*)
    let tannot_opt, k_env,_ = to_ast_tannot_opt k_env def_ord tannot_opt in
    FD_aux(FD_function(to_ast_rec rec_opt, tannot_opt, to_ast_effects_opt k_env effects_opt, List.map (to_ast_funcl (names, k_env, def_ord)) funcls), (l,NoTyp)), (names,k_env,def_ord)
    
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

let to_ast_alias_spec k_env def_ord (Parse_ast.E_aux(e,le)) = 
  AL_aux(
    (match e with
      | Parse_ast.E_field(Parse_ast.E_aux(Parse_ast.E_id id,li), field) -> 
	AL_subreg(RI_aux(RI_id (to_ast_id id),(li,NoTyp)),to_ast_id field)
      | Parse_ast.E_vector_access(Parse_ast.E_aux(Parse_ast.E_id id,li),range) ->
	AL_bit(RI_aux(RI_id (to_ast_id id),(li,NoTyp)),to_ast_exp k_env def_ord range)
      | Parse_ast.E_vector_subrange(Parse_ast.E_aux(Parse_ast.E_id id,li),base,stop) ->
	AL_slice(RI_aux(RI_id (to_ast_id id),(li,NoTyp)),to_ast_exp k_env def_ord base,to_ast_exp k_env def_ord stop)
      | Parse_ast.E_vector_append(Parse_ast.E_aux(Parse_ast.E_id first,lf),
				  Parse_ast.E_aux(Parse_ast.E_id second,ls)) ->
	AL_concat(RI_aux(RI_id (to_ast_id first),(lf,NoTyp)),
		  RI_aux(RI_id (to_ast_id second),(ls,NoTyp)))
      | _ -> raise (Reporting_basic.err_unreachable le "Found an expression not supported by parser in to_ast_alias_spec")
    ), (le,NoTyp))      

let to_ast_dec (names,k_env,def_ord) (Parse_ast.DEC_aux(regdec,l)) =
  DEC_aux(
    (match regdec with
      | Parse_ast.DEC_reg(typ,id) ->
	DEC_reg(to_ast_typ k_env def_ord typ,to_ast_id id)
      | Parse_ast.DEC_alias(id,e) ->
	DEC_alias(to_ast_id id,to_ast_alias_spec k_env def_ord e)
      | Parse_ast.DEC_typ_alias(typ,id,e) ->
	DEC_typ_alias(to_ast_typ k_env def_ord typ,to_ast_id id,to_ast_alias_spec k_env def_ord e)
    ),(l,NoTyp))
      
let to_ast_def (names, k_env, def_ord) partial_defs def : def_progress envs_out * (id * partial_def) list = 
  let envs = (names,k_env,def_ord) in
  match def with
  | Parse_ast.DEF_kind(k_def) ->
    let kd,envs = to_ast_kdef envs k_def in
    ((Finished(DEF_kind(kd))),envs),partial_defs
  | Parse_ast.DEF_type(t_def) -> 
    let td,envs = to_ast_typedef envs t_def in
    ((Finished(DEF_type(td))),envs),partial_defs
  | Parse_ast.DEF_fundef(f_def) -> 
    let fd,envs = to_ast_fundef envs f_def in
    ((Finished(DEF_fundef(fd))),envs),partial_defs
  | Parse_ast.DEF_val(lbind) -> 
    let lb = to_ast_letbind k_env def_ord lbind in
    ((Finished(DEF_val(lb))),envs),partial_defs
  | Parse_ast.DEF_spec(val_spec) -> 
    let vs,envs = to_ast_spec envs val_spec in
    ((Finished(DEF_spec(vs))),envs),partial_defs
  | Parse_ast.DEF_default(typ_spec) -> 
    let default,envs = to_ast_default envs typ_spec in
    ((Finished(DEF_default(default))),envs),partial_defs
  | Parse_ast.DEF_reg_dec(dec) ->
    let d = to_ast_dec envs dec in
    ((Finished(DEF_reg_dec(d))),envs),partial_defs
  | Parse_ast.DEF_scattered(Parse_ast.SD_aux(sd,l)) ->
    (match sd with
    | Parse_ast.SD_scattered_function(rec_opt, tannot_opt, effects_opt, id) ->
      let rec_opt = to_ast_rec rec_opt in
      let tannot,k_env',k_local = to_ast_tannot_opt k_env def_ord tannot_opt in
      let effects_opt = to_ast_effects_opt k_env' effects_opt in
      let id = to_ast_id id in
      (match (def_in_progress id partial_defs) with
      | None -> let partial_def = ref ((DEF_fundef(FD_aux(FD_function(rec_opt,tannot,effects_opt,[]),(l,NoTyp)))),false) in
                (No_def,envs),((id,(partial_def,k_local))::partial_defs)
      | Some(d,k) -> typ_error l "Scattered function definition header name already in use by scattered definition" (Some id) None None)
    | Parse_ast.SD_scattered_funcl(funcl) -> 
      (match funcl with
      | Parse_ast.FCL_aux(Parse_ast.FCL_Funcl(id,_,_),_) -> 
        let id = to_ast_id id in
        (match (def_in_progress id partial_defs) with
	| None -> typ_error l "Scattered function definition clause does not match any exisiting function definition headers" (Some id) None None
	| Some(d,k) ->
	 (* let _ = Printf.eprintf "SD_scattered_funcl processing\n" in
	  let _ = Envmap.iter (fun v' k -> Printf.eprintf "%s -> %s\n" v' (kind_to_string k)) k in 
	  let _ = Envmap.iter (fun v' k -> Printf.eprintf "%s -> %s\n" v' (kind_to_string k) ) (Envmap.union k k_env) in *)
	  (match !d with
	  | DEF_fundef(FD_aux(FD_function(r,t,e,fcls),fl)),false -> 
	    let funcl = to_ast_funcl (names,Envmap.union k k_env,def_ord) funcl in 
	    d:= DEF_fundef(FD_aux(FD_function(r,t,e,fcls@[funcl]),fl)),false;
	    (No_def,envs),partial_defs
	  | _,true -> typ_error l "Scattered funciton definition clauses extends ended defintion" (Some id) None None
	  | _ -> typ_error l "Scattered function definition clause matches an existing scattered type definition header" (Some id) None None)))
    | Parse_ast.SD_scattered_variant(id,naming_scheme_opt,typquant) -> 
      let id = to_ast_id id in
      let name = to_ast_namescm naming_scheme_opt in
      let typq, k_env',_ = to_ast_typquant k_env typquant in
      let kind = (match (typquant_to_quantkinds k_env' typq) with
        | [ ] -> {k = K_Typ}
        | typs -> {k = K_Lam(typs,{k=K_Typ})}) in
      (match (def_in_progress id partial_defs) with
      | None -> let partial_def = ref ((DEF_type(TD_aux(TD_variant(id,name,typq,[],false),(l,NoTyp)))),false) in
                (Def_place_holder(id,l),(names,Envmap.insert k_env ((id_to_string id),kind),def_ord)),(id,(partial_def,k_env'))::partial_defs
      | Some(d,k) -> typ_error l "Scattered type definition header name already in use by scattered definition" (Some id) None None)
    | Parse_ast.SD_scattered_unioncl(id,tu) -> 
      let id = to_ast_id id in
      (match (def_in_progress id partial_defs) with
      | None -> typ_error l "Scattered type definition clause does not match any existing type definition headers" (Some id) None None
      | Some(d,k) ->
        (match !d with
	| DEF_type(TD_aux(TD_variant(id,name,typq,arms,false),tl)), false -> 
	  d:= DEF_type(TD_aux(TD_variant(id,name,typq,arms@[to_ast_type_union k def_ord tu],false),tl)),false;
	  (No_def,envs),partial_defs
	| _,true -> typ_error l "Scattered type definition clause extends ended definition" (Some id) None None
	| _ -> typ_error l "Scattered type definition clause matches an existing scattered function definition header" (Some id) None None))
    | Parse_ast.SD_scattered_end(id) ->
      let id = to_ast_id id in
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
    
let rec to_ast_defs_helper envs partial_defs = function
  | [] -> ([],envs,partial_defs)
  | d::ds  -> let ((d', envs), partial_defs) = to_ast_def envs partial_defs d in
              let (defs,envs,partial_defs) = to_ast_defs_helper envs partial_defs ds in
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

let to_ast (default_names : Nameset.t) (kind_env : kind Envmap.t) (def_ord : order) (Parse_ast.Defs(defs)) =
  let defs,(_,k_env,def_ord),partial_defs = to_ast_defs_helper (default_names,kind_env,def_ord) [] defs in
  List.iter 
    (fun (id,(d,k)) -> 
      (match !d with
      | (d,false) -> typ_error Parse_ast.Unknown "Scattered definition never ended" (Some id) None None
      | (_, true) -> ()))
    partial_defs;
  (Defs defs),k_env,def_ord
