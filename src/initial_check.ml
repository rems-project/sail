open Type_internal
open Ast

type kind = Type_internal.kind
type typ = Type_internal.t

type envs = Nameset.t * kind Envmap.t * t Envmap.t
type 'a envs_out = 'a * envs

let id_to_string (Id_aux(id,l)) =
  match id with | Id(x) | DeIid(x) -> x

(*placeholder, write in type_internal*)
let kind_to_string _ = " kind pp place holder "

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
            | KOpt_aux(KOpt_none(id),l) | KOpt_aux(KOpt_kind(_,id),l) -> 
              (match Envmap.apply k_env (id_to_string id) with
              | Some(typ) -> typ::rst
              | None -> raise (Reporting_basic.err_unreachable l "Envmap didn't get an entry during typschm processing"))
          end)
        qlist
        [])

let typ_error l msg opt_id opt_kind =
  raise (Reporting_basic.err_typ 
           l
           (msg ^
              (match opt_id, opt_kind with
              | Some(id),Some(kind) -> (id_to_string id) ^ " of " ^ (kind_to_string kind)
              | Some(id),None -> ": " ^ (id_to_string id)
              | None,Some(kind) -> " " ^ (kind_to_string kind)
              | None,None -> "")))
                
let to_ast_id (Parse_ast.Id_aux(id,l)) =
    Id_aux( (match id with
             | Parse_ast.Id(x) -> Id(x)
             | Parse_ast.DeIid(x) -> DeIid(x)) , l)

let to_ast_base_kind (Parse_ast.BK_aux(k,l')) =
  match k with
  | Parse_ast.BK_type -> BK_aux(BK_type,l'), { k = K_Typ}
  | Parse_ast.BK_nat -> BK_aux(BK_nat,l'), { k = K_Nat }
  | Parse_ast.BK_order -> BK_aux(BK_order,l'), { k = K_Ord }
  | Parse_ast.BK_effects -> BK_aux(BK_effects,l'), { k = K_Efct }

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
          | _ -> typ_error l "Type constructor must have an -> kind ending in Type" None None

let rec to_ast_typ (k_env : kind Envmap.t) (t: Parse_ast.atyp) : Ast.typ =
  match t with
  | Parse_ast.ATyp_aux(t,l) ->
    Typ_aux( (match t with 
              | Parse_ast.ATyp_id(id) -> 
                let id = to_ast_id id in
                let mk = Envmap.apply k_env (id_to_string id) in
                (match mk with
                | Some(k) -> (match k.k with
                              | K_Typ -> Typ_var id
                              | K_infer -> k.k <- K_Typ; Typ_var id
                              | _ -> typ_error l "Required a variable with kind Type, encountered " (Some id) (Some k))
                | None -> typ_error l "Encountered an unbound variable" (Some id) None)
              | Parse_ast.ATyp_wild -> Typ_wild
              | Parse_ast.ATyp_fn(arg,ret,efct) -> Typ_fn( (to_ast_typ k_env arg),
                                                           (to_ast_typ k_env ret),
                                                           (to_ast_effects k_env efct))
              | Parse_ast.ATyp_tup(typs) -> Typ_tup( List.map (to_ast_typ k_env) typs)
              | Parse_ast.ATyp_app(pid,typs) ->
                  let id = to_ast_id pid in 
                  let k = Envmap.apply k_env (id_to_string id) in
                  (match k with 
                  | Some({k = K_Lam(args,t)}) -> Typ_app(id,(List.map2 (fun k a -> (to_ast_typ_arg k_env k a)) args typs))
                  | None -> typ_error l "Required a type constructor, encountered an unbound variable" (Some id) None
                  | _ -> typ_error l "Required a type constructor, encountered a base kind variable" (Some id) None)
              | _ -> typ_error l "Required an item of kind Type, encountered an illegal form for this kind" None None
    ), l)

and to_ast_nexp (k_env : kind Envmap.t) (n: Parse_ast.atyp) : Ast.nexp =
  match n with
  | Parse_ast.ATyp_aux(t,l) ->
    (match t with
    | Parse_ast.ATyp_id(id) ->                 
                let id = to_ast_id id in
                let mk = Envmap.apply k_env (id_to_string id) in
                (match mk with
                | Some(k) -> Nexp_aux((match k.k with
                                      | K_Nat -> Nexp_id id
                                      | K_infer -> k.k <- K_Nat; Nexp_id id
                                      | _ -> typ_error l "Required a variable with kind Nat, encountered " (Some id) (Some k)),l)
                | None -> typ_error l "Encountered an unbound variable" (Some id) None)
    | Parse_ast.ATyp_constant(i) -> Nexp_aux(Nexp_constant(i),l)
    | Parse_ast.ATyp_sum(t1,t2) ->
      let n1 = to_ast_nexp k_env t1 in
      let n2 = to_ast_nexp k_env t2 in
      Nexp_aux(Nexp_sum(n1,n2),l)
    | Parse_ast.ATyp_exp(t1) -> Nexp_aux(Nexp_exp(to_ast_nexp k_env t1),l)
    | Parse_ast.ATyp_tup(typs) ->
      let rec times_loop (typs : Parse_ast.atyp list) (one_ok : bool) : nexp =
        (match typs,one_ok with
        | [],_ | [_],false -> raise (Reporting_basic.err_unreachable l "to_ast_nexp has ATyp_tup with empty list or list with one element")
        | [t],true -> to_ast_nexp k_env t
        | (t1::typs),_ -> let n1 = to_ast_nexp k_env t1 in
                          let n2 = times_loop typs true in 
                          (Nexp_aux((Nexp_times(n1,n2)),l)))  (*TODO This needs just a portion of the l, think about adding a way to split*)
      in
      times_loop typs false
    | _ -> typ_error l "Requred an item of kind Nat, encountered an illegal form for this kind" None None)
    
and to_ast_order (k_env : kind Envmap.t) (o: Parse_ast.atyp) : Ast.order =
  match o with
  | Parse_ast.ATyp_aux(t,l) ->
    Ord_aux( (match t with
               | Parse_ast.ATyp_id(id) -> 
                let id = to_ast_id id in
                let mk = Envmap.apply k_env (id_to_string id) in
                (match mk with
                | Some(k) -> (match k.k with
                              | K_Ord -> Ord_id id
                              | K_infer -> k.k <- K_Ord; Ord_id id
                              | _ -> typ_error l "Required a variable with kind Order, encountered " (Some id) (Some k))
                | None -> typ_error l "Encountered an unbound variable" (Some id) None)
               | Parse_ast.ATyp_inc -> Ord_inc
               | Parse_ast.ATyp_dec -> Ord_dec
               | _ -> typ_error l "Requred an item of kind Order, encountered an illegal form for this kind" None None
    ), l)

and to_ast_effects (k_env : kind Envmap.t) (e : Parse_ast.atyp) : Ast.effects =
  match e with
  | Parse_ast.ATyp_aux(t,l) ->
    Effects_aux( (match t with
               | Parse_ast.ATyp_efid(id) ->  
                let id = to_ast_id id in
                let mk = Envmap.apply k_env (id_to_string id) in
                (match mk with
                | Some(k) -> (match k.k with
                              | K_Efct -> Effects_var id
                              | K_infer -> k.k <- K_Efct; Effects_var id
                              | _ -> typ_error l "Required a variable with kind Effect, encountered " (Some id) (Some k))
                | None -> typ_error l "Encountered an unbound variable" (Some id) None)
               | Parse_ast.ATyp_set(effects) ->
                 Effects_set( List.map 
                             (fun efct -> match efct with
                             | Parse_ast.Effect_aux(e,l) ->
                               Effect_aux((match e with 
                               | Parse_ast.Effect_rreg -> Effect_rreg
                               | Parse_ast.Effect_wreg -> Effect_wreg
                               | Parse_ast.Effect_rmem -> Effect_rmem
                               | Parse_ast.Effect_wmem -> Effect_wmem
                               | Parse_ast.Effect_undef -> Effect_undef
                               | Parse_ast.Effect_unspec -> Effect_unspec
                               | Parse_ast.Effect_nondet -> Effect_nondet),l))
                             effects)
               | _ -> typ_error l "Required an item of kind Effects, encountered an illegal form for this kind" None None
    ), l)

and to_ast_typ_arg (k_env : kind Envmap.t) (kind : kind) (arg : Parse_ast.atyp) : Ast.typ_arg =
  let l = (match arg with Parse_ast.ATyp_aux(_,l) -> l) in
  Typ_arg_aux (  
    (match kind.k with 
    | K_Typ -> Typ_arg_typ (to_ast_typ k_env arg)
    | K_Nat  -> Typ_arg_nexp (to_ast_nexp k_env arg)
    | K_Ord -> Typ_arg_order (to_ast_order k_env arg)
    | K_Efct -> Typ_arg_effects (to_ast_effects k_env arg)
    | _ -> raise (Reporting_basic.err_unreachable l "To_ast_typ_arg received Lam kind or infer kind")),
    l)

let to_ast_nexp_constraint (k_env : kind Envmap.t) (c : Parse_ast.nexp_constraint) : nexp_constraint =
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
               NC_nat_set_bounded(to_ast_id id, bounds)
    ), l)               

let to_ast_typquant (k_env: kind Envmap.t) (tq : Parse_ast.typquant) : typquant * kind Envmap.t =
  let opt_kind_to_ast k_env local_names (Parse_ast.KOpt_aux(ki,l)) =
    let id, key, kind, ktyp =
      match ki with
      | Parse_ast.KOpt_none(id) ->
	let id = to_ast_id id in
	let key = id_to_string id in
	let kind,ktyp = if (Envmap.in_dom key k_env) then None,(Envmap.apply k_env key) else None,(Some{ k = K_infer }) in
	id,key,kind, ktyp
      | Parse_ast.KOpt_kind(k,id) ->
	let id = to_ast_id id in
	let key = id_to_string id in
	let kind,ktyp = to_ast_kind k_env k in
	id,key,Some(kind),Some(ktyp)
    in
    if (Nameset.mem key local_names)
    then typ_error l "Encountered duplicate name in type scheme" (Some id) None
    else 
      let local_names = Nameset.add key local_names in
      let kopt,k_env = (match kind,ktyp with
        | Some(k),Some(kt) -> KOpt_kind(k,id), (Envmap.insert k_env (key,kt))
	| None, Some(kt) -> KOpt_none(id), (Envmap.insert k_env (key,kt))
	| _ -> raise (Reporting_basic.err_unreachable l "Envmap in dom true but apply gives None")) in
      KOpt_aux(kopt,l),k_env,local_names
  in
  match tq with
  | Parse_ast.TypQ_aux(tqa,l) ->
    (match tqa with
    | Parse_ast.TypQ_no_forall -> TypQ_aux(TypQ_no_forall,l), k_env
    | Parse_ast.TypQ_tq(qlist) ->
      let rec to_ast_q_items k_env local_names = function
	| [] -> [],k_env
	| q::qs -> (match q with
	            | Parse_ast.QI_aux(qi,l) ->
		      (match qi with
		      | Parse_ast.QI_const(n_const) -> 
			let c = QI_aux(QI_const(to_ast_nexp_constraint k_env n_const),l) in
			let qis,k_env = to_ast_q_items k_env local_names qs in
			(c::qis),k_env
		      | Parse_ast.QI_id(kid) ->
			let kid,k_env,local_names = opt_kind_to_ast k_env local_names kid in
			let c = QI_aux(QI_id(kid),l) in
			let qis,k_env = to_ast_q_items k_env local_names qs in
			(c::qis),k_env))	
      in
      let lst,k_env = to_ast_q_items k_env Nameset.empty qlist in
      TypQ_aux(TypQ_tq(lst),l), k_env)

let to_ast_typschm (k_env : kind Envmap.t) (tschm : Parse_ast.typschm) : Ast.typschm =
  match tschm with
  | Parse_ast.TypSchm_aux(ts,l) -> 
    (match ts with | Parse_ast.TypSchm_ts(tquant,t) ->
      let tq,k_env = to_ast_typquant k_env tquant in
      let typ = to_ast_typ k_env t in
      TypSchm_aux(TypSchm_ts(tq,typ),l))

let to_ast_lit (Parse_ast.L_aux(lit,l)) : lit = 
  L_aux(
    (match lit with
    | Parse_ast.L_unit -> L_unit
    | Parse_ast.L_zero -> L_zero
    | Parse_ast.L_one -> L_one
    | Parse_ast.L_true -> L_true
    | Parse_ast.L_false -> L_false
    | Parse_ast.L_num(i) -> L_num(i)
    | Parse_ast.L_hex(h) -> L_hex(h)
    | Parse_ast.L_bin(b) -> L_bin(b)
    | Parse_ast.L_string(s) -> L_string(s))
      ,l)

let rec to_ast_pat (k_env : kind Envmap.t) (Parse_ast.P_aux(pat,l) : Parse_ast.pat) : tannot pat = 
  P_aux(
    (match pat with 
    | Parse_ast.P_lit(lit) -> P_lit(to_ast_lit lit)
    | Parse_ast.P_wild -> P_wild
    | Parse_ast.P_as(pat,id) -> P_as(to_ast_pat k_env pat,to_ast_id id)
    | Parse_ast.P_typ(typ,pat) -> P_typ(to_ast_typ k_env typ,to_ast_pat k_env pat)
    | Parse_ast.P_id(id) -> P_id(to_ast_id id)
    | Parse_ast.P_app(id,pats) -> P_app(to_ast_id id, List.map (to_ast_pat k_env) pats)
    | Parse_ast.P_record(fpats,_) -> P_record(List.map 
                                                (fun (Parse_ast.FP_aux(Parse_ast.FP_Fpat(id,fp),l)) -> FP_aux(FP_Fpat(to_ast_id id, to_ast_pat k_env fp),(l,None)))
                                                fpats, false)
    | Parse_ast.P_vector(pats) -> P_vector(List.map (to_ast_pat k_env) pats)
    | Parse_ast.P_vector_indexed(ipats) -> P_vector_indexed(List.map (fun (i,pat) -> i,to_ast_pat k_env pat) ipats)
    | Parse_ast.P_vector_concat(pats) -> P_vector_concat(List.map (to_ast_pat k_env) pats)
    | Parse_ast.P_tup(pats) -> P_tup(List.map (to_ast_pat k_env) pats)
    | Parse_ast.P_list(pats) -> P_list(List.map (to_ast_pat k_env) pats)
    ), (l,None))

(*

type 
exp_aux =  (* Expression *)
   E_block of (exp) list (* block (parsing conflict with structs?) *)
 | E_id of id (* identifier *)
 | E_lit of lit (* literal constant *)
 | E_cast of atyp * exp (* cast *)
 | E_app of exp * (exp) list (* function application *)
 | E_app_infix of exp * id * exp (* infix function application *)
 | E_tuple of (exp) list (* tuple *)
 | E_if of exp * exp * exp (* conditional *)
 | E_vector of (exp) list (* vector (indexed from 0) *)
 | E_vector_indexed of ((int * exp)) list (* vector (indexed consecutively) *)
 | E_vector_access of exp * exp (* vector access *)
 | E_vector_subrange of exp * exp * exp (* subvector extraction *)
 | E_vector_update of exp * exp * exp (* vector functional update *)
 | E_vector_update_subrange of exp * exp * exp * exp (* vector subrange update (with vector) *)
 | E_list of (exp) list (* list *)
 | E_cons of exp * exp (* cons *)
 | E_record of fexps (* struct *) (*Not generated by parser, must be disambiguated from types *)
 | E_record_update of exp * fexps (* functional update of struct *)
 | E_field of exp * id (* field projection from struct *)
 | E_case of exp * (pexp) list (* pattern matching *)
 | E_let of letbind * exp (* let expression *)
 | E_assign of exp * exp (* imperative assignment *) (*left side not disambiguated to lexp by parser*)

__ ast __

and 'a exp_aux =  (* Expression *)
   E_block of ('a exp) list (* block (parsing conflict with structs?) *)
 | E_id of id (* identifier *)
 | E_lit of lit (* literal constant *)
 | E_cast of typ * 'a exp (* cast *)
 | E_app of 'a exp * ('a exp) list (* function application *)
 | E_app_infix of 'a exp * id * 'a exp (* infix function application *)
 | E_tuple of ('a exp) list (* tuple *)
 | E_if of 'a exp * 'a exp * 'a exp (* conditional *)
 | E_vector of ('a exp) list (* vector (indexed from 0) *)
 | E_vector_indexed of ((int * 'a exp)) list (* vector (indexed consecutively) *)
 | E_vector_access of 'a exp * 'a exp (* vector access *)
 | E_vector_subrange of 'a exp * 'a exp * 'a exp (* subvector extraction *)
 | E_vector_update of 'a exp * 'a exp * 'a exp (* vector functional update *)
 | E_vector_update_subrange of 'a exp * 'a exp * 'a exp * 'a exp (* vector subrange update (with vector) *)
 | E_list of ('a exp) list (* list *)
 | E_cons of 'a exp * 'a exp (* cons *)
 | E_record of 'a fexps (* struct *)
 | E_record_update of 'a exp * 'a fexps (* functional update of struct *)
 | E_field of 'a exp * id (* field projection from struct *)
 | E_case of 'a exp * ('a pexp) list (* pattern matching *)
 | E_let of 'a letbind * 'a exp (* let expression *)
 | E_assign of 'a lexp * 'a exp (* imperative assignment *)

*)

let rec to_ast_exp (k_env : kind Envmap.t) (Parse_ast.E_aux(exp,l) : Parse_ast.exp) : tannot exp = 
  E_aux(
    (match exp with
    | Parse_ast.E_block(exps) -> assert false
    | Parse_ast.E_id(id) -> E_id(to_ast_id id)
    | Parse_ast.E_lit(lit) -> E_lit(to_ast_lit lit)
    | Parse_ast.E_cast(typ,exp) -> E_cast(to_ast_typ k_env typ, to_ast_exp k_env exp)
    | Parse_ast.E_app(f,args) -> assert false
    | Parse_ast.E_app_infix(left,op,right) -> assert false
    | Parse_ast.E_tuple(exps) -> E_tuple(List.map (to_ast_exp k_env) exps)
    | Parse_ast.E_if(e1,e2,e3) -> E_if(to_ast_exp k_env e1, to_ast_exp k_env e2, to_ast_exp k_env e3)
    | Parse_ast.E_vector(exps) -> E_vector(List.map (to_ast_exp k_env) exps)
    | Parse_ast.E_vector_indexed(iexps) -> E_vector_indexed(List.map (fun (i,e) -> (i,to_ast_exp k_env e)) iexps)
    | Parse_ast.E_vector_access(vexp,exp) -> E_vector_access(to_ast_exp k_env vexp, to_ast_exp k_env exp)
    ), (l,None))

and to_ast_lexp (k_env : kind Envmap.t) (Parse_ast.E_aux(exp,l) : Parse_ast.exp) : tannot lexp = 
  LEXP_aux(
    (match exp with
    | Parse_ast.E_id(id) -> LEXP_id(to_ast_id id)
    | Parse_ast.E_vector_access(vexp,exp) -> LEXP_vector(to_ast_lexp k_env vexp, to_ast_exp k_env exp)
    | Parse_ast.E_vector_subrange(vexp,exp1,exp2) -> LEXP_vector_range(to_ast_lexp k_env vexp, to_ast_exp k_env exp1, to_ast_exp k_env exp2)
    | Parse_ast.E_field(fexp,id) -> LEXP_field(to_ast_lexp k_env fexp, to_ast_id id)
    | _ -> typ_error l "Only identifiers, vector accesses, vector slices, and fields can be on the lefthand side of an assignment" None None)
      , (l,None))
      
let to_ast_default (names, k_env, t_env) (default : Parse_ast.default_typing_spec) : (tannot default_typing_spec) envs_out =
  match default with
  | Parse_ast.DT_aux(df,l) ->
    (match df with 
    | Parse_ast.DT_kind(bk,id) ->
      let k,k_typ = to_ast_base_kind bk in
      let id = to_ast_id id in
      let key = id_to_string id in
      DT_aux(DT_kind(k,id),(l,None)),(names,(Envmap.insert k_env (key,k_typ)),t_env)
    | Parse_ast.DT_typ(typschm,id) ->
      let tps = to_ast_typschm k_env typschm in
      DT_aux(DT_typ(tps,to_ast_id id),(l,None)),(names,k_env,t_env) (* Does t_env need to be updated here in this pass? *)
    )

let to_ast_spec (names,k_env,t_env) (val_:Parse_ast.val_spec) : (tannot val_spec) envs_out =
  match val_ with
  | Parse_ast.VS_aux(vs,l) ->
    (match vs with
    | Parse_ast.VS_val_spec(ts,id) ->
      VS_aux(VS_val_spec(to_ast_typschm k_env ts,to_ast_id id),(l,None)),(names,k_env,t_env)) (*Do names and t_env need updating this pass? *)

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

let to_ast_typedef (names,k_env,t_env) (td:Parse_ast.type_def) : (tannot type_def) envs_out =
  match td with
  | Parse_ast.TD_aux(td,l) ->
  (match td with 
  | Parse_ast.TD_abbrev(id,name_scm_opt,typschm) ->
    let id = to_ast_id id in
    let key = id_to_string id in
    let typschm = to_ast_typschm k_env typschm in
    let td_abrv = TD_aux(TD_abbrev(id,to_ast_namescm name_scm_opt,typschm),(l,None)) in
    let typ = (match typschm with 
      | TypSchm_aux(TypSchm_ts(tq,typ), _) ->
        begin match (typquant_to_quantkinds k_env tq) with
        | [] -> {k = K_Typ}
        | typs -> {k= K_Lam(typs,{k=K_Typ})}
        end) in
    td_abrv,(names,Envmap.insert k_env (key,typ),t_env)
  | Parse_ast.TD_record(id,name_scm_opt,typq,fields,_) -> 
    let id = to_ast_id id in
    let key = id_to_string id in
    let typq,k_env = to_ast_typquant k_env typq in
    let fields = List.map (fun (atyp,id) -> (to_ast_typ k_env atyp),(to_ast_id id)) fields in (* Add check that all arms have unique names locally *)
    let td_rec = TD_aux(TD_record(id,to_ast_namescm name_scm_opt,typq,fields,false),(l,None)) in
    let typ = (match (typquant_to_quantkinds k_env typq) with
      | [ ] -> {k = K_Typ}
      | typs -> {k = K_Lam(typs,{k=K_Typ})}) in
    td_rec, (names,Envmap.insert k_env (key,typ), t_env)
  | Parse_ast.TD_variant(id,name_scm_opt,typq,arms,_) ->
    let id = to_ast_id id in
    let key = id_to_string id in
    let typq,k_env = to_ast_typquant k_env typq in
    let arms = List.map (fun (atyp,id) -> (to_ast_typ k_env atyp),(to_ast_id id)) arms in (* Add check that all arms have unique names *)
    let td_var = TD_aux(TD_variant(id,to_ast_namescm name_scm_opt,typq,arms,false),(l,None)) in
    let typ = (match (typquant_to_quantkinds k_env typq) with
      | [ ] -> {k = K_Typ}
      | typs -> {k = K_Lam(typs,{k=K_Typ})}) in
    td_var, (names,Envmap.insert k_env (key,typ), t_env)
  | Parse_ast.TD_enum(id,name_scm_opt,enums,_) -> 
    let id = to_ast_id id in
    let key = id_to_string id in
    let enums = List.map to_ast_id enums in
    let keys = List.map id_to_string enums in
    let td_enum = TD_aux(TD_enum(id,to_ast_namescm name_scm_opt,enums,false),(l,None)) in (* Add check that all enums have unique names *)
    let k_env = List.fold_right (fun k k_env -> Envmap.insert k_env (k,{k=K_Nat})) keys (Envmap.insert k_env (key,{k=K_Typ})) in
    td_enum, (names,k_env,t_env)
  | Parse_ast.TD_register(id,t1,t2,ranges) -> 
    let id = to_ast_id id in
    let key = id_to_string id in
    let n1 = to_ast_nexp k_env t1 in
    let n2 = to_ast_nexp k_env t2 in
    let ranges = List.map (fun (range,id) -> (to_ast_range range),to_ast_id id) ranges in
    TD_aux(TD_register(id,n1,n2,ranges),(l,None)), (names,k_env,t_env))

(*

type 
type_def = 
   TD_aux of type_def_aux * l

type 
type_def_aux =  (* Type definition body *)
   TD_abbrev of id * naming_scheme_opt * typschm (* type abbreviation *)
 | TD_record of id * naming_scheme_opt * typquant * ((atyp * id)) list * bool (* struct type definition *)
 | TD_variant of id * naming_scheme_opt * typquant * ((atyp * id)) list * bool (* union type definition *)
 | TD_enum of id * naming_scheme_opt * (id) list * bool (* enumeration type definition *)
 | TD_register of id * atyp * atyp * ((index_range * id)) list (* register mutable bitfield type definition *)


*)

(*

type 
def_aux =  (* Top-level definition *)
   DEF_type of type_def (* type definition *)
 | DEF_fundef of fundef (* function definition *)
 | DEF_val of letbind (* value definition *)
 | DEF_spec of val_spec (* top-level type constraint *)
 | DEF_default of default_typing_spec (* default kind and type assumptions *)
 | DEF_reg_dec of atyp * id (* register declaration *)
 | DEF_scattered_function of rec_opt * tannot_opt * effects_opt * id (* scattered function definition header *)
 | DEF_scattered_funcl of funcl (* scattered function definition clause *)
 | DEF_scattered_variant of id * naming_scheme_opt * typquant (* scattered union definition header *)
 | DEF_scattered_unioncl of id * atyp * id (* scattered union definition member *)
 | DEF_scattered_end of id (* scattered definition end *)
*)

let to_ast_def (names, k_env, t_env) partial_defs def : ((tannot def) option) envs_out * (tannot def) list = 
  let envs = (names,k_env,t_env) in
  match def with
  | Parse_ast.DEF_aux(d,l) ->
    (match d with
    | Parse_ast.DEF_type(t_def) -> 
      let td,envs = to_ast_typedef envs t_def in
      ((Some(DEF_aux(DEF_type(td),(l,None)))),envs),partial_defs
    | Parse_ast.DEF_fundef(f_def) -> assert false
    | Parse_ast.DEF_val(lbind) -> assert false
    | Parse_ast.DEF_spec(val_spec) -> 
      let vs,envs = to_ast_spec envs val_spec in
      ((Some(DEF_aux(DEF_spec(vs),(l,None)))),envs),partial_defs
    | Parse_ast.DEF_default(typ_spec) -> 
      let default,envs = to_ast_default envs typ_spec in
      ((Some(DEF_aux(DEF_default(default),(l,None)))),envs),partial_defs
    | Parse_ast.DEF_reg_dec(typ,id) ->
      let t = to_ast_typ k_env typ in
      let id = to_ast_id id in
      ((Some(DEF_aux(DEF_reg_dec(t,id),(l,None)))),envs),partial_defs (*If tracking types here, update tenv and None*)
    )


let rec to_ast_defs_helper envs partial_defs = function
  | [] -> ([],envs,partial_defs)
  | d::ds  -> let ((d', envs), partial_defs) = to_ast_def envs partial_defs d in
              match d' with
              | Some def -> let (defs, envs, p_defs) = to_ast_defs_helper envs partial_defs ds in 
                            (def::defs,envs, partial_defs)
              | None -> to_ast_defs_helper envs partial_defs ds
                

let to_ast (default_names : Nameset.t) (kind_env : kind Envmap.t) (typ_env : t Envmap.t) (Parse_ast.Defs(defs)) =
  let defs,_,partial_defs = to_ast_defs_helper (default_names,kind_env,typ_env) [] defs in
  (* (Defs defs) *) (*TODO there will be type defs in partial defs that need to replace "placeholders" in the def list *)
  (Defs [ ] ) (* Until not all forms return assert false *)
