open Big_int
open Ast
open Type_internal
type typ = Type_internal.t
type 'a exp = 'a Ast.exp
type 'a emap = 'a Envmap.t
type envs = Type_check.envs

let rec partial_assoc (v: 'a) (ls : ('a *'b) list ) : 'b option  = match ls with
  | [] -> None
  | (v1,v2)::ls -> if v1 = v then Some v2 else partial_assoc v ls

let mk_atom_typ i = {t=Tapp("atom",[TA_nexp i])}

let rec rewrite_nexp_to_exp program_vars l nexp = 
  let rewrite n = rewrite_nexp_to_exp program_vars l n in
  let typ = mk_atom_typ nexp in
  match nexp.nexp with
    | Nconst i -> E_aux (E_lit (L_aux (L_num (int_of_big_int i),l)), (l,simple_annot typ))
    | Nadd (n1,n2) -> E_aux (E_app_infix (rewrite n1,(Id_aux (Id "+",l)),rewrite n2),
			     (l, (tag_annot typ (External (Some "add")))))
    | Nmult (n1,n2) -> E_aux (E_app_infix (rewrite n1,(Id_aux (Id "*",l)),rewrite n2),
			      (l, tag_annot typ (External (Some "multiply"))))
    | Nsub (n1,n2) -> E_aux (E_app_infix (rewrite n1,(Id_aux (Id "-",l)),rewrite n2),
			     (l, tag_annot typ (External (Some "minus"))))
    | N2n (n, _) -> E_aux (E_app_infix (E_aux (E_lit (L_aux (L_num 2,l)), (l, simple_annot (mk_atom_typ n_two))),
					(Id_aux (Id "**",l)),
					rewrite n), (l, tag_annot typ (External (Some "power"))))
    | Npow(n,i) -> E_aux (E_app_infix 
			    (rewrite n, (Id_aux (Id "**",l)),
			     E_aux (E_lit (L_aux (L_num i,l)),
				    (l, simple_annot (mk_atom_typ {nexp = Nconst (big_int_of_int i)})))),
			  (l, tag_annot typ (External (Some "power"))))
    | Nneg(n) -> E_aux (E_app_infix (E_aux (E_lit (L_aux (L_num 0,l)), (l, simple_annot (mk_atom_typ n_zero))),
				     (Id_aux (Id "-",l)),
				     rewrite n),
			(l, tag_annot typ (External (Some "minus"))))
    | Nvar v -> 
      match program_vars with
	| None -> assert false
	| Some program_vars ->
	  (match partial_assoc v program_vars with
	    | None ->
	      (*TODO these need to generate an error as it's a place where there's insufficient specification. 
		But, for now I need to permit this to make power.sail compile, and most errors are in trap 
		or vectors *)
	      (*let _ = Printf.printf "unbound variable here %s\n" v in *)
	      E_aux (E_id (Id_aux (Id v,l)),(l,simple_annot typ))
	    | Some(None,ev) ->
	      (*let _ = Printf.printf "var case of nvar rewrite, %s\n" ev in*)
	      E_aux (E_id (Id_aux (Id ev,l)), (l, simple_annot typ))
	    | Some(Some f,ev) -> 
	      E_aux (E_app ((Id_aux (Id f,l)), [ (E_aux (E_id (Id_aux (Id ev,l)), (l,simple_annot typ)))]),
		     (l, tag_annot typ (External (Some f)))))

let rec match_to_program_vars vs bounds =
  match vs with
    | [] -> []
    | v::vs -> match find_var_from_nvar v bounds with
	| None -> match_to_program_vars vs bounds
	| Some(augment,ev) -> (v,(augment,ev))::(match_to_program_vars vs bounds)

let rec rewrite_exp (E_aux (exp,(l,annot))) = 
  let rewrap e = E_aux (e,(l,annot)) in
  match exp with
    | E_block exps -> rewrap (E_block (List.map rewrite_exp exps))
    | E_nondet exps -> rewrap (E_nondet (List.map rewrite_exp exps))
    | E_id _ | E_lit _  -> rewrap exp
    | E_cast (typ, exp) -> rewrap (E_cast (typ, rewrite_exp exp))
    | E_app (id,exps) -> rewrap (E_app (id,List.map rewrite_exp exps))
    | E_app_infix(el,id,er) -> rewrap (E_app_infix(rewrite_exp el,id,rewrite_exp er))
    | E_tuple exps -> rewrap (E_tuple (List.map rewrite_exp exps))
    | E_if (c,t,e) -> rewrap (E_if (rewrite_exp c,rewrite_exp t, rewrite_exp e))
    | E_for (id, e1, e2, e3, o, body) ->
      rewrap (E_for (id, rewrite_exp e1, rewrite_exp e2, rewrite_exp e3, o, rewrite_exp body))
    | E_vector exps -> rewrap (E_vector (List.map rewrite_exp exps))
    | E_vector_indexed (exps,(Def_val_aux(default,dannot))) ->
      let def = match default with
	| Def_val_empty -> default
	| Def_val_dec e -> Def_val_dec (rewrite_exp e) in
      rewrap (E_vector_indexed (List.map (fun (i,e) -> (i, rewrite_exp e)) exps, Def_val_aux(def,dannot)))
    | E_vector_access (vec,index) -> rewrap (E_vector_access (rewrite_exp vec,rewrite_exp index))
    | E_vector_subrange (vec,i1,i2) ->
      rewrap (E_vector_subrange (rewrite_exp vec,rewrite_exp i1,rewrite_exp i2))
    | E_vector_update (vec,index,new_v) -> 
      rewrap (E_vector_update (rewrite_exp vec,rewrite_exp index,rewrite_exp new_v))
    | E_vector_update_subrange (vec,i1,i2,new_v) ->
      rewrap (E_vector_update_subrange (rewrite_exp vec,rewrite_exp i1,rewrite_exp i2,rewrite_exp new_v))
    | E_vector_append (v1,v2) -> rewrap (E_vector_append (rewrite_exp v1,rewrite_exp v2))
    | E_list exps -> rewrap (E_list (List.map rewrite_exp exps)) 
    | E_cons(h,t) -> rewrap (E_cons (rewrite_exp h,rewrite_exp t))
    | E_record (FES_aux (FES_Fexps(fexps, bool),fannot)) -> 
      rewrap (E_record 
		(FES_aux (FES_Fexps 
			    (List.map (fun (FE_aux(FE_Fexp(id,e),fannot)) -> 
			      FE_aux(FE_Fexp(id,rewrite_exp e),fannot)) fexps, bool), fannot)))
    | E_record_update (re,(FES_aux (FES_Fexps(fexps, bool),fannot))) ->
      rewrap (E_record_update ((rewrite_exp re),
			       (FES_aux (FES_Fexps 
					   (List.map (fun (FE_aux(FE_Fexp(id,e),fannot)) -> 
					     FE_aux(FE_Fexp(id,rewrite_exp e),fannot)) fexps, bool), fannot))))
    | E_field(exp,id) -> rewrap (E_field(rewrite_exp exp,id))
    | E_case (exp ,pexps) -> 
      rewrap (E_case (rewrite_exp exp,
		      (List.map 
			 (fun (Pat_aux (Pat_exp(p,e),pannot)) -> 
			   Pat_aux (Pat_exp(p,rewrite_exp e),pannot)) pexps)))
    | E_let (letbind,body) -> rewrap (E_let(rewrite_let letbind,rewrite_exp body))
    | E_assign (lexp,exp) -> rewrap (E_assign(rewrite_lexp lexp,rewrite_exp exp))
    | E_exit e -> rewrap (E_exit (rewrite_exp e))
    | E_internal_cast ((_,casted_annot),exp) -> 
      let new_exp = rewrite_exp exp in
      (match casted_annot,exp with
	| NoTyp,_ | Overload _,_ -> new_exp
	| Base((_,t),_,_,_,_),E_aux(ec,(ecl,Base((_,exp_t),_,_,_,_))) ->
	  (match t.t,exp_t.t with
	    (*TODO should pass d_env into here so that I can look at the abbreviations if there are any here*)
	    | Tapp("vector",[TA_nexp n1;TA_nexp nw1;TA_ord o1;_]),
	      Tapp("vector",[TA_nexp n2;TA_nexp nw2;TA_ord o2;_]) ->
	      (match n1.nexp with
		| Nconst i1 -> if nexp_eq n1 n2 then new_exp else rewrap (E_cast (t_to_typ t,new_exp))
		| Nadd _ | Nsub _ -> (match o1.order with
		    | Oinc -> new_exp
		    | Odec -> 
		      if nexp_one_more_than nw1 n1 
		      then rewrap (E_cast (Typ_aux (Typ_var (Kid_aux((Var "length"), Unknown)), Unknown), new_exp))
		      else new_exp)
		| _ -> new_exp)
	    | _ -> new_exp))
    | E_internal_exp (l,impl) ->
      (*let _ = Printf.printf "Rewriting internal expression\n" in*) 
      (match impl with
	| Base((_,t),_,_,_,bounds) ->
	  match t.t with
	    (*Old case; should possibly be removed*)
	    | Tapp("register",[TA_typ {t= Tapp("vector",[ _; TA_nexp r;_;_])}])
	    | Tapp("vector", [_;TA_nexp r;_;_]) ->
	      let vars = get_all_nvar r in
	      (match vars with
		| [] -> rewrite_nexp_to_exp None l r
		| vars -> rewrite_nexp_to_exp (Some (match_to_program_vars vars bounds)) l r)
	    | Tapp("implicit", [TA_nexp i]) ->
	      (*let _ = Printf.printf "Implicit case with %s\n" (n_to_string i) in*)
	      let vars = get_all_nvar i in
	      (match vars with
		| [] -> rewrite_nexp_to_exp None l i
		| vars -> rewrite_nexp_to_exp (Some (match_to_program_vars vars bounds)) l i))
    | E_internal_exp_user ((l,user_spec),(_,impl)) -> 
      (match (user_spec,impl) with
	| (Base((_,tu),_,_,_,_), Base((_,ti),_,_,_,bounds)) ->
	  (*let _ = Printf.eprintf "E_interal_user getting rewritten two types are %s and %s\n" (t_to_string tu) (t_to_string ti) in*)
	  match (tu.t,ti.t) with
	    | (Tapp("implicit", [TA_nexp u]),Tapp("implicit",[TA_nexp i])) ->
	      let vars = get_all_nvar i in
	      (match vars with
		| [] -> rewrite_nexp_to_exp None l i
		  (*add u to program_vars env; for now it will work out properly by accident*)
		| vars -> rewrite_nexp_to_exp (Some (match_to_program_vars vars bounds)) l i))

and rewrite_let (LB_aux(letbind,(l,annot))) = match letbind with
  | LB_val_explicit (typschm, pat,exp) ->
    LB_aux(LB_val_explicit (typschm,pat, rewrite_exp exp),(l,annot))
  | LB_val_implicit ( pat, exp) ->
    LB_aux(LB_val_implicit (pat,rewrite_exp exp),(l,annot))

and rewrite_lexp (LEXP_aux(lexp,(l,annot))) = 
  let rewrap le = LEXP_aux(le,(l,annot)) in
  match lexp with
  | LEXP_id _ | LEXP_cast _ -> rewrap lexp
  | LEXP_memory (id,exps) -> rewrap (LEXP_memory(id,List.map rewrite_exp exps))
  | LEXP_vector (lexp,exp) -> rewrap (LEXP_vector (rewrite_lexp lexp,rewrite_exp exp))
  | LEXP_vector_range (lexp,exp1,exp2) -> 
    rewrap (LEXP_vector_range (rewrite_lexp lexp,rewrite_exp exp1,rewrite_exp exp2))
  | LEXP_field (lexp,id) -> rewrap (LEXP_field (rewrite_lexp lexp,id))

let rewrite_fun (FD_aux (FD_function(recopt,tannotopt,effectopt,funcls),(l,annot))) = 
  let rewrite_funcl (FCL_aux (FCL_Funcl(id,pat,exp),(l,annot))) = 
    (*let _ = Printf.printf "Rewriting function %s\n" (match id with (Id_aux (Id i,_)) -> i) in*)
    (FCL_aux (FCL_Funcl (id,pat,rewrite_exp exp),(l,annot))) 
  in FD_aux (FD_function(recopt,tannotopt,effectopt,List.map rewrite_funcl funcls),(l,annot))

let rewrite_def d = match d with
  | DEF_type _ | DEF_spec _ | DEF_default _ | DEF_reg_dec _ -> d
  | DEF_fundef fdef -> DEF_fundef (rewrite_fun fdef)
  | DEF_val letbind -> DEF_val (rewrite_let letbind)

let rewrite_defs (Defs defs) = 
  let rec rewrite ds = match ds with
    | [] -> []
    | d::ds -> (rewrite_def d)::(rewrite ds) in
  Defs (rewrite defs)
