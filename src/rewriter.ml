open Big_int
open Ast
open Type_internal
type typ = Type_internal.t
type 'a exp = 'a Ast.exp
type 'a emap = 'a Envmap.t
type envs = Type_check.envs

let rec partial_assoc (eq: 'a -> 'a -> bool) (v: 'a) (ls : ('a *'b) list ) : 'b option  = match ls with
  | [] -> None
  | (v1,v2)::ls -> if (eq v1 v) then Some v2 else partial_assoc eq v ls

let mk_atom_typ i = {t=Tapp("atom",[TA_nexp i])}

let rec rewrite_nexp_to_exp program_vars l nexp = 
  let rewrite n = rewrite_nexp_to_exp program_vars l n in
  let typ = mk_atom_typ nexp in
  let actual_rewrite_n nexp = 
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
                                      (l, simple_annot (mk_atom_typ (mk_c_int i))))),
                            (l, tag_annot typ (External (Some "power"))))
      | Nneg(n) -> E_aux (E_app_infix (E_aux (E_lit (L_aux (L_num 0,l)), (l, simple_annot (mk_atom_typ n_zero))),
                                       (Id_aux (Id "-",l)),
                                       rewrite n),
                          (l, tag_annot typ (External (Some "minus"))))
      | Nvar v -> (*TODO these need to generate an error as it's a place where there's insufficient specification. 
                    But, for now I need to permit this to make power.sail compile, and most errors are in trap 
                    or vectors *)
              (*let _ = Printf.eprintf "unbound variable here %s\n" v in*) 
        E_aux (E_id (Id_aux (Id v,l)),(l,simple_annot typ))
      | _ -> raise (Reporting_basic.err_unreachable l ("rewrite_nexp given n that can't be rewritten: " ^ (n_to_string nexp))) in
  match program_vars with
    | None -> actual_rewrite_n nexp
    | Some program_vars ->
      (match partial_assoc nexp_eq_check nexp program_vars with
        | None -> actual_rewrite_n nexp
        | Some(None,ev) ->
          (*let _ = Printf.eprintf "var case of rewrite, %s\n" ev in*)
          E_aux (E_id (Id_aux (Id ev,l)), (l, simple_annot typ))
        | Some(Some f,ev) -> 
          E_aux (E_app ((Id_aux (Id f,l)), [ (E_aux (E_id (Id_aux (Id ev,l)), (l,simple_annot typ)))]),
                 (l, tag_annot typ (External (Some f)))))

let rec match_to_program_vars ns bounds =
  match ns with
    | [] -> []
    | n::ns -> match find_var_from_nexp n bounds with
        | None -> match_to_program_vars ns bounds
        | Some(augment,ev) -> 
          (*let _ = Printf.eprintf "adding n %s to program var %s\n" (n_to_string n) ev in*)
          (n,(augment,ev))::(match_to_program_vars ns bounds)

let rec rewrite_exp nmap (E_aux (exp,(l,annot))) = 
  let rewrap e = E_aux (e,(l,annot)) in
  let rewrite = rewrite_exp nmap in
  match exp with
    | E_block exps -> rewrap (E_block (List.map rewrite exps))
    | E_nondet exps -> rewrap (E_nondet (List.map rewrite exps))
    | E_id _ | E_lit _  -> rewrap exp
    | E_cast (typ, exp) -> rewrap (E_cast (typ, rewrite exp))
    | E_app (id,exps) -> rewrap (E_app (id,List.map rewrite exps))
    | E_app_infix(el,id,er) -> rewrap (E_app_infix(rewrite el,id,rewrite er))
    | E_tuple exps -> rewrap (E_tuple (List.map rewrite exps))
    | E_if (c,t,e) -> rewrap (E_if (rewrite c,rewrite t, rewrite e))
    | E_for (id, e1, e2, e3, o, body) ->
      rewrap (E_for (id, rewrite e1, rewrite e2, rewrite e3, o, rewrite body))
    | E_vector exps -> rewrap (E_vector (List.map rewrite exps))
    | E_vector_indexed (exps,(Def_val_aux(default,dannot))) ->
      let def = match default with
        | Def_val_empty -> default
        | Def_val_dec e -> Def_val_dec (rewrite e) in
      rewrap (E_vector_indexed (List.map (fun (i,e) -> (i, rewrite e)) exps, Def_val_aux(def,dannot)))
    | E_vector_access (vec,index) -> rewrap (E_vector_access (rewrite vec,rewrite index))
    | E_vector_subrange (vec,i1,i2) ->
      rewrap (E_vector_subrange (rewrite vec,rewrite i1,rewrite i2))
    | E_vector_update (vec,index,new_v) -> 
      rewrap (E_vector_update (rewrite vec,rewrite index,rewrite new_v))
    | E_vector_update_subrange (vec,i1,i2,new_v) ->
      rewrap (E_vector_update_subrange (rewrite vec,rewrite i1,rewrite i2,rewrite new_v))
    | E_vector_append (v1,v2) -> rewrap (E_vector_append (rewrite v1,rewrite v2))
    | E_list exps -> rewrap (E_list (List.map rewrite exps)) 
    | E_cons(h,t) -> rewrap (E_cons (rewrite h,rewrite t))
    | E_record (FES_aux (FES_Fexps(fexps, bool),fannot)) -> 
      rewrap (E_record 
                (FES_aux (FES_Fexps 
                            (List.map (fun (FE_aux(FE_Fexp(id,e),fannot)) -> 
                              FE_aux(FE_Fexp(id,rewrite e),fannot)) fexps, bool), fannot)))
    | E_record_update (re,(FES_aux (FES_Fexps(fexps, bool),fannot))) ->
      rewrap (E_record_update ((rewrite re),
                               (FES_aux (FES_Fexps 
                                           (List.map (fun (FE_aux(FE_Fexp(id,e),fannot)) -> 
                                             FE_aux(FE_Fexp(id,rewrite e),fannot)) fexps, bool), fannot))))
    | E_field(exp,id) -> rewrap (E_field(rewrite exp,id))
    | E_case (exp ,pexps) -> 
      rewrap (E_case (rewrite exp,
                      (List.map 
                         (fun (Pat_aux (Pat_exp(p,e),pannot)) -> 
                           Pat_aux (Pat_exp(p,rewrite e),pannot)) pexps)))
    | E_let (letbind,body) -> rewrap (E_let(rewrite_let nmap letbind,rewrite body))
    | E_assign (lexp,exp) -> rewrap (E_assign(rewrite_lexp nmap lexp,rewrite exp))
    | E_exit e -> rewrap (E_exit (rewrite e))
    | E_internal_cast ((_,casted_annot),exp) -> 
      let new_exp = rewrite exp in
      (*let _ = Printf.eprintf "Removing an internal_cast with %s\n" (tannot_to_string casted_annot) in*)
      (match casted_annot,exp with
       | Base((_,t),_,_,_,_),E_aux(ec,(ecl,Base((_,exp_t),_,_,_,_))) ->
         (*let _ = Printf.eprintf "Considering removing an internal cast where the two types are %s and %s\n" (t_to_string t) (t_to_string exp_t) in*)
         (match t.t,exp_t.t with
          (*TODO should pass d_env into here so that I can look at the abbreviations if there are any here*)
          | Tapp("vector",[TA_nexp n1;TA_nexp nw1;TA_ord o1;_]),
            Tapp("vector",[TA_nexp n2;TA_nexp nw2;TA_ord o2;_]) 
          | Tapp("vector",[TA_nexp n1;TA_nexp nw1;TA_ord o1;_]),
            Tapp("reg",[TA_typ {t=(Tapp("vector",[TA_nexp n2; TA_nexp nw2; TA_ord o2;_]))}]) ->
            (match n1.nexp with
             | Nconst i1 -> if nexp_eq n1 n2 then new_exp else rewrap (E_cast (t_to_typ t,new_exp))
             | _ -> (match o1.order with
                 | Odec -> 
                   (*let _ = Printf.eprintf "Considering removing a cast or not: %s %s, %b\n" 
                     (n_to_string nw1) (n_to_string n1) (nexp_one_more_than nw1 n1) in*)
                   rewrap (E_cast (Typ_aux (Typ_var (Kid_aux((Var "length"),Parse_ast.Unknown)),
                                            Parse_ast.Unknown),new_exp))
                 | _ -> new_exp))
          | _ -> new_exp)
       | Base((_,t),_,_,_,_),_ ->
         (*let _ = Printf.eprintf "Considering removing an internal cast where the remaining type is %s\n%!"
            (t_to_string t) in*)
         (match t.t with
          | Tapp("vector",[TA_nexp n1;TA_nexp nw1;TA_ord o1;_]) ->
            (match o1.order with
             | Odec -> 
               (*let _ = Printf.eprintf "Considering removing a cast or not: %s %s, %b\n" 
                 (n_to_string nw1) (n_to_string n1) (nexp_one_more_than nw1 n1) in*)
               rewrap (E_cast (Typ_aux (Typ_var (Kid_aux((Var "length"), Parse_ast.Unknown)),
                                        Parse_ast.Unknown), new_exp))
             | _ -> new_exp)
          | _ -> new_exp)
       | _ -> (*let _ = Printf.eprintf "Not a base match?\n" in*) new_exp)
    | E_internal_exp (l,impl) ->
      (match impl with
       | Base((_,t),_,_,_,bounds) ->
         let bounds = match nmap with | None -> bounds | Some nm -> add_map_to_bounds nm bounds in
         (*let _ = Printf.eprintf "Rewriting internal expression, with type %s\n" (t_to_string t) in*)
          (match t.t with
            (*Old case; should possibly be removed*)
            | Tapp("register",[TA_typ {t= Tapp("vector",[ _; TA_nexp r;_;_])}])
            | Tapp("vector", [_;TA_nexp r;_;_]) ->
              (*let _ = Printf.eprintf "vector case with %s, bounds are %s\n" 
                (n_to_string r) (bounds_to_string bounds) in*)
              let nexps = expand_nexp r in
              (match (match_to_program_vars nexps bounds) with
                | [] -> rewrite_nexp_to_exp None l r
                | map -> rewrite_nexp_to_exp (Some map) l r)
            | Tapp("implicit", [TA_nexp i]) ->
              (*let _ = Printf.eprintf "Implicit case with %s\n" (n_to_string i) in*)
              let nexps = expand_nexp i in
              (match (match_to_program_vars nexps bounds) with
                | [] -> rewrite_nexp_to_exp None l i
                | map -> rewrite_nexp_to_exp (Some map) l i)
            | _ -> 
              raise (Reporting_basic.err_unreachable l 
                       ("Internal_exp given unexpected types " ^ (t_to_string t))))
        | _ -> raise (Reporting_basic.err_unreachable l ("Internal_exp given none Base annot")))
    | E_internal_exp_user ((l,user_spec),(_,impl)) -> 
      (match (user_spec,impl) with
        | (Base((_,tu),_,_,_,_), Base((_,ti),_,_,_,bounds)) ->
          (*let _ = Printf.eprintf "E_interal_user getting rewritten two types are %s and %s\n"
            (t_to_string tu) (t_to_string ti) in*)
          let bounds =  match nmap with | None -> bounds | Some nm -> add_map_to_bounds nm bounds in
          (match (tu.t,ti.t) with
            | (Tapp("implicit", [TA_nexp u]),Tapp("implicit",[TA_nexp i])) ->
              (*let _ = Printf.eprintf "Implicit case with %s\n" (n_to_string i) in*)
              let nexps = expand_nexp i in
              (match (match_to_program_vars nexps bounds) with
                | [] -> rewrite_nexp_to_exp None l i
                  (*add u to program_vars env; for now it will work out properly by accident*)
                | map -> rewrite_nexp_to_exp (Some map) l i)
            | _ -> 
              raise (Reporting_basic.err_unreachable l 
                       ("Internal_exp_user given unexpected types " ^ (t_to_string tu) ^ ", " ^ (t_to_string ti))))
        | _ -> raise (Reporting_basic.err_unreachable l ("Internal_exp_user given none Base annot")))

and rewrite_let map (LB_aux(letbind,(l,annot))) =
  let map = merge_option_maps map (get_map_tannot annot) in
  match letbind with
  | LB_val_explicit (typschm, pat,exp) ->
    LB_aux(LB_val_explicit (typschm,pat, rewrite_exp map exp),(l,annot))
  | LB_val_implicit ( pat, exp) ->
    LB_aux(LB_val_implicit (pat,rewrite_exp map exp),(l,annot))

and rewrite_lexp map (LEXP_aux(lexp,(l,annot))) = 
  let rewrap le = LEXP_aux(le,(l,annot)) in
  match lexp with
  | LEXP_id _ | LEXP_cast _ -> rewrap lexp
  | LEXP_memory (id,exps) -> rewrap (LEXP_memory(id,List.map (rewrite_exp map) exps))
  | LEXP_vector (lexp,exp) -> rewrap (LEXP_vector (rewrite_lexp map lexp,rewrite_exp map exp))
  | LEXP_vector_range (lexp,exp1,exp2) -> 
    rewrap (LEXP_vector_range (rewrite_lexp map lexp,rewrite_exp map exp1,rewrite_exp map exp2))
  | LEXP_field (lexp,id) -> rewrap (LEXP_field (rewrite_lexp map lexp,id))

let rewrite_fun (FD_aux (FD_function(recopt,tannotopt,effectopt,funcls),(l,fdannot))) = 
  let rewrite_funcl (FCL_aux (FCL_Funcl(id,pat,exp),(l,annot))) = 
    (*let _ = Printf.eprintf "Rewriting function %s, pattern %s\n" 
      (match id with (Id_aux (Id i,_)) -> i) (Pretty_print.pat_to_string pat) in*)
    (FCL_aux (FCL_Funcl (id,pat,rewrite_exp (get_map_tannot fdannot) exp),(l,annot))) 
  in FD_aux (FD_function(recopt,tannotopt,effectopt,List.map rewrite_funcl funcls),(l,fdannot))

let rewrite_def d = match d with
  | DEF_type _ | DEF_spec _ | DEF_default _ | DEF_reg_dec _ -> d
  | DEF_fundef fdef -> DEF_fundef (rewrite_fun fdef)
  | DEF_val letbind -> DEF_val (rewrite_let None letbind)
  | DEF_scattered _ -> raise (Reporting_basic.err_unreachable Parse_ast.Unknown "DEF_scattered survived to rewritter")

let rewrite_defs (Defs defs) = 
  let rec rewrite ds = match ds with
    | [] -> []
    | d::ds -> (rewrite_def d)::(rewrite ds) in
  Defs (rewrite defs)
