open Parse_ast
open Ast
open Type_internal

(* TODO: put this somewhere common *)

let id_to_string (Id_aux(id,l)) =
  match id with
    | Id(s) -> s
    | DeIid(s) -> s

(* TODO: check for temporary failwiths *)

let optmap v f =
  match v with
  | None -> None
  | Some v -> Some (f v)

let disable_const_propagation = ref false

(* Based on current type checker's behaviour *)
let pat_id_is_variable t_env id =
  match Envmap.apply t_env id with
  | Some (Base(_,Constructor _,_,_,_,_))
  | Some (Base(_,Enum _,_,_,_,_))
    -> false
  | _ -> true
  

let bindings_from_pat t_env p =
  let rec aux_pat (P_aux (p,annot)) =
  match p with
  | P_lit _
  | P_wild
    -> []
  | P_as (p,id) -> id_to_string id::(aux_pat p)
  | P_typ (_,p) -> aux_pat p
  | P_id id ->
     let i = id_to_string id in
     if pat_id_is_variable t_env i then [i] else []
  | P_vector ps
  | P_vector_concat ps
  | P_app (_,ps)
  | P_tup ps
  | P_list ps
    -> List.concat (List.map aux_pat ps)
  | P_record (fps,_) -> List.concat (List.map aux_fpat fps)
  | P_vector_indexed ips -> List.concat (List.map (fun (_,p) -> aux_pat p) ips)
  and aux_fpat (FP_aux (FP_Fpat (_,p), _)) = aux_pat p
  in aux_pat p

let remove_bound t_env env pat =
  let bound = bindings_from_pat t_env pat in
  List.fold_left (fun sub v -> Envmap.remove env v) env bound


let split_defs splits (Type_check.Env (d_env,t_env,b_env,tp_env)) defs =

  let can_match (E_aux (e,(l,annot)) as exp) cases =
    match e with
    | E_id id ->
       let i = id_to_string id in
       (match Envmap.apply t_env i with
       | Some(Base(_,Enum _,_,_,_,_)) ->
          let rec findpat cases =
            match cases with
            | [] -> (Reporting_basic.print_err false true l "Monomorphisation"
                       ("Failed to find a case for " ^ i); None)
            | [Pat_aux (Pat_exp (P_aux (P_wild,_),exp),_)] -> Some exp
            | (Pat_aux (Pat_exp (P_aux (P_id id',_),exp),_))::tl
            | (Pat_aux (Pat_exp (P_aux (P_app (id',[]),_),exp),_))::tl ->
               if i = id_to_string id' then Some exp else findpat tl
            | (Pat_aux (Pat_exp (P_aux (_,(l',_)),_),_))::_ ->
               (Reporting_basic.print_err false true l' "Monomorphisation"
                  "Unexpected kind of pattern for enumeration"; None)
          in findpat cases
       | _ -> None)
    | _ -> None
  in
  (* Constant propogation *)
  let rec const_prop_exp substs ((E_aux (e,(l,annot))) as exp) =
    let re e = E_aux (e,(l,annot)) in
    match e with
      (* TODO: are there circumstances in which we should get rid of these? *)
    | E_block es -> re (E_block (List.map (const_prop_exp substs) es))
    | E_nondet es -> re (E_nondet (List.map (const_prop_exp substs) es))
       
    | E_id id ->
       (match Envmap.apply substs (id_to_string id) with
       | None -> exp
       | Some exp' -> exp')
    | E_lit _
    | E_sizeof _
    | E_internal_exp _
    | E_sizeof_internal _
    | E_internal_exp_user _
    | E_comment _
      -> exp
    | E_cast (t,e') -> re (E_cast (t, const_prop_exp substs e'))
    | E_app (id,es) -> re (E_app (id,List.map (const_prop_exp substs) es))
    | E_app_infix (e1,id,e2) -> re (E_app_infix (const_prop_exp substs e1,id,const_prop_exp substs e2))
    | E_tuple es -> re (E_tuple (List.map (const_prop_exp substs) es))
    | E_if (e1,e2,e3) -> re (E_if (const_prop_exp substs e1, const_prop_exp substs e2, const_prop_exp substs e3))
    | E_for (id,e1,e2,e3,ord,e4) -> re (E_for (id,const_prop_exp substs e1,const_prop_exp substs e2,const_prop_exp substs e3,ord,const_prop_exp (Envmap.remove substs (id_to_string id)) e4))
    | E_vector es -> re (E_vector (List.map (const_prop_exp substs) es))
    | E_vector_indexed (ies,ed) -> re (E_vector_indexed (List.map (fun (i,e) -> (i,const_prop_exp substs e)) ies,
                                                         const_prop_opt_default substs ed))
    | E_vector_access (e1,e2) -> re (E_vector_access (const_prop_exp substs e1,const_prop_exp substs e2))
    | E_vector_subrange (e1,e2,e3) -> re (E_vector_subrange (const_prop_exp substs e1,const_prop_exp substs e2,const_prop_exp substs e3))
    | E_vector_update (e1,e2,e3) -> re (E_vector_update (const_prop_exp substs e1,const_prop_exp substs e2,const_prop_exp substs e3))
    | E_vector_update_subrange (e1,e2,e3,e4) -> re (E_vector_update_subrange (const_prop_exp substs e1,const_prop_exp substs e2,const_prop_exp substs e3,const_prop_exp substs e4))
    | E_vector_append (e1,e2) -> re (E_vector_append (const_prop_exp substs e1,const_prop_exp substs e2))
    | E_list es -> re (E_list (List.map (const_prop_exp substs) es))
    | E_cons (e1,e2) -> re (E_cons (const_prop_exp substs e1,const_prop_exp substs e2))
    | E_record fes -> re (E_record (const_prop_fexps substs fes))
    | E_record_update (e,fes) -> re (E_record_update (const_prop_exp substs e, const_prop_fexps substs fes))
    | E_field (e,id) -> re (E_field (const_prop_exp substs e,id))
    | E_case (e,cases) ->
       let e' = const_prop_exp substs e in
       (* TODO: ought to propagate type substitution to other terms *)
       (match can_match e' cases with
       | None -> re (E_case (e', List.map (const_prop_pexp substs) cases))
       | Some e'' -> const_prop_exp substs e'')
    | E_let (lb,e) ->
       let (lb',substs') = const_prop_letbind substs lb in
       re (E_let (lb', const_prop_exp substs' e))
    | E_assign (le,e) -> re (E_assign (const_prop_lexp substs le, const_prop_exp substs e))
    | E_exit e -> re (E_exit (const_prop_exp substs e))
    | E_return e -> re (E_return (const_prop_exp substs e))
    | E_assert (e1,e2) -> re (E_assert (const_prop_exp substs e1,const_prop_exp substs e2))
    | E_internal_cast (ann,e) -> re (E_internal_cast (ann,const_prop_exp substs e))
    | E_comment_struc e -> re (E_comment_struc e)
    | E_internal_let _
    | E_internal_plet _
    | E_internal_return _
      -> raise (Reporting_basic.err_unreachable l
                  "Unexpected internal expression encountered in monomorphisation")
    and const_prop_opt_default substs ((Def_val_aux (ed,annot)) as eda) =
    match ed with
    | Def_val_empty -> eda
    | Def_val_dec e -> Def_val_aux (Def_val_dec (const_prop_exp substs e),annot)
  and const_prop_fexps substs (FES_aux (FES_Fexps (fes,flag), annot)) =
    FES_aux (FES_Fexps (List.map (const_prop_fexp substs) fes, flag), annot)
  and const_prop_fexp substs (FE_aux (FE_Fexp (id,e), annot)) =
    FE_aux (FE_Fexp (id,const_prop_exp substs e),annot)
  and const_prop_pexp substs (Pat_aux (Pat_exp (p,e),l)) =
    Pat_aux (Pat_exp (p,const_prop_exp (remove_bound t_env substs p) e),l)
  and const_prop_letbind substs (LB_aux (lb,annot)) =
    match lb with
    | LB_val_explicit (tysch,p,e) ->
       (LB_aux (LB_val_explicit (tysch,p,const_prop_exp substs e), annot),
        remove_bound t_env substs p)
    | LB_val_implicit (p,e) ->
       (LB_aux (LB_val_implicit (p,const_prop_exp substs e), annot),
        remove_bound t_env substs p)
  and const_prop_lexp substs ((LEXP_aux (e,annot)) as le) =
    let re e = LEXP_aux (e,annot) in
    match e with
    | LEXP_id _ (* shouldn't end up substituting here *)
    | LEXP_cast _
      -> le
    | LEXP_memory (id,es) -> re (LEXP_memory (id,List.map (const_prop_exp substs) es)) (* or here *)
    | LEXP_tup les -> re (LEXP_tup (List.map (const_prop_lexp substs) les))
    | LEXP_vector (le,e) -> re (LEXP_vector (const_prop_lexp substs le, const_prop_exp substs e))
    | LEXP_vector_range (le,e1,e2) -> re (LEXP_vector_range (const_prop_lexp substs le, const_prop_exp substs e1, const_prop_exp substs e2))
    | LEXP_field (le,id) -> re (LEXP_field (const_prop_lexp substs le, id))
  in

  let subst_exp subst exp =
    if !disable_const_propagation then
    (* TODO: This just sticks a let in - we really need propogation *)
      let (subi,(E_aux (_,subannot) as sube)) = subst in
      let E_aux (e,(l,annot)) = exp in
      let lg = Generated l in
      let p = P_aux (P_id (Id_aux (Id subi, lg)), subannot) in
      E_aux (E_let (LB_aux (LB_val_implicit (p,sube),(lg,annot)), exp),(lg,annot))
    else 
      let substs = Envmap.from_list [subst] in
      const_prop_exp substs exp
  in
    

  (* Split a variable pattern into every possible value *)

  let split id l tannot =
    let new_l = Generated l in
    let new_id i = Id_aux (Id i, new_l) in
    match tannot with
    | Type_internal.NoTyp ->
       raise (Reporting_basic.err_general l ("No type information for variable " ^ id ^ " to split on"))
    | Type_internal.Overload _ ->
       raise (Reporting_basic.err_general l ("Type for variable " ^ id ^ " to split on is overloaded"))
    | Type_internal.Base ((tparams,ty0),_,cs,_,_,_) ->
       let () = match tparams with
         | [] -> ()
         | _ -> raise (Reporting_basic.err_general l ("Type for variable " ^ id ^ " to split on has parameters"))
       in
       let ty = match ty0.t with Tabbrev(_,ty) -> ty | _ -> ty0 in
       let cannot () =
         raise (Reporting_basic.err_general l
                  ("Cannot split type " ^ Type_internal.t_to_string ty ^ " for variable " ^ id))
       in
       (match ty.t with
       | Tid i ->
          (match Envmap.apply d_env.enum_env i with
          (* enumerations *)
          | Some ns -> List.map (fun n -> (P_aux (P_id (new_id n),(l,tannot)),
                                           (id,E_aux (E_id (new_id n),(new_l,tannot))))) ns
          | None -> cannot ())
     (*|  vectors TODO *)
     (*|  numbers TODO *)
       | _ -> cannot ())
  in
  
  (* Split variable patterns at the given locations *)

  let map_locs ls (Defs defs) =
    let rec match_l = function
      | Unknown
      | Int _ -> []
      | Generated l -> [] (* Could do match_l l, but only want to split user-written patterns *)
      | Range (p,q) ->
         List.filter (fun ((filename,line),_) ->
           Filename.basename p.Lexing.pos_fname = filename &&
             p.Lexing.pos_lnum <= line && line <= q.Lexing.pos_lnum) ls
    in 
    
    let split_pat var p =
      let rec list f = function
        | [] -> None
        | h::t ->
           match f h with
           | None -> (match list f t with None -> None | Some (l,ps,r) -> Some (h::l,ps,r))
           | Some ps -> Some ([],ps,t)
      in
      let rec spl (P_aux (p,(l,annot))) =
        let relist f ctx ps =
          optmap (list f ps) 
            (fun (left,ps,right) ->
              List.map (fun (p,sub) -> P_aux (ctx (left@p::right),(l,annot)),sub) ps)
        in
        let re f p =
          optmap (spl p)
            (fun ps -> List.map (fun (p,sub) -> (P_aux (f p,(l,annot)), sub)) ps)
        in
        let fpat (FP_aux ((FP_Fpat (id,p),annot))) =
          optmap (spl p)
            (fun ps -> List.map (fun (p,sub) -> FP_aux (FP_Fpat (id,p), annot), sub) ps)
        in
        let ipat (i,p) = optmap (spl p) (List.map (fun (p,sub) -> (i,p),sub))
        in
        match p with
        | P_lit _
        | P_wild
          -> None
        | P_as (p',id) ->
           let i = id_to_string id in
           if i = var
           then raise (Reporting_basic.err_general l
                         ("Cannot split " ^ var ^ " on 'as' pattern"))
           else re (fun p -> P_as (p,id)) p'
        | P_typ (t,p') -> re (fun p -> P_typ (t,p)) p'
        | P_id id ->
           let i = id_to_string id in
           if i = var
           then Some (split i l annot)
           else None
        | P_app (id,ps) ->
           relist spl (fun ps -> P_app (id,ps)) ps
        | P_record (fps,flag) ->
           relist fpat (fun fps -> P_record (fps,flag)) fps
        | P_vector ps ->
           relist spl (fun ps -> P_vector ps) ps
        | P_vector_indexed ips ->
           relist ipat (fun ips -> P_vector_indexed ips) ips
        | P_vector_concat ps ->
           relist spl (fun ps -> P_vector_concat ps) ps
        | P_tup ps ->
           relist spl (fun ps -> P_tup ps) ps
        | P_list ps ->
           relist spl (fun ps -> P_list ps) ps
      in spl p
    in
    
    let map_pat (P_aux (_,(l,_)) as p) =
      match match_l l with
      | [] -> None
      | [(_,var)] -> split_pat var p
      | lvs -> raise (Reporting_basic.err_general l
                        ("Multiple variables to split on: " ^ String.concat ", " (List.map snd lvs)))
    in

    let check_single_pat (P_aux (_,(l,_)) as p) =
      match match_l l with
      | [] -> p
      | lvs ->
         let pvs = bindings_from_pat t_env p in
         let overlap = List.exists (fun (_,v) -> List.mem v pvs) lvs in
         let () =
           if overlap then
             Reporting_basic.print_err false true l "Monomorphisation"
               "Splitting a singleton pattern is not possible"
         in p
    in

    let rec map_exp ((E_aux (e,annot)) as ea) =
      let re e = E_aux (e,annot) in
      match e with
      | E_block es -> re (E_block (List.map map_exp es))
      | E_nondet es -> re (E_nondet (List.map map_exp es))
      | E_id _
      | E_lit _
      | E_sizeof _
      | E_internal_exp _
      | E_sizeof_internal _
      | E_internal_exp_user _
      | E_comment _
        -> ea
      | E_cast (t,e') -> re (E_cast (t, map_exp e'))
      | E_app (id,es) -> re (E_app (id,List.map map_exp es))
      | E_app_infix (e1,id,e2) -> re (E_app_infix (map_exp e1,id,map_exp e2))
      | E_tuple es -> re (E_tuple (List.map map_exp es))
      | E_if (e1,e2,e3) -> re (E_if (map_exp e1, map_exp e2, map_exp e3))
      | E_for (id,e1,e2,e3,ord,e4) -> re (E_for (id,map_exp e1,map_exp e2,map_exp e3,ord,map_exp e4))
      | E_vector es -> re (E_vector (List.map map_exp es))
      | E_vector_indexed (ies,ed) -> re (E_vector_indexed (List.map (fun (i,e) -> (i,map_exp e)) ies,
                                                           map_opt_default ed))
      | E_vector_access (e1,e2) -> re (E_vector_access (map_exp e1,map_exp e2))
      | E_vector_subrange (e1,e2,e3) -> re (E_vector_subrange (map_exp e1,map_exp e2,map_exp e3))
      | E_vector_update (e1,e2,e3) -> re (E_vector_update (map_exp e1,map_exp e2,map_exp e3))
      | E_vector_update_subrange (e1,e2,e3,e4) -> re (E_vector_update_subrange (map_exp e1,map_exp e2,map_exp e3,map_exp e4))
      | E_vector_append (e1,e2) -> re (E_vector_append (map_exp e1,map_exp e2))
      | E_list es -> re (E_list (List.map map_exp es))
      | E_cons (e1,e2) -> re (E_cons (map_exp e1,map_exp e2))
      | E_record fes -> re (E_record (map_fexps fes))
      | E_record_update (e,fes) -> re (E_record_update (map_exp e, map_fexps fes))
      | E_field (e,id) -> re (E_field (map_exp e,id))
      | E_case (e,cases) -> re (E_case (map_exp e, List.concat (List.map map_pexp cases)))
      | E_let (lb,e) -> re (E_let (map_letbind lb, map_exp e))
      | E_assign (le,e) -> re (E_assign (map_lexp le, map_exp e))
      | E_exit e -> re (E_exit (map_exp e))
      | E_return e -> re (E_return (map_exp e))
      | E_assert (e1,e2) -> re (E_assert (map_exp e1,map_exp e2))
      | E_internal_cast (ann,e) -> re (E_internal_cast (ann,map_exp e))
      | E_comment_struc e -> re (E_comment_struc e)
      | E_internal_let (le,e1,e2) -> re (E_internal_let (map_lexp le, map_exp e1, map_exp e2))
      | E_internal_plet (p,e1,e2) -> re (E_internal_plet (check_single_pat p, map_exp e1, map_exp e2))
      | E_internal_return e -> re (E_internal_return (map_exp e))
    and map_opt_default ((Def_val_aux (ed,annot)) as eda) =
      match ed with
      | Def_val_empty -> eda
      | Def_val_dec e -> Def_val_aux (Def_val_dec (map_exp e),annot)
    and map_fexps (FES_aux (FES_Fexps (fes,flag), annot)) =
      FES_aux (FES_Fexps (List.map map_fexp fes, flag), annot)
    and map_fexp (FE_aux (FE_Fexp (id,e), annot)) =
      FE_aux (FE_Fexp (id,map_exp e),annot)
    and map_pexp (Pat_aux (Pat_exp (p,e),l)) =
      match map_pat p with
      | None -> [Pat_aux (Pat_exp (p,map_exp e),l)]
      | Some patsubsts ->
         List.map (fun (pat',subst) ->
           let exp' = subst_exp subst e in
           Pat_aux (Pat_exp (pat', map_exp exp'),l))
           patsubsts
    and map_letbind (LB_aux (lb,annot)) =
      match lb with
      | LB_val_explicit (tysch,p,e) -> LB_aux (LB_val_explicit (tysch,check_single_pat p,map_exp e), annot)
      | LB_val_implicit (p,e) -> LB_aux (LB_val_implicit (check_single_pat p,map_exp e), annot)
    and map_lexp ((LEXP_aux (e,annot)) as le) =
      let re e = LEXP_aux (e,annot) in
      match e with
      | LEXP_id _
      | LEXP_cast _
        -> le
      | LEXP_memory (id,es) -> re (LEXP_memory (id,List.map map_exp es))
      | LEXP_tup les -> re (LEXP_tup (List.map map_lexp les))
      | LEXP_vector (le,e) -> re (LEXP_vector (map_lexp le, map_exp e))
      | LEXP_vector_range (le,e1,e2) -> re (LEXP_vector_range (map_lexp le, map_exp e1, map_exp e2))
      | LEXP_field (le,id) -> re (LEXP_field (map_lexp le, id))
    in

    let map_funcl (FCL_aux (FCL_Funcl (id,pat,exp),annot)) =
      match map_pat pat with
      | None -> [FCL_aux (FCL_Funcl (id, pat, map_exp exp), annot)]
      | Some patsubsts ->
         List.map (fun (pat',subst) ->
           let exp' = subst_exp subst exp in
           FCL_aux (FCL_Funcl (id, pat', map_exp exp'), annot))
           patsubsts
    in

    let map_fundef (FD_aux (FD_function (r,t,e,fcls),annot)) =
      FD_aux (FD_function (r,t,e,List.concat (List.map map_funcl fcls)),annot)
    in
    let map_scattered_def sd =
      match sd with
      | SD_aux (SD_scattered_funcl fcl, annot) ->
         List.map (fun fcl' -> SD_aux (SD_scattered_funcl fcl', annot)) (map_funcl fcl)
      | _ -> [sd]
    in
    let map_def d =
      match d with
      | DEF_kind _
      | DEF_type _
      | DEF_spec _
      | DEF_default _
      | DEF_reg_dec _
      | DEF_comm _
        -> [d]
      | DEF_fundef fd -> [DEF_fundef (map_fundef fd)]
      | DEF_val lb -> [DEF_val (map_letbind lb)]
      | DEF_scattered sd -> List.map (fun x -> DEF_scattered x) (map_scattered_def sd)

    in
    Defs (List.concat (List.map map_def defs))

  in map_locs splits defs
