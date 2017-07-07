open Parse_ast
open Ast
open Type_internal

let disable_const_propagation = ref false

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

(* We need to be able to substitute in source types to monomorphise
   datatype constructors *)

let rec nexp_to_snexp ne =
  let mkne n = Nexp_aux (n,Unknown) in
  match ne.nexp with
  | Nvar s -> mkne (Nexp_var (Kid_aux (Var s,Unknown)))
  | Nid (s,ne) -> mkne (Nexp_id (Id_aux (Id s,Unknown)))
  | Nconst i -> mkne (Nexp_constant (Big_int.int_of_big_int i))
  | Npos_inf
  | Nneg_inf ->
     raise (Reporting_basic.err_general Unknown ("Can't translate inf nexps back into source nexps"))
  | Nadd (n1,n2) -> mkne (Nexp_sum (nexp_to_snexp n1, nexp_to_snexp n2))
  | Nsub (n1,n2) -> mkne (Nexp_minus (nexp_to_snexp n1, nexp_to_snexp n2))
  | Nmult (n1,n2) -> mkne (Nexp_times (nexp_to_snexp n1, nexp_to_snexp n2))
  | N2n (ne,_) -> mkne (Nexp_exp (nexp_to_snexp ne))
  | Npow _ ->
     raise (Reporting_basic.err_general Unknown ("Can't translate pow nexps back into source nexps"))
  | Nneg ne -> mkne (Nexp_neg (nexp_to_snexp ne))
  | Ninexact ->
     raise (Reporting_basic.err_general Unknown ("Can't translate inexact nexps back into source nexps"))
  | Nuvar _ ->
     raise (Reporting_basic.err_general Unknown ("Can't translate uvar nexps back into source nexps"))


let subst_src_typ substs t =
  let rec s_snexp (Nexp_aux (ne,l) as nexp) =
    let re ne = Nexp_aux (ne,l) in
    match ne with
    | Nexp_var (Kid_aux (Var i,l)) ->
       (match Envmap.apply substs i with
       | Some (TA_nexp ne) -> nexp_to_snexp ne
       | _ -> re (Nexp_var (Kid_aux(Var i,Generated l))))
    | Nexp_id _
    | Nexp_constant _ -> nexp
    | Nexp_times (n1,n2) -> re (Nexp_times (s_snexp n1, s_snexp n2))
    | Nexp_sum (n1,n2)   -> re (Nexp_sum   (s_snexp n1, s_snexp n2))
    | Nexp_minus (n1,n2) -> re (Nexp_minus (s_snexp n1, s_snexp n2))
    | Nexp_exp ne -> re (Nexp_exp (s_snexp ne))
    | Nexp_neg ne -> re (Nexp_neg (s_snexp ne))
  in
  let rec s_styp ((Typ_aux (t,l)) as ty) =
    let re t = Typ_aux (t,l) in
    match t with
    | Typ_wild
    | Typ_id _
    | Typ_var _
      -> ty
    | Typ_fn (t1,t2,e) -> re (Typ_fn (s_styp t1, s_styp t2,e))
    | Typ_tup ts -> re (Typ_tup (List.map s_styp ts))
    | Typ_app (id,tas) -> re (Typ_app (id,List.map s_starg tas))
  and s_starg (Typ_arg_aux (ta,l) as targ) =
    match ta with
    | Typ_arg_nexp ne -> Typ_arg_aux (Typ_arg_nexp (s_snexp ne),l)
    | Typ_arg_typ t -> Typ_arg_aux (Typ_arg_typ (s_styp t),l)
    | Typ_arg_order _
    | Typ_arg_effect _ -> targ
  in s_styp t




(* Based on current type checker's behaviour *)
let pat_id_is_variable t_env id =
  match Envmap.apply t_env id with
  | Some (Base(_,Constructor _,_,_,_,_))
  | Some (Base(_,Enum _,_,_,_,_))
    -> false
  | _ -> true

let rec list_extract f = function
  | [] -> None
  | h::t -> match f h with None -> list_extract f t | Some v -> Some v

let rec cross = function
  | [] -> failwith "cross"
  | [(x,l)] -> List.map (fun y -> [(x,y)]) l
  | (x,l)::t -> 
     let t' = cross t in
     List.concat (List.map (fun y -> List.map (fun l' -> (x,y)::l') t') l)

(* Given a type for a constructor, work out which refinements we ought to produce *)
(* TODO collision avoidance *)
let split_src_type i ty (TypQ_aux (q,ql)) =
  let rec size_nvars_nexp (Nexp_aux (ne,_)) =
    match ne with
    | Nexp_var (Kid_aux (Var v,_)) -> [v]
    | Nexp_id _
    | Nexp_constant _
      -> []
    | Nexp_times (n1,n2)
    | Nexp_sum (n1,n2)
    | Nexp_minus (n1,n2)
      -> size_nvars_nexp n1 @ size_nvars_nexp n2
    | Nexp_exp n
    | Nexp_neg n
      -> size_nvars_nexp n
  in
  let rec size_nvars_ty (Typ_aux (ty,l)) =
    match ty with
    | Typ_wild
    | Typ_id _
    | Typ_var _
      -> []
    | Typ_fn _ ->
       raise (Reporting_basic.err_general l ("Function type in constructor " ^ i))
    | Typ_tup ts -> List.concat (List.map size_nvars_ty ts)
    | Typ_app (Id_aux (Id "vector",_),
               [_;Typ_arg_aux (Typ_arg_nexp sz,_);
                _;Typ_arg_aux (Typ_arg_typ (Typ_aux (Typ_id (Id_aux (Id "bit",_)),_)),_)]) ->
       size_nvars_nexp sz
    | Typ_app (_, tas) ->
       []  (* We only support sizes for bitvectors mentioned explicitly, not any buried
              inside another type *)
  in
  let nvars = List.sort_uniq (String.compare) (size_nvars_ty ty) in
  match nvars with
  | [] -> None
  | sample::__ ->
     (* Only check for constraints if we found a size to constrain *)
     let qs =
       match q with
       | TypQ_no_forall -> 
          raise (Reporting_basic.err_general ql
                   ("No set constraint for variable " ^ sample ^ " in constructor " ^ i))
       | TypQ_tq qs -> qs
     in
     let find_set nvar =
       match list_extract (function
       | QI_aux (QI_const (NC_aux (NC_nat_set_bounded (Kid_aux (Var nvar',_),vals),_)),_)
         -> if nvar = nvar' then Some vals else None
       | _ -> None) qs with
       | None ->
          raise (Reporting_basic.err_general ql
                   ("No set constraint for variable " ^ nvar ^ " in constructor " ^ i))
       | Some vals -> (nvar,vals)
     in
     let nvar_sets = List.map find_set nvars in
     let total_variants = List.fold_left ( * ) 1 (List.map (fun (_,l) -> List.length l) nvar_sets) in
     let limit = 8 in
     let () = if total_variants > limit then
         raise (Reporting_basic.err_general ql
                  (string_of_int total_variants ^ "variants for constructor " ^ i ^
                     "bigger than limit " ^ string_of_int limit)) else ()
     in
     let variants = cross nvar_sets in
     let name l = String.concat "_" (i::(List.map (fun (v,i) -> v ^ string_of_int i) l)) in
     Some (List.map (fun l -> (l, name l)) variants)

(* TODO: maybe fold this into subst_src_typ? *)
let inst_src_type insts ty =
  let insts = List.map (fun (v,i) -> (v,TA_nexp {nexp=Nconst (Big_int.big_int_of_int i); imp_param=false})) insts in
  let subst = Envmap.from_list insts in
  subst_src_typ subst ty

let reduce_nexp subst ne =
  let ne = subst_n_with_env subst ne in
  let rec eval ne =
    match ne.nexp with
    | Nconst i -> i
    | Nadd (n1,n2) -> Big_int.add_big_int (eval n1) (eval n2)
    | Nsub (n1,n2) -> Big_int.sub_big_int (eval n1) (eval n2)
    | Nmult (n1,n2) -> Big_int.mult_big_int (eval n1) (eval n2)
    | N2n (n,_) -> Big_int.power_int_positive_big_int 2 (eval n)
    | Npow (n,i) -> Big_int.power_big_int_positive_int (eval n) i
    | Nneg n -> Big_int.minus_big_int (eval n)
    | _ ->
       raise (Reporting_basic.err_general Unknown ("Couldn't turn nexp " ^
                                                      n_to_string ne ^ " into concrete value"))
  in Big_int.int_of_big_int (eval ne)

(* Check to see if we need to monomorphise a use of a constructor.  Currently
   assumes that bitvector sizes are always given as a variable; don't yet handle
   more general cases (e.g., 8 * var) *)

let refine_constructor refinements i substs arg t =
  let rec derive_vars t (E_aux (e,(l,tannot)) as exp) =
    match t.t with
    | Tapp ("vector", [_;TA_nexp {nexp = Nvar v};_;TA_typ {t=Tid "bit"}]) ->
       (match tannot with
       | Base ((_,{t=Tapp ("vector", [_;TA_nexp ne;_;TA_typ {t=Tid "bit"}])}),_,_,_,_,_) ->
          [(v,reduce_nexp substs ne)]
       | _ -> [])
    | Tvar _
    | Tid _
    | Tfn _
    | Tapp _
    | Tuvar _
      -> []
    | Tabbrev (_,t)
    | Toptions (t,_)
      -> derive_vars t exp
    | Ttup ts ->
       match e with
       | E_tuple es -> List.concat (List.map2 derive_vars ts es)
       | _ -> [] (* TODO? *)
  in
  try
    let irefinements = List.assoc i refinements in
    let vars = List.sort_uniq (fun x y -> String.compare (fst x) (fst y)) (derive_vars t arg) in
    Some (List.assoc vars irefinements)
  with Not_found -> None


(* Substitute found nexps for variables in an expression, and rename constructors to reflect
   specialisation *)

let nexp_subst_fns t_env substs refinements =
  let s_t t = typ_subst substs true t in
(*  let s_typschm (TypSchm_aux (TypSchm_ts (q,t),l)) = TypSchm_aux (TypSchm_ts (q,s_t t),l) in
   hopefully don't need this anyway *)
  let s_typschm tsh = tsh in
  let s_tannot = function
    | Base ((params,t),tag,ranges,effl,effc,bounds) ->
       (* TODO: do other fields need mapped? *)
       Base ((params,s_t t),tag,ranges,effl,effc,bounds)
    | tannot -> tannot
  in
  let rec s_pat (P_aux (p,(l,annot))) =
    let re p = P_aux (p,(l,s_tannot annot)) in
    match p with
    | P_lit _ | P_wild | P_id _ -> re p
    | P_as (p',id) -> re (P_as (s_pat p', id))
    | P_typ (ty,p') -> re (P_typ (ty,s_pat p'))
    | P_app (id,ps) -> re (P_app (id, List.map s_pat ps))
    | P_record (fps,flag) -> re (P_record (List.map s_fpat fps, flag))
    | P_vector ps -> re (P_vector (List.map s_pat ps))
    | P_vector_indexed ips -> re (P_vector_indexed (List.map (fun (i,p) -> (i,s_pat p)) ips))
    | P_vector_concat ps -> re (P_vector_concat (List.map s_pat ps))
    | P_tup ps -> re (P_tup (List.map s_pat ps))
    | P_list ps -> re (P_list (List.map s_pat ps))
  and s_fpat (FP_aux (FP_Fpat (id, p), (l,annot))) =
    FP_aux (FP_Fpat (id, s_pat p), (l,s_tannot annot))
  in
  let rec s_exp (E_aux (e,(l,annot))) =
    let re e = E_aux (e,(l,s_tannot annot)) in
      match e with
      | E_block es -> re (E_block (List.map s_exp es))
      | E_nondet es -> re (E_nondet (List.map s_exp es))
      | E_id _
      | E_lit _
      | E_comment _ -> re e
      | E_sizeof ne -> re (E_sizeof ne) (* TODO: do this need done?  does it appear in type checked code? *)
      | E_internal_exp (l,annot) -> re (E_internal_exp (l, s_tannot annot))
      | E_sizeof_internal (l,annot) -> re (E_sizeof_internal (l, s_tannot annot))
      | E_internal_exp_user ((l1,annot1),(l2,annot2)) ->
         re (E_internal_exp_user ((l1, s_tannot annot1),(l2, s_tannot annot2)))
      | E_cast (t,e') -> re (E_cast (t, s_exp e'))
      | E_app (id,es) ->
         let es' = List.map s_exp es in
         let arg =
           match es' with
           | [] -> E_aux (E_lit (L_aux (L_unit,Unknown)),(Unknown,simple_annot unit_t))
           | [e] -> e
           | _ -> E_aux (E_tuple es',(Unknown,NoTyp))
         in
         let i = id_to_string id in
         let id' = 
           match Envmap.apply t_env i with
           | Some (Base((t_params,{t=Tfn(inty,outty,_,_)}),Constructor _,_,_,_,_)) ->
              (match refine_constructor refinements i substs arg inty with
              | None -> id
              | Some i -> Id_aux (Id i,Generated l))
           | _ -> id
         in re (E_app (id',es'))
      | E_app_infix (e1,id,e2) -> re (E_app_infix (s_exp e1,id,s_exp e2))
      | E_tuple es -> re (E_tuple (List.map s_exp es))
      | E_if (e1,e2,e3) -> re (E_if (s_exp e1, s_exp e2, s_exp e3))
      | E_for (id,e1,e2,e3,ord,e4) -> re (E_for (id,s_exp e1,s_exp e2,s_exp e3,ord,s_exp e4))
      | E_vector es -> re (E_vector (List.map s_exp es))
      | E_vector_indexed (ies,ed) -> re (E_vector_indexed (List.map (fun (i,e) -> (i,s_exp e)) ies,
                                                           s_opt_default ed))
      | E_vector_access (e1,e2) -> re (E_vector_access (s_exp e1,s_exp e2))
      | E_vector_subrange (e1,e2,e3) -> re (E_vector_subrange (s_exp e1,s_exp e2,s_exp e3))
      | E_vector_update (e1,e2,e3) -> re (E_vector_update (s_exp e1,s_exp e2,s_exp e3))
      | E_vector_update_subrange (e1,e2,e3,e4) -> re (E_vector_update_subrange (s_exp e1,s_exp e2,s_exp e3,s_exp e4))
      | E_vector_append (e1,e2) -> re (E_vector_append (s_exp e1,s_exp e2))
      | E_list es -> re (E_list (List.map s_exp es))
      | E_cons (e1,e2) -> re (E_cons (s_exp e1,s_exp e2))
      | E_record fes -> re (E_record (s_fexps fes))
      | E_record_update (e,fes) -> re (E_record_update (s_exp e, s_fexps fes))
      | E_field (e,id) -> re (E_field (s_exp e,id))
      | E_case (e,cases) -> re (E_case (s_exp e, List.map s_pexp cases))
      | E_let (lb,e) -> re (E_let (s_letbind lb, s_exp e))
      | E_assign (le,e) -> re (E_assign (s_lexp le, s_exp e))
      | E_exit e -> re (E_exit (s_exp e))
      | E_return e -> re (E_return (s_exp e))
      | E_assert (e1,e2) -> re (E_assert (s_exp e1,s_exp e2))
      | E_internal_cast ((l,ann),e) -> re (E_internal_cast ((l,s_tannot ann),s_exp e))
      | E_comment_struc e -> re (E_comment_struc e)
      | E_internal_let (le,e1,e2) -> re (E_internal_let (s_lexp le, s_exp e1, s_exp e2))
      | E_internal_plet (p,e1,e2) -> re (E_internal_plet (s_pat p, s_exp e1, s_exp e2))
      | E_internal_return e -> re (E_internal_return (s_exp e))
    and s_opt_default (Def_val_aux (ed,(l,annot))) =
      match ed with
      | Def_val_empty -> Def_val_aux (Def_val_empty,(l,s_tannot annot))
      | Def_val_dec e -> Def_val_aux (Def_val_dec (s_exp e),(l,s_tannot annot))
    and s_fexps (FES_aux (FES_Fexps (fes,flag), (l,annot))) =
      FES_aux (FES_Fexps (List.map s_fexp fes, flag), (l,s_tannot annot))
    and s_fexp (FE_aux (FE_Fexp (id,e), (l,annot))) =
      FE_aux (FE_Fexp (id,s_exp e),(l,s_tannot annot))
    and s_pexp (Pat_aux (Pat_exp (p,e),(l,annot))) =
      Pat_aux (Pat_exp (s_pat p, s_exp e),(l,s_tannot annot))
    and s_letbind (LB_aux (lb,(l,annot))) =
      match lb with
      | LB_val_explicit (tysch,p,e) ->
         LB_aux (LB_val_explicit (s_typschm tysch,s_pat p,s_exp e), (l,s_tannot annot))
      | LB_val_implicit (p,e) -> LB_aux (LB_val_implicit (s_pat p,s_exp e), (l,s_tannot annot))
    and s_lexp (LEXP_aux (e,(l,annot))) =
      let re e = LEXP_aux (e,(l,s_tannot annot)) in
      match e with
      | LEXP_id _
      | LEXP_cast _
        -> re e
      | LEXP_memory (id,es) -> re (LEXP_memory (id,List.map s_exp es))
      | LEXP_tup les -> re (LEXP_tup (List.map s_lexp les))
      | LEXP_vector (le,e) -> re (LEXP_vector (s_lexp le, s_exp e))
      | LEXP_vector_range (le,e1,e2) -> re (LEXP_vector_range (s_lexp le, s_exp e1, s_exp e2))
      | LEXP_field (le,id) -> re (LEXP_field (s_lexp le, id))
  in (s_pat,s_exp)
let nexp_subst_pat t_env substs refinements = fst (nexp_subst_fns t_env substs refinements)
let nexp_subst_exp t_env substs refinements = snd (nexp_subst_fns t_env substs refinements)

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

(* We may need to split up a pattern match if (1) we've been told to case split
   on a variable by the user, or (2) we monomorphised a constructor that's used
   in the pattern. *)
type split =
  | NoSplit
  | VarSplit of (tannot pat * (string * tannot Ast.exp)) list
  | ConstrSplit of (tannot pat * t_arg Envmap.t) list

let split_defs splits (Type_check.Env (d_env,t_env,b_env,tp_env)) defs =
  let split_constructors (Defs defs) =
    let sc_type_union q (Tu_aux (tu,l) as tua) =
      match tu with
      | Tu_id id -> [],[tua]
      | Tu_ty_id (ty,id) ->
         let i = id_to_string id in
         (match split_src_type i ty q with
         | None -> ([],[Tu_aux (Tu_ty_id (ty,id),l)])
         | Some variants ->
            ([(i,variants)],
             List.map (fun (insts, i') -> Tu_aux (Tu_ty_id (inst_src_type insts ty,Id_aux (Id i',Generated l)),Generated l)) variants))
    in
    let sc_type_def ((TD_aux (tda,annot)) as td) =
      match tda with
      | TD_variant (id,nscm,quant,tus,flag) ->
         let (refinements, tus') = List.split (List.map (sc_type_union quant) tus) in
         (List.concat refinements, TD_aux (TD_variant (id,nscm,quant,List.concat tus',flag),annot))
      | _ -> ([],td)
    in
    let sc_def d =
      match d with
    | DEF_type td -> let (refinements,td') = sc_type_def td in (refinements, DEF_type td')
    | _ -> ([], d)
    in
    let (refinements, defs') = List.split (List.map sc_def defs)
    in (List.concat refinements, Defs defs')
  in

  let (refinements, defs') = split_constructors defs in

  (* Attempt simple pattern matches *)
  let can_match (E_aux (e,(l,annot))) cases =
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
    (* TODO: could generalise Lit matching *)
    | E_lit (L_aux ((L_zero | L_one | L_true | L_false) as bit, _)) ->
       let rec findpat cases =
         match cases with
         | [] -> (Reporting_basic.print_err false true l "Monomorphisation"
                    ("Failed to find a case for bit"); None)
         | [Pat_aux (Pat_exp (P_aux (P_wild,_),exp),_)] -> Some exp
         | (Pat_aux (Pat_exp (P_aux (P_lit (L_aux (lit, _)),_),exp),_))::tl ->
            (match bit,lit with
            | (L_zero | L_false), (L_zero | L_false) -> Some exp
            | (L_one  | L_true ), (L_one  | L_true ) -> Some exp
            | _ -> findpat tl)
         | (Pat_aux (Pat_exp (P_aux (_,(l',_)),_),_))::_ ->
            (Reporting_basic.print_err false true l' "Monomorphisation"
               "Unexpected kind of pattern for bit"; None)
       in findpat cases
    | _ -> None
  in

  (* Similarly, simple conditionals *)
  (* TODO: doublecheck *)
  let lit_eq (L_aux (l1,_)) (L_aux (l2,_)) =
    match l1,l2 with
    | (L_zero|L_false), (L_zero|L_false)
    | (L_one |L_true ), (L_one |L_true)
      -> Some true
    | L_undef, _ | _, L_undef -> None
    | _ -> Some (l1 = l2)
  in

  (* TODO: any useful type information revealed? (probably not) *)
  let try_app_infix (l,ann) (E_aux (e1,ann1)) id (E_aux (e2,ann2)) =
    let new_l = Generated l in
    match e1, id, e2 with
    | E_lit l1, ("=="|"!="), E_lit l2 ->
       let lit b = if b then L_true else L_false in
       let lit b = lit (if id = "==" then b else not b) in
       (match lit_eq l1 l2 with
       | Some b -> Some (E_aux (E_lit (L_aux (lit b,new_l)), (l,ann)))
       | None -> None)
    | _ -> None
  in

  (* Extract nvar substitution by comparing two types *)
  let build_nexp_subst l t1 t2 =
    let rec from_types t1 t2 =
      let t1 = match t1.t with Tabbrev(_,t) -> t | _ -> t1 in
      let t2 = match t2.t with Tabbrev(_,t) -> t | _ -> t2 in
      if t1 = t2 then [] else
        match t1.t,t2.t with
        | Tapp (s1,args1), Tapp (s2,args2) ->
           if s1 = s2 then
             List.concat (List.map2 from_args args1 args2)
           else (Reporting_basic.print_err false true l "Monomorphisation"
                   "Unexpected type mismatch"; [])
        | Ttup ts1, Ttup ts2 ->
           if List.length ts1 = List.length ts2 then
             List.concat (List.map2 from_types ts1 ts2)
           else (Reporting_basic.print_err false true l "Monomorphisation"
                   "Unexpected type mismatch"; [])
        | _ -> []
    and from_args arg1 arg2 =
    match arg1,arg2 with
    | TA_typ t1, TA_typ t2 -> from_types t1 t2
    | TA_nexp n1, TA_nexp n2 -> from_nexps n1 n2
    | _ -> []
    and from_nexps n1 n2 =
      match n1.nexp, n2.nexp with
      | Nvar s, Nvar s' when s = s' -> []
      | Nvar s, _ -> [(s,n2)]
      | Nadd (n3,n4), Nadd (n5,n6)
      | Nsub (n3,n4), Nsub (n5,n6)
      | Nmult (n3,n4), Nmult (n5,n6)
        -> from_nexps n3 n5 @ from_nexps n4 n6
      | N2n (n3,p1), N2n (n4,p2) when p1 = p2 -> from_nexps n3 n4
      | Npow (n3,p1), Npow (n4,p2) when p1 = p2 -> from_nexps n3 n4
      | Nneg n3, Nneg n4 -> from_nexps n3 n4
      | _ -> []
    in match t1,t2 with
    | Base ((_,t1),_,_,_,_,_),Base ((_,t2),_,_,_,_,_) -> from_types t1 t2
    | _ -> []
  in

  let nexp_substs = ref [] in

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
    | E_app_infix (e1,id,e2) ->
       let e1',e2' = const_prop_exp substs e1,const_prop_exp substs e2 in
       (match try_app_infix (l,annot) e1' (id_to_string id) e2' with
       | Some exp -> exp
       | None -> re (E_app_infix (e1',id,e2')))
    | E_tuple es -> re (E_tuple (List.map (const_prop_exp substs) es))
    | E_if (e1,e2,e3) ->
       let e1' = const_prop_exp substs e1 in
       let e2',e3' = const_prop_exp substs e2, const_prop_exp substs e3 in
       (match e1' with
       | E_aux (E_lit (L_aux ((L_true|L_false) as lit ,_)),_) ->
          let e' = match lit with L_true -> e2' | _ -> e3' in
          (match e' with E_aux (_,(_,annot')) ->
            nexp_substs := build_nexp_subst l annot annot' @ !nexp_substs;
            e')
       | _ -> re (E_if (e1',e2',e3')))
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
       (match can_match e' cases with
       | None -> re (E_case (e', List.map (const_prop_pexp substs) cases))
       | Some (E_aux (_,(_,annot')) as exp) ->
          nexp_substs := build_nexp_subst l annot annot' @ !nexp_substs;
          const_prop_exp substs exp)
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
      let () = nexp_substs := [] in
      let exp' = const_prop_exp substs exp in
      (* Substitute what we've learned about nvars into the term *)
      let nsubsts = Envmap.from_list (List.map (fun (id,ne) -> (id,TA_nexp ne)) !nexp_substs) in
      let () = nexp_substs := [] in
      nexp_subst_exp t_env nsubsts refinements exp'
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
          | None ->
             if i = "bit" then
               List.map (fun b ->
                 P_aux (P_lit (L_aux (b,new_l)),(l,tannot)),
                 (id,E_aux (E_lit (L_aux (b,new_l)),(new_l, tannot))))
                 [L_zero; L_one]
             else cannot ())
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

    let map_pat_by_loc (P_aux (p,(l,_)) as pat) =
      match match_l l with
      | [] -> None
      | [(_,var)] -> split_pat var pat
      | lvs -> raise (Reporting_basic.err_general l
                        ("Multiple variables to split on: " ^ String.concat ", " (List.map snd lvs)))
    in
    let map_pat (P_aux (p,(l,tannot)) as pat) =
      match map_pat_by_loc pat with
      | Some l -> VarSplit l
      | None ->
         match p with
         | P_app (id,args) ->
            (try
              let i = id_to_string id in
              let variants = List.assoc i refinements in
              let constr_tannot =
                match Envmap.apply t_env i with
                | Some (Base ((_,{t=Tfn(_,outt,_,_)}),_,_,_,_,_)) -> simple_annot outt
                | _ -> raise (Reporting_basic.err_general l
                                ("Constructor missing from environment: " ^ i))
              in
              let varmap = build_nexp_subst l constr_tannot tannot in
              let map_inst (insts,i') =
                let insts = List.map (fun (v,i) ->
                  ((match List.assoc v varmap with
                  | {nexp=Nvar s} -> s
                  | _ -> raise (Reporting_basic.err_general l
                                  ("Constructor parameter not a variable: " ^ v))),
                   TA_nexp {nexp=Nconst (Big_int.big_int_of_int i);imp_param=false}))
                  insts in
                P_aux (P_app (Id_aux (Id i',Generated l),args),(Generated l,tannot)),
                Envmap.from_list insts
              in
              ConstrSplit (List.map map_inst variants)
            with Not_found -> NoSplit)
         | _ -> NoSplit
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
      | NoSplit -> [Pat_aux (Pat_exp (p,map_exp e),l)]
      | VarSplit patsubsts ->
         List.map (fun (pat',subst) ->
           let exp' = subst_exp subst e in
           Pat_aux (Pat_exp (pat', map_exp exp'),l))
           patsubsts
      | ConstrSplit patnsubsts ->
         List.map (fun (pat',nsubst) ->
           (* Leave refinements to later *)
           let pat' = nexp_subst_pat t_env nsubst [] pat' in
           let exp' = nexp_subst_exp t_env nsubst [] e in
           Pat_aux (Pat_exp (pat', map_exp exp'),l)
         ) patnsubsts
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
      | NoSplit -> [FCL_aux (FCL_Funcl (id, pat, map_exp exp), annot)]
      | VarSplit patsubsts ->
         List.map (fun (pat',subst) ->
           let exp' = subst_exp subst exp in
           FCL_aux (FCL_Funcl (id, pat', map_exp exp'), annot))
           patsubsts
      | ConstrSplit patnsubsts ->
         List.map (fun (pat',nsubst) ->
           (* Leave refinements to later *)
           let pat' = nexp_subst_pat t_env nsubst [] pat' in
           let exp' = nexp_subst_exp t_env nsubst [] exp in
           FCL_aux (FCL_Funcl (id, pat', map_exp exp'), annot)
         ) patnsubsts
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
  in
  map_locs splits defs'
