open Parse_ast
open Ast
open Ast_util
open Type_check

let size_set_limit = 8
let vector_split_limit = 4

let optmap v f =
  match v with
  | None -> None
  | Some v -> Some (f v)

let env_typ_expected l : tannot -> Env.t * typ = function
  | None -> raise (Reporting_basic.err_unreachable l "Missing type environment")
  | Some (env,ty,_) -> env,ty

module KSubst = Map.Make(Kid)
module ISubst = Map.Make(Id)
let ksubst_from_list = List.fold_left (fun s (v,i) -> KSubst.add v i s) KSubst.empty
let isubst_from_list = List.fold_left (fun s (v,i) -> ISubst.add v i s) ISubst.empty
(* union was introduced in 4.03.0, a bit too recently *)
let isubst_union s1 s2 =
  ISubst.merge (fun _ x y -> match x,y with
  |  _, (Some x) -> Some x
  |  (Some x), _ -> Some x
  |  _,  _ -> None) s1 s2

let subst_nexp substs nexp =
  let rec s_snexp substs (Nexp_aux (ne,l) as nexp) =
    let re ne = Nexp_aux (ne,l) in
    let s_snexp = s_snexp substs in
    match ne with
    | Nexp_var (Kid_aux (_,l) as kid) ->
       (try KSubst.find kid substs
       with Not_found -> nexp)
    | Nexp_id _
    | Nexp_constant _ -> nexp
    | Nexp_times (n1,n2) -> re (Nexp_times (s_snexp n1, s_snexp n2))
    | Nexp_sum (n1,n2)   -> re (Nexp_sum   (s_snexp n1, s_snexp n2))
    | Nexp_minus (n1,n2) -> re (Nexp_minus (s_snexp n1, s_snexp n2))
    | Nexp_exp ne -> re (Nexp_exp (s_snexp ne))
    | Nexp_neg ne -> re (Nexp_neg (s_snexp ne))
  in s_snexp substs nexp

let rec subst_nc substs (NC_aux (nc,l) as n_constraint) =
  let snexp nexp = subst_nexp substs nexp in
  let snc nc = subst_nc substs nc in
  let re nc = NC_aux (nc,l) in
  match nc with
  | NC_fixed (n1,n2) -> re (NC_fixed (snexp n1, snexp n2))
  | NC_bounded_ge (n1,n2) -> re (NC_bounded_ge (snexp n1, snexp n2))
  | NC_bounded_le (n1,n2) -> re (NC_bounded_le (snexp n1, snexp n2))
  | NC_not_equal (n1,n2) -> re (NC_not_equal (snexp n1, snexp n2))
  | NC_nat_set_bounded (kid,is) ->
     begin
       match KSubst.find kid substs with
       | Nexp_aux (Nexp_constant i,_) ->
          if List.mem i is then re NC_true else re NC_false
       | nexp -> 
          raise (Reporting_basic.err_general l
                   ("Unable to substitute " ^ string_of_nexp nexp ^
                       " into set constraint " ^ string_of_n_constraint n_constraint))
       | exception Not_found -> n_constraint
     end
  | NC_or (nc1,nc2) -> re (NC_or (snc nc1, snc nc2))
  | NC_and (nc1,nc2) -> re (NC_and (snc nc1, snc nc2))
  | NC_true
  | NC_false
      -> n_constraint



let subst_src_typ substs t =
  let rec s_styp substs ((Typ_aux (t,l)) as ty) =
    let re t = Typ_aux (t,l) in
    match t with
    | Typ_wild
    | Typ_id _
    | Typ_var _
      -> ty
    | Typ_fn (t1,t2,e) -> re (Typ_fn (s_styp substs t1, s_styp substs t2,e))
    | Typ_tup ts -> re (Typ_tup (List.map (s_styp substs) ts))
    | Typ_app (id,tas) -> re (Typ_app (id,List.map (s_starg substs) tas))
    | Typ_exist (kids,nc,t) ->
       let substs = List.fold_left (fun sub v -> KSubst.remove v sub) substs kids in
       re (Typ_exist (kids,nc,s_styp substs t))
  and s_starg substs (Typ_arg_aux (ta,l) as targ) =
    match ta with
    | Typ_arg_nexp ne -> Typ_arg_aux (Typ_arg_nexp (subst_nexp substs ne),l)
    | Typ_arg_typ t -> Typ_arg_aux (Typ_arg_typ (s_styp substs t),l)
    | Typ_arg_order _ -> targ
  in s_styp substs t

let make_vector_lit sz i =
  let f j = if (i lsr (sz-j-1)) mod 2 = 0 then '0' else '1' in
  let s = String.init sz f in
  L_aux (L_bin s,Generated Unknown)

let tabulate f n =
  let rec aux acc n =
    let acc' = f n::acc in
    if n = 0 then acc' else aux acc' (n-1)
  in if n = 0 then [] else aux [] (n-1)

let make_vectors sz =
  tabulate (make_vector_lit sz) (1 lsl sz)
  
  


let pat_id_is_variable env id =
  match Env.lookup_id id env with
  (* Unbound is returned for both variables and constructors which take
     arguments, but the latter only don't appear in a P_id *)
  | Unbound
  (* Shadowing of immutable locals is allowed; mutable locals and registers
     are rejected by the type checker, so don't matter *)
  | Local _
  | Register _
    -> true
  | Enum _
  | Union _
    -> false

let rec is_value (E_aux (e,(l,annot))) =
  let is_constructor id =
    match annot with
    | None -> 
       (Reporting_basic.print_err false true l "Monomorphisation"
          ("Missing type information for identifier " ^ string_of_id id);
        false) (* Be conservative if we have no info *)
    | Some (env,_,_) ->
       Env.is_union_constructor id env ||
         (match Env.lookup_id id env with
         | Enum _ | Union _ -> true 
         | Unbound | Local _ | Register _ -> false)
  in
  match e with
  | E_id id -> is_constructor id
  | E_lit _ -> true
  | E_tuple es -> List.for_all is_value es
  | E_app (id,es) -> is_constructor id && List.for_all is_value es
(* TODO: more? *)
  | _ -> false

let is_pure (Effect_opt_aux (e,_)) =
  match e with
  | Effect_opt_pure -> true
  | Effect_opt_effect (Effect_aux (Effect_set [],_)) -> true
  | _ -> false

let rec list_extract f = function
  | [] -> None
  | h::t -> match f h with None -> list_extract f t | Some v -> Some v

let rec cross = function
  | [] -> failwith "cross"
  | [(x,l)] -> List.map (fun y -> [(x,y)]) l
  | (x,l)::t -> 
     let t' = cross t in
     List.concat (List.map (fun y -> List.map (fun l' -> (x,y)::l') t') l)

let rec cross' = function
  | [] -> [[]]
  | (h::t) ->
     let t' = cross' t in
     List.concat (List.map (fun x -> List.map (List.cons x) t') h)

let rec cross'' = function
  | [] -> [[]]
  | (k,None)::t -> List.map (List.cons (k,None)) (cross'' t)
  | (k,Some h)::t ->
     let t' = cross'' t in
     List.concat (List.map (fun x -> List.map (List.cons (k,Some x)) t') h)

let kidset_bigunion = function
  | [] -> KidSet.empty
  | h::t -> List.fold_left KidSet.union h t

(* TODO: deal with non-set constraints, intersections, etc somehow *)
let extract_set_nc var (NC_aux (_,l) as nc) =
  let rec aux (NC_aux (nc,l)) =
    let re nc = NC_aux (nc,l) in
    match nc with
    | NC_nat_set_bounded (id,is) when Kid.compare id var = 0 -> Some (is,re NC_true)
    | NC_and (nc1,nc2) ->
       (match aux nc1, aux nc2 with
       | None, None -> None
       | None, Some (is,nc2') -> Some (is, re (NC_and (nc1,nc2')))
       | Some (is,nc1'), None -> Some (is, re (NC_and (nc1',nc2)))
       | Some _, Some _ ->
          raise (Reporting_basic.err_general l ("Multiple set constraints for " ^ string_of_kid var)))
    | _ -> None
  in match aux nc with
  | Some is -> is
  | None ->
     raise (Reporting_basic.err_general l ("No set constraint for " ^ string_of_kid var))

let rec peel = function
  | [], l -> ([], l)
  | h1::t1, h2::t2 -> let (l1,l2) = peel (t1, t2) in ((h1,h2)::l1,l2)
  | _,_ -> assert false

let rec split_insts = function
  | [] -> [],[]
  | (k,None)::t -> let l1,l2 = split_insts t in l1,k::l2
  | (k,Some v)::t -> let l1,l2 = split_insts t in (k,v)::l1,l2

let apply_kid_insts kid_insts t =
  let kid_insts, kids' = split_insts kid_insts in
  let kid_insts = List.map (fun (v,i) -> (v,Nexp_aux (Nexp_constant i,Generated Unknown))) kid_insts in
  let subst = ksubst_from_list kid_insts in
  kids', subst_src_typ subst t

let rec inst_src_type insts (Typ_aux (ty,l) as typ) =
  match ty with
  | Typ_wild
  | Typ_id _
  | Typ_var _
    -> insts,typ
  | Typ_fn _ ->
     raise (Reporting_basic.err_general l "Function type in constructor")
  | Typ_tup ts ->
     let insts,ts = 
       List.fold_right
         (fun typ (insts,ts) -> let insts,typ = inst_src_type insts typ in insts,typ::ts)
         ts (insts,[])
     in insts, Typ_aux (Typ_tup ts,l)
  | Typ_app (id,args) ->
     let insts,ts = 
       List.fold_right
         (fun arg (insts,args) -> let insts,arg = inst_src_typ_arg insts arg in insts,arg::args)
         args (insts,[])
     in insts, Typ_aux (Typ_app (id,ts),l)
  | Typ_exist (kids, nc, t) ->
     let kid_insts, insts' = peel (kids,insts) in
     let kids', t' = apply_kid_insts kid_insts t in
     (* TODO: subst in nc *)
     match kids' with
     | [] -> insts', t'
     | _ -> insts', Typ_aux (Typ_exist (kids', nc, t'), l)
and inst_src_typ_arg insts (Typ_arg_aux (ta,l) as tyarg) =
  match ta with
  | Typ_arg_nexp _
  | Typ_arg_order _
      -> insts, tyarg
  | Typ_arg_typ typ ->
     let insts', typ' = inst_src_type insts typ in
     insts', Typ_arg_aux (Typ_arg_typ typ',l)

let rec contains_exist (Typ_aux (ty,_)) =
  match ty with
  | Typ_wild
  | Typ_id _
  | Typ_var _
    -> false
  | Typ_fn (t1,t2,_) -> contains_exist t1 || contains_exist t2
  | Typ_tup ts -> List.exists contains_exist ts
  | Typ_app (_,args) -> List.exists contains_exist_arg args
  | Typ_exist _ -> true
and contains_exist_arg (Typ_arg_aux (arg,_)) =
  match arg with
  | Typ_arg_nexp _
  | Typ_arg_order _
      -> false
  | Typ_arg_typ typ -> contains_exist typ

(* Given a type for a constructor, work out which refinements we ought to produce *)
(* TODO collision avoidance *)
let split_src_type id ty (TypQ_aux (q,ql)) =
  let i = string_of_id id in
  let rec size_nvars_nexp (Nexp_aux (ne,_)) =
    match ne with
    | Nexp_var v -> [v]
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
  (* This was originally written for the general case, but I cut it down to the
     more manageable prenex-form below *)
  let rec size_nvars_ty (Typ_aux (ty,l) as typ) =
    match ty with
    | Typ_wild
    | Typ_id _
    | Typ_var _
      -> (KidSet.empty,[[],typ])
    | Typ_fn _ ->
       raise (Reporting_basic.err_general l ("Function type in constructor " ^ i))
    | Typ_tup ts ->
       let (vars,tys) = List.split (List.map size_nvars_ty ts) in
       let insttys = List.map (fun x -> let (insts,tys) = List.split x in
                                        List.concat insts, Typ_aux (Typ_tup tys,l)) (cross' tys) in
       (kidset_bigunion vars, insttys)
    | Typ_app (Id_aux (Id "vector",_),
               [_;Typ_arg_aux (Typ_arg_nexp sz,_);
                _;Typ_arg_aux (Typ_arg_typ (Typ_aux (Typ_id (Id_aux (Id "bit",_)),_)),_)]) ->
       (KidSet.of_list (size_nvars_nexp sz), [[],typ])
    | Typ_app (_, tas) ->
       (KidSet.empty,[[],typ])  (* We only support sizes for bitvectors mentioned explicitly, not any buried
                      inside another type *)
    | Typ_exist (kids, nc, t) ->
       let (vars,tys) = size_nvars_ty t in
       let find_insts k (insts,nc) =
         let inst,nc' =
           if KidSet.mem k vars then
             let is,nc' = extract_set_nc k nc in
             Some is,nc'
           else None,nc
         in (k,inst)::insts,nc'
       in
       let (insts,nc') = List.fold_right find_insts kids ([],nc) in
       let insts = cross'' insts in
       let ty_and_inst (inst0,ty) inst =
         let kids, ty = apply_kid_insts inst ty in
         let ty = Typ_aux (Typ_exist (kids, nc', ty),l) in
         inst@inst0, ty
       in
       let tys = List.concat (List.map (fun instty -> List.map (ty_and_inst instty) insts) tys) in
       let free = List.fold_left (fun vars k -> KidSet.remove k vars) vars kids in
       (free,tys)
  in
  (* Only single-variable prenex-form for now *)
  let size_nvars_ty (Typ_aux (ty,l) as typ) =
    match ty with
    | Typ_exist (kids,_,t) ->
       begin
         match snd (size_nvars_ty typ) with
         | [] -> []
         | tys ->
            if contains_exist t then
              raise (Reporting_basic.err_general l
                       "Only prenex types in unions are supported by monomorphisation")
            else if List.length kids > 1 then
              raise (Reporting_basic.err_general l
                       "Only single-variable existential types in unions are currently supported by monomorphisation")
            else tys
       end
    | _ -> []
  in
  (* TODO: reject universally quantification or monomorphise it *)
  let variants = size_nvars_ty ty in
  match variants with
  | [] -> None
  | sample::__ ->
     let () = if List.length variants > size_set_limit then
         raise (Reporting_basic.err_general ql
                  (string_of_int (List.length variants) ^ "variants for constructor " ^ i ^
                     "bigger than limit " ^ string_of_int size_set_limit)) else ()
     in
     let wrap = match id with
       | Id_aux (Id i,l) -> (fun f -> Id_aux (Id (f i),Generated l))
       | Id_aux (DeIid i,l) -> (fun f -> Id_aux (DeIid (f i),l))
     in
     let name_seg = function
       | (_,None) -> ""
       | (k,Some i) -> string_of_kid k ^ string_of_int i
     in
     let name l i = String.concat "_" (i::(List.map name_seg l)) in
     Some (List.map (fun (l,ty) -> (l, wrap (name l),ty)) variants)

let reduce_nexp subst ne =
  let rec eval (Nexp_aux (ne,_) as nexp) =
    match ne with
    | Nexp_constant i -> i
    | Nexp_sum (n1,n2) -> (eval n1) + (eval n2)
    | Nexp_minus (n1,n2) -> (eval n1) - (eval n2)
    | Nexp_times (n1,n2) -> (eval n1) * (eval n2)
    | Nexp_exp n -> 1 lsl (eval n)
    | Nexp_neg n -> - (eval n)
    | _ ->
       raise (Reporting_basic.err_general Unknown ("Couldn't turn nexp " ^
                                                      string_of_nexp nexp ^ " into concrete value"))
  in eval ne

(* Check to see if we need to monomorphise a use of a constructor.  Currently
   assumes that bitvector sizes are always given as a variable; don't yet handle
   more general cases (e.g., 8 * var) *)

(* TODO: use type checker's instantiation instead *)
let refine_constructor refinements id substs (E_aux (_,(l,_)) as arg) t =
  let rec derive_vars (Typ_aux (t,_)) (E_aux (e,(l,tannot))) =
    match t with
    | Typ_app (Id_aux (Id "vector",_), [_;Typ_arg_aux (Typ_arg_nexp (Nexp_aux (Nexp_var v,_)),_);_;Typ_arg_aux (Typ_arg_typ (Typ_aux (Typ_id (Id_aux (Id "bit",_)),_)),_)]) ->
       (match tannot with
       | Some (_,Typ_aux (Typ_app (Id_aux (Id "vector",_), [_;Typ_arg_aux (Typ_arg_nexp ne,_);_;Typ_arg_aux (Typ_arg_typ (Typ_aux (Typ_id (Id_aux (Id "bit",_)),_)),_)]),_),_) ->
          [(v,reduce_nexp substs ne)]
       | _ -> [])
    | Typ_wild
    | Typ_var _
    | Typ_id _
    | Typ_fn _
    | Typ_app _
      -> []
    | Typ_tup ts ->
       match e with
       | E_tuple es -> List.concat (List.map2 derive_vars ts es)
       | _ -> [] (* TODO? *)
  in
  try
    let (_,irefinements) = List.find (fun (id',_) -> Id.compare id id' = 0) refinements in
    let vars = List.sort_uniq (fun x y -> Kid.compare (fst x) (fst y)) (derive_vars t arg) in
    try
      Some (List.assoc vars irefinements)
    with Not_found ->
      (Reporting_basic.print_err false true l "Monomorphisation"
         ("Failed to find a monomorphic constructor for " ^ string_of_id id ^ " instance " ^
             match vars with [] -> "<empty>"
             | _ -> String.concat "," (List.map (fun (x,y) -> string_of_kid x ^ "=" ^ string_of_int y) vars)); None)
  with Not_found -> None


(* Substitute found nexps for variables in an expression, and rename constructors to reflect
   specialisation *)

(* TODO: kid shadowing *)
let nexp_subst_fns substs refinements =

  let s_t t = subst_src_typ substs t in
(*  let s_typschm (TypSchm_aux (TypSchm_ts (q,t),l)) = TypSchm_aux (TypSchm_ts (q,s_t t),l) in
   hopefully don't need this anyway *)(*
  let s_typschm tsh = tsh in*)
  let s_tannot = function
    | None -> None
    | Some (env,t,eff) -> Some (env,s_t t,eff) (* TODO: what about env? *)
  in
(*  let rec s_pat (P_aux (p,(l,annot))) =
    let re p = P_aux (p,(l,(*s_tannot*) annot)) in
    match p with
    | P_lit _ | P_wild | P_id _ -> re p
    | P_var kid -> re p
    | P_as (p',id) -> re (P_as (s_pat p', id))
    | P_typ (ty,p') -> re (P_typ (ty,s_pat p'))
    | P_app (id,ps) -> re (P_app (id, List.map s_pat ps))
    | P_record (fps,flag) -> re (P_record (List.map s_fpat fps, flag))
    | P_vector ps -> re (P_vector (List.map s_pat ps))
    | P_vector_indexed ips -> re (P_vector_indexed (List.map (fun (i,p) -> (i,s_pat p)) ips))
    | P_vector_concat ps -> re (P_vector_concat (List.map s_pat ps))
    | P_tup ps -> re (P_tup (List.map s_pat ps))
    | P_list ps -> re (P_list (List.map s_pat ps))
    | P_cons (p1,p2) -> re (P_cons (s_pat p1, s_pat p2))
  and s_fpat (FP_aux (FP_Fpat (id, p), (l,annot))) =
    FP_aux (FP_Fpat (id, s_pat p), (l,s_tannot annot))
  in*)
  let rec s_exp (E_aux (e,(l,annot))) =
    let re e = E_aux (e,(l,s_tannot annot)) in
      match e with
      | E_block es -> re (E_block (List.map s_exp es))
      | E_nondet es -> re (E_nondet (List.map s_exp es))
      | E_id _
      | E_lit _
      | E_comment _ -> re e
      | E_sizeof ne -> re (E_sizeof ne) (* TODO: does this need done?  does it appear in type checked code? *)
      | E_constraint nc -> re (E_constraint (subst_nc substs nc))
      | E_internal_exp (l,annot) -> re (E_internal_exp (l, s_tannot annot))
      | E_sizeof_internal (l,annot) -> re (E_sizeof_internal (l, s_tannot annot))
      | E_internal_exp_user ((l1,annot1),(l2,annot2)) ->
         re (E_internal_exp_user ((l1, s_tannot annot1),(l2, s_tannot annot2)))
      | E_cast (t,e') -> re (E_cast (t, s_exp e'))
      | E_app (id,es) ->
         let es' = List.map s_exp es in
         let arg =
           match es' with
           | [] -> E_aux (E_lit (L_aux (L_unit,Unknown)),(l,None))
           | [e] -> e
           | _ -> E_aux (E_tuple es',(l,None))
         in
         let id' = 
           let env,_ = env_typ_expected l annot in
           if Env.is_union_constructor id env then
             let (qs,ty) = Env.get_val_spec id env in
             match ty with (Typ_aux (Typ_fn(inty,outty,_),_)) ->
               (match refine_constructor refinements id substs arg inty with
               | None -> id
               | Some id' -> id')
             | _ -> id
           else id
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
      | E_internal_plet (p,e1,e2) -> re (E_internal_plet ((*s_pat*) p, s_exp e1, s_exp e2))
      | E_internal_return e -> re (E_internal_return (s_exp e))
      | E_throw e -> re (E_throw (s_exp e))
      | E_try (e,cases) -> re (E_try (s_exp e, List.map s_pexp cases))
    and s_opt_default (Def_val_aux (ed,(l,annot))) =
      match ed with
      | Def_val_empty -> Def_val_aux (Def_val_empty,(l,s_tannot annot))
      | Def_val_dec e -> Def_val_aux (Def_val_dec (s_exp e),(l,s_tannot annot))
    and s_fexps (FES_aux (FES_Fexps (fes,flag), (l,annot))) =
      FES_aux (FES_Fexps (List.map s_fexp fes, flag), (l,s_tannot annot))
    and s_fexp (FE_aux (FE_Fexp (id,e), (l,annot))) =
      FE_aux (FE_Fexp (id,s_exp e),(l,s_tannot annot))
    and s_pexp = function
      | (Pat_aux (Pat_exp (p,e),(l,annot))) ->
         Pat_aux (Pat_exp ((*s_pat*) p, s_exp e),(l,s_tannot annot))
      | (Pat_aux (Pat_when (p,e1,e2),(l,annot))) ->
         Pat_aux (Pat_when ((*s_pat*) p, s_exp e1, s_exp e2),(l,s_tannot annot))
    and s_letbind (LB_aux (lb,(l,annot))) =
      match lb with
      | LB_val_explicit (tysch,p,e) ->
         LB_aux (LB_val_explicit ((*s_typschm*) tysch,(*s_pat*) p,s_exp e), (l,s_tannot annot))
      | LB_val_implicit (p,e) -> LB_aux (LB_val_implicit ((*s_pat*) p,s_exp e), (l,s_tannot annot))
    and s_lexp (LEXP_aux (e,(l,annot))) =
      let re e = LEXP_aux (e,(l,s_tannot annot)) in
      match e with
      | LEXP_id _ -> re e
      | LEXP_cast (typ,id) -> re (LEXP_cast (s_t typ, id))
      | LEXP_memory (id,es) -> re (LEXP_memory (id,List.map s_exp es))
      | LEXP_tup les -> re (LEXP_tup (List.map s_lexp les))
      | LEXP_vector (le,e) -> re (LEXP_vector (s_lexp le, s_exp e))
      | LEXP_vector_range (le,e1,e2) -> re (LEXP_vector_range (s_lexp le, s_exp e1, s_exp e2))
      | LEXP_field (le,id) -> re (LEXP_field (s_lexp le, id))
  in ((fun x -> x (*s_pat*)),s_exp)
let nexp_subst_pat substs refinements = fst (nexp_subst_fns substs refinements)
let nexp_subst_exp substs refinements = snd (nexp_subst_fns substs refinements)

let bindings_from_pat p =
  let rec aux_pat (P_aux (p,(l,annot))) =
    let env,_ = env_typ_expected l annot in
    match p with
    | P_lit _
    | P_wild
      -> []
    | P_as (p,id) -> id::(aux_pat p)
    | P_typ (_,p) -> aux_pat p
    | P_id id ->
       if pat_id_is_variable env id then [id] else []
    | P_var kid -> [id_of_kid kid]
    | P_vector ps
    | P_vector_concat ps
    | P_app (_,ps)
    | P_tup ps
    | P_list ps
      -> List.concat (List.map aux_pat ps)
    | P_record (fps,_) -> List.concat (List.map aux_fpat fps)
    | P_vector_indexed ips -> List.concat (List.map (fun (_,p) -> aux_pat p) ips)
    | P_cons (p1,p2) -> aux_pat p1 @ aux_pat p2
  and aux_fpat (FP_aux (FP_Fpat (_,p), _)) = aux_pat p
  in aux_pat p

let remove_bound env pat =
  let bound = bindings_from_pat pat in
  List.fold_left (fun sub v -> ISubst.remove v sub) env bound

(* Remove explicit existential types from the AST, so that the sizes of
   bitvectors will be filled in throughout.

   Problems: there might be other existential types that we want to keep (e.g.
   because they describe conditions needed for a vector index to be in range),
   and inference might not be able to find a sufficiently precise type. *)
let rec deexist_exp (E_aux (e,(l,(annot : Type_check.tannot))) as exp) =
  let re e = E_aux (e,(l,annot)) in
  match e with
  | E_block es -> re (E_block (List.map deexist_exp es))
  | E_nondet es -> re (E_nondet (List.map deexist_exp es))
  | E_id _
  | E_lit _
  | E_sizeof _
  | E_constraint _
    -> (*Type_check.strip_exp*) exp
  | E_cast (Typ_aux (Typ_exist (kids, nc, ty),l),(E_aux (_,(l',annot')) as e)) ->
(*     let env,_ = env_typ_expected l' annot' in
     let plain_e = deexist_exp e in
     let E_aux (_,(_,annot'')) = Type_check.infer_exp env plain_e in
*)
     deexist_exp e
  | E_cast (ty,e) -> re (E_cast (ty,deexist_exp e))
  | E_app (id,args) -> re (E_app (id,List.map deexist_exp args))
  | E_app_infix (e1,id,e2) -> re (E_app_infix (deexist_exp e1,id,deexist_exp e2))
  | E_tuple es -> re (E_tuple (List.map deexist_exp es))
  | E_if (e1,e2,e3) -> re (E_if (deexist_exp e1,deexist_exp e2,deexist_exp e3))
  | E_for (id,e1,e2,e3,ord,e4) ->
     re (E_for (id,deexist_exp e1,deexist_exp e2,deexist_exp e3,ord,deexist_exp e4))
  | E_vector es -> re (E_vector (List.map deexist_exp es))
  | E_vector_indexed (ies,def) ->
     re (E_vector_indexed
           (List.map (fun (i,e) -> (i,deexist_exp e)) ies,
            match def with
            | Def_val_aux (Def_val_empty,(l,ann)) -> Def_val_aux (Def_val_empty,(l,ann))
            | Def_val_aux (Def_val_dec e,(l,ann)) -> Def_val_aux (Def_val_dec (deexist_exp e),(l,ann))))
  | E_vector_access (e1,e2) -> re (E_vector_access (deexist_exp e1,deexist_exp e2))
  | E_vector_subrange (e1,e2,e3) -> re (E_vector_subrange (deexist_exp e1,deexist_exp e2,deexist_exp e3))
  | E_vector_update (e1,e2,e3) -> re (E_vector_update (deexist_exp e1,deexist_exp e2,deexist_exp e3))
  | E_vector_update_subrange (e1,e2,e3,e4) ->
     re (E_vector_update_subrange (deexist_exp e1,deexist_exp e2,deexist_exp e3,deexist_exp e4))
  | E_vector_append (e1,e2) -> re (E_vector_append (deexist_exp e1,deexist_exp e2))
  | E_list es -> re (E_list (List.map deexist_exp es))
  | E_cons (e1,e2) -> re (E_cons (deexist_exp e1,deexist_exp e2))
  | E_record _ -> (*Type_check.strip_exp*) exp (* TODO *)
  | E_record_update  _ -> (*Type_check.strip_exp*) exp (* TODO *)
  | E_field (e1,fld) -> re (E_field (deexist_exp e1,fld))
  | E_case (e1,cases) -> re (E_case (deexist_exp e1, List.map deexist_pexp cases))
  | E_let (lb,e1) -> re (E_let (deexist_letbind lb, deexist_exp e1))
  | E_assign (le,e1) -> re (E_assign (deexist_lexp le, deexist_exp e1))
  | E_exit e1 -> re (E_exit (deexist_exp e1))
  | E_throw e1 -> re (E_throw (deexist_exp e1))
  | E_try (e1,cases) -> re (E_try (deexist_exp e1, List.map deexist_pexp cases))
  | E_return e1 -> re (E_return (deexist_exp e1))
  | E_assert (e1,e2) -> re (E_assert (deexist_exp e1,deexist_exp e2))
and deexist_pexp (Pat_aux (pe,(l,annot))) =
  match pe with
  | Pat_exp (p,e) -> Pat_aux (Pat_exp ((*Type_check.strip_pat*) p,deexist_exp e),(l,annot))
  | Pat_when (p,e1,e2) -> Pat_aux (Pat_when ((*Type_check.strip_pat*) p,deexist_exp e1,deexist_exp e2),(l,annot))
and deexist_letbind (LB_aux (lb,(l,annot))) =
  match lb with (* TODO, drop tysc if there's an exist? Do they even appear here? *)
  | LB_val_explicit (tysc,p,e) -> LB_aux (LB_val_explicit (tysc,(*Type_check.strip_pat*) p,deexist_exp e),(l,annot))
  | LB_val_implicit (p,e) -> LB_aux (LB_val_implicit ((*Type_check.strip_pat*) p,deexist_exp e),(l,annot))
and deexist_lexp (LEXP_aux (le,(l,annot))) =
  let re le = LEXP_aux (le,(l,annot)) in
  match le with
  | LEXP_id id -> re (LEXP_id id)
  | LEXP_memory (id,es) -> re (LEXP_memory (id,List.map deexist_exp es))
  | LEXP_cast (Typ_aux (Typ_exist _,_),id) -> re (LEXP_id id)
  | LEXP_cast (ty,id) -> re (LEXP_cast (ty,id))
  | LEXP_tup lexps -> re (LEXP_tup (List.map deexist_lexp lexps))
  | LEXP_vector (le,e) -> re (LEXP_vector (deexist_lexp le, deexist_exp e))
  | LEXP_vector_range (le,e1,e2) -> re (LEXP_vector_range (deexist_lexp le, deexist_exp e1, deexist_exp e2))
  | LEXP_field (le,id) -> re (LEXP_field (deexist_lexp le, id))

let deexist_funcl (FCL_aux (FCL_Funcl (id,p,e),(l,annot))) =
  FCL_aux (FCL_Funcl (id, (*Type_check.strip_pat*) p, deexist_exp e),(l,annot))

let deexist_def = function
  | DEF_kind kd -> DEF_kind kd
  | DEF_type td -> DEF_type td
  | DEF_fundef (FD_aux (FD_function (recopt,topt,effopt,fcls),(l,annot))) ->
     DEF_fundef (FD_aux (FD_function (recopt,topt,effopt,List.map deexist_funcl fcls),(l,annot)))
  | x -> x

let deexist (Defs defs) = Defs (List.map deexist_def defs)


(* Attempt simple pattern matches *)
let lit_match = function
  | (L_zero | L_false), (L_zero | L_false) -> true
  | (L_one  | L_true ), (L_one  | L_true ) -> true
  | l1,l2 -> l1 = l2

type 'a matchresult =
  | DoesMatch of 'a
  | DoesNotMatch
  | GiveUp

let can_match (E_aux (e,(l,annot)) as exp0) cases =
  let (env,_) = env_typ_expected l annot in
  let rec findpat_generic check_pat description = function
    | [] -> (Reporting_basic.print_err false true l "Monomorphisation"
               ("Failed to find a case for " ^ description); None)
    | [Pat_aux (Pat_exp (P_aux (P_wild,_),exp),_)] -> Some (exp,[],[])
    | (Pat_aux (Pat_exp (P_aux (P_typ (_,p),_),exp),ann))::tl ->
       findpat_generic check_pat description ((Pat_aux (Pat_exp (p,exp),ann))::tl)
    | (Pat_aux (Pat_exp (P_aux (P_id id',_),exp),_))::tl
        when pat_id_is_variable env id' ->
       Some (exp, [(id', exp0)], [])
    | (Pat_aux (Pat_when _,_))::_ -> None
    | (Pat_aux (Pat_exp (p,exp),_))::tl ->
       match check_pat p with
       | DoesNotMatch -> findpat_generic check_pat description tl
       | DoesMatch (subst,ksubst) -> Some (exp,subst,ksubst)
       | GiveUp -> None
  in
  match e with
  | E_id id ->
     (match Env.lookup_id id env with
     | Enum _ ->
        let checkpat = function
          | P_aux (P_id id',_)
          | P_aux (P_app (id',[]),_) ->
             if Id.compare id id' = 0 then DoesMatch ([],[]) else DoesNotMatch
          | P_aux (_,(l',_)) ->
             (Reporting_basic.print_err false true l' "Monomorphisation"
                "Unexpected kind of pattern for enumeration"; GiveUp)
        in findpat_generic checkpat (string_of_id id) cases
     | _ -> None)
  | E_lit (L_aux (lit_e, lit_l)) ->
     let checkpat = function
       | P_aux (P_lit (L_aux (lit_p, _)),_) ->
          if lit_match (lit_e,lit_p) then DoesMatch ([],[]) else DoesNotMatch
       | P_aux (P_var kid,_) ->
          begin
            match lit_e with
            | L_num i ->
               DoesMatch ([id_of_kid kid, E_aux (e,(l,annot))],
                          [kid,Nexp_aux (Nexp_constant i,Unknown)])
            | _ ->
               (Reporting_basic.print_err false true lit_l "Monomorphisation"
                  "Unexpected kind of literal for var match"; GiveUp)
          end
       | P_aux (_,(l',_)) ->
          (Reporting_basic.print_err false true l' "Monomorphisation"
             "Unexpected kind of pattern for literal"; GiveUp)
     in findpat_generic checkpat "literal" cases
  | _ -> None

(* Remove top-level casts from an expression.  Useful when we need to look at
   subexpressions to reduce something, but could break type-checking if we used
   it everywhere. *)
let rec drop_casts = function
  | E_aux (E_cast (_,e),_) -> drop_casts e
  | exp -> exp

(* TODO: ought to be a big int of some form, but would need L_num to be one *)
let int_of_lit = function
  | L_hex hex -> int_of_string ("0x" ^ hex)
  | L_bin bin -> int_of_string ("0b" ^ bin)
  | _ -> assert false

let lit_eq (L_aux (l1,_)) (L_aux (l2,_)) =
  match l1,l2 with
  | (L_zero|L_false), (L_zero|L_false)
  | (L_one |L_true ), (L_one |L_true)
    -> Some true
  | (L_hex _| L_bin _), (L_hex _|L_bin _)
    -> Some (int_of_lit l1 = int_of_lit l2)
  | L_undef, _ | _, L_undef -> None
  | _ -> Some (l1 = l2)

(* TODO: we should really specify which functions are equality in the prelude,
   rather than fixing them here. *)
let eq_fns = [Id "eq_int"; Id "eq_vec"; Id "eq_string"; Id "eq_real"]
let neq_fns = [Id "neq_anything"]

let try_app (l,ann) (Id_aux (id,_),args) =
  let is_eq = List.mem id eq_fns in
  let is_neq = (not is_eq) && List.mem id neq_fns in
  let new_l = Generated l in
  if is_eq || is_neq then
    match args with
    | [E_aux (E_lit l1,_); E_aux (E_lit l2,_)] ->
       let lit b = if b then L_true else L_false in
       let lit b = lit (if is_eq then b else not b) in
       (match lit_eq l1 l2 with
       | None -> None
       | Some b -> Some (E_aux (E_lit (L_aux (lit b,new_l)),(l,ann))))
    | _ -> None
  else if id = Id "cast_bit_bool" then
    match args with
    | [E_aux (E_lit L_aux (L_zero,_),_)] -> Some (E_aux (E_lit (L_aux (L_false,new_l)),(l,ann)))
    | [E_aux (E_lit L_aux (L_one ,_),_)] -> Some (E_aux (E_lit (L_aux (L_true ,new_l)),(l,ann)))
    | _ -> None
  else if id = Id "UInt" then
    match args with
    | [E_aux (E_lit L_aux ((L_hex _| L_bin _) as lit,_), _)] ->
       Some (E_aux (E_lit (L_aux (L_num (int_of_lit lit),new_l)),(l,ann)))
    | _ -> None
  else if id = Id "shl_int" then
    match args with
    | [E_aux (E_lit L_aux (L_num i,_),_); E_aux (E_lit L_aux (L_num j,_),_)] ->
       Some (E_aux (E_lit (L_aux (L_num (i lsl j),new_l)),(l,ann)))
    | _ -> None
  else if id = Id "ex_int" then
    match args with
    | [E_aux (E_lit _,_) as exp] -> Some exp
    | _ -> None
  else if id = Id "vector_access" then
    match args with
    | [E_aux (E_lit L_aux ((L_hex _ | L_bin _) as lit,_),_);
       E_aux (E_lit L_aux (L_num i,_),_)] ->
       let v = int_of_lit lit in
       let b = (v lsr i) land 1 in
       let lit' = if b = 1 then L_one else L_zero in
       Some (E_aux (E_lit (L_aux (lit',new_l)),(l,ann)))
    | _ -> None
  else None


let try_app_infix (l,ann) (E_aux (e1,ann1)) (Id_aux (id,_)) (E_aux (e2,ann2)) =
  let i = match id with Id x -> x | DeIid x -> x in
  let new_l = Generated l in
  match e1, i, e2 with
  | E_lit l1, ("=="|"!="), E_lit l2 ->
     let lit b = if b then L_true else L_false in
     let lit b = lit (if i = "==" then b else not b) in
     (match lit_eq l1 l2 with
     | Some b -> Some (E_aux (E_lit (L_aux (lit b,new_l)), (l,ann)))
     | None -> None)
  | _ -> None

let construct_lit_vector args =
  let rec aux l = function
    | [] -> Some (L_aux (L_bin (String.concat "" (List.rev l)),Unknown))
    | E_aux (E_lit (L_aux ((L_zero | L_one) as lit,_)),_)::t ->
       aux ((if lit = L_zero then "0" else "1")::l) t
    | _ -> None
  in aux [] args

(* We may need to split up a pattern match if (1) we've been told to case split
   on a variable by the user, or (2) we monomorphised a constructor that's used
   in the pattern. *)
type split =
  | NoSplit
  | VarSplit of (tannot pat * (id * tannot Ast.exp) list) list
  | ConstrSplit of (tannot pat * nexp KSubst.t) list

let split_defs splits defs =
  let split_constructors (Defs defs) =
    let sc_type_union q (Tu_aux (tu,l) as tua) =
      match tu with
      | Tu_id id -> [],[tua]
      | Tu_ty_id (ty,id) ->
         (match split_src_type id ty q with
         | None -> ([],[Tu_aux (Tu_ty_id (ty,id),l)])
         | Some variants ->
            ([(id,variants)],
             List.map (fun (insts, id', ty) -> Tu_aux (Tu_ty_id (ty,id'),Generated l)) variants))
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

  (* Constant propogation *)
  let rec const_prop_exp substs ((E_aux (e,(l,annot))) as exp) =
    let re e = E_aux (e,(l,annot)) in
    match e with
      (* TODO: are there more circumstances in which we should get rid of these? *)
    | E_block [e] -> const_prop_exp substs e
    | E_block es -> re (E_block (List.map (const_prop_exp substs) es))
    | E_nondet es -> re (E_nondet (List.map (const_prop_exp substs) es))
       
    | E_id id ->
       (try ISubst.find id substs
        with Not_found -> exp)
    | E_lit _
    | E_sizeof _
    | E_internal_exp _
    | E_sizeof_internal _
    | E_internal_exp_user _
    | E_comment _
    | E_constraint _
      -> exp
    | E_cast (t,e') -> re (E_cast (t, const_prop_exp substs e'))
    | E_app (id,es) ->
       let es' = List.map (const_prop_exp substs) es in
       (match try_app (l,annot) (id,es') with
       | None ->
          (match const_prop_try_fn (id,es') with
          | None -> re (E_app (id,es'))
          | Some r -> r)
       | Some r -> r)
    | E_app_infix (e1,id,e2) ->
       let e1',e2' = const_prop_exp substs e1,const_prop_exp substs e2 in
       (match try_app_infix (l,annot) e1' id e2' with
       | Some exp -> exp
       | None -> re (E_app_infix (e1',id,e2')))
    | E_tuple es -> re (E_tuple (List.map (const_prop_exp substs) es))
    | E_if (e1,e2,e3) ->
       let e1' = const_prop_exp substs e1 in
       let e2',e3' = const_prop_exp substs e2, const_prop_exp substs e3 in
       (match drop_casts e1' with
       | E_aux (E_lit (L_aux ((L_true|L_false) as lit ,_)),_) ->
          (match lit with L_true -> e2' | _ -> e3')
       | _ -> re (E_if (e1',e2',e3')))
    | E_for (id,e1,e2,e3,ord,e4) -> re (E_for (id,const_prop_exp substs e1,const_prop_exp substs e2,const_prop_exp substs e3,ord,const_prop_exp (ISubst.remove id substs) e4))
    | E_vector es ->
       let es' = List.map (const_prop_exp substs) es in
       begin
         match construct_lit_vector es' with
         | None -> re (E_vector es')
         | Some lit -> re (E_lit lit)
       end
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
       | Some (E_aux (_,(_,annot')) as exp,newbindings,kbindings) ->
          let exp = nexp_subst_exp (ksubst_from_list kbindings) [] (*???*) exp in
          let newbindings_env = isubst_from_list newbindings in
          let substs' = isubst_union substs newbindings_env in
          const_prop_exp substs' exp)
    | E_let (lb,e2) ->
       begin
         match lb with
         | LB_aux (LB_val_explicit (tysch,p,e),annot) ->
            let substs' = remove_bound substs p in
            re (E_let (LB_aux (LB_val_explicit (tysch,p,const_prop_exp substs e), annot),
                       const_prop_exp substs' e2))
         | LB_aux (LB_val_implicit (p,e), annot) ->
            let e' = const_prop_exp substs e in
            let substs' = remove_bound substs p in
            let plain () =
              re (E_let (LB_aux (LB_val_implicit (p,e'), annot),
                         const_prop_exp substs' e2)) in
            if is_value e' && not (is_value e) then
              match can_match e' [Pat_aux (Pat_exp (p,e2),(Unknown,None))] with
              | None -> plain ()
              | Some (e'',bindings,kbindings) ->
                 let e'' = nexp_subst_exp (ksubst_from_list kbindings) [] (*???*) e'' in
                 let bindings = isubst_from_list bindings in
                 let substs'' = isubst_union substs' bindings in
                 const_prop_exp substs'' e''
            else plain ()
       end
    | E_assign (le,e) -> re (E_assign (const_prop_lexp substs le, const_prop_exp substs e))
    | E_exit e -> re (E_exit (const_prop_exp substs e))
    | E_throw e -> re (E_throw (const_prop_exp substs e))
    | E_try (e,cases) ->
       let e' = const_prop_exp substs e in
       re (E_case (e', List.map (const_prop_pexp substs) cases))
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
  and const_prop_pexp substs = function
    | (Pat_aux (Pat_exp (p,e),l)) ->
       Pat_aux (Pat_exp (p,const_prop_exp (remove_bound substs p) e),l)
    | (Pat_aux (Pat_when (p,e1,e2),l)) ->
       let substs' = remove_bound substs p in
       Pat_aux (Pat_when (p, const_prop_exp substs' e1, const_prop_exp substs' e2),l)
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
  (* Reduce a function when
     1. all arguments are values,
     2. the function is pure,
     3. the result is a value
     (and 4. the function is not scattered, but that's not terribly important)
     to try and keep execution time and the results managable.
  *)
  and const_prop_try_fn (id,args) =
    if not (List.for_all is_value args) then
      None
    else
      let Defs ds = defs in
      match list_extract (function
      | (DEF_fundef (FD_aux (FD_function (_,_,eff,((FCL_aux (FCL_Funcl (id',_,_),_))::_ as fcls)),_)))
        -> if Id.compare id id' = 0 then Some (eff,fcls) else None
      | _ -> None) ds with
      | None -> None
      | Some (eff,_) when not (is_pure eff) -> None
      | Some (_,fcls) ->
         let arg = match args with
           | [] -> E_aux (E_lit (L_aux (L_unit,Unknown)),(Unknown,None))
           | [e] -> e
           | _ -> E_aux (E_tuple args,(Unknown,None)) in
         let cases = List.map (function
           | FCL_aux (FCL_Funcl (_,pat,exp), ann) -> Pat_aux (Pat_exp (pat,exp),ann))
           fcls in
         match can_match arg cases with
         | Some (exp,bindings,kbindings) ->
            let substs = isubst_from_list bindings in
            let result = const_prop_exp substs exp in
            if is_value result then Some result else None
         | None -> None
  in

  let subst_exp substs exp =
    let substs = isubst_from_list substs in
    const_prop_exp substs exp
  in
    
  (* Split a variable pattern into every possible value *)

  let split var l annot =
    let v = string_of_id var in
    let env, typ = env_typ_expected l annot in
    let typ = Env.expand_synonyms env typ in
    let Typ_aux (ty,l) = typ in
    let new_l = Generated l in
    let renew_id (Id_aux (id,l)) = Id_aux (id,new_l) in
    let cannot () =
      raise (Reporting_basic.err_general l
               ("Cannot split type " ^ string_of_typ typ ^ " for variable " ^ v))
    in
    match ty with
    | Typ_id id ->
       (try
         (* enumerations *)
         let ns = Env.get_enum id env in
         List.map (fun n -> (P_aux (P_id (renew_id n),(l,annot)),
                             [var,E_aux (E_id (renew_id n),(new_l,annot))])) ns
       with Type_error _ ->
         match id with
         | Id_aux (Id "bit",_) ->
            List.map (fun b ->
              P_aux (P_lit (L_aux (b,new_l)),(l,annot)),
              [var,E_aux (E_lit (L_aux (b,new_l)),(new_l, annot))])
              [L_zero; L_one]
         | _ -> cannot ())
    | Typ_app (Id_aux (Id "vector",_), [_;Typ_arg_aux (Typ_arg_nexp len,_);_;Typ_arg_aux (Typ_arg_typ (Typ_aux (Typ_id (Id_aux (Id "bit",_)),_)),_)]) ->
       (match len with
       | Nexp_aux (Nexp_constant sz,_) ->
          if sz <= vector_split_limit then
            let lits = make_vectors sz in
            List.map (fun lit ->
              P_aux (P_lit lit,(l,annot)),
              [var,E_aux (E_lit lit,(new_l,annot))]) lits
          else
            raise (Reporting_basic.err_general l
                     ("Refusing to split vector type of length " ^ string_of_int sz ^
                         " above limit " ^ string_of_int vector_split_limit ^ 
                         " for variable " ^ v))
       | _ ->
          cannot ()
       )
    (*|  set constrained numbers TODO *)
    | _ -> cannot ()
  in
  

  (* Split variable patterns at the given locations *)

  let map_locs ls (Defs defs) =
    let rec match_l = function
      | Unknown
      | Int _ -> []
      | Generated l -> [] (* Could do match_l l, but only want to split user-written patterns *)
      | Range (p,q) ->
         let matches =
           List.filter (fun ((filename,line),_) ->
             Filename.basename p.Lexing.pos_fname = filename &&
               p.Lexing.pos_lnum <= line && line <= q.Lexing.pos_lnum) ls
         in List.map snd matches
    in 

    let split_pat vars p =
      let id_matches = function
        | Id_aux (Id x,_) -> List.mem x vars
        | Id_aux (DeIid x,_) -> List.mem x vars
      in

      let rec list f = function
        | [] -> None
        | h::t ->
           let t' =
             match list f t with
             | None -> [t,[]]
             | Some t' -> t'
           in
           let h' =
             match f h with
             | None -> [h,[]]
             | Some ps -> ps
           in
           Some (List.concat (List.map (fun (h,hsubs) -> List.map (fun (t,tsubs) -> (h::t,hsubs@tsubs)) t') h'))
      in
      let rec spl (P_aux (p,(l,annot))) =
        let relist f ctx ps =
          optmap (list f ps) 
            (fun ps ->
              List.map (fun (ps,sub) -> P_aux (ctx ps,(l,annot)),sub) ps)
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
        | P_var _
          -> None
        | P_as (p',id) when id_matches id ->
           raise (Reporting_basic.err_general l
                    ("Cannot split " ^ string_of_id id ^ " on 'as' pattern"))
        | P_as (p',id) ->
           re (fun p -> P_as (p,id)) p'
        | P_typ (t,p') -> re (fun p -> P_typ (t,p)) p'
        | P_id id when id_matches id ->
           Some (split id l annot)
        | P_id _ ->
           None
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
        | P_cons (p1,p2) ->
           match spl p1, spl p2 with
           | None, None -> None
           | p1', p2' ->
              let p1' = match p1' with None -> [p1,[]] | Some p1' -> p1' in
              let p2' = match p2' with None -> [p2,[]] | Some p2' -> p2' in
              let ps = List.map (fun (p1',subs1) -> List.map (fun (p2',subs2) ->
                P_aux (P_cons (p1',p2'),(l,annot)),subs1@subs2) p2') p1' in
              Some (List.concat ps)
      in spl p
    in

    let map_pat_by_loc (P_aux (p,(l,_)) as pat) =
      match match_l l with
      | [] -> None
      | vars -> split_pat vars pat
    in
    let map_pat (P_aux (p,(l,tannot)) as pat) =
      match map_pat_by_loc pat with
      | Some l -> VarSplit l
      | None ->
         match p with
         | P_app (id,args) ->
            begin
              let kid,kid_annot =
                match args with
                | [P_aux (P_var kid,ann)] -> kid,ann
                | _ -> 
                   raise (Reporting_basic.err_general l
                            "Pattern match not currently supported by monomorphisation")
              in match List.find (fun (id',_) -> Id.compare id id' = 0) refinements with
              | (_,variants) ->
                 let map_inst (insts,id',_) =
                   let insts =
                     match insts with [(v,Some i)] -> [(kid,Nexp_aux (Nexp_constant i, Generated l))]
                     | _ -> assert false
                   in
(*
                   let insts,_ = split_insts insts in
                   let insts = List.map (fun (v,i) ->
                     (??,
                      Nexp_aux (Nexp_constant i,Generated l)))
                     insts in
  P_aux (P_app (id',args),(Generated l,tannot)),
*)
                   P_aux (P_app (id',[P_aux (P_id (id_of_kid kid),kid_annot)]),(Generated l,tannot)),
                   ksubst_from_list insts
                 in
                 ConstrSplit (List.map map_inst variants)
              | exception Not_found -> NoSplit
            end
         | _ -> NoSplit
    in

    let check_single_pat (P_aux (_,(l,annot)) as p) =
      match match_l l with
      | [] -> p
      | lvs ->
         let pvs = bindings_from_pat p in
         let pvs = List.map string_of_id pvs in
         let overlap = List.exists (fun v -> List.mem v pvs) lvs in
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
      | E_constraint _
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
      | E_throw e -> re (E_throw e)
      | E_try (e,cases) -> re (E_try (map_exp e, List.concat (List.map map_pexp cases)))
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
    and map_pexp = function
      | Pat_aux (Pat_exp (p,e),l) ->
         (match map_pat p with
         | NoSplit -> [Pat_aux (Pat_exp (p,map_exp e),l)]
         | VarSplit patsubsts ->
            List.map (fun (pat',substs) ->
              let exp' = subst_exp substs e in
              Pat_aux (Pat_exp (pat', map_exp exp'),l))
              patsubsts
         | ConstrSplit patnsubsts ->
            List.map (fun (pat',nsubst) ->
           (* Leave refinements to later *)
              let pat' = nexp_subst_pat nsubst [] pat' in
              let exp' = nexp_subst_exp nsubst [] e in
              Pat_aux (Pat_exp (pat', map_exp exp'),l)
            ) patnsubsts)
      | Pat_aux (Pat_when (p,e1,e2),l) ->
         (match map_pat p with
         | NoSplit -> [Pat_aux (Pat_when (p,map_exp e1,map_exp e2),l)]
         | VarSplit patsubsts ->
            List.map (fun (pat',substs) ->
              let exp1' = subst_exp substs e1 in
              let exp2' = subst_exp substs e2 in
              Pat_aux (Pat_when (pat', map_exp exp1', map_exp exp2'),l))
              patsubsts
         | ConstrSplit patnsubsts ->
            List.map (fun (pat',nsubst) ->
           (* Leave refinements to later *)
              let pat' = nexp_subst_pat nsubst [] pat' in
              let exp1' = nexp_subst_exp nsubst [] e1 in
              let exp2' = nexp_subst_exp nsubst [] e2 in
              Pat_aux (Pat_when (pat', map_exp exp1', map_exp exp2'),l)
            ) patnsubsts)
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
         List.map (fun (pat',substs) ->
           let exp' = subst_exp substs exp in
           FCL_aux (FCL_Funcl (id, pat', map_exp exp'), annot))
           patsubsts
      | ConstrSplit patnsubsts ->
         List.map (fun (pat',nsubst) ->
           (* Leave refinements to later *)
           let pat' = nexp_subst_pat nsubst [] pat' in
           let exp' = nexp_subst_exp nsubst [] exp in
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
      | DEF_overload _
        -> [d]
      | DEF_fundef fd -> [DEF_fundef (map_fundef fd)]
      | DEF_val lb -> [DEF_val (map_letbind lb)]
      | DEF_scattered sd -> List.map (fun x -> DEF_scattered x) (map_scattered_def sd)

    in
    Defs (List.concat (List.map map_def defs))
  in
  (*deexist*) (map_locs splits defs')

