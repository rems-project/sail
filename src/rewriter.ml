open Big_int
open Ast
open Type_internal
type typ = Type_internal.t
type 'a exp = 'a Ast.exp
type 'a emap = 'a Envmap.t
type envs = Type_check.envs

type 'a rewriters = { rewrite_exp : 'a rewriters -> nexp_map option -> 'a exp -> 'a exp;
                      rewrite_lexp : 'a rewriters -> nexp_map option -> 'a lexp -> 'a lexp;
                      rewrite_pat  : 'a rewriters -> nexp_map option -> 'a pat -> 'a pat;
                      rewrite_let  : 'a rewriters -> nexp_map option -> 'a letbind -> 'a letbind;
                      rewrite_fun  : 'a rewriters -> 'a fundef -> 'a fundef;
                      rewrite_def  : 'a rewriters -> 'a def -> 'a def;
                      rewrite_defs : 'a rewriters -> 'a defs -> 'a defs;
                    }

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

let explode s =
  let rec exp i l = if i < 0 then l else exp (i - 1) (s.[i] :: l) in
  exp (String.length s - 1) []


let vector_string_to_bit_list lit = 

  let hexchar_to_binlist = function
    | '0' -> ['0';'0';'0';'0']
    | '1' -> ['0';'0';'0';'1']
    | '2' -> ['0';'0';'1';'0']
    | '3' -> ['0';'0';'1';'1']
    | '4' -> ['0';'1';'0';'0']
    | '5' -> ['0';'1';'0';'1']
    | '6' -> ['0';'1';'1';'0']
    | '7' -> ['0';'1';'1';'1']
    | '8' -> ['1';'0';'0';'0']
    | '9' -> ['1';'0';'0';'1']
    | 'A' -> ['1';'0';'1';'0']
    | 'B' -> ['1';'0';'1';'1']
    | 'C' -> ['1';'1';'0';'0']
    | 'D' -> ['1';'1';'0';'1']
    | 'E' -> ['1';'1';'1';'0']
    | 'F' -> ['1';'1';'1';'1']
    | _ -> raise (Reporting_basic.err_unreachable Parse_ast.Unknown "hexchar_to_binlist given unrecognized character") in
  
  let s_bin = match lit with
    | L_hex s_hex -> List.flatten (List.map hexchar_to_binlist (explode (String.uppercase s_hex)))
    | L_bin s_bin -> explode s_bin
    | _ -> raise (Reporting_basic.err_unreachable Parse_ast.Unknown "s_bin given non vector literal") in

  List.map (function '0' -> L_aux (L_zero, Parse_ast.Unknown)
                   | '1' -> L_aux (L_one,Parse_ast.Unknown)
                   | _ -> raise (Reporting_basic.err_unreachable Parse_ast.Unknown "binary had non-zero or one")) s_bin

let rewrite_pat rewriters nmap (P_aux (pat,(l,annot))) =
  let rewrap p = P_aux (p,(l,annot)) in
  let rewrite = rewriters.rewrite_pat rewriters nmap in
  match pat with
  | P_lit (L_aux ((L_hex _ | L_bin _) as lit,_)) ->
    let ps =  List.map (fun p -> P_aux (P_lit p,(Parse_ast.Unknown,simple_annot {t = Tid "bit"})))
        (vector_string_to_bit_list lit) in
    rewrap (P_vector ps)
  | P_lit _ | P_wild | P_id _ -> rewrap pat
  | P_as(pat,id) -> rewrap (P_as( rewrite pat, id))
  | P_typ(typ,pat) -> rewrite pat
  | P_app(id ,pats) -> rewrap (P_app(id, List.map rewrite pats))
  | P_record(fpats,_) ->
    rewrap (P_record(List.map (fun (FP_aux(FP_Fpat(id,pat),pannot)) -> FP_aux(FP_Fpat(id, rewrite pat), pannot)) fpats,
                     false))
  | P_vector pats -> rewrap (P_vector(List.map rewrite pats))
  | P_vector_indexed ipats -> rewrap (P_vector_indexed(List.map (fun (i,pat) -> (i, rewrite pat)) ipats))
  | P_vector_concat pats -> rewrap (P_vector_concat (List.map rewrite pats))
  | P_tup pats -> rewrap (P_tup (List.map rewrite pats))
  | P_list pats -> rewrap (P_list (List.map rewrite pats))

let rewrite_exp rewriters nmap (E_aux (exp,(l,annot))) = 
  let rewrap e = E_aux (e,(l,annot)) in
  let rewrite = rewriters.rewrite_exp rewriters nmap in
  match exp with
    | E_block exps -> rewrap (E_block (List.map rewrite exps))
    | E_nondet exps -> rewrap (E_nondet (List.map rewrite exps))
    | E_lit (L_aux ((L_hex _ | L_bin _) as lit,_)) ->
      let es = List.map (fun p -> E_aux (E_lit p ,(Parse_ast.Unknown,simple_annot {t = Tid "bit"})))
          (vector_string_to_bit_list lit) in
      rewrap (E_vector es)
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
    | E_let (letbind,body) -> rewrap (E_let(rewriters.rewrite_let rewriters nmap letbind,rewrite body))
    | E_assign (lexp,exp) -> rewrap (E_assign(rewriters.rewrite_lexp rewriters nmap lexp,rewrite exp))
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
    | E_internal_let _ -> raise (Reporting_basic.err_unreachable l "Internal let found before it should have been introduced")

let rewrite_let rewriters map (LB_aux(letbind,(l,annot))) =
  let map = merge_option_maps map (get_map_tannot annot) in
  match letbind with
  | LB_val_explicit (typschm, pat,exp) ->
    LB_aux(LB_val_explicit (typschm,pat, rewriters.rewrite_exp rewriters map exp),(l,annot))
  | LB_val_implicit ( pat, exp) ->
    LB_aux(LB_val_implicit (pat,rewriters.rewrite_exp rewriters map exp),(l,annot))

let rewrite_lexp rewriters map (LEXP_aux(lexp,(l,annot))) = 
  let rewrap le = LEXP_aux(le,(l,annot)) in
  match lexp with
  | LEXP_id _ | LEXP_cast _ -> rewrap lexp
  | LEXP_memory (id,exps) -> rewrap (LEXP_memory(id,List.map (rewriters.rewrite_exp rewriters map) exps))
  | LEXP_vector (lexp,exp) ->
    rewrap (LEXP_vector (rewriters.rewrite_lexp rewriters map lexp,rewriters.rewrite_exp rewriters map exp))
  | LEXP_vector_range (lexp,exp1,exp2) -> 
    rewrap (LEXP_vector_range (rewriters.rewrite_lexp rewriters map lexp,
                               rewriters.rewrite_exp rewriters map exp1,
                               rewriters.rewrite_exp rewriters map exp2))
  | LEXP_field (lexp,id) -> rewrap (LEXP_field (rewriters.rewrite_lexp rewriters map lexp,id))

let rewrite_fun rewriters (FD_aux (FD_function(recopt,tannotopt,effectopt,funcls),(l,fdannot))) = 
  let rewrite_funcl (FCL_aux (FCL_Funcl(id,pat,exp),(l,annot))) = 
    (*let _ = Printf.eprintf "Rewriting function %s, pattern %s\n" 
      (match id with (Id_aux (Id i,_)) -> i) (Pretty_print.pat_to_string pat) in*)
    let map = get_map_tannot fdannot in
    (FCL_aux (FCL_Funcl (id,rewriters.rewrite_pat rewriters map pat,
                            rewriters.rewrite_exp rewriters map exp),(l,annot))) 
  in FD_aux (FD_function(recopt,tannotopt,effectopt,List.map rewrite_funcl funcls),(l,fdannot))

let rewrite_def rewriters d = match d with
  | DEF_type _ | DEF_spec _ | DEF_default _ | DEF_reg_dec _ -> d
  | DEF_fundef fdef -> DEF_fundef (rewriters.rewrite_fun rewriters fdef)
  | DEF_val letbind -> DEF_val (rewriters.rewrite_let rewriters None letbind)
  | DEF_scattered _ -> raise (Reporting_basic.err_unreachable Parse_ast.Unknown "DEF_scattered survived to rewritter")

let rewrite_defs_base rewriters (Defs defs) = 
  let rec rewrite ds = match ds with
    | [] -> []
    | d::ds -> (rewriters.rewrite_def rewriters d)::(rewrite ds) in
  Defs (rewrite defs)
    
let rewrite_defs (Defs defs) = rewrite_defs_base
    {rewrite_exp = rewrite_exp;
     rewrite_pat = rewrite_pat;
     rewrite_let = rewrite_let;
     rewrite_lexp = rewrite_lexp;
     rewrite_fun = rewrite_fun;
     rewrite_def = rewrite_def;
     rewrite_defs = rewrite_defs_base} (Defs defs)

type ('a,'pat,'pat_aux,'fpat,'fpat_aux) pat_alg =
  { p_lit            : lit -> 'pat_aux
  ; p_wild           : 'pat_aux
  ; p_as             : 'pat * id -> 'pat_aux
  ; p_typ            : Ast.typ * 'pat -> 'pat_aux
  ; p_id             : id -> 'pat_aux
  ; p_app            : id * 'pat list -> 'pat_aux
  ; p_record         : 'fpat list * bool -> 'pat_aux
  ; p_vector         : 'pat list -> 'pat_aux
  ; p_vector_indexed : (int * 'pat) list -> 'pat_aux
  ; p_vector_concat  : 'pat list -> 'pat_aux
  ; p_tup            : 'pat list -> 'pat_aux
  ; p_list           : 'pat list -> 'pat_aux
  ; p_aux            : 'pat_aux * 'a annot -> 'pat
  ; fP_aux           : 'fpat_aux * 'a annot -> 'fpat
  ; fP_Fpat          : id * 'pat -> 'fpat_aux
  }

let rec fold_pat_aux (alg : ('a,'pat,'pat_aux,'fpat,'fpat_aux) pat_alg) : 'a pat_aux -> 'pat_aux =
  function
  | P_lit lit           -> alg.p_lit lit
  | P_wild              -> alg.p_wild
  | P_id id             -> alg.p_id id
  | P_as (p,id)         -> alg.p_as (fold_pat alg p,id)
  | P_typ (typ,p)       -> alg.p_typ (typ,fold_pat alg p)
  | P_app (id,ps)       -> alg.p_app (id,List.map (fold_pat alg) ps)
  | P_record (ps,b)     -> alg.p_record (List.map (fold_fpat alg) ps, b)
  | P_vector ps         -> alg.p_vector (List.map (fold_pat alg) ps)
  | P_vector_indexed ps -> alg.p_vector_indexed (List.map (fun (i,p) -> (i, fold_pat alg p)) ps)
  | P_vector_concat ps  -> alg.p_vector_concat (List.map (fold_pat alg) ps)
  | P_tup ps            -> alg.p_tup (List.map (fold_pat alg) ps)
  | P_list ps           -> alg.p_list (List.map (fold_pat alg) ps)


and fold_pat (alg : ('a,'pat,'pat_aux,'fpat,'fpat_aux) pat_alg) : 'a pat -> 'pat =
  function
  | P_aux (pat,annot)   -> alg.p_aux (fold_pat_aux alg pat,annot)
and fold_fpat_aux (alg : ('a,'pat,'pat_aux,'fpat,'fpat_aux) pat_alg) : 'a fpat_aux -> 'fpat_aux =
  function
  | FP_Fpat (id,pat)    -> alg.fP_Fpat (id,fold_pat alg pat)
and fold_fpat (alg : ('a,'pat,'pat_aux,'fpat,'fpat_aux) pat_alg) : 'a fpat -> 'fpat =
  function
  | FP_aux (fpat,annot) -> alg.fP_aux (fold_fpat_aux alg fpat,annot)
                                      
(* identity fold from term alg to term alg *)
let id_pat_alg : ('a,'a pat, 'a pat_aux, 'a fpat, 'a fpat_aux) pat_alg = 
  { p_lit            = (fun lit -> P_lit lit)
  ; p_wild           = P_wild
  ; p_as             = (fun (pat,id) -> P_as (pat,id))
  ; p_typ            = (fun (typ,pat) -> P_typ (typ,pat))
  ; p_id             = (fun id -> P_id id)
  ; p_app            = (fun (id,ps) -> P_app (id,ps))
  ; p_record         = (fun (ps,b) -> P_record (ps,b))
  ; p_vector         = (fun ps -> P_vector ps)
  ; p_vector_indexed = (fun ps -> P_vector_indexed ps)
  ; p_vector_concat  = (fun ps -> P_vector_concat ps)
  ; p_tup            = (fun ps -> P_tup ps)
  ; p_list           = (fun ps -> P_list ps)
  ; p_aux            = (fun (pat,annot) -> P_aux (pat,annot))
  ; fP_aux           = (fun (fpat,annot) -> FP_aux (fpat,annot))
  ; fP_Fpat          = (fun (id,pat) -> FP_Fpat (id,pat))
  }
  
type ('a,'exp,'exp_aux,'lexp,'lexp_aux,'fexp,'fexp_aux,'fexps,'fexps_aux,
      'opt_default_aux,'opt_default,'pexp,'pexp_aux,'letbind_aux,'letbind,
      'pat,'pat_aux,'fpat,'fpat_aux) exp_alg = 
  { e_block                  : 'exp list -> 'exp_aux
  ; e_nondet                 : 'exp list -> 'exp_aux
  ; e_id                     : id -> 'exp_aux
  ; e_lit                    : lit -> 'exp_aux
  ; e_cast                   : Ast.typ * 'exp -> 'exp_aux
  ; e_app                    : id * 'exp list -> 'exp_aux
  ; e_app_infix              : 'exp * id * 'exp -> 'exp_aux
  ; e_tuple                  : 'exp list -> 'exp_aux
  ; e_if                     : 'exp * 'exp * 'exp -> 'exp_aux
  ; e_for                    : id * 'exp * 'exp * 'exp * Ast.order * 'exp -> 'exp_aux
  ; e_vector                 : 'exp list -> 'exp_aux
  ; e_vector_indexed         : (int * 'exp) list * 'opt_default -> 'exp_aux
  ; e_vector_access          : 'exp * 'exp -> 'exp_aux
  ; e_vector_subrange        : 'exp * 'exp * 'exp -> 'exp_aux
  ; e_vector_update          : 'exp * 'exp * 'exp -> 'exp_aux
  ; e_vector_update_subrange : 'exp * 'exp * 'exp * 'exp -> 'exp_aux
  ; e_vector_append          : 'exp * 'exp -> 'exp_aux
  ; e_list                   : 'exp list -> 'exp_aux
  ; e_cons                   : 'exp * 'exp -> 'exp_aux
  ; e_record                 : 'fexps -> 'exp_aux
  ; e_record_update          : 'exp * 'fexps -> 'exp_aux
  ; e_field                  : 'exp * id -> 'exp_aux
  ; e_case                   : 'exp * 'pexp list -> 'exp_aux
  ; e_let                    : 'letbind * 'exp -> 'exp_aux
  ; e_assign                 : 'lexp * 'exp -> 'exp_aux
  ; e_exit                   : 'exp -> 'exp_aux
  ; e_internal_cast          : 'a annot * 'exp -> 'exp_aux
  ; e_internal_exp           : 'a annot -> 'exp_aux
  ; e_internal_exp_user      : 'a annot * 'a annot -> 'exp_aux
  ; e_internal_let           : 'lexp * 'exp * 'exp -> 'exp_aux
  ; e_aux                    : 'exp_aux * 'a annot -> 'exp
  ; lEXP_id                  : id -> 'lexp_aux
  ; lEXP_memory              : id * 'exp list -> 'lexp_aux
  ; lEXP_cast                : Ast.typ * id -> 'lexp_aux
  ; lEXP_vector              : 'lexp * 'exp -> 'lexp_aux
  ; lEXP_vector_range        : 'lexp * 'exp * 'exp -> 'lexp_aux
  ; lEXP_field               : 'lexp * id -> 'lexp_aux
  ; lEXP_aux                 : 'lexp_aux * 'a annot -> 'lexp
  ; fE_Fexp                  : id * 'exp -> 'fexp_aux
  ; fE_aux                   : 'fexp_aux * 'a annot -> 'fexp
  ; fES_Fexps                : 'fexp list * bool -> 'fexps_aux
  ; fES_aux                  : 'fexps_aux * 'a annot -> 'fexps
  ; def_val_empty            : 'opt_default_aux
  ; def_val_dec              : 'exp -> 'opt_default_aux
  ; def_val_aux              : 'opt_default_aux * 'a annot -> 'opt_default
  ; pat_exp                  : 'pat * 'exp -> 'pexp_aux
  ; pat_aux                  : 'pexp_aux * 'a annot -> 'pexp
  ; lB_val_explicit          : typschm * 'pat * 'exp -> 'letbind_aux
  ; lB_val_implicit          : 'pat * 'exp -> 'letbind_aux
  ; lB_aux                   : 'letbind_aux * 'a annot -> 'letbind
  ; pat_alg                  : ('a,'pat,'pat_aux,'fpat,'fpat_aux) pat_alg
  }
    
let rec fold_exp_aux alg = function
  | E_block es -> alg.e_block (List.map (fold_exp alg) es)
  | E_nondet es -> alg.e_nondet (List.map (fold_exp alg) es)
  | E_id id -> alg.e_id id
  | E_lit lit -> alg.e_lit lit
  | E_cast (typ,e) -> alg.e_cast (typ, fold_exp alg e)
  | E_app (id,es) -> alg.e_app (id, List.map (fold_exp alg) es)
  | E_app_infix (e1,id,e2) -> alg.e_app_infix (fold_exp alg e1, id, fold_exp alg e2)
  | E_tuple es -> alg.e_tuple (List.map (fold_exp alg) es)
  | E_if (e1,e2,e3) -> alg.e_if (fold_exp alg e1, fold_exp alg e2, fold_exp alg e3)
  | E_for (id,e1,e2,e3,order,e4) ->
     alg.e_for (id,fold_exp alg e1, fold_exp alg e2, fold_exp alg e3, order, fold_exp alg e4)
  | E_vector es -> alg.e_vector (List.map (fold_exp alg) es)
  | E_vector_indexed (es,opt) ->
     alg.e_vector_indexed (List.map (fun (id,e) -> (id,fold_exp alg e)) es, fold_opt_default alg opt)
  | E_vector_access (e1,e2) -> alg.e_vector_access (fold_exp alg e1, fold_exp alg e2)
  | E_vector_subrange (e1,e2,e3) ->
     alg.e_vector_subrange (fold_exp alg e1, fold_exp alg e2, fold_exp alg e3)
  | E_vector_update (e1,e2,e3) ->
     alg.e_vector_update (fold_exp alg e1, fold_exp alg e2, fold_exp alg e3)
  | E_vector_update_subrange (e1,e2,e3,e4) ->
     alg.e_vector_update_subrange (fold_exp alg e1,fold_exp alg e2, fold_exp alg e3, fold_exp alg e4)
  | E_vector_append (e1,e2) -> alg.e_vector_append (fold_exp alg e1, fold_exp alg e2)
  | E_list es -> alg.e_list (List.map (fold_exp alg) es)
  | E_cons (e1,e2) -> alg.e_cons (fold_exp alg e1, fold_exp alg e2)
  | E_record fexps -> alg.e_record (fold_fexps alg fexps)
  | E_record_update (e,fexps) -> alg.e_record_update (fold_exp alg e, fold_fexps alg fexps)
  | E_field (e,id) -> alg.e_field (fold_exp alg e, id)
  | E_case (e,pexps) -> alg.e_case (fold_exp alg e, List.map (fold_pexp alg) pexps)
  | E_let (letbind,e) -> alg.e_let (fold_letbind alg letbind, fold_exp alg e)
  | E_assign (lexp,e) -> alg.e_assign (fold_lexp alg lexp, fold_exp alg e)
  | E_exit e -> alg.e_exit (fold_exp alg e)
  | E_internal_cast (annot,e) -> alg.e_internal_cast (annot, fold_exp alg e)
  | E_internal_exp annot -> alg.e_internal_exp annot
  | E_internal_exp_user (annot1,annot2) -> alg.e_internal_exp_user (annot1,annot2)
  | E_internal_let (lexp,e1,e2) ->
     alg.e_internal_let (fold_lexp alg lexp, fold_exp alg e1, fold_exp alg e2)
and fold_exp alg (E_aux (exp_aux,annot)) = alg.e_aux (fold_exp_aux alg exp_aux, annot)
and fold_lexp_aux alg = function
  | LEXP_id id -> alg.lEXP_id id
  | LEXP_memory (id,es) -> alg.lEXP_memory (id, List.map (fold_exp alg) es)
  | LEXP_cast (typ,id) -> alg.lEXP_cast (typ,id)
  | LEXP_vector (lexp,e) -> alg.lEXP_vector (fold_lexp alg lexp, fold_exp alg e)
  | LEXP_vector_range (lexp,e1,e2) ->
     alg.lEXP_vector_range (fold_lexp alg lexp, fold_exp alg e1, fold_exp alg e2)
 | LEXP_field (lexp,id) -> alg.lEXP_field (fold_lexp alg lexp, id)
and fold_lexp alg (LEXP_aux (lexp_aux,annot)) =
  alg.lEXP_aux (fold_lexp_aux alg lexp_aux, annot)
and fold_fexp_aux alg (FE_Fexp (id,e)) = alg.fE_Fexp (id, fold_exp alg e)
and fold_fexp alg (FE_aux (fexp_aux,annot)) = alg.fE_aux (fold_fexp_aux alg fexp_aux,annot)
and fold_fexps_aux alg (FES_Fexps (fexps,b)) = alg.fES_Fexps (List.map (fold_fexp alg) fexps, b)
and fold_fexps alg (FES_aux (fexps_aux,annot)) = alg.fES_aux (fold_fexps_aux alg fexps_aux, annot)
and fold_opt_default_aux alg = function
  | Def_val_empty -> alg.def_val_empty
  | Def_val_dec e -> alg.def_val_dec (fold_exp alg e)
and fold_opt_default alg (Def_val_aux (opt_default_aux,annot)) =
  alg.def_val_aux (fold_opt_default_aux alg opt_default_aux, annot)
and fold_pexp_aux alg (Pat_exp (pat,e)) = alg.pat_exp (fold_pat alg.pat_alg pat, fold_exp alg e)
and fold_pexp alg (Pat_aux (pexp_aux,annot)) = alg.pat_aux (fold_pexp_aux alg pexp_aux, annot)
and fold_letbind_aux alg = function
  | LB_val_explicit (t,pat,e) -> alg.lB_val_explicit (t,fold_pat alg.pat_alg pat, fold_exp alg e)
  | LB_val_implicit (pat,e) -> alg.lB_val_implicit (fold_pat alg.pat_alg pat, fold_exp alg e)
and fold_letbind alg (LB_aux (letbind_aux,annot)) = alg.lB_aux (fold_letbind_aux alg letbind_aux, annot)


let remove_vector_concat_pat pat =
  
  let counter = ref 0 in
  let fresh_name () =
    let current = !counter in
    let () = counter := (current + 1) in
    Id_aux (Id ("__v" ^ string_of_int current), Parse_ast.Unknown) in
  
  (* expects that P_typ elements have been removed from AST,
     that the length of all vectors involved is known,
     that we don't have indexed vectors *)

  (* introduce names for all patterns of form P_vector_concat *)
  let name_vector_concat_roots =
    let p_aux (pat,annot) = match pat with
      | P_vector_concat pats -> P_aux (P_as (P_aux (pat,annot),fresh_name()),annot)
      | _ -> P_aux (pat,annot) in 
    {id_pat_alg with p_aux = p_aux} in

  let pat = fold_pat name_vector_concat_roots pat in

  (* introduce names for all unnamed child nodes of P_vector_concat *)
  let name_vector_concat_elements =
    let p_vector_concat pats =
      let aux ((P_aux (p,a)) as pat) = match p with
        | P_vector _ -> P_aux (P_as (pat,fresh_name()),a)
     (* | P_vector_concat. cannot happen after folding function name_vector_concat_roots *)
        | _ -> pat in (* this can only be P_as and P_id *)
      P_vector_concat (List.map aux pats) in
    {id_pat_alg with p_vector_concat = p_vector_concat} in

  let pat = fold_pat name_vector_concat_elements pat in

  (* remove names from vectors in vector_concat patterns and collect them as declarations for the
     function body or expression *)
  let unname_vector_concat_elements :
        ('a,
         'a pat *      ((tannot exp -> tannot exp) list),
         'a pat_aux *  ((tannot exp -> tannot exp) list),
         'a fpat *     ((tannot exp -> tannot exp) list),
         'a fpat_aux * ((tannot exp -> tannot exp) list))
          pat_alg =

    (* build a let-expression of the form "let child = root[i..j] in body" *)
    let letbind_vec (rootid,rannot) (child,cannot) (i,j) body =
      let index n =
        let typ = simple_annot {t = Tapp ("atom",[TA_nexp (mk_c (big_int_of_int n))])} in
        E_aux (E_lit (L_aux (L_num n,Parse_ast.Unknown)), (Parse_ast.Unknown,typ)) in
      let subv = E_aux (E_vector_subrange (E_aux (E_id rootid,rannot),index i,index j),cannot) in
      let typ = (Parse_ast.Unknown,simple_annot {t = Tid "unit"}) in
      E_aux (E_let (LB_aux (LB_val_implicit (P_aux (P_id child,cannot),subv),cannot),body),typ) in

    let p_aux ((pattern,decls),rannot) = match pattern with
      | P_as (P_aux (P_vector_concat pats,_),rootid) ->
         let aux (pos,pat_acc,decl_acc) (P_aux (p,cannot)) = match cannot with
           | (_,Base((_,{t = Tapp ("vector",[_;TA_nexp {nexp = Nconst length};_;_])}),_,_,_,_)) ->
              let length  = int_of_big_int length in
              (match p with 
               (* if we see a named vector pattern, remove the name and remember to 
                  declare it later *)
               | P_as (P_aux (p,cannot),cname) ->
                  (pos + length, pat_acc @ [P_aux (p,cannot)],
                   decl_acc @ [letbind_vec (rootid,rannot) (cname,cannot) (pos,pos + length - 1)])
               (* if we see a P_id variable, remember to declare it later *)
               | P_id cname ->
                  (pos + length, pat_acc @ [P_aux (P_id cname,cannot)],
                   decl_acc @ [letbind_vec (rootid,rannot) (cname,cannot) (pos,pos + length - 1)])
               (* normal vector patterns are fine *)
               | _ -> (pos + length, pat_acc @ [P_aux (p,cannot)],decl_acc) )
           (* non-vector patterns aren't *)
           | (l,_) -> raise (Reporting_basic.err_unreachable
                               l "Non-vector in vector-concat pattern") in
         let (_,pats',decls') = List.fold_left aux (0,[],[]) pats in
         (P_aux (P_vector_concat pats',rannot),decls @ decls')
      | _ -> (P_aux (pattern,rannot),decls) in
    
    { p_lit            = (fun lit -> (P_lit lit,[]))
    ; p_wild           = (P_wild,[])
    ; p_as             = (fun ((pat,decls),id) -> (P_as (pat,id),decls))
    ; p_typ            = (fun (typ,(pat,decls)) -> (P_typ (typ,pat),decls))
    ; p_id             = (fun id -> (P_id id,[]))
    ; p_app            = (fun (id,ps) -> let (ps,decls) = List.split ps in
                                         (P_app (id,ps),List.flatten decls))
    ; p_record         = (fun (ps,b) -> let (ps,decls) = List.split ps in
                                        (P_record (ps,b),List.flatten decls))
    ; p_vector         = (fun ps -> let (ps,decls) = List.split ps in
                                    (P_vector ps,List.flatten decls))
    ; p_vector_indexed = (fun ps -> let (is,ps) = List.split ps in
                                    let (ps,decls) = List.split ps in
                                    let ps = List.combine is ps in
                                    (P_vector_indexed ps,List.flatten decls))
    ; p_vector_concat  = (fun ps -> let (ps,decls) = List.split ps in
                                    (P_vector_concat ps,List.flatten decls))
    ; p_tup            = (fun ps -> let (ps,decls) = List.split ps in
                                    (P_tup ps,List.flatten decls))
    ; p_list           = (fun ps -> let (ps,decls) = List.split ps in
                                    (P_list ps,List.flatten decls))
    ; p_aux            = (fun ((pat,decls),annot) -> p_aux ((pat,decls),annot))
    ; fP_aux           = (fun ((fpat,decls),annot) -> (FP_aux (fpat,annot),decls))
    ; fP_Fpat          = (fun (id,(pat,decls)) -> (FP_Fpat (id,pat),decls))
    } in

  let (pat,decls_list) = fold_pat unname_vector_concat_elements pat in

  let decls = List.fold_right (fun f g x -> f (g x)) decls_list (fun b -> b) in
             
  (* at this point shouldn't have P_as patterns in P_vector_concat patterns any more,
     all P_as and P_id vectors should have their declarations in decls.
     Now flatten all vector_concat patterns *)
  
  let flatten =
    let p_vector_concat ps =
      let aux p acc = match p with
        | (P_aux (P_vector_concat pats,_)) -> pats @ acc
        | pat -> pat :: acc in
      P_vector_concat (List.fold_right aux ps []) in
    {id_pat_alg with p_vector_concat = p_vector_concat} in
  
  let pat = fold_pat flatten pat in

  (* at this point pat should be a flat pattern: no vector_concat patterns
     with vector_concats patterns as direct child-nodes anymore *)

  let range a b =
    let rec aux a b = if a > b then [] else a :: aux (a+1) b in
    if a > b then List.rev (aux b a) else aux a b in

  let remove_vector_concats =
    let p_vector_concat ps =
      let aux acc (P_aux (p,annot)) = match p,annot with
        | P_vector ps,_ -> acc @ ps
        | P_id _,
          (_,Base((_,{t = Tapp ("vector", [_;TA_nexp {nexp = Nconst length};_;_])}),_,_,_,_)) ->
           let wild _ = P_aux (P_wild,(Parse_ast.Unknown,simple_annot {t = Tid "bit"})) in
           acc @ (List.map wild (range 0 ((int_of_big_int length) - 1)))
        | _,(l,_) -> raise (Reporting_basic.err_unreachable l "Non-vector in vector-concat pattern") in
      P_vector_concat (List.fold_left aux [] ps) in
    {id_pat_alg with p_vector_concat = p_vector_concat} in
  
  let pat = fold_pat remove_vector_concats pat in
  
  (pat,decls)

(* assumes there are no more E_internal expressions *)
let rewrite_exp_remove_vector_concat_pat rewriters nmap (E_aux (exp,(l,annot)) as full_exp) = 
  let rewrap e = E_aux (e,(l,annot)) in
  let rewrite_rec = rewriters.rewrite_exp rewriters nmap in
  let rewrite_base = rewrite_exp rewriters nmap in
  match exp with
  | E_case (e,ps) ->
     let aux (Pat_aux (Pat_exp (pat,body),annot')) =
       let (pat,decls) = remove_vector_concat_pat pat in
       Pat_aux (Pat_exp (pat,decls (rewrite_rec body)),annot') in
     rewrap (E_case (rewrite_rec e,List.map aux ps))
  | E_let (LB_aux (LB_val_explicit (typ,pat,v),annot'),body) ->
     let (pat,decls) = remove_vector_concat_pat pat in
     rewrap (E_let (LB_aux (LB_val_explicit (typ,pat,rewrite_rec v),annot'),
                    decls (rewrite_rec body)))
  | E_let (LB_aux (LB_val_implicit (pat,v),annot'),body) ->
     let (pat,decls) = remove_vector_concat_pat pat in
     rewrap (E_let (LB_aux (LB_val_implicit (pat,rewrite_rec v),annot'),
                    decls (rewrite_rec body)))
  | exp -> rewrite_base full_exp

let rewrite_fun_remove_vector_concat_pat
      rewriters (FD_aux (FD_function(recopt,tannotopt,effectopt,funcls),(l,fdannot))) = 
  let rewrite_funcl (FCL_aux (FCL_Funcl(id,pat,exp),(l,annot))) =
    let (pat,decls) = remove_vector_concat_pat pat in
    (FCL_aux (FCL_Funcl (id,pat,rewriters.rewrite_exp rewriters (get_map_tannot fdannot) (decls exp)),(l,annot))) 
  in FD_aux (FD_function(recopt,tannotopt,effectopt,List.map rewrite_funcl funcls),(l,fdannot))


let rewrite_defs_remove_vector_concat defs = rewrite_defs_base
    {rewrite_exp = rewrite_exp_remove_vector_concat_pat;
     rewrite_pat = rewrite_pat;
     rewrite_let = rewrite_let;
     rewrite_lexp = rewrite_lexp;
     rewrite_fun = rewrite_fun_remove_vector_concat_pat;
     rewrite_def = rewrite_def;
     rewrite_defs = rewrite_defs_base} defs
    
(*Expects to be called after rewrite_defs; thus the following should not appear:
  internal_exp of any form
  lit vectors in patterns or expressions
 *)
let rewrite_exp_lift_assign_intro rewriters nmap ((E_aux (exp,(l,annot))) as full_exp) = 
  let rewrap e = E_aux (e,(l,annot)) in
  let rewrite_rec = rewriters.rewrite_exp rewriters nmap in
  let rewrite_base = rewrite_exp rewriters nmap in
  match exp with
  | E_block exps ->
    let rec walker exps = match exps with
      | [] -> []
      | (E_aux(E_assign(le,e), (l, Base((_,t),Emp_intro,_,_,_))))::exps ->
        let le' = rewriters.rewrite_lexp rewriters nmap le in
        let e' = rewrite_base e in
        let exps' = walker exps in
        [(E_aux (E_internal_let(le', e', E_aux(E_block exps', (l, simple_annot {t=Tid "unit"}))),
                 (l, simple_annot t)))]
      | e::exps -> (rewrite_rec e)::(walker exps)
    in
    rewrap (E_block (walker exps))
  | E_assign(le,e) ->
    (match annot with
     | Base((_,t),Emp_intro,_,_,_) ->
       let le' = rewriters.rewrite_lexp rewriters nmap le in
       let e' = rewrite_base e in
       rewrap (E_internal_let(le', e', E_aux(E_block [], (l, simple_annot {t=Tid "unit"}))))
     | _ -> rewrite_base full_exp)         
  | _ -> rewrite_base full_exp

let rewrite_defs_exp_lift_assign defs = rewrite_defs_base
    {rewrite_exp = rewrite_exp_lift_assign_intro;
     rewrite_pat = rewrite_pat;
     rewrite_let = rewrite_let;
     rewrite_lexp = rewrite_lexp;
     rewrite_fun = rewrite_fun;
     rewrite_def = rewrite_def;
     rewrite_defs = rewrite_defs_base} defs

let rewrite_defs_ocaml defs =
  let defs_vec_concat_removed = rewrite_defs_remove_vector_concat defs in
  let defs_lifted_assign = rewrite_defs_exp_lift_assign defs_vec_concat_removed in
  defs_lifted_assign


let normalise_exp exp =

  let compose f g x = f (g x) in

  let counter = ref 0 in
  let fresh_name () =
    let current = !counter in
    let () = counter := (current + 1) in
    Id_aux (Id ("__w" ^ string_of_int current), Parse_ast.Unknown) in
  
  let aux (((E_aux (_,annot)) as e,b) : ('a exp * bool)) : (('a exp -> 'a exp) * 'a exp * bool) =
    (* for a tuple (e, b = is e effectful) return 
       1. a function that let-binds e to the argument (body)
       2. something to access e's value, which is either e itself if b = false or an id to access the
          value bound to id in the let-expression
       3. b *)

    let letbind id body =
      let typ = (Parse_ast.Unknown,simple_annot {t = Tid "unit"}) in
      E_aux (E_let (LB_aux (LB_val_implicit (P_aux (P_id id,annot),e),annot),body),typ) in

    if b then
      let freshid = fresh_name () in
      let decl = letbind freshid in
      (decl,E_aux (E_id freshid,annot),b)
    else
      ((fun x -> x),e,b) in

  let list_aux es =
    List.fold_left
      (fun (acc_decl, acc_es, acc_b) e ->
       let (decl,e,b) = aux e in
       (compose acc_decl decl, acc_es @ [e], acc_b || b))
      ((fun x -> x), [], false) es in
            
  (* for each expression e: return a tuple (normalised e, does e contain effectful terms) *)
  fold_exp 
    { e_block =
        (fun es ->
         let (es,effs) = List.split es in
         ((fun x -> x), E_block es,List.fold_left (||) false effs)
        )
    ; e_nondet =
        (fun es ->
         let (es,effs) = List.split es in
         ((fun x -> x), E_block es,List.fold_left (||) false effs)
        )
    ; e_id = (fun id -> ((fun x -> x), E_id id,false))
    ; e_lit = (fun lit -> ((fun x -> x), E_lit lit,false))
    ; e_cast = (fun (typ,(e,b)) -> ((fun x -> x), E_cast (typ,e),b))
    ; e_app =
        (fun (id,es) ->
         let (decl,params,b) = list_aux es in
         (decl,E_app (id,params),b)
        )
    ; e_app_infix =
        (fun (e1,id,e2) ->
         let (decl1,e1,b1) = aux e1 in
         let (decl2,e2,b2) = aux e2 in
         (compose decl1 decl2, E_app_infix (e1,id,e2), b1 || b2)
        )
    ; e_tuple =
        (fun es ->
         let (decl,es,b) = list_aux es in
         (decl, E_tuple es,b)
        )
    ; e_if =
        (fun (e1,(e2,b2),(e3,b3)) ->
         let (decl,e1,b1) = aux e1 in
         (decl, E_if (e1,e2,e3), b1 || b2 || b3)
        )
    ; e_for =
        (fun (id,e1,e2,e3,order,(e4,b4)) ->
         let (decl1,e1,b1) = aux e1 in
         let (decl2,e2,b2) = aux e2 in
         let (decl3,e3,b3) = aux e3 in
         (compose decl1 (compose decl2 decl3), E_for (id,e1,e2,e3,order,e4), b1 || b2 || b3 || b4)
        )
    ; e_vector = 
        (fun es ->
         let (decl,es,b) = list_aux es in
         (decl, E_vector es, b)
        )
    ; e_vector_indexed =
        (fun (es,(decl2,opt2,b2)) ->
         let (is,es) = List.split es in
         let (decl1,es,b1) = list_aux es in
         (compose decl1 decl2, E_vector_indexed (List.combine is es,opt2), b1 || b2)
        )
    ; e_vector_access =
        (function
          | ((E_aux (E_id _,_) as e1,b1),e2) ->
            (* then e1 is OK: the whole e_vector_access has to be
               translated to a monadic expression *)
             let (decl2,e2,b2) = aux e2 in
             (decl2, E_vector_access (e1,e2), b1 || b2)
          | (e1,e2) ->
             let (decl1,e1,b1) = aux e1 in
             let (decl2,e2,b2) = aux e2 in
             (compose decl1 decl2, E_vector_access (e1,e2), b1 || b2)
        )
    ; e_vector_subrange = 
        (function
          | ((E_aux (E_id _,_) as e1,b1),e2,e3) ->
            (* then e1 is OK: the whole e_vector_access has to be
               translated to a monadic expression *)
             let (decl2,e2,b2) = aux e2 in
             let (decl3,e3,b3) = aux e3 in
             (compose decl2 decl3, E_vector_subrange (e1,e2,e3), b1 || b2 || b3)
          | (e1,e2,e3) ->
             let (decl1,e1,b1) = aux e1 in
             let (decl2,e2,b2) = aux e2 in
             let (decl3,e3,b3) = aux e3 in
             (compose decl1 (compose decl2 decl3), E_vector_subrange (e1,e2,e3), b1 || b2)
        )
    ; e_vector_update =
        (fun (e1,e2,e3) -> 
         let (decl1,e1,b1) = aux e1 in
         let (decl2,e2,b2) = aux e2 in
         let (decl3,e3,b3) = aux e3 in
         (compose decl1 (compose decl2 decl3), E_vector_update (e1,e2,e3), b1 || b2)
        )
    ; e_vector_update_subrange = 
        (fun (e1,e2,e3,e4) -> 
         let (decl1,e1,b1) = aux e1 in
         let (decl2,e2,b2) = aux e2 in
         let (decl3,e3,b3) = aux e3 in
         let (decl4,e4,b4) = aux e4 in
         (compose decl1 (compose decl2 (compose decl3 decl4)), E_vector_update_subrange (e1,e2,e3,e4),
          b1 || b2)
        )
    ; e_vector_append = 
        (fun (e1,e2) ->
         let (decl1,e1,b1) = aux e1 in
         let (decl2,e2,b2) = aux e2 in
         (compose decl1 decl2, E_vector_append (e1,e2), b1 || b2)
        )
    ; e_list =
        (fun es ->
         let (decl,params,b) = list_aux es in
         (decl, E_list params,b)
        )
    ; e_cons = 
        (fun (e1,e2) ->
         let (decl1,e1,b1) = aux e1 in
         let (decl2,e2,b2) = aux e2 in
         (compose decl1 decl2, E_cons (e1,e2), b1 || b2)
        )
    ; e_record = (fun (decl,fexps,b) -> (decl, E_record fexps,b))
    ; e_record_update =
        (fun (e1,(decl2,fexp,b2)) ->
         let (decl1,e1,b1) = aux e1 in
         (compose decl1 decl2, E_record_update (e1,fexp), b1 || b2)
        )
    ; e_field =
        (fun (e1,id) ->
         let (decl,e1,b) = aux e1 in
         (decl, E_field (e1,id),b)
        )
    ; e_case =
        (fun (e1,pexps) ->
         let (decl,e1,b1) = aux e1 in
         let (pexps,b2) =
           List.fold_left
             (fun (acc,b_acc) (pat,b) -> (acc @ [pat], b_acc || b))
             ([],false) pexps in
         (decl, E_case (e1,pexps), b1 || b2)
        )
    ; e_let = (fun ((lb,b1),(exp,b2)) -> ((fun x -> x), E_let (lb,exp), b1 || b2))
    ; e_assign =
        (fun ((decl1,lexp),e2) ->
         let (decl2,e2,b2) = aux e2 in
         (compose decl1 decl2, E_assign (lexp,e2), b2)
        )
    ; e_exit = (fun e1 -> let (decl,e1,b) = aux e1 in (decl, E_exit e1,b))
    ; e_internal_cast = (fun (a,e1) -> let (decl,e1,b) = aux e1 in (decl, E_internal_cast (a,e1),b))
    ; e_internal_exp = (fun a -> ((fun x -> x), E_internal_exp a,false))
    ; e_internal_exp_user = (fun (a1,a2) -> ((fun x -> x), E_internal_exp_user (a1,a2),false))
    ; e_internal_let =
        (fun ((decl1,lexp), e2, e3) ->
         let (decl2,e2,b2) = aux e2 in
         let (decl3,e3,b3) = aux e3 in
         (compose decl1 (compose decl2 decl3), E_internal_let (lexp,e2,e3), b2 || b3)
        )
    ; e_aux = 
        (fun ((decl,e,b),((_,typ) as a : ('a annot))) ->
         match typ with
         | Base (_,_,_, {effect = Eset effs}, _) ->
            (decl (E_aux (e,a)),
             List.exists (function BE_aux (BE_undef,_)
                                 | BE_aux (BE_unspec,_) -> false | _ -> true) effs)
         | Base (_,_,_, {effect = Evar _},_) ->
            failwith "Effect_var not supported."
         | Overload (_,_,_) ->
            failwith "Overload not supported."
         | NoTyp -> (decl (E_aux (e,a)),false)
        )
    ; lEXP_id = (fun id -> ((fun x -> x), LEXP_id id))
    ; lEXP_memory =
        (fun (id,es) ->
         let (decl,es,_) = list_aux es in
         (decl, LEXP_memory (id,es))
        )
    ; lEXP_cast = (fun (typ,id) -> ((fun x -> x), LEXP_cast (typ,id)))
    ; lEXP_vector =
        (fun ((decl1,lexp),e2) ->
         let (decl2,e2,_) = aux e2 in
         (compose decl1 decl2, LEXP_vector (lexp,e2))
        )
    ; lEXP_vector_range = 
        (fun ((decl1,lexp),e2,e3) ->
         let (decl2,e2,_) = aux e2 in
         let (decl3,e3,_) = aux e3 in
         (compose decl1 (compose decl2 decl3), LEXP_vector_range (lexp,e2,e3))
        )
    ; lEXP_field = (fun ((decl,lexp),id) -> (decl, LEXP_field (lexp,id)))
    ; lEXP_aux = (fun ((decl,lexp),a) -> (decl,LEXP_aux (lexp,a)))
    ; fE_Fexp = (fun (id,e) -> let (decl,e,b) = aux e in (decl,FE_Fexp (id,e),b))
    ; fE_aux = (fun ((decl,fexp,b),annot) -> (decl, FE_aux (fexp,annot),b))
    ; fES_Fexps =
        (fun (fexps,bool) ->
         let (decl,fexps,b) =
           List.fold_left
             (fun (acc_decls,acc_fexps,acc_b) (decl,fexp,b) ->
              (compose acc_decls decl, acc_fexps @ [fexp], acc_b || b))
             ((fun x -> x), [], false) fexps in
         (decl, FES_Fexps (fexps,bool), b)
        )
    ; fES_aux = (fun ((decl,fexp,b),a) -> (decl, FES_aux (fexp,a), b))
    ; def_val_empty = ((fun x -> x), Def_val_empty,false)
    ; def_val_dec = (fun e -> let (decl,e,b) = aux e in (decl, Def_val_dec e, b))
    ; def_val_aux = (fun ((decl,defval,b),a) -> (decl, Def_val_aux (defval,a), b))
    ; pat_exp = (fun (pat,(e,b)) -> (Pat_exp (pat,e),b))
    ; pat_aux = (fun ((pexp,b),a) -> (Pat_aux (pexp,a),b))
    ; lB_val_explicit = (fun (typ,pat,(e,b)) -> (LB_val_explicit (typ,pat,e),b))
    ; lB_val_implicit = (fun (pat,(e,b)) -> (LB_val_implicit (pat,e),b))
    ; lB_aux = (fun ((lb,b),a) -> (LB_aux (lb,a),b))
    ; pat_alg = id_pat_alg
    } exp
