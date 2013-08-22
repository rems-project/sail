open Ast

open Format

let rec list_format (sep : string) (fmt : 'a -> string) (ls : 'a list) : string =
  match ls with
  | [] -> ""
  | [a] -> fmt a
  | a::ls -> (fmt a) ^ sep ^ (list_format sep fmt ls)

let rec list_pp i_format l_format =
  fun ppf l ->
    match l with
    | [] -> fprintf ppf ""
    | [i] -> fprintf ppf "%a" l_format i
    | i::is -> fprintf ppf "%a%a" i_format i (list_pp i_format l_format) is

let kwd ppf s = fprintf ppf "%s" s
let base ppf s = fprintf ppf "%s" s

let parens is_atomic v base =
  if (is_atomic v) then base
  else "(" ^ base ^ ")"

let pp_parens is_atomic format =
  fun ppf v -> 
    if (is_atomic v)
    then format ppf v
    else fprintf ppf "%a %a %a" kwd "(" format v kwd ")"

let pp_format_id (Id_aux(i,_)) =
  match i with
  | Id(i) -> i
  | DeIid(x) -> "(:" ^ x ^ ")"

let pp_id ppf id = base ppf (pp_format_id id)

let pp_format_bkind (BK_aux(k,_)) =
  match k with
  | BK_type -> "Type"
  | BK_nat -> "Nat"
  | BK_order -> "Order"
  | BK_effects -> "Effects"

let pp_bkind ppf bk = base ppf (pp_format_bkind bk)

let pp_format_kind (K_aux(K_kind(klst),_)) = 
  list_format " -> " pp_format_bkind klst

let pp_kind ppf k = base ppf (pp_format_kind k)

let is_atomic_typ (Typ_aux(t,_)) =
  match t with
  | Typ_var _ | Typ_tup _ -> true
  | _ -> false
let is_atomic_nexp (Nexp_aux(n,_)) =
  match n with
  | Nexp_id _ | Nexp_constant _ | Nexp_exp _ -> true
  | _ -> false
 
let rec pp_format_typ (Typ_aux(t,_)) =
  match t with
  | Typ_var(id) -> pp_format_id id
  | Typ_wild -> "_"
  | Typ_fn(arg,ret,efct) -> "(" ^ (parens is_atomic_typ arg (pp_format_typ arg)) ^ " -> " ^ 
                            (parens is_atomic_typ ret (pp_format_typ ret)) ^ " " ^
                            (pp_format_effects efct) ^ ")"
  | Typ_tup(typs) -> "(" ^ (list_format " * " pp_format_typ typs) ^ ")"
  | Typ_app(id,args) -> "(" ^ (pp_format_id id) ^ " " ^ (list_format " " pp_format_typ_arg args) ^ ")"
and pp_format_nexp (Nexp_aux(n,_)) = 
  match n with
  | Nexp_id(id) -> pp_format_id id
  | Nexp_constant(i) -> string_of_int i
  | Nexp_sum(n1,n2) -> "(" ^ (pp_format_nexp n1) ^ " + " ^ (pp_format_nexp n2) ^ ")"
  | Nexp_times(n1,n2) -> "(" ^  (pp_format_nexp n1) ^ " * " ^ (pp_format_nexp n2) ^ ")"
  | Nexp_exp(n1) -> "2** (" ^ (pp_format_nexp n1) ^ ")"
and pp_format_ord (Ord_aux(o,_)) = 
  match o with
  | Ord_id(id) -> pp_format_id id
  | Ord_inc -> "inc"
  | Ord_dec -> "dec"  
and pp_format_effects (Effects_aux(e,_)) =
  match e with
  | Effects_var(id) -> "effect " ^ pp_format_id id
  | Effects_set(efcts) ->
    if (efcts = []) 
    then "pure"
    else "effect {" ^
      (list_format "," 
         (fun (Effect_aux(e,l)) ->
	   match e with
	   | Effect_rreg -> "rreg"
	   | Effect_wreg -> "wreg"
	   | Effect_rmem -> "rmem"
	   | Effect_wmem -> "wmem"
	   | Effect_undef -> "undef"
	   | Effect_unspec -> "unspec"
	   | Effect_nondet -> "nondet")
	 efcts) ^ " }"
and pp_format_typ_arg (Typ_arg_aux(t,_)) = 
  match t with
  | Typ_arg_typ(t) -> pp_format_typ t
  | Typ_arg_nexp(n) -> pp_format_nexp n
  | Typ_arg_order(o) -> pp_format_ord o
  | Typ_arg_effects(e) -> pp_format_effects e

let pp_typ ppf t = base ppf (pp_format_typ t)
let pp_nexp ppf n = base ppf (pp_format_nexp n)
let pp_ord ppf o = base ppf (pp_format_ord o)
let pp_effects ppf e = base ppf (pp_format_effects e)

let pp_format_nexp_constraint (NC_aux(nc,_)) =
  match nc with
  | NC_fixed(n1,n2) -> pp_format_nexp n1 ^ " = " ^ pp_format_nexp n2
  | NC_bounded_ge(n1,n2) -> pp_format_nexp n1 ^ " >= " ^ pp_format_nexp n2
  | NC_bounded_le(n1,n2) -> pp_format_nexp n1 ^ " <= " ^ pp_format_nexp n2
  | NC_nat_set_bounded(id,bounds) -> 
    pp_format_id id ^
      " In {" ^
      list_format ", " string_of_int bounds ^
      "}"

let pp_nexp_constraint ppf nc = base ppf (pp_format_nexp_constraint nc)

let pp_format_qi (QI_aux(qi,_)) =
  match qi with
  | QI_const(n_const) -> pp_format_nexp_constraint n_const
  | QI_id(KOpt_aux(ki,_)) ->
    (match ki with
    | KOpt_none(id) -> pp_format_id id
    | KOpt_kind(k,id) -> pp_format_kind k ^ " " ^ pp_format_id id)

let pp_qi ppf qi = base ppf (pp_format_qi qi)

let pp_format_typquant (TypQ_aux(tq,_)) =
  match tq with
  | TypQ_no_forall -> ""
  | TypQ_tq(qlist) ->
    "forall " ^ 
    (list_format ", " pp_format_qi qlist) ^
    ". "

let pp_typquant ppf tq = base ppf (pp_format_typquant tq)

let pp_format_typscm (TypSchm_aux(TypSchm_ts(tq,t),_)) =
  (pp_format_typquant tq) ^ pp_format_typ t
 
let pp_typscm ppf ts = base ppf (pp_format_typscm ts)

let pp_format_lit (L_aux(l,_)) =
  match l with
  | L_unit -> "()"
  | L_zero -> "0"
  | L_one -> "1"
  | L_true -> "true"
  | L_false -> "false"
  | L_num(i) -> string_of_int i
  | L_hex(n) | L_bin(n) -> n
  | L_string(s) -> "\"" ^ s ^ "\"" 

let pp_lit ppf l = base ppf (pp_format_lit l)

let rec pp_format_pat (P_aux(p,l)) =
  match p with
  | P_lit(lit) -> pp_format_lit lit
  | P_wild -> "_"
  | P_id(id) -> pp_format_id id
  | P_as(pat,id) -> "(" ^ pp_format_pat pat ^ " as " ^ pp_format_id id ^ ")"
  | P_typ(typ,pat) -> "<" ^ pp_format_typ typ ^ "> " ^ pp_format_pat pat
  | P_app(id,pats) -> pp_format_id id ^ "(" ^
                      list_format ", " pp_format_pat pats ^ ")"
  | P_record(fpats,_) -> "{" ^
                       list_format "; " (fun (FP_aux(FP_Fpat(id,fpat),_)) -> 
			                  pp_format_id id ^ " = " ^ pp_format_pat fpat) fpats
                       ^ "}"
  | P_vector(pats) -> "[" ^ list_format "; " pp_format_pat pats ^ "]"
  | P_vector_indexed(ipats) ->
    "[" ^ list_format "; " (fun (i,p) -> string_of_int i ^ " = " ^ pp_format_pat p) ipats ^ "]"
  | P_vector_concat(pats) -> list_format " ^ " pp_format_pat pats
  | P_tup(pats) -> "(" ^ (list_format ", " pp_format_pat pats) ^ ")"
  | P_list(pats) -> "[|" ^ (list_format "; " pp_format_pat pats) ^ "|]"

let pp_pat ppf p = base ppf (pp_format_pat p)

let rec pp_let ppf (LB_aux(lb,_)) =
  match lb with
  | LB_val_explicit(ts,pat,exp) -> fprintf ppf "@[<0>%a %a %a %a@ %a@]" kwd "let" pp_typscm ts pp_pat pat kwd " =" pp_exp exp
  | LB_val_implicit(pat,exp) -> fprintf ppf "@[<0>%a %a %a@ %a@]" kwd "let" pp_pat pat kwd " =" pp_exp exp

(* Need an is_atomic? check and insert parens otherwise *)
and pp_exp ppf (E_aux(e,_)) = 
  match e with
  | E_block(exps) -> fprintf ppf "@[<0>%a %a@ %a@]" 
                                 kwd "{" 
                                 (list_pp pp_semi_exp pp_exp) exps
                                 kwd "}"
  | E_id(id) -> pp_id ppf id
  | E_lit(lit) -> pp_lit ppf lit
  | E_cast(typ,exp) -> fprintf ppf "@[<0>%a%a%a %a@]" kwd "<" pp_typ typ kwd ">" pp_exp exp 
  | E_app(f,args) -> fprintf ppf "@[<0>%a %a@]" pp_exp f (list_pp pp_exp pp_exp) args
  | E_app_infix(l,op,r) -> fprintf ppf "@[<0>%a %a %a@]" pp_exp l pp_id op pp_exp r
  | E_tuple(exps) -> fprintf ppf "@[<0>%a %a %a@]" kwd "(" (list_pp pp_comma_exp pp_exp) exps kwd ")"
  | E_if(c,t,e) -> fprintf ppf "@[<0> %a %a @[<1> %a %a@] @[<1> %a@ %a@]@]" kwd "if " pp_exp c kwd "then" pp_exp t kwd "else" pp_exp e
  | E_for(id,exp1,exp2,exp3,exp4) ->
    fprintf ppf "@[<0> %a %a %a %a %a %a %a %a@ @[<1> %a @] @]" 
      kwd "foreach " pp_id id kwd " from " pp_exp exp1 kwd " to " pp_exp exp2 kwd "by " pp_exp exp3 pp_exp exp4
  | E_vector(exps) -> fprintf ppf "@[<0> %a %a %a @]" kwd "[" (list_pp pp_comma_exp pp_exp) exps kwd "]"
  | E_vector_indexed(iexps) -> 
    let iformat ppf (i,e) = fprintf ppf "@[<1>%i %a %a %a@]" i kwd " = " pp_exp e kwd "," in
    let lformat ppf (i,e) = fprintf ppf "@[<1>%i %a %a @]" i kwd " = " pp_exp e in
    fprintf ppf "@[<0> %a %a %a @]" kwd "[" (list_pp iformat lformat) iexps kwd "]"
  | E_vector_access(v,e) -> fprintf ppf "@[<0>%a %a %a %a@]" pp_exp v kwd "[" pp_exp e kwd "]"
  | E_vector_subrange(v,e1,e2) -> fprintf ppf "@[<0> %a %a %a %a %a %a@]" pp_exp v kwd "[" pp_exp e1 kwd " : " pp_exp e1 kwd "]"
  | E_vector_update(v,e1,e2) -> 
    fprintf ppf "@[<0> %a %a %a %a %a %a %a@]" kwd "[" pp_exp v kwd "with" pp_exp e1 kwd " = " pp_exp e2 kwd "]"
  | E_vector_update_subrange(v,e1,e2,e3) -> 
    fprintf ppf "@[<0>%a%a %a %a %a %a %a %a %a@]" kwd "[" pp_exp v kwd "with" pp_exp e1 kwd ":" pp_exp e2 kwd " = " pp_exp e3 kwd "]"
  | E_list(exps) -> fprintf ppf "@[<0> %a %a %a@]" kwd "[|" (list_pp pp_comma_exp pp_exp) exps kwd "|]"
  | E_cons(e1,e2) -> fprintf ppf "@[<0> %a %a %a@]" pp_exp e1 kwd ":" pp_exp e2
  | E_record(FES_aux(FES_Fexps(fexps,_),_)) -> fprintf ppf "@[<0> %a %a %a@]" kwd "{" (list_pp pp_semi_fexp pp_fexp) fexps kwd "}"
  | E_record_update(exp,(FES_aux(FES_Fexps(fexps,_),_))) ->
    fprintf ppf "@[<0> %a %a %a %a %a @]" kwd "{" pp_exp exp kwd " with " (list_pp pp_semi_fexp pp_fexp) fexps kwd "}"
  | E_field(fexp,id) -> fprintf ppf "@[<0> %a%a%a@]" pp_exp fexp kwd "." pp_id id
  | E_case(exp,pexps) -> fprintf ppf "@[<0> %a %a %a %a %a@]" kwd "switch " pp_exp exp kwd "{" (list_pp pp_case pp_case) pexps kwd "}"
  | E_let(leb,exp) -> fprintf ppf "@[<0> %a@ %a@ %a @]" pp_let leb kwd "in" pp_exp exp
  | E_assign(lexp,exp) -> fprintf ppf "@[<0> %a %a %a@]" pp_lexp lexp kwd " := " pp_exp exp

and pp_semi_exp ppf e = fprintf ppf "@[<1>%a %a@]" pp_exp e kwd ";"

and pp_comma_exp ppf e = fprintf ppf "@[<1>%a %a@]" pp_exp e kwd ","

and pp_fexp ppf (FE_aux(FE_Fexp(id,exp),_)) = fprintf ppf "@[<1>%a %a %a@]" pp_id id kwd " = " pp_exp exp
and pp_semi_fexp ppf fexp = fprintf ppf "@[<1>%a %a@]" pp_fexp fexp kwd ";"

and pp_case ppf (Pat_aux(Pat_exp(pat,exp),_)) = fprintf ppf "@[<1>%a %a@ @[<1> %a @] @]" pp_pat pat kwd "-> " pp_exp exp 

and pp_lexp ppf (LEXP_aux(lexp,_)) =
  match lexp with
  | LEXP_id(id) -> pp_id ppf id
  | LEXP_vector(v,exp) -> fprintf ppf "@[%a %a %a %a@]" pp_lexp v kwd "[" pp_exp exp kwd "]"
  | LEXP_vector_range(v,e1,e2) -> fprintf ppf "@[%a %a %a %a %a %a@]" pp_lexp v kwd "[" pp_exp e1 kwd ":" pp_exp e2 kwd "]"
  | LEXP_field(v,id) -> fprintf ppf "@[%a%a%a@]" pp_lexp v kwd "." pp_id id

let pp_default ppf (DT_aux(df,_)) =
  match df with
  | DT_kind(bk,id) -> fprintf ppf "@[<0>%a %a %a@]@\n" kwd "default" pp_bkind bk pp_id id
  | DT_typ(ts,id) -> fprintf ppf "@[<0>%a %a %a@]@\n" kwd "default" pp_typscm ts pp_id id

let pp_spec ppf (VS_aux(VS_val_spec(ts,id),_)) =
  fprintf ppf "@[<0>%a %a %a@]@\n" kwd "val" pp_typscm ts pp_id id

let pp_namescm ppf (Name_sect_aux(ns,_)) =
  match ns with
  | Name_sect_none -> fprintf ppf ""
  | Name_sect_some(s) -> fprintf ppf "[%a \"%s\"]" kwd "name =" s

let rec pp_range ppf (BF_aux(r,_)) =
  match r with 
  | BF_single(i) -> fprintf ppf "%i" i
  | BF_range(i1,i2) -> fprintf ppf "%i .. %i" i1 i2
  | BF_concat(ir1,ir2) -> fprintf ppf "%a %a %a" pp_range ir1 kwd ", " pp_range ir2

let pp_typdef ppf (TD_aux(td,_)) =
  match td with
  | TD_abbrev(id,namescm,typschm) -> 
    fprintf ppf "@[<0>%a %a %a %a %a@]@\n" kwd "typedef" pp_id id pp_namescm namescm kwd "=" pp_typscm typschm
  | TD_record(id,nm,typq,fs,_) -> 
    let f_pp ppf (typ,id) =
      fprintf ppf "@[<1>%a %a%a@]" pp_typ typ pp_id id kwd ";" in
    fprintf ppf "@[<0>%a %a %a %a %a %a %a %a@[<1>%a@] %a]@\n" 
      kwd "typedef" pp_id id pp_namescm nm kwd "=" kwd "const" kwd "struct" pp_typquant typq kwd "{" (list_pp f_pp f_pp) fs kwd "}"
  | TD_variant(id,nm,typq,ar,_) ->
    let a_pp ppf (typ,id) = 
      fprintf ppf "@[<1>%a %a%a@]" pp_typ typ pp_id id kwd ";" in
    fprintf ppf "@[<0>%a %a %a %a %a %a %a %a@[<1>%a@] %a]@\n" 
      kwd "typedef" pp_id id pp_namescm nm kwd "=" kwd "const" kwd "union" pp_typquant typq kwd "{" (list_pp a_pp a_pp) ar kwd "}"
  | TD_enum(id,ns,enums,_) ->
    let pp_id_semi ppf id = fprintf ppf "%a%a " pp_id id kwd ";" in
    fprintf ppf "@[<0>%a %a %a %a %a %a%a %a@]@\n"
      kwd "typedef" pp_id id pp_namescm ns kwd "=" kwd "enumerate" kwd "{" (list_pp pp_id_semi pp_id) enums kwd "}"
  | TD_register(id,n1,n2,rs) -> 
    let pp_rid ppf (r,id) = fprintf ppf "%a %a %a%a " pp_range r kwd ":" pp_id id kwd ";" in
    let pp_rids = (list_pp pp_rid pp_rid) in
    fprintf ppf "@[<0>%a %a %a %a %a %a %a %a %a %a %a %a%a@]@\n"
     kwd "typedef" pp_id id kwd "=" kwd "register" kwd "bits" kwd "[" pp_nexp n1 kwd ":" pp_nexp n2 kwd "]" kwd "{" pp_rids rs kwd "}"

let pp_rec ppf (Rec_aux(r,_)) =
  match r with
  | Rec_nonrec -> fprintf ppf ""
  | Rec_rec -> fprintf ppf "rec "

let pp_tannot_opt ppf (Typ_annot_opt_aux(t,_)) =
  match t with
  | Typ_annot_opt_some(tq,typ) -> fprintf ppf "%a %a " pp_typquant tq pp_typ typ

let pp_effects_opt ppf (Effects_opt_aux(e,_)) =
  match e with
  | Effects_opt_pure -> fprintf ppf ""
  | Effects_opt_effects e -> pp_effects ppf e

let pp_funcl ppf (FCL_aux(FCL_Funcl(id,pat,exp),_)) =
  fprintf ppf "@[<0>%a %a %a @[<1>%a@] @]@\n" pp_id id pp_pat pat kwd "=" pp_exp exp 

let pp_fundef ppf (FD_aux(FD_function(r, typa, efa, fcls),_)) =
  let pp_funcls ppf funcl = fprintf ppf "%a %a" kwd "and" pp_funcl funcl in
  fprintf ppf "@[<0>%a %a%a%a%a@ @[<1>%a@] @]@\n" 
    kwd "function" pp_rec r pp_tannot_opt typa pp_effects_opt efa pp_funcl (List.hd fcls) (list_pp pp_funcls pp_funcls) (List.tl fcls)

let pp_def ppf (DEF_aux(d,(l,_))) =
  match d with
  | DEF_default(df) -> pp_default ppf df
  | DEF_spec(v_spec) -> pp_spec ppf v_spec
  | DEF_type(t_def) -> pp_typdef ppf t_def
  | DEF_fundef(f_def) -> pp_fundef ppf f_def
  | DEF_val(lbind) -> pp_let ppf lbind
  | DEF_reg_dec(typ,id) -> fprintf ppf "@[<0>%a %a %a@]@\n" kwd "register" pp_typ typ pp_id id
  | _ -> raise (Reporting_basic.err_unreachable l "initial_check didn't remove all scattered Defs")

let pp_defs ppf (Defs(defs)) =
  fprintf ppf "@[%a@]@\n" (list_pp pp_def pp_def) defs
