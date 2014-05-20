open Type_internal
open Ast
open Format

let is_atomic_typ (Typ_aux(t,_)) =
  match t with
  | Typ_id _ | Typ_var _ | Typ_tup _ -> true
  | _ -> false
let is_atomic_nexp (Nexp_aux(n,_)) =
  match n with
  | Nexp_var _ | Nexp_constant _ | Nexp_exp _ -> true
  | _ -> false
 
let is_atomic_pat (P_aux(p,l)) =
  match p with
  | P_lit(_) | P_wild | P_id(_) | P_as _ | P_typ _ -> true
  | P_app(_,pats) -> if (pats = []) then true else false
  | P_record(_,_) | P_vector(_) | P_vector_indexed(_) | P_tup(_) | P_list(_) -> true
  | _ -> false

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

let parens is_atomic to_base v =
  if (is_atomic v) then to_base v
  else "(" ^ to_base v ^ ")"

let pp_parens is_atomic format =
  fun ppf v -> 
    if (is_atomic v)
    then format ppf v
    else fprintf ppf "%a %a %a" kwd "(" format v kwd ")"

(****************************************************************************
 * source to source pretty printer
****************************************************************************)

let pp_format_id (Id_aux(i,_)) =
  match i with
  | Id(i) -> i
  | DeIid(x) -> "(deinfix " ^ x ^ ")"

let pp_id ppf id = base ppf (pp_format_id id)

let pp_format_var (Kid_aux(Var v,_)) = v

let pp_var ppf var = base ppf (pp_format_var var)

let pp_format_bkind (BK_aux(k,_)) =
  match k with
  | BK_type -> "Type"
  | BK_nat -> "Nat"
  | BK_order -> "Order"
  | BK_effect -> "Effect"

let pp_bkind ppf bk = base ppf (pp_format_bkind bk)

let pp_format_kind (K_aux(K_kind(klst),_)) = 
  list_format " -> " pp_format_bkind klst

let pp_kind ppf k = base ppf (pp_format_kind k)

let rec pp_format_typ (Typ_aux(t,_)) =
  match t with
  | Typ_id(id) -> pp_format_id id
  | Typ_var(var) -> pp_format_var var
  | Typ_wild -> "_"
  | Typ_fn(arg,ret,efct) -> "(" ^ (parens is_atomic_typ pp_format_typ arg) ^ " -> " ^ 
                            (parens is_atomic_typ pp_format_typ ret) ^ " effect " ^ 
                            (pp_format_effects efct) ^ ")"
  | Typ_tup(typs) -> "(" ^ (list_format " * " pp_format_typ typs) ^ ")"
  | Typ_app(id,args) -> (pp_format_id id) ^ "<" ^ (list_format ", " pp_format_typ_arg args) ^ ">"
and pp_format_nexp (Nexp_aux(n,_)) = 
  match n with
  | Nexp_var(var) -> pp_format_var var
  | Nexp_constant(i) -> string_of_int i
  | Nexp_sum(n1,n2) -> "(" ^ (pp_format_nexp n1) ^ " + " ^ (pp_format_nexp n2) ^ ")"
  | Nexp_times(n1,n2) -> "(" ^  (pp_format_nexp n1) ^ " * " ^ (pp_format_nexp n2) ^ ")"
  | Nexp_exp(n1) -> "2** (" ^ (pp_format_nexp n1) ^ ")"
  | Nexp_neg(n1) -> "(* - *)" ^ (pp_format_nexp n1)
and pp_format_ord (Ord_aux(o,_)) = 
  match o with
  | Ord_var(var) -> pp_format_var var
  | Ord_inc -> "inc"
  | Ord_dec -> "dec"  
and pp_format_effects (Effect_aux(e,_)) =
  match e with
  | Effect_var(var) -> pp_format_var var
  | Effect_set(efcts) ->
    if (efcts = []) 
    then "pure"
    else "{" ^
      (list_format "," 
         (fun (BE_aux(e,l)) ->
	   match e with
	   | BE_rreg -> "rreg"
	   | BE_wreg -> "wreg"
	   | BE_rmem -> "rmem"
	   | BE_wmem -> "wmem"
	   | BE_undef -> "undef"
	   | BE_unspec -> "unspec"
	   | BE_nondet -> "nondet")
	 efcts) ^ " }"
and pp_format_typ_arg (Typ_arg_aux(t,_)) = 
  match t with
  | Typ_arg_typ(t) -> pp_format_typ t
  | Typ_arg_nexp(n) -> pp_format_nexp n
  | Typ_arg_order(o) -> pp_format_ord o
  | Typ_arg_effect(e) -> pp_format_effects e

let pp_typ ppf t = base ppf (pp_format_typ t)
let pp_nexp ppf n = base ppf (pp_format_nexp n)
let pp_ord ppf o = base ppf (pp_format_ord o)
let pp_effects ppf e = base ppf (pp_format_effects e)

let pp_format_nexp_constraint (NC_aux(nc,_)) =
  match nc with
  | NC_fixed(n1,n2) -> pp_format_nexp n1 ^ " = " ^ pp_format_nexp n2
  | NC_bounded_ge(n1,n2) -> pp_format_nexp n1 ^ " >= " ^ pp_format_nexp n2
  | NC_bounded_le(n1,n2) -> pp_format_nexp n1 ^ " <= " ^ pp_format_nexp n2
  | NC_nat_set_bounded(var,bounds) -> 
    pp_format_var var ^
      " IN {" ^
      list_format ", " string_of_int bounds ^
      "}"

let pp_nexp_constraint ppf nc = base ppf (pp_format_nexp_constraint nc)

let pp_format_qi (QI_aux(qi,_)) =
  match qi with
  | QI_const(n_const) -> pp_format_nexp_constraint n_const
  | QI_id(KOpt_aux(ki,_)) ->
    (match ki with
    | KOpt_none(var) -> pp_format_var var
    | KOpt_kind(k,var) -> pp_format_kind k ^ " " ^ pp_format_var var)

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
  | L_zero -> "bitzero"
  | L_one -> "bitone"
  | L_true -> "true"
  | L_false -> "false"
  | L_num(i) -> string_of_int i
  | L_hex(n) -> "0x" ^ n
  | L_bin(n) -> "0b" ^ n
  | L_undef -> "undefined"
  | L_string(s) -> "\"" ^ s ^ "\"" 

let pp_lit ppf l = base ppf (pp_format_lit l)

let rec pp_format_pat (P_aux(p,l)) =
  match p with
  | P_lit(lit) -> pp_format_lit lit
  | P_wild -> "_"
  | P_id(id) -> pp_format_id id
  | P_as(pat,id) -> "(" ^ pp_format_pat pat ^ " as " ^ pp_format_id id ^ ")"
  | P_typ(typ,pat) -> "(" ^ pp_format_typ typ ^ ") " ^ pp_format_pat pat
  | P_app(id,pats) -> if (pats = [])
                      then pp_format_id id 
                      else pp_format_id id ^ "(" ^
                      list_format ", " (parens is_atomic_pat pp_format_pat) pats ^ ")"
  | P_record(fpats,_) -> "{" ^
                       list_format "; " (fun (FP_aux(FP_Fpat(id,fpat),_)) -> 
			                  pp_format_id id ^ " = " ^ pp_format_pat fpat) fpats
                       ^ "}"
  | P_vector(pats) -> "[" ^ list_format "; " (parens is_atomic_pat pp_format_pat) pats ^ "]"
  | P_vector_indexed(ipats) ->
    "[" ^ list_format "; " (fun (i,p) -> string_of_int i ^ " = " ^ pp_format_pat p) ipats ^ "]"
  | P_vector_concat(pats) -> list_format " ^ " pp_format_pat pats
  | P_tup(pats) -> "(" ^ (list_format ", " (parens is_atomic_pat pp_format_pat) pats) ^ ")"
  | P_list(pats) -> "[||" ^ (list_format "; " (parens is_atomic_pat pp_format_pat) pats) ^ "||]"

let pp_pat ppf p = base ppf (pp_format_pat p)
let pp_pat_atomic ppf p = base ppf (parens is_atomic_pat pp_format_pat p)

let rec pp_let ppf (LB_aux(lb,_)) =
  match lb with
  | LB_val_explicit(ts,pat,exp) -> fprintf ppf "@[<0>%a %a %a %a@ %a@]" kwd "let" pp_typscm ts pp_pat_atomic pat kwd " =" pp_exp exp
  | LB_val_implicit(pat,exp) -> fprintf ppf "@[<0>%a %a %a@ %a@]" kwd "let" pp_pat_atomic pat kwd " =" pp_exp exp

(* Need an is_atomic? check and insert parens otherwise *)
and pp_exp ppf (E_aux(e,(_,annot))) = 
  match e with
  | E_block(exps) -> fprintf ppf "@[<0>%a%a@ %a@]" 
                                 kwd "{" 
                                 (list_pp pp_semi_exp pp_exp) exps
                                 kwd "}"
  | E_id(id) -> pp_id ppf id
  | E_lit(lit) -> pp_lit ppf lit
  | E_cast(typ,exp) -> fprintf ppf "@[<0>%a%a%a %a@]" kwd "(" pp_typ typ kwd ")" pp_exp exp 
  | E_internal_cast((_,NoTyp),e) -> pp_exp ppf e
  | E_internal_cast((_,Base((_,t),_,_,_)), (E_aux(_,(_,eannot)) as exp)) ->
    (match t.t,eannot with
      | Tapp("vector",[TA_nexp n1;_;_;_]),Base((_,{t=Tapp("vector",[TA_nexp n2;_;_;_])}),_,_,_) ->
	if nexp_eq n1 n2 
	then pp_exp ppf exp
	else 
	  fprintf ppf "@[<0>%a%a%a %a@]" kwd "(" pp_typ (t_to_typ t) kwd ")" pp_exp exp
      | _ -> fprintf ppf "@[<0>%a%a%a %a@]" kwd "(" pp_typ (t_to_typ t) kwd ")" pp_exp exp)
  | E_app(f,args) -> fprintf ppf "@[<0>%a(%a)@]" pp_id f (list_pp pp_comma_exp pp_exp) args 
  | E_app_infix(l,op,r) -> fprintf ppf "@[<0>%a %a %a@]" pp_exp l pp_id op pp_exp r
  | E_tuple(exps) -> fprintf ppf "@[<0>%a %a %a@]" kwd "(" (list_pp pp_comma_exp pp_exp) exps kwd ")"
  | E_if(c,t,e) -> fprintf ppf "@[<0>%a %a @[<1>%a %a@] @[<1>%a@ %a@]@]" kwd "if " pp_exp c kwd "then" pp_exp t kwd "else" pp_exp e
  | E_for(id,exp1,exp2,exp3,order,exp4) ->
    fprintf ppf "@[<0> %a %a (%a %a %a %a %a %a %a %a)@ @[<1>%a@]@]" 
      kwd "foreach " pp_id id kwd "from " pp_exp exp1 kwd " to " pp_exp exp2 kwd "by " pp_exp exp3 kwd "in" pp_ord order pp_exp exp4
  | E_vector(exps) -> fprintf ppf "@[<0>%a%a%a@]" kwd "[" (list_pp pp_comma_exp pp_exp) exps kwd "]"
  | E_vector_indexed(iexps,default) -> 
    let iformat ppf (i,e) = fprintf ppf "@[<1>%i%a %a%a@]" i kwd " = " pp_exp e kwd "," in
    let lformat ppf (i,e) = fprintf ppf "@[<1>%i%a %a@]" i kwd " = " pp_exp e in
    fprintf ppf "@[<0> %a%a%a@]" kwd "[" (list_pp iformat lformat) iexps kwd "]"
  | E_vector_access(v,e) -> fprintf ppf "@[<0>%a%a%a%a@]" pp_exp v kwd "[" pp_exp e kwd "]"
  | E_vector_subrange(v,e1,e2) -> fprintf ppf "@[<0>%a%a%a%a%a%a@]" pp_exp v kwd "[" pp_exp e1 kwd " : " pp_exp e1 kwd "]"
  | E_vector_update(v,e1,e2) -> 
    fprintf ppf "@[<0>%a%a %a %a%a%a%a@]" kwd "[" pp_exp v kwd "with" pp_exp e1 kwd " = " pp_exp e2 kwd "]"
  | E_vector_update_subrange(v,e1,e2,e3) -> 
    fprintf ppf "@[<0>%a%a %a %a %a %a %a %a %a@]" kwd "[" pp_exp v kwd "with" pp_exp e1 kwd ":" pp_exp e2 kwd " = " pp_exp e3 kwd "]"
  | E_list(exps) -> fprintf ppf "@[<0>%a%a%a@]" kwd "[||" (list_pp pp_comma_exp pp_exp) exps kwd "||]"
  | E_cons(e1,e2) -> fprintf ppf "@[<0>%a%a%a@]" pp_exp e1 kwd ":" pp_exp e2
  | E_record(FES_aux(FES_Fexps(fexps,_),_)) -> fprintf ppf "@[<0>%a%a%a@]" kwd "{" (list_pp pp_semi_fexp pp_fexp) fexps kwd "}"
  | E_record_update(exp,(FES_aux(FES_Fexps(fexps,_),_))) ->
    fprintf ppf "@[<0>%a%a %a %a%a@]" kwd "{" pp_exp exp kwd " with " (list_pp pp_semi_fexp pp_fexp) fexps kwd "}"
  | E_field(fexp,id) -> fprintf ppf "@[<0>%a%a%a@]" pp_exp fexp kwd "." pp_id id
  | E_case(exp,pexps) -> fprintf ppf "@[<0>%a %a %a %a %a@]" kwd "switch " pp_exp exp kwd "{" (list_pp pp_case pp_case) pexps kwd "}"
  | E_let(leb,exp) -> fprintf ppf "@[<0>%a@ %a@ %a@]" pp_let leb kwd "in" pp_exp exp
  | E_assign(lexp,exp) -> fprintf ppf "@[<0>%a%a%a@]" pp_lexp lexp kwd " := " pp_exp exp
  (* XXX missing cases *)
  | E_internal_cast ((_, Overload (_, _)), _) | E_internal_exp _ -> assert false


and pp_semi_exp ppf e = fprintf ppf "@[<1>%a%a@]" pp_exp e kwd ";"

and pp_comma_exp ppf e = fprintf ppf "@[<1>%a%a@]" pp_exp e kwd ","

and pp_fexp ppf (FE_aux(FE_Fexp(id,exp),_)) = fprintf ppf "@[<1>%a %a %a@]" pp_id id kwd " = " pp_exp exp
and pp_semi_fexp ppf fexp = fprintf ppf "@[<1>%a%a@]" pp_fexp fexp kwd ";"

and pp_case ppf (Pat_aux(Pat_exp(pat,exp),_)) = 
  fprintf ppf "@[<1>%a %a@@[<1>%a@]@]" pp_pat_atomic pat kwd "-> " pp_exp exp 

and pp_lexp ppf (LEXP_aux(lexp,_)) =
  match lexp with
  | LEXP_id(id) -> pp_id ppf id
  | LEXP_memory(id,args) -> fprintf ppf "@[%a(%a)@]" pp_id id (list_pp pp_exp pp_exp) args
  | LEXP_cast(typ,id) -> fprintf ppf "@[(%a) %a@]" pp_typ typ pp_id id
  | LEXP_vector(v,exp) -> fprintf ppf "@[%a%a%a%a@]" pp_lexp v kwd "[" pp_exp exp kwd "]"
  | LEXP_vector_range(v,e1,e2) -> fprintf ppf "@[%a%a%a%a%a%a@]" pp_lexp v kwd "[" pp_exp e1 kwd ":" pp_exp e2 kwd "]"
  | LEXP_field(v,id) -> fprintf ppf "@[%a%a%a@]" pp_lexp v kwd "." pp_id id

let pp_default ppf (DT_aux(df,_)) =
  match df with
  | DT_kind(bk,var) -> fprintf ppf "@[<0>%a %a %a@]@\n" kwd "default" pp_bkind bk pp_var var
  | DT_typ(ts,id) -> fprintf ppf "@[<0>%a %a %a@]@\n" kwd "default" pp_typscm ts pp_id id

let pp_spec ppf (VS_aux(v,_)) =
  match v with
  | VS_val_spec(ts,id) -> fprintf ppf "@[<0>%a %a %a@]@\n" kwd "val" pp_typscm ts pp_id id
  | VS_extern_spec(ts,id,s) -> fprintf ppf "@[<0>%a %a %a %a %a \"%s\"@]@\n" kwd "val" kwd "extern" pp_typscm ts pp_id id kwd "=" s
  | VS_extern_no_rename(ts,id) -> fprintf ppf "@[<0>%a %a %a %a@]@\n" kwd "val" kwd "extern" pp_typscm ts pp_id id

let pp_namescm ppf (Name_sect_aux(ns,_)) =
  match ns with
  | Name_sect_none -> fprintf ppf ""
  | Name_sect_some(s) -> fprintf ppf "[%a \"%s\"]" kwd "name =" s

let rec pp_range ppf (BF_aux(r,_)) =
  match r with 
  | BF_single(i) -> fprintf ppf "%i" i
  | BF_range(i1,i2) -> fprintf ppf "%i..%i" i1 i2
  | BF_concat(ir1,ir2) -> fprintf ppf "%a%a %a" pp_range ir1 kwd ", " pp_range ir2

let pp_typdef ppf (TD_aux(td,_)) =
  match td with
  | TD_abbrev(id,namescm,typschm) -> 
    fprintf ppf "@[<0>%a %a %a %a %a@]@\n" kwd "typedef" pp_id id pp_namescm namescm kwd "=" pp_typscm typschm
  | TD_record(id,nm,typq,fs,_) -> 
    let f_pp ppf (typ,id) =
      fprintf ppf "@[<1>%a %a%a@]" pp_typ typ pp_id id kwd ";" in
    fprintf ppf "@[<0>%a %a %a%a %a %a %a%a@[<1>%a@]%a@]@\n" 
      kwd "typedef" pp_id id pp_namescm nm kwd "=" kwd "const" kwd "struct" pp_typquant typq kwd "{" (list_pp f_pp f_pp) fs kwd "}"
  | TD_variant(id,nm,typq,ar,_) ->
    let a_pp ppf (Tu_aux(typ_u,_)) = 
      match typ_u with
      | Tu_ty_id(typ,id) -> fprintf ppf "@[<1>%a %a%a@]" pp_typ typ pp_id id kwd ";" 
      | Tu_id(id) -> fprintf ppf "@[<1>%a%a@]" pp_id id kwd ";"
    in
    fprintf ppf "@[<0>%a %a %a %a %a %a %a %a@[<1>%a@] %a@]@\n" 
      kwd "typedef" pp_id id pp_namescm nm kwd "=" kwd "const" kwd "union" pp_typquant typq kwd "{" (list_pp a_pp a_pp) ar kwd "}"
  | TD_enum(id,ns,enums,_) ->
    let pp_id_semi ppf id = fprintf ppf "%a%a " pp_id id kwd ";" in
    fprintf ppf "@[<0>%a %a %a %a %a %a%a %a@]@\n"
      kwd "typedef" pp_id id pp_namescm ns kwd "=" kwd "enumerate" kwd "{" (list_pp pp_id_semi pp_id) enums kwd "}"
  | TD_register(id,n1,n2,rs) -> 
    let pp_rid ppf (r,id) = fprintf ppf "%a%a%a%a " pp_range r kwd ":" pp_id id kwd ";" in
    let pp_rids = (list_pp pp_rid pp_rid) in
    fprintf ppf "@[<0>%a %a %a %a %a %a%a%a%a%a %a%a%a@]@\n"
     kwd "typedef" pp_id id kwd "=" kwd "register" kwd "bits" kwd "[" pp_nexp n1 kwd ":" pp_nexp n2 kwd "]" kwd "{" pp_rids rs kwd "}"

let pp_rec ppf (Rec_aux(r,_)) =
  match r with
  | Rec_nonrec -> fprintf ppf ""
  | Rec_rec -> fprintf ppf "rec "

let pp_tannot_opt ppf (Typ_annot_opt_aux(t,_)) =
  match t with
  | Typ_annot_opt_some(tq,typ) -> fprintf ppf "%a%a " pp_typquant tq pp_typ typ

let pp_effects_opt ppf (Effect_opt_aux(e,_)) =
  match e with
  | Effect_opt_pure -> fprintf ppf "effect pure"
  | Effect_opt_effect e -> fprintf ppf "effect %a" pp_effects e

let pp_funcl ppf (FCL_aux(FCL_Funcl(id,pat,exp),_)) =
  fprintf ppf "%a %a %a @[<1>%a@]@\n" pp_id id pp_pat_atomic pat kwd "=" pp_exp exp 

let pp_fundef ppf (FD_aux(FD_function(r, typa, efa, fcls),_)) =
  let pp_funcls ppf funcl = fprintf ppf "%a %a" kwd "and" pp_funcl funcl in
  fprintf ppf "@[<0>%a %a%a%a @[<1>%a@] @[<1>%a@] @]@\n"
    kwd "function" pp_rec r pp_tannot_opt typa pp_effects_opt efa pp_funcl (List.hd fcls) (list_pp pp_funcls pp_funcls) (List.tl fcls)

let pp_dec ppf (DEC_aux(DEC_reg(typ,id),_)) =
  fprintf ppf "@[<0>register %a %a@]@\n" pp_typ typ pp_id id

let pp_def ppf d =
  match d with
  | DEF_default(df) -> pp_default ppf df
  | DEF_spec(v_spec) -> pp_spec ppf v_spec
  | DEF_type(t_def) -> pp_typdef ppf t_def
  | DEF_fundef(f_def) -> pp_fundef ppf f_def
  | DEF_val(lbind) -> fprintf ppf "@[<0>%a@]@\n" pp_let lbind
  | DEF_reg_dec(dec) -> pp_dec ppf dec
  | _ -> raise (Reporting_basic.err_unreachable Parse_ast.Unknown "initial_check didn't remove all scattered Defs")

let pp_defs ppf (Defs(defs)) =
  fprintf ppf "@[%a@]@\n" (list_pp pp_def pp_def) defs


(****************************************************************************
 * annotated source to Lem ast pretty printer
****************************************************************************)

let rec pp_format_l_lem = function
  | Parse_ast.Unknown -> "Unknown"
  | Parse_ast.Int(s,None) -> "(Int \"" ^ s ^ "\" Nothing)"
  | Parse_ast.Int(s,(Some l)) -> "(Int \"" ^  s ^ "\" (Just " ^ (pp_format_l_lem l) ^ "))"
  | Parse_ast.Range(p1,p2) -> "(Range \"" ^ p1.Lexing.pos_fname ^ "\" " ^
                               (string_of_int p1.Lexing.pos_lnum) ^ " " ^ 
                               (string_of_int (p1.Lexing.pos_cnum - p1.Lexing.pos_bol)) ^ " " ^
                               (string_of_int p2.Lexing.pos_lnum) ^ " " ^
                               (string_of_int (p2.Lexing.pos_cnum - p2.Lexing.pos_bol)) ^ ")"

let pp_lem_l ppf l = base ppf (pp_format_l_lem l)

let pp_format_id_lem (Id_aux(i,l)) =
  "(Id_aux " ^
    (match i with
      | Id(i) -> "(Id \"" ^ i ^ "\")"
      | DeIid(x) -> "(DeIid \"" ^ x ^ "\")") ^ " " ^
   (pp_format_l_lem l) ^ ")"

let pp_lem_id ppf id = base ppf (pp_format_id_lem id)

let pp_format_var_lem (Kid_aux(Var v,l)) = "(Kid_aux (Var \"" ^ v ^ "\") " ^ (pp_format_l_lem l) ^ ")"

let pp_lem_var ppf var = base ppf (pp_format_var_lem var)

let pp_format_bkind_lem (BK_aux(k,l)) =
  "(BK_aux " ^
  (match k with
    | BK_type -> "BK_type"
    | BK_nat -> "BK_nat"
    | BK_order -> "BK_order"
    | BK_effect -> "BK_effect") ^ " " ^
  (pp_format_l_lem l) ^ ")"

let pp_lem_bkind ppf bk = base ppf (pp_format_bkind_lem bk)

let pp_format_kind_lem (K_aux(K_kind(klst),l)) = 
  "(K_aux (K_kind [" ^ list_format "; " pp_format_bkind_lem klst ^ "]) " ^ (pp_format_l_lem l) ^ ")"

let pp_lem_kind ppf k = base ppf (pp_format_kind_lem k)

let rec pp_format_typ_lem (Typ_aux(t,l)) =
  "(Typ_aux " ^
  (match t with
    | Typ_id(id) -> "(Typ_id " ^ pp_format_id_lem id ^ ")"
    | Typ_var(var) -> "(Typ_var " ^ pp_format_var_lem var ^ ")"
    | Typ_fn(arg,ret,efct) -> "(Typ_fn " ^ pp_format_typ_lem arg ^ " " ^ 
                              pp_format_typ_lem ret ^ " " ^
                              (pp_format_effects_lem efct) ^ ")"
    | Typ_tup(typs) -> "(Typ_tup [" ^ (list_format "; " pp_format_typ_lem typs) ^ "])"
    | Typ_app(id,args) -> "(Typ_app " ^ (pp_format_id_lem id) ^ " [" ^ (list_format "; " pp_format_typ_arg_lem args) ^ "])"
    | Typ_wild -> "Typ_wild") ^ " " ^
    (pp_format_l_lem l) ^ ")"
and pp_format_nexp_lem (Nexp_aux(n,l)) = 
  "(Nexp_aux " ^
  (match n with
    | Nexp_var(v) -> "(Nexp_var " ^ pp_format_var_lem v ^ ")"
    | Nexp_constant(i) -> "(Nexp_constant " ^ string_of_int i ^ ")"
    | Nexp_sum(n1,n2) -> "(Nexp_sum " ^ (pp_format_nexp_lem n1) ^ " " ^ (pp_format_nexp_lem n2) ^ ")"
    | Nexp_times(n1,n2) -> "(Nexp_times " ^  (pp_format_nexp_lem n1) ^ " " ^ (pp_format_nexp_lem n2) ^ ")"
    | Nexp_exp(n1) -> "(Nexp_exp " ^ (pp_format_nexp_lem n1) ^ ")"
    | Nexp_neg(n1) -> "(Nexp_neg " ^ (pp_format_nexp_lem n1) ^ ")") ^ " " ^
    (pp_format_l_lem l) ^ ")"
and pp_format_ord_lem (Ord_aux(o,l)) = 
  "(Ord_aux " ^ 
  (match o with
    | Ord_var(v) -> "(Ord_var " ^ pp_format_var_lem v ^ ")"
    | Ord_inc -> "Ord_inc"
    | Ord_dec -> "Ord_dec") ^ " " ^
   (pp_format_l_lem l) ^ ")"
and pp_format_base_effect_lem (BE_aux(e,l)) =
  "(BE_aux " ^
  (match e with
    | BE_rreg -> "BE_rreg"
    | BE_wreg -> "BE_wreg"
    | BE_rmem -> "BE_rmem"
    | BE_wmem -> "BE_wmem"
    | BE_undef -> "BE_undef"
    | BE_unspec -> "BE_unspec"
    | BE_nondet -> "BE_nondet") ^ " " ^
  (pp_format_l_lem l) ^ ")"
and pp_format_effects_lem (Effect_aux(e,l)) =
  "(Effect_aux " ^
  (match e with
  | Effect_var(v) -> "(Effect_var " ^ pp_format_var v ^ ")"
  | Effect_set(efcts) ->
    "(Effect_set [" ^
      (list_format "; " pp_format_base_effect_lem efcts) ^ " ])") ^ " " ^
  (pp_format_l_lem l) ^ ")"
and pp_format_typ_arg_lem (Typ_arg_aux(t,l)) = 
  "(Typ_arg_aux " ^
  (match t with
  | Typ_arg_typ(t) -> "(Typ_arg_typ " ^ pp_format_typ_lem t ^ ")"
  | Typ_arg_nexp(n) -> "(Typ_arg_nexp " ^ pp_format_nexp_lem n ^ ")"
  | Typ_arg_order(o) -> "(Typ_arg_order " ^ pp_format_ord_lem o ^ ")"
  | Typ_arg_effect(e) -> "(Typ_arg_effect " ^ pp_format_effects_lem e ^ ")") ^ " " ^
  (pp_format_l_lem l) ^ ")"

let pp_lem_typ ppf t = base ppf (pp_format_typ_lem t)
let pp_lem_nexp ppf n = base ppf (pp_format_nexp_lem n)
let pp_lem_ord ppf o = base ppf (pp_format_ord_lem o)
let pp_lem_effects ppf e = base ppf (pp_format_effects_lem e)
let pp_lem_beffect ppf be = base ppf (pp_format_base_effect_lem be)

let pp_format_nexp_constraint_lem (NC_aux(nc,l)) =
  "(NC_aux " ^
  (match nc with
  | NC_fixed(n1,n2) -> "(NC_fixed " ^ pp_format_nexp_lem n1 ^ " " ^ pp_format_nexp_lem n2 ^ ")"
  | NC_bounded_ge(n1,n2) -> "(NC_bounded_ge " ^ pp_format_nexp_lem n1 ^ " " ^ pp_format_nexp_lem n2 ^ ")"
  | NC_bounded_le(n1,n2) -> "(NC_bounded_le " ^ pp_format_nexp_lem n1 ^ " " ^ pp_format_nexp_lem n2 ^ ")"
  | NC_nat_set_bounded(id,bounds) -> "(NC_nat_set_bounded " ^ 
    pp_format_var_lem id ^
      " [" ^
      list_format "; " string_of_int bounds ^
      "])") ^ " " ^
  (pp_format_l_lem l) ^ ")"

let pp_lem_nexp_constraint ppf nc = base ppf (pp_format_nexp_constraint_lem nc)

let pp_format_qi_lem (QI_aux(qi,lq)) =
  "(QI_aux " ^ 
  (match qi with
  | QI_const(n_const) -> "(QI_const " ^ pp_format_nexp_constraint_lem n_const ^ ")"
  | QI_id(KOpt_aux(ki,lk)) ->
    "(QI_id (KOpt_aux " ^
    (match ki with
    | KOpt_none(var) -> "(KOpt_none " ^ pp_format_var_lem var ^ ")"
    | KOpt_kind(k,var) -> "(KOpt_kind " ^ pp_format_kind_lem k ^ " " ^ pp_format_var_lem var ^ ")") ^ " " ^
      (pp_format_l_lem lk) ^ "))") ^ " " ^ 
  (pp_format_l_lem lq) ^ ")"

let pp_lem_qi ppf qi = base ppf (pp_format_qi_lem qi)

let pp_format_typquant_lem (TypQ_aux(tq,l)) =
  "(TypQ_aux " ^ 
  (match tq with
  | TypQ_no_forall -> "TypQ_no_forall"
  | TypQ_tq(qlist) ->
    "(TypQ_tq [" ^ 
    (list_format "; " pp_format_qi_lem qlist) ^
    "])") ^ " " ^ 
  (pp_format_l_lem l) ^ ")"

let pp_lem_typquant ppf tq = base ppf (pp_format_typquant_lem tq)

let pp_format_typscm_lem (TypSchm_aux(TypSchm_ts(tq,t),l)) =
  "(TypSchm_aux (TypSchm_ts " ^ (pp_format_typquant_lem tq) ^ " " ^ pp_format_typ_lem t ^ ") " ^
                (pp_format_l_lem l) ^ ")"
 
let pp_lem_typscm ppf ts = base ppf (pp_format_typscm_lem ts)

let pp_format_lit_lem (L_aux(lit,l)) =
  "(L_aux " ^
  (match lit with
  | L_unit -> "L_unit"
  | L_zero -> "L_zero"
  | L_one -> "L_one"
  | L_true -> "L_true"
  | L_false -> "L_false"
  | L_num(i) -> "(L_num " ^ string_of_int i ^ ")"
  | L_hex(n) -> "(L_hex \"" ^ n ^ "\")"
  | L_bin(n) -> "(L_bin \"" ^ n ^ "\")"
  | L_undef -> "L_undef"
  | L_string(s) -> "(L_string \"" ^ s ^ "\")") ^ " " ^
  (pp_format_l_lem l) ^ ")"

let pp_lem_lit ppf l = base ppf (pp_format_lit_lem l)


let rec pp_format_t t =
  match t.t with
    | Tid i -> "(T_id \"" ^ i ^ "\")"
    | Tvar i -> "(T_var \"" ^ i ^ "\")"
    | Tfn(t1,t2,e) -> "(T_fn " ^ (pp_format_t t1) ^ " " ^ (pp_format_t t2) ^ " " ^ pp_format_e e ^ ")"
    | Ttup(tups) -> "(T_tup [" ^ (list_format "; " pp_format_t tups) ^ "])"
    | Tapp(i,args) -> "(T_app \"" ^ i ^ "\" (T_args [" ^  list_format "; " pp_format_targ args ^ "]))"
    | Tabbrev(ti,ta) -> "(T_abbrev " ^ (pp_format_t ti) ^ " " ^ (pp_format_t ta) ^ ")"
    | Tuvar(_) -> "(T_var (Kid_aux (Var \"fresh_v\") Unknown))"
and pp_format_targ = function
  | TA_typ t -> "(T_arg_typ " ^ pp_format_t t ^ ")"
  | TA_nexp n -> "(T_arg_nexp " ^ pp_format_n n ^ ")"
  | TA_eft e -> "(T_arg_effect " ^ pp_format_e e ^ ")"
  | TA_ord o -> "(T_arg_order " ^ pp_format_o o ^ ")"
and pp_format_n n =
  match n.nexp with
    | Nvar i -> "(Ne_var \"" ^ i ^ "\")"
    | Nconst i -> "(Ne_const " ^ string_of_int i ^ ")"
    | Nadd(n1,n2) -> "(Ne_add [" ^ (pp_format_n n1) ^ "; " ^ (pp_format_n n2) ^ "])"
    | Nmult(n1,n2) -> "(Ne_mult " ^ (pp_format_n n1) ^ " " ^ (pp_format_n n2) ^ ")"
    | N2n n -> "(Ne_exp " ^ (pp_format_n n) ^ ")"
    | Nneg n -> "(Ne_unary " ^ (pp_format_n n) ^ ")"
    | Nuvar _ -> "(Ne_var \"fresh_v_" ^ string_of_int (get_index n) ^ "\")"
and pp_format_e e = 
  "(Effect_aux " ^
  (match e.effect with
  | Evar i -> "(Effect_var (Kid_aux (Var \"" ^ i ^ "\") Unknown))"
  | Eset es -> "(Effect_set [" ^
                  (list_format "; " pp_format_base_effect_lem es) ^ " ])"
  | Euvar(_) -> "(Effect_var (Kid_aux (Var \"fresh_v\") Unknown))")
  ^ " Unknown)"
and pp_format_o o = 
  "(Ord_aux " ^ 
  (match o.order with
  | Ovar i -> "(Ord_var (Kid_aux (Var \"" ^ i ^ "\") Unknown))"
  | Oinc -> "Ord_inc"
  | Odec -> "Ord_dec"
  | Ouvar(_) -> "(Ord_var (Kid_aux (Var \"fresh_v\") Unknown))")
  ^ " Unknown)"

let pp_format_tag = function
  | Emp_local | Emp_global -> "Tag_empty"
  | External (Some s) -> "(Tag_extern (Just \""^s^"\"))"
  | External None -> "(Tag_extern Nothing)"
  | Default -> "Tag_default"
  | Constructor -> "Tag_ctor"
  | Enum -> "Tag_enum"
  | Spec -> "Tag_spec"

let pp_format_nes nes = 
  "[" ^ 
  (*(list_format "; "
     (fun ne -> match ne with
       | LtEq(_,n1,n2) -> "(Nec_lteq " ^ pp_format_n n1 ^ " " ^ pp_format_n n2 ^ ")"
       | Eq(_,n1,n2) -> "(Nec_eq " ^ pp_format_n n1 ^ " " ^ pp_format_n n2 ^ ")"
       | GtEq(_,n1,n2) -> "(Nec_gteq " ^ pp_format_n n1 ^ " " ^ pp_format_n n2 ^ ")"
       | In(_,i,ns) | InS(_,{nexp=Nvar i},ns) -> 
	 "(Nec_in \"" ^ i ^ "\" [" ^ (list_format "; " string_of_int ns)^ "])"
       | InS(_,{nexp = Nuvar _},ns)  ->  
	 "(Nec_in \"fresh\" [" ^ (list_format "; " string_of_int ns)^ "])"
     )
     nes) ^*) "]"

let pp_format_annot = function
  | NoTyp -> "Nothing"
  | Base((_,t),tag,nes,efct) -> 
    "(Just (" ^ pp_format_t t ^ ", " ^ pp_format_tag tag ^ ", " ^ pp_format_nes nes ^ ", " ^ pp_format_e efct ^ "))"
  (* XXX missing case *)
  | Overload _ -> assert false

let pp_annot ppf ant = base ppf (pp_format_annot ant)


let rec pp_format_pat_lem (P_aux(p,(l,annot))) =
  "(P_aux " ^
  (match p with
  | P_lit(lit) -> "(P_lit " ^ pp_format_lit_lem lit ^ ")"
  | P_wild -> "P_wild"
  | P_id(id) -> "(P_id " ^ pp_format_id_lem id ^ ")"
  | P_as(pat,id) -> "(P_as " ^ pp_format_pat_lem pat ^ " " ^ pp_format_id_lem id ^ ")"
  | P_typ(typ,pat) -> "(P_typ " ^ pp_format_typ_lem typ ^ " " ^ pp_format_pat_lem pat ^ ")"
  | P_app(id,pats) -> "(P_app " ^ pp_format_id_lem id ^ " [" ^
                      list_format "; " pp_format_pat_lem pats ^ "])"
  | P_record(fpats,_) -> "(P_record [" ^
                       list_format "; " (fun (FP_aux(FP_Fpat(id,fpat),_)) -> 
			                  "(FP_Fpat " ^ pp_format_id_lem id ^ " " ^ pp_format_pat_lem fpat ^ ")") fpats
                       ^ "])"
  | P_vector(pats) -> "(P_vector [" ^ list_format "; " pp_format_pat_lem pats ^ "])"
  | P_vector_indexed(ipats) ->
    "(P_vector_indexed [" ^ list_format "; " (fun (i,p) -> Printf.sprintf "(%d, %s)" i (pp_format_pat_lem p)) ipats ^ "])"
  | P_vector_concat(pats) -> "(P_vector_concat [" ^ list_format "; " pp_format_pat_lem pats ^ "])"
  | P_tup(pats) -> "(P_tup [" ^ (list_format "; " pp_format_pat_lem pats) ^ "])"
  | P_list(pats) -> "(P_list [" ^ (list_format "; " pp_format_pat_lem pats) ^ "])") ^ 
  " (" ^ pp_format_l_lem l ^ ", " ^ pp_format_annot annot ^ "))"

let pp_lem_pat ppf p = base ppf (pp_format_pat_lem p)

let rec pp_lem_let ppf (LB_aux(lb,(l,annot))) =
  let print_lb ppf lb = 
    match lb with
      | LB_val_explicit(ts,pat,exp) -> 
	fprintf ppf "@[<0>(%a %a %a %a)@]" kwd "LB_val_explicit" pp_lem_typscm ts pp_lem_pat pat pp_lem_exp exp
      | LB_val_implicit(pat,exp) -> 
	fprintf ppf "@[<0>(%a %a %a)@]" kwd "LB_val_implicit" pp_lem_pat pat  pp_lem_exp exp in
  fprintf ppf "@[<0>(LB_aux %a (%a, %a))@]" print_lb lb pp_lem_l l pp_annot annot

and pp_lem_exp ppf (E_aux(e,(l,annot))) = 
  let print_e ppf e = 
    match e with
    | E_block(exps) -> fprintf ppf "@[<0>(E_aux %a [%a] %a (%a, %a))@]"
      kwd "(E_block" 
      (list_pp pp_semi_lem_exp pp_lem_exp) exps
      kwd ")" pp_lem_l l pp_annot annot
    | E_id(id) -> fprintf ppf "(E_aux (%a %a) (%a, %a))" kwd "E_id" pp_lem_id id pp_lem_l l pp_annot annot
    | E_lit(lit) -> fprintf ppf "(E_aux (%a %a) (%a, %a))" kwd "E_lit" pp_lem_lit lit pp_lem_l l pp_annot annot
    | E_cast(typ,exp) -> fprintf ppf "@[<0>(E_aux (%a %a %a) (%a, %a))@]" kwd "E_cast" pp_lem_typ typ pp_lem_exp exp pp_lem_l l pp_annot annot
    | E_internal_cast((_,NoTyp),e) -> pp_lem_exp ppf e
    | E_internal_cast((_,Base((_,t),_,_,_)), (E_aux(ec,(_,eannot)) as exp)) ->
      (match t.t,eannot with
      | Tapp("vector",[TA_nexp n1;_;_;_]),Base((_,{t=Tapp("vector",[TA_nexp n2;_;_;_])}),_,_,_) ->
	if nexp_eq n1 n2 
	  then pp_lem_exp ppf exp
	else fprintf ppf "@[<0>(E_aux (E_cast %a %a) (%a, %a))@]" pp_lem_typ (t_to_typ t) pp_lem_exp exp pp_lem_l l pp_annot annot
      | _ -> fprintf ppf "@[<0>(E_aux (E_cast %a %a) (%a, %a))@]" pp_lem_typ (t_to_typ t) pp_lem_exp exp pp_lem_l l pp_annot annot)
    | E_app(f,args) -> fprintf ppf "@[<0>(E_aux (%a %a [%a]) (%a, %a))@]" kwd "E_app" pp_lem_id f (list_pp pp_semi_lem_exp pp_lem_exp) args pp_lem_l l pp_annot annot
    | E_app_infix(l',op,r) -> fprintf ppf "@[<0>(E_aux (%a %a %a %a) (%a, %a))@]" kwd "E_app_infix" pp_lem_exp l' pp_lem_id op pp_lem_exp r pp_lem_l l pp_annot annot
    | E_tuple(exps) -> fprintf ppf "@[<0>(E_aux %a [%a] %a (%a, %a))@]" kwd "(E_tuple" (list_pp pp_semi_lem_exp pp_lem_exp) exps kwd ")" pp_lem_l l pp_annot annot
    | E_if(c,t,e) -> fprintf ppf "@[<0>(E_aux (%a %a @[<1>%a@] @[<1> %a@]) (%a, %a))@]" kwd "E_if" pp_lem_exp c pp_lem_exp t pp_lem_exp e pp_lem_l l pp_annot annot
    | E_for(id,exp1,exp2,exp3,order,exp4) ->
      fprintf ppf "@[<0>(E_aux (%a %a %a %a %a %a @ @[<1> %a @]) (%a, %a))@]" 
	kwd "E_for" pp_lem_id id pp_lem_exp exp1 pp_lem_exp exp2 pp_lem_exp exp3 pp_lem_ord order pp_lem_exp exp4 pp_lem_l l pp_annot annot
    | E_vector(exps) -> fprintf ppf "@[<0>(E_aux (%a [%a]) (%a, %a))@]" kwd "E_vector" (list_pp pp_semi_lem_exp pp_lem_exp) exps pp_lem_l l pp_annot annot
    | E_vector_indexed(iexps,default) -> (*TODO print out default when it is an nonempty*) 
      let iformat ppf (i,e) = fprintf ppf "@[<1>(%i %a %a) %a@]" i kwd ", " pp_lem_exp e kwd ";" in
      let lformat ppf (i,e) = fprintf ppf "@[<1>(%i %a %a) @]" i kwd ", " pp_lem_exp e in
      fprintf ppf "@[<0>(E_aux (%a [%a]) (%a, %a))@]" kwd "E_vector_indexed" (list_pp iformat lformat) iexps pp_lem_l l pp_annot annot
    | E_vector_access(v,e) -> fprintf ppf "@[<0>(E_aux (%a %a %a) (%a, %a))@]" kwd "E_vector_access" pp_lem_exp v pp_lem_exp e pp_lem_l l pp_annot annot
    | E_vector_subrange(v,e1,e2) -> 
      fprintf ppf "@[<0>(E_aux (%a %a %a %a) (%a, %a))@]" kwd "E_vector_subrange" pp_lem_exp v pp_lem_exp e1 pp_lem_exp e2 pp_lem_l l pp_annot annot
    | E_vector_update(v,e1,e2) -> 
      fprintf ppf "@[<0>(E_aux (%a %a %a %a) (%a, %a))@]" kwd "E_vector_update" pp_lem_exp v pp_lem_exp e1 pp_lem_exp e2 pp_lem_l l pp_annot annot
    | E_vector_update_subrange(v,e1,e2,e3) -> 
      fprintf ppf "@[<0>(E_aux (%a %a %a %a %a) (%a, %a))@]" kwd "E_vector_update_subrange" pp_lem_exp v pp_lem_exp e1 pp_lem_exp e2 pp_lem_exp e3 pp_lem_l l pp_annot annot
    | E_list(exps) -> fprintf ppf "@[<0>(E_aux (%a [%a]) (%a, %a))@]" kwd "E_list" (list_pp pp_semi_lem_exp pp_lem_exp) exps pp_lem_l l pp_annot annot
    | E_cons(e1,e2) -> fprintf ppf "@[<0>(E_aux (%a %a %a) (%a, %a))@]" kwd "E_cons" pp_lem_exp e1 pp_lem_exp e2 pp_lem_l l pp_annot annot
    | E_record(FES_aux(FES_Fexps(fexps,_),_)) -> 
      fprintf ppf "@[<0>(E_aux (%a [%a])) (%a, %a))@]" kwd "E_record(FES_Fexps" (list_pp pp_semi_lem_fexp pp_lem_fexp) fexps pp_lem_l l pp_annot annot
    | E_record_update(exp,(FES_aux(FES_Fexps(fexps,_),_))) ->
      fprintf ppf "@[<0>(E_aux (%a %a (%a [%a])) (%a, %a))@]" 
	kwd "E_record_update" pp_lem_exp exp kwd "FES_Fexps" (list_pp pp_semi_lem_fexp pp_lem_fexp) fexps pp_lem_l l pp_annot annot
    | E_field(fexp,id) -> fprintf ppf "@[<0>(E_aux (%a %a %a) (%a, %a))@]" kwd "E_field" pp_lem_exp fexp pp_lem_id id pp_lem_l l pp_annot annot
    | E_case(exp,pexps) -> 
      fprintf ppf "@[<0>(E_aux (%a %a [%a]) (%a, %a))@]" kwd "E_case" pp_lem_exp exp (list_pp pp_semi_lem_case pp_lem_case) pexps pp_lem_l l pp_annot annot
    | E_let(leb,exp) -> fprintf ppf "@[<0>(E_aux (%a %a %a) (%a, %a))@]" kwd "E_let" pp_lem_let leb pp_lem_exp exp pp_lem_l l pp_annot annot
    | E_assign(lexp,exp) -> fprintf ppf "@[<0>(E_aux (%a %a %a) (%a, %a))@]" kwd "E_assign" pp_lem_lexp lexp pp_lem_exp exp pp_lem_l l pp_annot annot
  (* XXX missing cases *)
  | E_internal_cast ((_, Overload (_, _)), _) | E_internal_exp _ -> assert false
  in
  print_e ppf e

and pp_semi_lem_exp ppf e = fprintf ppf "@[<1>%a%a@]" pp_lem_exp e kwd ";"

and pp_lem_fexp ppf (FE_aux(FE_Fexp(id,exp),(l,annot))) = 
  fprintf ppf "@[<1>(FE_aux (%a %a %a) (%a, %a))@]" kwd "FE_Fexp" pp_lem_id id pp_lem_exp exp pp_lem_l l pp_annot annot
and pp_semi_lem_fexp ppf fexp = fprintf ppf "@[<1>%a %a@]" pp_lem_fexp fexp kwd ";"

and pp_lem_case ppf (Pat_aux(Pat_exp(pat,exp),(l,annot))) = 
  fprintf ppf "@[<1>(Pat_aux (%a %a@ %a) (%a, %a))@]" kwd "Pat_exp" pp_lem_pat pat pp_lem_exp exp pp_lem_l l pp_annot annot
and pp_semi_lem_case ppf case = fprintf ppf "@[<1>%a %a@]" pp_lem_case case kwd ";"

and pp_lem_lexp ppf (LEXP_aux(lexp,(l,annot))) =
  let print_le ppf lexp = 
    match lexp with
      | LEXP_id(id) -> fprintf ppf "(%a %a)" kwd "LEXP_id" pp_lem_id id
      | LEXP_memory(id,args) -> fprintf ppf "(%a %a [%a])" kwd "LEXP_memory" pp_lem_id id (list_pp pp_semi_lem_exp pp_lem_exp) args
      | LEXP_cast(typ,id) -> fprintf ppf "(LEXP_cast %a %a)" pp_lem_typ typ pp_lem_id id
      | LEXP_vector(v,exp) -> fprintf ppf "@[(%a %a %a)@]" kwd "LEXP_vector" pp_lem_lexp v pp_lem_exp exp
      | LEXP_vector_range(v,e1,e2) -> 
	fprintf ppf "@[(%a %a %a %a)@]" kwd "LEXP_vector_range" pp_lem_lexp v  pp_lem_exp e1 pp_lem_exp e2
      | LEXP_field(v,id) -> fprintf ppf "@[(%a %a %a)@]" kwd "LEXP_field" pp_lem_lexp v pp_lem_id id
  in
  fprintf ppf "@[(LEXP_aux %a (%a, %a))@]" print_le lexp pp_lem_l l pp_annot annot

let pp_lem_default ppf (DT_aux(df,l)) =
  let print_de ppf df =
    match df with
      | DT_kind(bk,var) -> fprintf ppf "@[<0>(%a %a %a)@]" kwd "DT_kind" pp_lem_bkind bk pp_lem_var var
      | DT_typ(ts,id) -> fprintf ppf "@[<0>(%a %a %a)@]" kwd "DT_typ" pp_lem_typscm ts pp_lem_id id
  in
  fprintf ppf "@[<0>(DT_aux %a %a)@]" print_de df pp_lem_l l

let pp_lem_spec ppf (VS_aux(v,(l,annot))) =
  let print_spec ppf v =
    match v with
      | VS_val_spec(ts,id) -> fprintf ppf "@[<0>(%a %a %a)@]@\n" kwd "VS_val_spec" pp_lem_typscm ts pp_lem_id id
      | VS_extern_spec(ts,id,s) -> fprintf ppf "@[<0>(%a %a %a \"%s\")@]@\n" kwd "VS_extern_spec" pp_lem_typscm ts pp_lem_id id s
      | VS_extern_no_rename(ts,id) -> fprintf ppf "@[<0>(%a %a %a)@]@\n" kwd "VS_extern_no_rename" pp_lem_typscm ts pp_lem_id id
  in
  fprintf ppf "@[<0>(VS_aux %a (%a, %a))@]" print_spec v pp_lem_l l pp_annot annot

let pp_lem_namescm ppf (Name_sect_aux(ns,l)) =
  match ns with
  | Name_sect_none -> fprintf ppf "(Name_sect_aux Name_sect_none %a)" pp_lem_l l
  | Name_sect_some(s) -> fprintf ppf "(Name_sect_aux (Name_sect_some \"%s\") %a)" s pp_lem_l l

let rec pp_lem_range ppf (BF_aux(r,l)) =
  match r with 
  | BF_single(i) -> fprintf ppf "(BF_aux (BF_single %i) %a)" i pp_lem_l l
  | BF_range(i1,i2) -> fprintf ppf "(BF_aux (BF_range %i %i) %a)" i1 i2 pp_lem_l l
  | BF_concat(ir1,ir2) -> fprintf ppf "(BF_aux (BF_concat %a %a) %a)" pp_lem_range ir1 pp_lem_range ir2 pp_lem_l l

let pp_lem_typdef ppf (TD_aux(td,(l,annot))) =
  let print_td ppf td = 
    match td with
      | TD_abbrev(id,namescm,typschm) -> 
	fprintf ppf "@[<0>(%a %a %a %a)@]" kwd "TD_abbrev" pp_lem_id id pp_lem_namescm namescm pp_lem_typscm typschm
      | TD_record(id,nm,typq,fs,_) -> 
	let f_pp ppf (typ,id) =
	  fprintf ppf "@[<1>(%a, %a)%a@]" pp_lem_typ typ pp_lem_id id kwd ";" in
	fprintf ppf "@[<0>(%a %a %a %a [%a] false)@]" 
	  kwd "TD_record" pp_lem_id id pp_lem_namescm nm pp_lem_typquant typq (list_pp f_pp f_pp) fs
      | TD_variant(id,nm,typq,ar,_) ->
	let a_pp ppf (Tu_aux(typ_u,l)) = 
	  match typ_u with
	    | Tu_ty_id(typ,id) -> fprintf ppf "@[<1>(Tu_aux (Tu_ty_id %a %a) %a);@]" 
	                          pp_lem_typ typ pp_lem_id id pp_lem_l l
	    | Tu_id(id) -> fprintf ppf "@[<1>(Tu_aux (Tu_id %a) %a);@]" pp_lem_id id pp_lem_l l
	in
	fprintf ppf "@[<0>(%a %a %a %a [%a] false)@]" 
	  kwd "TD_variant" pp_lem_id id pp_lem_namescm nm pp_lem_typquant typq (list_pp a_pp a_pp) ar 
      | TD_enum(id,ns,enums,_) ->
	let pp_id_semi ppf id = fprintf ppf "%a%a " pp_lem_id id kwd ";" in
	fprintf ppf "@[<0>(%a %a %a [%a] false)@]"
	  kwd "TD_enum" pp_lem_id id pp_lem_namescm ns (list_pp pp_id_semi pp_lem_id) enums
      | TD_register(id,n1,n2,rs) -> 
	let pp_rid ppf (r,id) = fprintf ppf "(%a, %a)%a " pp_lem_range r pp_lem_id id kwd ";" in
	let pp_rids = (list_pp pp_rid pp_rid) in
	fprintf ppf "@[<0>(%a %a %a %a [%a])@]"
	  kwd "TD_register" pp_lem_id id pp_lem_nexp n1 pp_lem_nexp n2 pp_rids rs
  in
  fprintf ppf "@[<0>(TD_aux %a (%a, %a))@]" print_td td pp_lem_l l pp_annot annot

let pp_lem_rec ppf (Rec_aux(r,l)) =
  match r with
  | Rec_nonrec -> fprintf ppf "(Rec_aux Rec_nonrec %a)" pp_lem_l l
  | Rec_rec -> fprintf ppf "(Rec_aux Rec_rec %a)" pp_lem_l l
  
let pp_lem_tannot_opt ppf (Typ_annot_opt_aux(t,l)) =
  match t with
  | Typ_annot_opt_some(tq,typ) -> 
    fprintf ppf "(Typ_annot_opt_aux (Typ_annot_opt_some %a %a) %a)" pp_lem_typquant tq pp_lem_typ typ pp_lem_l l

let pp_lem_effects_opt ppf (Effect_opt_aux(e,l)) =
  match e with
  | Effect_opt_pure -> fprintf ppf "(Effect_opt_aux Effect_opt_pure %a)" pp_lem_l l
  | Effect_opt_effect e -> fprintf ppf "(Effect_opt_aux (Effect_opt_effect %a) %a)" pp_lem_effects e pp_lem_l l

let pp_lem_funcl ppf (FCL_aux(FCL_Funcl(id,pat,exp),l)) =
  fprintf ppf "@[<0>(FCL_aux (%a %a %a %a) %a)@]@\n" 
    kwd "FCL_Funcl" pp_lem_id id pp_lem_pat pat pp_lem_exp exp pp_lem_l l

let pp_lem_fundef ppf (FD_aux(FD_function(r, typa, efa, fcls),(l,annot))) =
  let pp_funcls ppf funcl = fprintf ppf "%a %a" pp_lem_funcl funcl kwd ";" in
  fprintf ppf "@[<0>(FD_aux (%a %a %a %a [%a]) (%a, %a))@]" 
    kwd "FD_function" pp_lem_rec r pp_lem_tannot_opt typa pp_lem_effects_opt efa (list_pp pp_funcls pp_funcls) fcls
    pp_lem_l l pp_annot annot

let pp_lem_dec ppf (DEC_aux(DEC_reg(typ,id),(l,annot))) =
  fprintf ppf "@[<0>(DEC_aux (DEC_reg %a %a) (%a,%a))@]" pp_lem_typ typ pp_lem_id id pp_lem_l l pp_annot annot

let pp_lem_def ppf d =
  match d with
  | DEF_default(df) -> fprintf ppf "(DEF_default %a);" pp_lem_default df
  | DEF_spec(v_spec) -> fprintf ppf "(DEF_spec %a);" pp_lem_spec v_spec
  | DEF_type(t_def) -> fprintf ppf "(DEF_type %a);" pp_lem_typdef t_def
  | DEF_fundef(f_def) -> fprintf ppf "(DEF_fundef %a);" pp_lem_fundef f_def
  | DEF_val(lbind) -> fprintf ppf "(DEF_val %a);" pp_lem_let lbind
  | DEF_reg_dec(dec) -> fprintf ppf "(DEF_reg_dec %a);" pp_lem_dec dec
  | _ -> raise (Reporting_basic.err_unreachable Parse_ast.Unknown "initial_check didn't remove all scattered Defs")

let pp_lem_defs ppf (Defs(defs)) =
  fprintf ppf "Defs [@[%a@]]@\n" (list_pp pp_lem_def pp_lem_def) defs


(** PPrint based source-to-source pretty-printer *)

open PPrint

let doc_id (Id_aux(i,_)) =
  match i with
  | Id i -> string i
  | DeIid x ->
      (* add an extra space through empty to avoid a closing-comment
       * token in case of x ending with star. *)
      parens (separate space [string "deinfix"; string x; empty])

let doc_var (Kid_aux(Var v,_)) = string v

let doc_int i = string (string_of_int i)

let doc_bkind (BK_aux(k,_)) =
  string (match k with
  | BK_type -> "Type"
  | BK_nat -> "Nat"
  | BK_order -> "Order"
  | BK_effect -> "Effect")

let doc_op symb a b = infix 2 1 symb a b
let doc_unop symb a = prefix 2 1 symb a

let arrow = string "->"
let dotdot = string ".."
let coloneq = string ":="
let lsquarebarbar = string "[||"
let rsquarebarbar = string "||]"
let squarebarbars = enclose lsquarebarbar rsquarebarbar
let spaces op = enclose space space op
let semi_sp = semi ^^ space
let comma_sp = comma ^^ space
let colon_sp = spaces colon

let doc_kind (K_aux(K_kind(klst),_)) =
  separate_map (spaces arrow) doc_bkind klst

let doc_effect (BE_aux (e,_)) =
  string (match e with
  | BE_rreg -> "rreg"
  | BE_wreg -> "wreg"
  | BE_rmem -> "rmem"
  | BE_wmem -> "wmem"
  | BE_undef -> "undef"
  | BE_unspec -> "unspec"
  | BE_nondet -> "nondet")

let doc_effects (Effect_aux(e,_)) = match e with
  | Effect_var v -> doc_var v
  | Effect_set [] -> string "pure"
  | Effect_set s -> braces (separate_map comma_sp doc_effect s)

let doc_ord (Ord_aux(o,_)) = match o with
  | Ord_var v -> doc_var v
  | Ord_inc -> string "inc"
  | Ord_dec -> string "dec"

let doc_typ, doc_atomic_typ, doc_nexp =
  (* following the structure of parser for precedence *)
  let rec typ ty = fn_typ ty
  and fn_typ ((Typ_aux (t, _)) as ty) = match t with
  | Typ_fn(arg,ret,efct) ->
      separate space [tup_typ arg; arrow; fn_typ ret; string "effect"; doc_effects efct]
  | _ -> tup_typ ty
  and tup_typ ((Typ_aux (t, _)) as ty) = match t with
  | Typ_tup typs -> parens (separate_map comma_sp app_typ typs)
  | _ -> app_typ ty
  and app_typ ((Typ_aux (t, _)) as ty) = match t with
  | Typ_app(id,args) ->
      (* trailing space to avoid >> token in case of nested app types *)
      (doc_id id) ^^ (angles (separate_map comma_sp doc_typ_arg args)) ^^ space
  | _ -> atomic_typ ty (* for simplicity, skip vec_typ - which is only sugar *)
  and atomic_typ ((Typ_aux (t, _)) as ty) = match t with
  | Typ_id id  -> doc_id id
  | Typ_var v  -> doc_var v
  | Typ_wild -> underscore
  | Typ_app _ | Typ_tup _ | Typ_fn _ ->
      (* exhaustiveness matters here to avoid infinite loops
       * if we add a new Typ constructor *)
      group (parens (typ ty))
  and doc_typ_arg (Typ_arg_aux(t,_)) = match t with
  (* Be careful here because typ_arg is implemented as nexp in the
   * parser - in practice falling through app_typ after all the proper nexp
   * cases; so Typ_arg_typ has the same precedence as a Typ_app *)
  | Typ_arg_typ t -> app_typ t
  | Typ_arg_nexp n -> nexp n
  | Typ_arg_order o -> doc_ord o
  | Typ_arg_effect e -> doc_effects e

  (* same trick to handle precedence of nexp *)
  and nexp ne = sum_typ ne
  and sum_typ ((Nexp_aux(n,_)) as ne) = match n with
  | Nexp_sum(n1,n2) -> doc_op plus (sum_typ n1) (star_typ n2)
  | _ -> star_typ ne
  and star_typ ((Nexp_aux(n,_)) as ne) = match n with
  | Nexp_times(n1,n2) -> doc_op star (star_typ n1) (exp_typ n2)
  | _ -> exp_typ ne
  and exp_typ ((Nexp_aux(n,_)) as ne) = match n with
  | Nexp_exp n1 -> doc_unop (string "2**") (neg_typ n1)
  | _ -> neg_typ ne
  and neg_typ ((Nexp_aux(n,_)) as ne) = match n with
  | Nexp_neg n1 ->
      (* XXX this is not valid Sail, only an internal representation -
       * work around by commenting it *)
      let minus = concat [string "(*"; minus; string "*)"] in
      minus ^^ (atomic_nexp_typ n1)
  | _ -> atomic_nexp_typ ne
  and atomic_nexp_typ ((Nexp_aux(n,_)) as ne) = match n with
  | Nexp_var v -> doc_var v
  | Nexp_constant i -> doc_int i
  | Nexp_neg _ | Nexp_exp _ | Nexp_times _ | Nexp_sum _ ->
      group (parens (nexp ne))

  (* expose doc_typ, doc_atomic_typ and doc_nexp *)
  in typ, atomic_typ, nexp

let doc_nexp_constraint (NC_aux(nc,_)) = match nc with
  | NC_fixed(n1,n2) -> doc_op equals (doc_nexp n1) (doc_nexp n2)
  | NC_bounded_ge(n1,n2) -> doc_op (string ">=") (doc_nexp n1) (doc_nexp n2)
  | NC_bounded_le(n1,n2) -> doc_op (string "<=") (doc_nexp n1) (doc_nexp n2)
  | NC_nat_set_bounded(v,bounds) ->
      doc_op (string "IN") (doc_var v)
        (braces (separate_map comma_sp doc_int bounds))

let doc_qi (QI_aux(qi,_)) = match qi with
  | QI_const n_const -> doc_nexp_constraint n_const
  | QI_id(KOpt_aux(ki,_)) ->
    match ki with
    | KOpt_none v -> doc_var v
    | KOpt_kind(k,v) -> separate space [doc_kind k; doc_var v]

(* typ_doc is the doc for the type being quantified *)
let doc_typquant (TypQ_aux(tq,_)) typ_doc = match tq with
  | TypQ_no_forall -> typ_doc
  | TypQ_tq [] -> failwith "TypQ_tq with empty list"
  | TypQ_tq qlist ->
    (* include trailing break because the caller doesn't know if tq is empty *)
    doc_op dot
      (separate space [string "forall"; separate_map comma_sp doc_qi qlist])
      typ_doc

let doc_typscm (TypSchm_aux(TypSchm_ts(tq,t),_)) =
  (doc_typquant tq (doc_typ t))

let doc_typscm_atomic (TypSchm_aux(TypSchm_ts(tq,t),_)) =
  (doc_typquant tq (doc_atomic_typ t))

let doc_lit (L_aux(l,_)) =
  utf8string (match l with
  | L_unit  -> "()"
  | L_zero  -> "bitzero"
  | L_one   -> "bitone"
  | L_true  -> "true"
  | L_false -> "false"
  | L_num i -> string_of_int i
  | L_hex n -> "0x" ^ n
  | L_bin n -> "0b" ^ n
  | L_undef -> "undefined"
  | L_string s -> "\"" ^ s ^ "\"")

let doc_pat, doc_atomic_pat =
  let rec pat pa = pat_colons pa
  and pat_colons ((P_aux(p,l)) as pa) = match p with
  | P_vector_concat pats  -> separate_map colon_sp atomic_pat pats
  | _ -> app_pat pa
  and app_pat ((P_aux(p,l)) as pa) = match p with
  | P_app(id, ((_ :: _) as pats)) -> doc_unop (doc_id id) (parens (separate_map comma_sp atomic_pat pats))
  | _ -> atomic_pat pa
  and atomic_pat ((P_aux(p,l)) as pa) = match p with
  | P_lit lit  -> doc_lit lit
  | P_wild -> underscore
  | P_id id -> doc_id id
  | P_as(p,id) -> parens (separate space [pat p; string "as"; doc_id id])
  | P_typ(typ,p) -> separate space [parens (doc_typ typ); atomic_pat p]
  | P_app(id,[]) -> doc_id id
  | P_record(fpats,_) -> braces (separate_map semi_sp fpat fpats)
  | P_vector pats  -> brackets (separate_map comma_sp atomic_pat pats)
  | P_vector_indexed ipats  -> brackets (separate_map comma_sp npat ipats)
  | P_tup pats  -> parens (separate_map comma_sp atomic_pat pats)
  | P_list pats  -> squarebarbars (separate_map semi_sp atomic_pat pats)
  | P_app(_, _ :: _) | P_vector_concat _ ->
      group (parens (pat pa))
  and fpat (FP_aux(FP_Fpat(id,fpat),_)) = doc_op equals (doc_id id) (pat fpat)
  and npat (i,p) = doc_op equals (doc_int i) (pat p)

  (* expose doc_pat and doc_atomic_pat *)
  in pat, atomic_pat

let doc_exp, doc_let =
  let rec exp e = group (or_exp e)
  and or_exp ((E_aux(e,_)) as expr) = match e with
  | E_app_infix(l,(Id_aux(Id ("|" | "||"),_) as op),r) ->
      doc_op (doc_id op) (and_exp l) (or_exp r)
  | _ -> and_exp expr
  and and_exp ((E_aux(e,_)) as expr) = match e with
  | E_app_infix(l,(Id_aux(Id ("&" | "&&"),_) as op),r) ->
      doc_op (doc_id op) (eq_exp l) (and_exp r)
  | _ -> eq_exp expr
  and eq_exp ((E_aux(e,_)) as expr) = match e with
  | E_app_infix(l,(Id_aux(Id (
    (* XXX this is not very consistent - is the parser bogus here? *)
      "=" | "==" | "!="
    | ">=" | ">=_s" | ">=_u" | ">" | ">_s" | ">_u"
    | "<=" | "<=_s" | "<" | "<_s" | "<_si" | "<_u"
    ),_) as op),r) ->
      doc_op (doc_id op) (eq_exp l) (at_exp r)
  (* XXX assignment should not have the same precedence as equal etc. *)
  | E_assign(le,exp) -> doc_op coloneq (doc_lexp le) (at_exp exp)
  | _ -> at_exp expr
  and at_exp ((E_aux(e,_)) as expr) = match e with
  | E_app_infix(l,(Id_aux(Id ("@" | "^^" | "^" | "~^"),_) as op),r) ->
      doc_op (doc_id op) (cons_exp l) (at_exp r)
  | _ -> cons_exp expr
  and cons_exp ((E_aux(e,_)) as expr) = match e with
  | E_app_infix(l,(Id_aux(Id (":"),_) as op),r) ->
      doc_op (doc_id op) (shift_exp l) (cons_exp r)
  | E_cons(l,r) ->
      doc_op colon (shift_exp l) (cons_exp r)
  | _ -> shift_exp expr
  and shift_exp ((E_aux(e,_)) as expr) = match e with
  | E_app_infix(l,(Id_aux(Id (">>" | ">>>" | "<<" | "<<<"),_) as op),r) ->
      doc_op (doc_id op) (shift_exp l) (plus_exp r)
  | _ -> plus_exp expr
  and plus_exp ((E_aux(e,_)) as expr) = match e with
  | E_app_infix(l,(Id_aux(Id ("+" | "-"),_) as op),r) ->
      doc_op (doc_id op) (plus_exp l) (star_exp r)
  | _ -> star_exp expr
  and star_exp ((E_aux(e,_)) as expr) = match e with
  | E_app_infix(l,(Id_aux(Id (
      "*" | "/"
    | "div" | "quot" | "rem" | "mod"
    | "*_s" | "*_si" | "*_u" | "*_ui"),_) as op),r) ->
      doc_op (doc_id op) (star_exp l) (starstar_exp r)
  | _ -> starstar_exp expr
  and starstar_exp ((E_aux(e,_)) as expr) = match e with
  | E_app_infix(l,(Id_aux(Id "**",_) as op),r) ->
      doc_op (doc_id op) (starstar_exp l) (app_exp r)
  | E_if _ | E_for _ | E_let _ -> right_atomic_exp expr
  | _ -> app_exp expr
  and right_atomic_exp ((E_aux(e,_)) as expr) = match e with
  (* Special case: omit "else ()" when the else branch is empty. *)
  | E_if(c,t,E_aux(E_block [], _)) ->
      string "if" ^^ space ^^ group (exp c) ^/^
      string "then" ^^ space ^^ group (exp t)
  | E_if(c,t,e) ->
      string "if" ^^ space ^^ group (exp c) ^/^
      string "then" ^^ space ^^ group (exp t) ^/^
      string "else" ^^ space ^^ group (exp e)
  | E_for(id,exp1,exp2,exp3,order,exp4) ->
      string "foreach" ^^ space ^^
      group (parens (
        separate (break 1) [
          doc_id id;
          string "from " ^^ atomic_exp exp1;
          string "to " ^^ atomic_exp exp2;
          string "by " ^^ atomic_exp exp3;
          string "in " ^^ doc_ord order
        ]
      )) ^/^
      exp exp4
  | E_let(leb,e) -> doc_op (string "in") (let_exp leb) (exp e)
  | _ -> group (parens (exp expr))
  and app_exp ((E_aux(e,_)) as expr) = match e with
  | E_app(f,args) ->
      doc_unop (doc_id f) (parens (separate_map comma exp args))
  | _ -> vaccess_exp expr
  and vaccess_exp ((E_aux(e,_)) as expr) = match e with
  | E_vector_access(v,e) ->
      atomic_exp v ^^ brackets (exp e)
  | E_vector_subrange(v,e1,e2) ->
      atomic_exp v ^^ brackets (doc_op dotdot (exp e1) (exp e2))
  | _ -> field_exp expr
  and field_exp ((E_aux(e,_)) as expr) = match e with
  | E_field(fexp,id) -> atomic_exp fexp ^^ dot ^^ doc_id id
  | _ -> atomic_exp expr
  and atomic_exp ((E_aux(e,_)) as expr) = match e with
  (* Special case: an empty block is equivalent to unit, but { } would
   * be parsed as a struct. *)
  | E_block [] -> string "()"
  | E_block exps ->
      let exps_doc = separate_map (semi ^^ hardline) exp exps in
      surround 2 1 lbrace exps_doc rbrace
  | E_id id -> doc_id id
  | E_lit lit -> doc_lit lit
  | E_cast(typ,e) -> prefix 2 1 (parens (doc_typ typ)) (group (atomic_exp e))
  | E_internal_cast((_,NoTyp),e) -> atomic_exp e
  | E_internal_cast((_,Base((_,t),_,_,_)), (E_aux(_,(_,eannot)) as e)) ->
      (match t.t,eannot with
      (* XXX I don't understand why we can hide the internal cast here *)
      | Tapp("vector",[TA_nexp n1;_;_;_]),Base((_,{t=Tapp("vector",[TA_nexp n2;_;_;_])}),_,_,_)
          when nexp_eq n1 n2 -> atomic_exp e
      | _ -> prefix 2 1 (parens (doc_typ (t_to_typ t))) (group (atomic_exp e)))
  | E_tuple exps ->
      parens (separate_map comma exp exps)
  | E_record(FES_aux(FES_Fexps(fexps,_),_)) ->
      (* XXX E_record is not handled by parser currently *)
      braces (separate_map semi_sp doc_fexp fexps)
  | E_record_update(e,(FES_aux(FES_Fexps(fexps,_),_))) ->
      braces (doc_op (string "with") (exp e) (separate_map semi_sp doc_fexp fexps))
  | E_vector exps ->
      brackets (separate_map comma exp exps)
  | E_vector_indexed (iexps, default) ->
      (* XXX TODO print default when it is non-empty *)
      let iexp (i,e) = doc_op equals (doc_int i) (exp e) in
      brackets (separate_map comma iexp iexps)
  | E_vector_update(v,e1,e2) ->
      brackets (doc_op (string "with") (exp v) (doc_op equals (atomic_exp e1) (exp e2)))
  | E_vector_update_subrange(v,e1,e2,e3) ->
      brackets (
        doc_op (string "with") (exp v)
        (doc_op equals (atomic_exp e1 ^^ colon ^^ atomic_exp e2) (exp e3)))
  | E_list exps ->
      squarebarbars (separate_map comma exp exps)
  | E_case(e,pexps) ->
      let opening = separate space [string "switch"; exp e; lbrace] in
      let cases = separate_map (break 1) doc_case pexps in
      surround 2 1 opening cases rbrace
  (* adding parens and loop for lower precedence *)
  | E_app (_, _)|E_vector_access (_, _)|E_vector_subrange (_, _, _)
  | E_cons (_, _)|E_field (_, _)|E_assign (_, _)
  | E_app_infix (_,
    (* for every app_infix operator caught at a higher precedence,
     * we need to wrap around with parens *)
    (Id_aux(Id("|" | "||"
    | "&" | "&&"
    | "=" | "==" | "!="
    | ">=" | ">=_s" | ">=_u" | ">" | ">_s" | ">_u"
    | "<=" | "<=_s" | "<" | "<_s" | "<_si" | "<_u"
    | "@" | "^^" | "^" | "~^"
    | ":"
    | ">>" | ">>>" | "<<" | "<<<"
    | "+" | "-"
    | "*" | "/"
    | "div" | "quot" | "rem" | "mod"
    | "*_s" | "*_si" | "*_u" | "*_ui"
    | "**"), _))
    , _) ->
      group (parens (exp expr))
  (* XXX default precedence for app_infix? *)
  | E_app_infix(l,op,r) ->
      failwith ("unexpected app_infix operator " ^ (pp_format_id op))
      (* doc_op (doc_id op) (exp l) (exp r) *)
  (* XXX missing case *)
  | E_internal_cast ((_, Overload (_, _)), _) | E_internal_exp _ -> assert false

  and let_exp (LB_aux(lb,_)) = match lb with
  | LB_val_explicit(ts,pat,e) ->
      prefix 2 1
        (separate space [string "let"; doc_typscm_atomic ts; doc_atomic_pat pat; equals])
        (exp e)
  | LB_val_implicit(pat,e) ->
      prefix 2 1
        (separate space [string "let"; doc_atomic_pat pat; equals])
        (exp e)

  and doc_fexp (FE_aux(FE_Fexp(id,e),_)) = doc_op equals (doc_id id) (exp e)

  and doc_case (Pat_aux(Pat_exp(pat,e),_)) =
    doc_op arrow (separate space [string "case"; doc_atomic_pat pat]) (group (exp e))

  (* lexps are parsed as eq_exp - we need to duplicate the precedence
   * structure for them *)
  and doc_lexp le = app_lexp le
  and app_lexp ((LEXP_aux(lexp,_)) as le) = match lexp with
  | LEXP_memory(id,args) -> doc_id id ^^ parens (separate_map comma exp args)
  | _ -> vaccess_lexp le
  and vaccess_lexp ((LEXP_aux(lexp,_)) as le) = match lexp with
  | LEXP_vector(v,e) -> atomic_lexp v ^^ brackets (exp e)
  | LEXP_vector_range(v,e1,e2) ->
      atomic_lexp v ^^ brackets (exp e1 ^^ dotdot ^^ exp e2)
  | _ -> field_lexp le
  and field_lexp ((LEXP_aux(lexp,_)) as le) = match lexp with
  | LEXP_field(v,id) -> atomic_lexp v ^^ dot ^^ doc_id id
  | _ -> atomic_lexp le
  and atomic_lexp ((LEXP_aux(lexp,_)) as le) = match lexp with
  | LEXP_id id -> doc_id id
  | LEXP_cast(typ,id) -> prefix 2 1 (parens (doc_typ typ)) (doc_id id)
  | LEXP_memory _ | LEXP_vector _ | LEXP_vector_range _
  | LEXP_field _ -> group (parens (doc_lexp le))

  (* expose doc_exp and doc_let *)
  in exp, let_exp

let doc_default (DT_aux(df,_)) = match df with
  | DT_kind(bk,v) -> separate space [string "default"; doc_bkind bk; doc_var v]
  | DT_typ(ts,id) -> separate space [string "default"; doc_typscm ts; doc_id id]

let doc_spec (VS_aux(v,_)) = match v with
  | VS_val_spec(ts,id) ->
      separate space [string "val"; doc_typscm ts; doc_id id]
  | VS_extern_no_rename(ts,id) ->
      separate space [string "val"; string "extern"; doc_typscm ts; doc_id id]
  | VS_extern_spec(ts,id,s) ->
      separate space [string "val"; string "extern"; doc_typscm ts;
      doc_op equals (doc_id id) (dquotes (string s))]

let doc_namescm (Name_sect_aux(ns,_)) = match ns with
  | Name_sect_none -> empty
  (* include leading space because the caller doesn't know if ns is
   * empty, and trailing break already added by the following equals *)
  | Name_sect_some s -> space ^^ brackets (doc_op equals (string "name") (dquotes (string s)))

let rec doc_range (BF_aux(r,_)) = match r with
  | BF_single i -> doc_int i
  | BF_range(i1,i2) -> doc_op dotdot (doc_int i1) (doc_int i2)
  | BF_concat(ir1,ir2) -> (doc_range ir1) ^^ comma ^^ (doc_range ir2)

let doc_type_union (Tu_aux(typ_u,_)) = match typ_u with
  | Tu_ty_id(typ,id) -> concat [doc_typ typ; space; doc_id id; semi]
  | Tu_id id -> doc_id id ^^ semi

let doc_typdef (TD_aux(td,_)) = match td with
  | TD_abbrev(id,nm,typschm) ->
      doc_op equals (concat [string "typedef"; space; doc_id id; doc_namescm nm]) (doc_typscm typschm)
  | TD_record(id,nm,typq,fs,_) ->
      let f_pp (typ,id) = concat [doc_typ typ; space; doc_id id; semi] in
      let fs_doc = group (separate_map (break 1) f_pp fs) in
      doc_op equals
        (concat [string "typedef"; space; doc_id id; doc_namescm nm])
        (string "const struct" ^^ space ^^ doc_typquant typq (braces fs_doc))
  | TD_variant(id,nm,typq,ar,_) ->
      let ar_doc = group (separate_map (break 1) doc_type_union ar) in
      doc_op equals
        (concat [string "typedef"; space; doc_id id; doc_namescm nm])
        (string "const union" ^^ space ^^ doc_typquant typq (braces ar_doc))
  | TD_enum(id,nm,enums,_) ->
      let enums_doc = group (separate_map (semi ^^ break 1) doc_id enums) in
      doc_op equals
        (concat [string "typedef"; space; doc_id id; doc_namescm nm])
        (string "enumerate" ^^ space ^^ braces enums_doc)
  | TD_register(id,n1,n2,rs) ->
      let doc_rid (r,id) = separate space [doc_range r; colon; doc_id id] ^^ semi in
      let doc_rids = group (separate_map (break 1) doc_rid rs) in
      doc_op equals
        (string "typedef" ^^ space ^^ doc_id id)
        (separate space [
          string "register bits";
          brackets (doc_nexp n1 ^^ colon ^^ doc_nexp n2);
          braces doc_rids;
        ])

let doc_rec (Rec_aux(r,_)) = match r with
  | Rec_nonrec -> empty
  (* include trailing space because caller doesn't know if we return
   * empty *)
  | Rec_rec -> string "rec" ^^ space

let doc_tannot_opt (Typ_annot_opt_aux(t,_)) = match t with
  | Typ_annot_opt_some(tq,typ) -> doc_typquant tq (doc_typ typ)

let doc_effects_opt (Effect_opt_aux(e,_)) = match e with
  | Effect_opt_pure -> string "pure"
  | Effect_opt_effect e -> doc_effects e

let doc_funcl (FCL_aux(FCL_Funcl(id,pat,exp),_)) =
  group (doc_op equals (separate space [doc_id id; doc_atomic_pat pat]) (doc_exp exp))

let doc_fundef (FD_aux(FD_function(r, typa, efa, fcls),_)) =
  match fcls with
  | [] -> failwith "FD_function with empty function list"
  | _ ->
      let sep = hardline ^^ string "and" ^^ space in
      let clauses = separate_map sep doc_funcl fcls in
      separate space [string "function";
        doc_rec r ^^ doc_tannot_opt typa;
        string "effect"; doc_effects_opt efa;
        clauses]

let doc_dec (DEC_aux(DEC_reg(typ,id),_)) =
  separate space [string "register"; doc_atomic_typ typ; doc_id id]

let doc_scattered (SD_aux (sdef, _)) = match sdef with
 | SD_scattered_function (r, typa, efa, id) ->
     separate space [
       string "scattered function";
       doc_rec r ^^ doc_tannot_opt typa;
       string "effect"; doc_effects_opt efa;
       doc_id id]
 | SD_scattered_variant (id, ns, tq) ->
     doc_op equals
       (string "scattered typedef" ^^ space ^^ doc_id id ^^ doc_namescm ns)
       (doc_typquant tq empty)
 | SD_scattered_funcl funcl ->
     string "function clause" ^^ space ^^ doc_funcl funcl
 | SD_scattered_unioncl (id, tu) ->
     separate space [string "union"; doc_id id;
     string "member"; doc_type_union tu]
 | SD_scattered_end id -> string "end" ^^ space ^^ doc_id id

let doc_def def = group (match def with
  | DEF_default df -> doc_default df
  | DEF_spec v_spec -> doc_spec v_spec
  | DEF_type t_def -> doc_typdef t_def
  | DEF_fundef f_def -> doc_fundef f_def
  | DEF_val lbind -> doc_let lbind
  | DEF_reg_dec dec -> doc_dec dec
  | DEF_scattered sdef -> doc_scattered sdef
  ) ^^ hardline

let doc_defs (Defs(defs)) =
  separate_map hardline doc_def defs

let print ?(len=80) channel doc = ToChannel.pretty 1. len channel doc
let to_buf ?(len=80) buf doc = ToBuffer.pretty 1. len buf doc

let pp_defs f d = print f (doc_defs d)
let pp_exp b e = to_buf b (doc_exp e)
