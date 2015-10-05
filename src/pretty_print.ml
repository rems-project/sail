open Type_internal
open Ast
open Format
open Big_int

(****************************************************************************
 * annotated source to Lem ast pretty printer
****************************************************************************)

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

let lemnum default n = match n with
  | 0   -> "zero"
  | 1   -> "one"
  | 2   -> "two"
  | 3   -> "three"
  | 4   -> "four"
  | 5   -> "five"
  | 6   -> "six"
  | 7   -> "seven"
  | 8   -> "eight" 
  | 15  -> "fifteen"
  | 16  -> "sixteen"
  | 20  -> "twenty"
  | 23  -> "twentythree"
  | 24  -> "twentyfour"
  | 30  -> "thirty"
  | 31  -> "thirtyone"
  | 32  -> "thirtytwo"
  | 35  -> "thirtyfive"
  | 39  -> "thirtynine"
  | 40  -> "forty"
  | 47  -> "fortyseven"
  | 48  -> "fortyeight"
  | 55  -> "fiftyfive"
  | 56  -> "fiftysix"
  | 57  -> "fiftyseven"
  | 61  -> "sixtyone"
  | 63  -> "sixtythree"
  | 64  -> "sixtyfour"
  | 127 -> "onetwentyseven"
  | 128 -> "onetwentyeight"
  | _   -> if n >= 0 then default n else ("(zero - " ^ (default (abs n)) ^ ")")

let pp_format_id (Id_aux(i,_)) =
  match i with
  | Id(i) -> i
  | DeIid(x) -> "(deinfix " ^ x ^ ")"

let pp_format_var (Kid_aux(Var v,_)) = v

let rec pp_format_l_lem = function
  | Parse_ast.Unknown -> "Unknown"
  | _ -> "Unknown"
(*  | Parse_ast.Int(s,None) -> "(Int \"" ^ s ^ "\" Nothing)"
  | Parse_ast.Int(s,(Some l)) -> "(Int \"" ^  s ^ "\" (Just " ^ (pp_format_l_lem l) ^ "))"
  | Parse_ast.Range(p1,p2) -> "(Range \"" ^ p1.Lexing.pos_fname ^ "\" " ^
                               (string_of_int p1.Lexing.pos_lnum) ^ " " ^ 
                               (string_of_int (p1.Lexing.pos_cnum - p1.Lexing.pos_bol)) ^ " " ^
                               (string_of_int p2.Lexing.pos_lnum) ^ " " ^
                               (string_of_int (p2.Lexing.pos_cnum - p2.Lexing.pos_bol)) ^ ")"*)

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
    | Nexp_constant(i) -> "(Nexp_constant " ^ (lemnum string_of_int i) ^ ")"
    | Nexp_sum(n1,n2) -> "(Nexp_sum " ^ (pp_format_nexp_lem n1) ^ " " ^ (pp_format_nexp_lem n2) ^ ")"
    | Nexp_minus(n1,n2) -> "(Nexp_minus " ^ (pp_format_nexp_lem n1)^ " " ^ (pp_format_nexp_lem n2) ^ ")"
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
    | BE_wmv  -> "BE_wmv"
    | BE_eamem -> "BE_eamem"
    | BE_barr -> "BE_barr"
    | BE_depend -> "BE_depend"
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
  | L_num(i) -> "(L_num " ^ (lemnum string_of_int i) ^ ")"
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
    | Tfn(t1,t2,_,e) -> "(T_fn " ^ (pp_format_t t1) ^ " " ^ (pp_format_t t2) ^ " " ^ pp_format_e e ^ ")"
    | Ttup(tups) -> "(T_tup [" ^ (list_format "; " pp_format_t tups) ^ "])"
    | Tapp(i,args) -> "(T_app \"" ^ i ^ "\" (T_args [" ^  list_format "; " pp_format_targ args ^ "]))"
    | Tabbrev(ti,ta) -> "(T_abbrev " ^ (pp_format_t ti) ^ " " ^ (pp_format_t ta) ^ ")"
    | Tuvar(_) -> "(T_var \"fresh_v\")"
    | Toptions _ -> "(T_var \"fresh_v\")"
and pp_format_targ = function
  | TA_typ t -> "(T_arg_typ " ^ pp_format_t t ^ ")"
  | TA_nexp n -> "(T_arg_nexp " ^ pp_format_n n ^ ")"
  | TA_eft e -> "(T_arg_effect " ^ pp_format_e e ^ ")"
  | TA_ord o -> "(T_arg_order " ^ pp_format_o o ^ ")"
and pp_format_n n =
  match n.nexp with
    | Nvar i -> "(Ne_var \"" ^ i ^ "\")"
    | Nconst i -> "(Ne_const " ^ (lemnum string_of_int (int_of_big_int i)) ^ ")"
    | Npos_inf -> "Ne_inf"
    | Nadd(n1,n2) -> "(Ne_add [" ^ (pp_format_n n1) ^ "; " ^ (pp_format_n n2) ^ "])"
    | Nsub(n1,n2) -> "(Ne_minus "^ (pp_format_n n1) ^ " " ^ (pp_format_n n2) ^ ")"
    | Nmult(n1,n2) -> "(Ne_mult " ^ (pp_format_n n1) ^ " " ^ (pp_format_n n2) ^ ")"
    | N2n(n,Some i) -> "(Ne_exp " ^ (pp_format_n n) ^ "(*" ^ string_of_big_int i ^ "*)" ^ ")"
    | N2n(n,None) -> "(Ne_exp " ^ (pp_format_n n) ^ ")"
    | Nneg n -> "(Ne_unary " ^ (pp_format_n n) ^ ")"
    | Nuvar _ -> "(Ne_var \"fresh_v_" ^ string_of_int (get_index n) ^ "\")"
    | Nneg_inf -> "(Ne_unary Ne_inf)"
    | Npow _ -> "power_not_implemented"
    | Ninexact -> "(Ne_add Ne_inf (Ne_unary Ne_inf)"
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
  | Emp_local -> "Tag_empty"
  | Emp_intro -> "Tag_intro"
  | Emp_set -> "Tag_set" 
  | Emp_global -> "Tag_global"
  | External (Some s) -> "(Tag_extern (Just \""^s^"\"))"
  | External None -> "(Tag_extern Nothing)"
  | Default -> "Tag_default"
  | Constructor -> "Tag_ctor"
  | Enum i -> "(Tag_enum " ^ (lemnum string_of_int i) ^ ")"
  | Alias alias_inf -> "Tag_alias"
  | Spec -> "Tag_spec"

let rec pp_format_nes nes = 
  "[" ^ (*
  (list_format "; "
     (fun ne -> match ne with
       | LtEq(_,n1,n2) -> "(Nec_lteq " ^ pp_format_n n1 ^ " " ^ pp_format_n n2 ^ ")"
       | Eq(_,n1,n2) -> "(Nec_eq " ^ pp_format_n n1 ^ " " ^ pp_format_n n2 ^ ")"
       | GtEq(_,n1,n2) -> "(Nec_gteq " ^ pp_format_n n1 ^ " " ^ pp_format_n n2 ^ ")"
       | In(_,i,ns) | InS(_,{nexp=Nvar i},ns) -> 
         "(Nec_in \"" ^ i ^ "\" [" ^ (list_format "; " string_of_int ns)^ "])"
       | InS(_,_,ns)  ->  
         "(Nec_in \"fresh\" [" ^ (list_format "; " string_of_int ns)^ "])"
       | CondCons(_,nes_c,nes_t) -> 
         "(Nec_cond " ^ (pp_format_nes nes_c) ^ " " ^ (pp_format_nes nes_t) ^ ")"
       | BranchCons(_,nes_b) ->
         "(Nec_branch " ^ (pp_format_nes nes_b) ^ ")"
     )
     nes) ^*) "]"

let pp_format_annot = function
  | NoTyp -> "Nothing"
  | Base((_,t),tag,nes,efct,_) -> 
    (*TODO print out bindings for use in pattern match in interpreter*)
    "(Just (" ^ pp_format_t t ^ ", " ^ pp_format_tag tag ^ ", " ^ pp_format_nes nes ^ ", " ^ pp_format_e efct ^ "))"
  | Overload _ -> "Nothing"

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
    | E_nondet(exps) -> fprintf ppf "@[<0>(E_aux %a [%a] %a (%a, %a))@]"
      kwd "(E_nondet" 
      (list_pp pp_semi_lem_exp pp_lem_exp) exps
      kwd ")" pp_lem_l l pp_annot annot
    | E_id(id) -> fprintf ppf "(E_aux (%a %a) (%a, %a))" kwd "E_id" pp_lem_id id pp_lem_l l pp_annot annot
    | E_lit(lit) -> fprintf ppf "(E_aux (%a %a) (%a, %a))" kwd "E_lit" pp_lem_lit lit pp_lem_l l pp_annot annot
    | E_cast(typ,exp) -> fprintf ppf "@[<0>(E_aux (%a %a %a) (%a, %a))@]" kwd "E_cast" pp_lem_typ typ pp_lem_exp exp pp_lem_l l pp_annot annot
    | E_internal_cast((_,NoTyp),e) -> pp_lem_exp ppf e
    | E_internal_cast((_,Base((_,t),_,_,_,bindings)), (E_aux(ec,(_,eannot)) as exp)) ->
      (*TODO use bindings*)
      let print_cast () = fprintf ppf "@[<0>(E_aux (E_cast %a %a) (%a, %a))@]" 
        pp_lem_typ (t_to_typ t) pp_lem_exp exp pp_lem_l l pp_annot annot in
      (match t.t,eannot with
      | Tapp("vector",[TA_nexp n1;_;_;_]),Base((_,{t=Tapp("vector",[TA_nexp n2;_;_;_])}),_,_,_,bindings_int) ->
        if nexp_eq n1 n2 
          then pp_lem_exp ppf exp
        else (match (n1.nexp,n2.nexp) with 
          | Nconst i1,Nconst i2 -> if eq_big_int i1 i2 then pp_lem_exp ppf exp else print_cast ()
          | Nconst i1,_ -> print_cast ()
          | _ -> pp_lem_exp ppf exp)
      | _ -> pp_lem_exp ppf exp)
    | E_app(f,args) -> fprintf ppf "@[<0>(E_aux (%a %a [%a]) (%a, %a))@]" kwd "E_app" pp_lem_id f (list_pp pp_semi_lem_exp pp_lem_exp) args pp_lem_l l pp_annot annot
    | E_app_infix(l',op,r) -> fprintf ppf "@[<0>(E_aux (%a %a %a %a) (%a, %a))@]" kwd "E_app_infix" pp_lem_exp l' pp_lem_id op pp_lem_exp r pp_lem_l l pp_annot annot
    | E_tuple(exps) -> fprintf ppf "@[<0>(E_aux %a [%a] %a (%a, %a))@]" kwd "(E_tuple" (list_pp pp_semi_lem_exp pp_lem_exp) exps kwd ")" pp_lem_l l pp_annot annot
    | E_if(c,t,e) -> fprintf ppf "@[<0>(E_aux (%a %a @[<1>%a@] @[<1> %a@]) (%a, %a))@]" kwd "E_if" pp_lem_exp c pp_lem_exp t pp_lem_exp e pp_lem_l l pp_annot annot
    | E_for(id,exp1,exp2,exp3,order,exp4) ->
      fprintf ppf "@[<0>(E_aux (%a %a %a %a %a %a @ @[<1> %a @]) (%a, %a))@]" 
        kwd "E_for" pp_lem_id id pp_lem_exp exp1 pp_lem_exp exp2 pp_lem_exp exp3 pp_lem_ord order pp_lem_exp exp4 pp_lem_l l pp_annot annot
    | E_vector(exps) -> fprintf ppf "@[<0>(E_aux (%a [%a]) (%a, %a))@]" kwd "E_vector" (list_pp pp_semi_lem_exp pp_lem_exp) exps pp_lem_l l pp_annot annot
    | E_vector_indexed(iexps,(Def_val_aux (default, (dl,dannot)))) -> 
      let iformat ppf (i,e) = fprintf ppf "@[<1>(%i %a %a) %a@]" i kwd ", " pp_lem_exp e kwd ";" in
      let lformat ppf (i,e) = fprintf ppf "@[<1>(%i %a %a) @]" i kwd ", " pp_lem_exp e in
      let default_string ppf _ = (match default with
        | Def_val_empty -> fprintf ppf "(Def_val_aux Def_val_empty (%a,%a))" pp_lem_l dl pp_annot dannot 
        | Def_val_dec e -> fprintf ppf "(Def_val_aux (Def_val_dec %a) (%a,%a))" pp_lem_exp e pp_lem_l dl pp_annot dannot) in 
      fprintf ppf "@[<0>(E_aux (%a [%a] %a) (%a, %a))@]" kwd "E_vector_indexed" (list_pp iformat lformat) iexps default_string () pp_lem_l l pp_annot annot
    | E_vector_access(v,e) -> fprintf ppf "@[<0>(E_aux (%a %a %a) (%a, %a))@]" kwd "E_vector_access" pp_lem_exp v pp_lem_exp e pp_lem_l l pp_annot annot
    | E_vector_subrange(v,e1,e2) -> 
      fprintf ppf "@[<0>(E_aux (%a %a %a %a) (%a, %a))@]" kwd "E_vector_subrange" pp_lem_exp v pp_lem_exp e1 pp_lem_exp e2 pp_lem_l l pp_annot annot
    | E_vector_update(v,e1,e2) -> 
      fprintf ppf "@[<0>(E_aux (%a %a %a %a) (%a, %a))@]" kwd "E_vector_update" pp_lem_exp v pp_lem_exp e1 pp_lem_exp e2 pp_lem_l l pp_annot annot
    | E_vector_update_subrange(v,e1,e2,e3) -> 
      fprintf ppf "@[<0>(E_aux (%a %a %a %a %a) (%a, %a))@]" kwd "E_vector_update_subrange" pp_lem_exp v pp_lem_exp e1 pp_lem_exp e2 pp_lem_exp e3 pp_lem_l l pp_annot annot
    | E_vector_append(v1,v2) ->
      fprintf ppf "@[<0>(E_aux (E_vector_append %a %a) (%a, %a))@]" pp_lem_exp v1 pp_lem_exp v2 pp_lem_l l pp_annot annot
    | E_list(exps) -> fprintf ppf "@[<0>(E_aux (%a [%a]) (%a, %a))@]" kwd "E_list" (list_pp pp_semi_lem_exp pp_lem_exp) exps pp_lem_l l pp_annot annot
    | E_cons(e1,e2) -> fprintf ppf "@[<0>(E_aux (%a %a %a) (%a, %a))@]" kwd "E_cons" pp_lem_exp e1 pp_lem_exp e2 pp_lem_l l pp_annot annot
    | E_record(FES_aux(FES_Fexps(fexps,_),(fl,fannot))) -> 
      fprintf ppf "@[<0>(E_aux (E_record (FES_aux (FES_Fexps [%a] false) (%a,%a))) (%a, %a))@]"
        (list_pp pp_semi_lem_fexp pp_lem_fexp) fexps pp_lem_l fl pp_annot fannot pp_lem_l l pp_annot annot
    | E_record_update(exp,(FES_aux(FES_Fexps(fexps,_),(fl,fannot)))) ->
      fprintf ppf "@[<0>(E_aux (E_record_update %a (FES_aux (FES_Fexps [%a] false) (%a,%a))) (%a,%a))@]"
        pp_lem_exp exp (list_pp pp_semi_lem_fexp pp_lem_fexp) fexps pp_lem_l fl pp_annot fannot pp_lem_l l pp_annot annot
    | E_field(fexp,id) -> fprintf ppf "@[<0>(E_aux (%a %a %a) (%a, %a))@]" kwd "E_field" pp_lem_exp fexp pp_lem_id id pp_lem_l l pp_annot annot
    | E_case(exp,pexps) -> 
      fprintf ppf "@[<0>(E_aux (%a %a [%a]) (%a, %a))@]" kwd "E_case" pp_lem_exp exp (list_pp pp_semi_lem_case pp_lem_case) pexps pp_lem_l l pp_annot annot
    | E_let(leb,exp) -> fprintf ppf "@[<0>(E_aux (%a %a %a) (%a, %a))@]" kwd "E_let" pp_lem_let leb pp_lem_exp exp pp_lem_l l pp_annot annot
    | E_assign(lexp,exp) -> fprintf ppf "@[<0>(E_aux (%a %a %a) (%a, %a))@]" kwd "E_assign" pp_lem_lexp lexp pp_lem_exp exp pp_lem_l l pp_annot annot
    | E_exit exp -> fprintf ppf "@[<0>(E_aux (E_exit %a) (%a, %a))@]" pp_lem_exp exp pp_lem_l l pp_annot annot
    | E_internal_exp ((l, Base((_,t),_,_,_,bindings))) ->
      (*TODO use bindings where appropriate*)
      (match t.t with
        | Tapp("register",[TA_typ {t=Tapp("vector",[TA_nexp _;TA_nexp r;_;_])}])
        | Tapp("vector",[TA_nexp _;TA_nexp r;_;_]) ->
          (match r.nexp with
          | Nconst bi -> fprintf ppf "@[<0>(E_aux (E_lit (L_aux (L_num %a) %a)) (%a, %a))@]" 
                                       kwd (lemnum string_of_int (int_of_big_int bi)) pp_lem_l l pp_lem_l l pp_annot (Base(([],nat_t),Emp_local,[],pure_e,nob))
          | Nvar v -> fprintf ppf  "@[<0>(E_aux (E_id (Id_aux (Id \"%a\") %a)) (%a,%a))@]"
                                     kwd v pp_lem_l l pp_lem_l l pp_annot (Base(([],nat_t),Emp_local,[],pure_e,nob))
          | _ ->  raise (Reporting_basic.err_unreachable l "Internal exp given vector without known length"))
        | Tapp("implicit",[TA_nexp r]) ->
          (match r.nexp with
            | Nconst bi -> fprintf ppf "@[<0>(E_aux (E_lit (L_aux (L_num %a) %a)) (%a, %a))@]" 
                                       kwd (lemnum string_of_int (int_of_big_int bi)) pp_lem_l l pp_lem_l l pp_annot (Base(([],nat_t),Emp_local,[],pure_e,nob))
            | Nvar v -> fprintf ppf "@[<0>(E_aux (E_id (Id_aux (Id \"%a\") %a)) (%a,%a))@]"
                                     kwd v pp_lem_l l pp_lem_l l pp_annot (Base(([],nat_t),Emp_local,[],pure_e,nob))
            | _ -> raise (Reporting_basic.err_unreachable l "Internal_exp given implicit without variable or const"))
        | _ ->  raise (Reporting_basic.err_unreachable l "Internal exp given non-vector or implicit"))
    | E_internal_cast ((_, Overload (_,_, _)), _) | E_internal_exp _ ->  raise (Reporting_basic.err_unreachable l "Found internal cast or exp with overload")
   | E_internal_exp_user _ -> (raise (Reporting_basic.err_unreachable l "Found non-rewritten internal_exp_user"))
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
      | DT_order(ord) -> fprintf ppf "@[<0>(DT_order %a)@]" pp_lem_ord ord
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

let pp_lem_funcl ppf (FCL_aux(FCL_Funcl(id,pat,exp),(l,annot))) =
  fprintf ppf "@[<0>(FCL_aux (%a %a %a %a) (%a,%a))@]@\n" 
    kwd "FCL_Funcl" pp_lem_id id pp_lem_pat pat pp_lem_exp exp pp_lem_l l pp_annot annot

let pp_lem_fundef ppf (FD_aux(FD_function(r, typa, efa, fcls),(l,annot))) =
  let pp_funcls ppf funcl = fprintf ppf "%a %a" pp_lem_funcl funcl kwd ";" in
  fprintf ppf "@[<0>(FD_aux (%a %a %a %a [%a]) (%a, %a))@]" 
    kwd "FD_function" pp_lem_rec r pp_lem_tannot_opt typa pp_lem_effects_opt efa (list_pp pp_funcls pp_funcls) fcls
    pp_lem_l l pp_annot annot

let pp_lem_aspec ppf (AL_aux(aspec,(l,annot))) =
  let pp_reg_id ppf (RI_aux((RI_id ri),(l,annot))) =
    fprintf ppf "@[<0>(RI_aux (RI_id %a) (%a,%a))@]" pp_lem_id ri pp_lem_l l pp_annot annot in
  match aspec with
    | AL_subreg(reg,subreg) -> 
      fprintf ppf "@[<0>(AL_aux (AL_subreg %a %a) (%a,%a))@]" pp_reg_id reg pp_lem_id subreg pp_lem_l l pp_annot annot
    | AL_bit(reg,ac) ->
      fprintf ppf "@[<0>(AL_aux (AL_bit %a %a) (%a,%a))@]" pp_reg_id reg pp_lem_exp ac pp_lem_l l pp_annot annot
    | AL_slice(reg,b,e) ->
      fprintf ppf "@[<0>(AL_aux (AL_slice %a %a %a) (%a,%a))@]" pp_reg_id reg pp_lem_exp b pp_lem_exp e pp_lem_l l pp_annot annot
    | AL_concat(f,s) ->
      fprintf ppf "@[<0>(AL_aux (AL_concat %a %a) (%a,%a))@]" pp_reg_id f pp_reg_id s pp_lem_l l pp_annot annot

let pp_lem_dec ppf (DEC_aux(reg,(l,annot))) =
  match reg with 
    | DEC_reg(typ,id) ->
      fprintf ppf "@[<0>(DEC_aux (DEC_reg %a %a) (%a,%a))@]" pp_lem_typ typ pp_lem_id id pp_lem_l l pp_annot annot
    | DEC_alias(id,alias_spec) ->
      fprintf ppf "@[<0>(DEC_aux (DEC_alias %a %a) (%a, %a))@]" pp_lem_id id pp_lem_aspec alias_spec pp_lem_l l pp_annot annot
    | DEC_typ_alias(typ,id,alias_spec) ->
      fprintf ppf "@[<0>(DEC_aux (DEC_typ_alias %a %a %a) (%a, %a))@]" pp_lem_typ typ pp_lem_id id pp_lem_aspec alias_spec pp_lem_l l pp_annot annot

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


(****************************************************************************
 * PPrint-based source-to-source pretty printer
****************************************************************************)

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

let pipe = string "|"
let arrow = string "->"
let dotdot = string ".."
let coloneq = string ":="
let lsquarebar = string "[|"
let rsquarebar = string "|]"
let squarebars = enclose lsquarebar rsquarebar
let lsquarebarbar = string "[||"
let rsquarebarbar = string "||]"
let squarebarbars = enclose lsquarebarbar rsquarebarbar
let lsquarecolon = string "[:"
let rsquarecolon = string ":]"
let squarecolons = enclose lsquarecolon rsquarecolon
let string_lit = enclose dquote dquote
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
  | BE_wmv  -> "wmv"
  | BE_eamem -> "eamem"
  | BE_barr -> "barr"
  | BE_depend -> "depend"
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
  (*TODO Need to un bid-endian-ify this here, since both can transform to the shorthand, especially with <: and :> *)
  (* Special case simple vectors to improve legibility
   * XXX we assume big-endian here, as usual *)
  | Typ_app(Id_aux (Id "vector", _), [
      Typ_arg_aux(Typ_arg_nexp (Nexp_aux(Nexp_constant n, _)), _);
      Typ_arg_aux(Typ_arg_nexp (Nexp_aux(Nexp_constant m, _)), _);
      Typ_arg_aux (Typ_arg_order (Ord_aux (Ord_inc, _)), _);
      Typ_arg_aux (Typ_arg_typ (Typ_aux (Typ_id id, _)), _)]) ->
        (doc_id id) ^^ (brackets (if n = 0 then doc_int m else doc_op colon (doc_int n) (doc_int (n+m-1))))
  | Typ_app(Id_aux (Id "range", _), [
    Typ_arg_aux(Typ_arg_nexp (Nexp_aux(Nexp_constant n, _)), _);
    Typ_arg_aux(Typ_arg_nexp m, _);]) ->
    (squarebars (if n = 0 then nexp m else doc_op colon (doc_int n) (nexp m))) 
  | Typ_app(Id_aux (Id "atom", _), [Typ_arg_aux(Typ_arg_nexp n,_)]) ->
    (squarecolons (nexp n))
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
  | Nexp_minus(n1,n2) -> doc_op minus (sum_typ n1) (star_typ n2)
  | _ -> star_typ ne
  and star_typ ((Nexp_aux(n,_)) as ne) = match n with
  | Nexp_times(n1,n2) -> doc_op star (star_typ n1) (exp_typ n2)
  | _ -> exp_typ ne
  and exp_typ ((Nexp_aux(n,_)) as ne) = match n with
  | Nexp_exp n1 -> doc_unop (string "2**") (atomic_nexp_typ n1)
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
  | Nexp_neg _ | Nexp_exp _ | Nexp_times _ | Nexp_sum _ | Nexp_minus _->
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
  (* XXX add leading indentation if not flat - we need to define our own
   * combinator for that *)
  | P_vector_concat pats  -> separate_map (space ^^ colon ^^ break 1) atomic_pat pats
  | _ -> app_pat pa
  and app_pat ((P_aux(p,l)) as pa) = match p with
  | P_app(id, ((_ :: _) as pats)) -> doc_unop (doc_id id) (parens (separate_map comma_sp atomic_pat pats))
  | _ -> atomic_pat pa
  and atomic_pat ((P_aux(p,(l,annot))) as pa) = match p with
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
  | E_vector_append(l,r) ->
      doc_op colon (shift_exp l) (cons_exp r)
  | E_cons(l,r) ->
      doc_op colon (shift_exp l) (cons_exp r)
  | _ -> shift_exp expr
  and shift_exp ((E_aux(e,_)) as expr) = match e with
  | E_app_infix(l,(Id_aux(Id (">>" | ">>>" | "<<" | "<<<"),_) as op),r) ->
      doc_op (doc_id op) (shift_exp l) (plus_exp r)
  | _ -> plus_exp expr
  and plus_exp ((E_aux(e,_)) as expr) = match e with
  | E_app_infix(l,(Id_aux(Id ("+" | "-" | "+_s" | "-_s"),_) as op),r) ->
      doc_op (doc_id op) (plus_exp l) (star_exp r)
  | _ -> star_exp expr
  and star_exp ((E_aux(e,_)) as expr) = match e with
  | E_app_infix(l,(Id_aux(Id (
      "*" | "/"
    | "div" | "quot" | "quot_s" | "rem" | "mod"
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
  | E_nondet exps ->
    let exps_doc = separate_map (semi ^^ hardline) exp exps in
    string "nondet" ^^ space ^^ (surround 2 1 lbrace exps_doc rbrace)
  | E_id id -> doc_id id
  | E_lit lit -> doc_lit lit
  | E_cast(typ,e) -> prefix 2 1 (parens (doc_typ typ)) (group (atomic_exp e))
  | E_internal_cast((_,NoTyp),e) -> atomic_exp e
  | E_internal_cast((_,Base((_,t),_,_,_,bindings)), (E_aux(_,(_,eannot)) as e)) ->
      (match t.t,eannot with
      (* XXX I don't understand why we can hide the internal cast here
         AAA Because an internal cast between vectors is only generated to reset the base access;
             the type checker generates far more than are needed and they're pruned off here, after constraint resolution *)
      | Tapp("vector",[TA_nexp n1;_;_;_]),Base((_,{t=Tapp("vector",[TA_nexp n2;_;_;_])}),_,_,_,_)
          when nexp_eq n1 n2 -> atomic_exp e
      | _ -> prefix 2 1 (parens (doc_typ (t_to_typ t))) (group (atomic_exp e)))
  | E_tuple exps ->
      parens (separate_map comma exp exps)
  | E_record(FES_aux(FES_Fexps(fexps,_),_)) ->
      (* XXX E_record is not handled by parser currently
         AAA The parser can't handle E_record due to ambiguity with blocks; initial_check looks for blocks that are all field assignments and converts *)
      braces (separate_map semi_sp doc_fexp fexps)
  | E_record_update(e,(FES_aux(FES_Fexps(fexps,_),_))) ->
      braces (doc_op (string "with") (exp e) (separate_map semi_sp doc_fexp fexps))
  | E_vector exps ->
    let default_print _ = brackets (separate_map comma exp exps) in
    (match exps with
      | [] -> default_print ()
      | E_aux(e,_)::es ->
        (match e with
          | E_lit (L_aux(L_one, _)) | E_lit (L_aux(L_zero, _)) ->
            utf8string
              ("0b" ^ 
                  (List.fold_right (fun (E_aux( e,_)) rst ->
                    (match e with 
                      | E_lit(L_aux(l, _)) ->
                        ((match l with | L_one -> "1" | L_zero -> "0" | L_undef -> "u" | _ -> assert false) ^ rst)
                      | _ -> assert false)) exps "")) 
          | _ -> default_print ()))
  | E_vector_indexed (iexps, (Def_val_aux (default,_))) ->
    let default_string = 
      (match default with
        | Def_val_empty -> string "" 
        | Def_val_dec e -> concat [semi; space; string "default"; equals; (exp e)]) in 
      let iexp (i,e) = doc_op equals (doc_int i) (exp e) in
      brackets (concat [(separate_map comma iexp iexps); default_string])
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
  | E_exit e ->
    separate space [string "exit"; exp e;]
  (* adding parens and loop for lower precedence *)
  | E_app (_, _)|E_vector_access (_, _)|E_vector_subrange (_, _, _)
  | E_cons (_, _)|E_field (_, _)|E_assign (_, _)
  | E_if _ | E_for _ | E_let _
  | E_vector_append _
  | E_app_infix (_,
    (* for every app_infix operator caught at a higher precedence,
     * we need to wrap around with parens *)
    (Id_aux(Id("|" | "||"
    | "&" | "&&"
    | "=" | "==" | "!="
    | ">=" | ">=_s" | ">=_u" | ">" | ">_s" | ">_u"
    | "<=" | "<=_s" | "<" | "<_s" | "<_si" | "<_u"
    | "@" | "^^" | "^" | "~^"
    | ">>" | ">>>" | "<<" | "<<<"
    | "+" | "-" | "+_s" | "-_s"
    | "*" | "/"
    | "div" | "quot" | "quot_s" | "rem" | "mod"
    | "*_s" | "*_si" | "*_u" | "*_ui"
    | "**"), _))
    , _) ->
      group (parens (exp expr))
  (* XXX default precedence for app_infix? *)
  | E_app_infix(l,op,r) ->
      failwith ("unexpected app_infix operator " ^ (pp_format_id op))
      (* doc_op (doc_id op) (exp l) (exp r) *)
  | E_internal_exp((l, Base((_,t),_,_,_,bindings))) -> (*TODO use bindings, and other params*)
    (match t.t with
      | Tapp("register",[TA_typ {t=Tapp("vector",[TA_nexp _;TA_nexp r;_;_])}])
      | Tapp("vector",[TA_nexp _;TA_nexp r;_;_]) ->
        (match r.nexp with
          | Nvar v -> utf8string v
          | Nconst bi -> utf8string (Big_int.string_of_big_int bi)
          | _ ->  raise (Reporting_basic.err_unreachable l 
                           ("Internal exp given vector without known length, instead given " ^ n_to_string r)))
      | Tapp("implicit",[TA_nexp r]) ->
        (match r.nexp with
          | Nconst bi -> utf8string (Big_int.string_of_big_int bi)
          | Nvar v -> utf8string v
          | _ -> raise (Reporting_basic.err_unreachable l "Internal exp given implicit without var or const"))
      | _ ->  raise (Reporting_basic.err_unreachable l ("Internal exp given non-vector, non-implicit " ^ t_to_string t)))
  | E_internal_exp_user _ -> raise (Reporting_basic.err_unreachable Unknown ("internal_exp_user not rewritten away"))
  | E_internal_cast ((_, Overload (_, _,_ )), _) | E_internal_exp _ -> assert false

  and let_exp (LB_aux(lb,_)) = match lb with
  | LB_val_explicit(ts,pat,e) ->
      prefix 2 1
        (separate space [string "let"; doc_typscm_atomic ts; doc_atomic_pat pat; equals])
        (atomic_exp e)
  | LB_val_implicit(pat,e) ->
      prefix 2 1
        (separate space [string "let"; doc_atomic_pat pat; equals])
        (atomic_exp e)

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
  | DT_order(ord) -> separate space [string "default"; string "order"; doc_ord ord]

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
  | Tu_ty_id(typ,id) -> separate space [doc_typ typ; doc_id id]
  | Tu_id id -> doc_id id

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
      let ar_doc = group (separate_map (semi ^^ break 1) doc_type_union ar) in
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

let doc_alias (AL_aux (alspec,_)) =
  match alspec with
    | AL_subreg((RI_aux (RI_id id,_)),subid) -> doc_id id ^^ dot ^^ doc_id subid
    | AL_bit((RI_aux (RI_id id,_)),ac) -> doc_id id ^^ brackets (doc_exp ac)
    | AL_slice((RI_aux (RI_id id,_)),b,e) -> doc_id id ^^ brackets (doc_op dotdot (doc_exp b) (doc_exp e))
    | AL_concat((RI_aux (RI_id f,_)),(RI_aux (RI_id s,_))) -> doc_op colon (doc_id f) (doc_id s)

let doc_dec (DEC_aux (reg,_)) =
  match reg with
    | DEC_reg(typ,id) -> separate space [string "register"; doc_atomic_typ typ; doc_id id]
    | DEC_alias(id,alspec) ->
        doc_op equals (string "register alias" ^^ space ^^ doc_id id) (doc_alias alspec)
    | DEC_typ_alias(typ,id,alspec) -> 
        doc_op equals (string "register alias" ^^ space ^^ doc_atomic_typ typ) (doc_alias alspec)

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
let pat_to_string p = 
  let b = Buffer.create 20 in
  to_buf b (doc_pat p);
  Buffer.contents b

(****************************************************************************
 * PPrint-based sail-to-ocaml pretty printer
****************************************************************************)

let star_sp = star ^^ space

let doc_id_ocaml (Id_aux(i,_)) =
  match i with
  | Id("bit") -> string "vbit" 
  | Id i -> string (if i.[0] = '\'' then "_" ^ i else i)
  | DeIid x ->
      (* add an extra space through empty to avoid a closing-comment
       * token in case of x ending with star. *)
      parens (separate space [colon; string x; empty])

let doc_id_ocaml_type (Id_aux(i,_)) =
  match i with
  | Id("bit") -> string "vbit" 
  | Id i -> string (String.uncapitalize i)
  | DeIid x ->
      (* add an extra space through empty to avoid a closing-comment
       * token in case of x ending with star. *)
      parens (separate space [colon; string (String.uncapitalize x); empty])

let doc_id_ocaml_ctor (Id_aux(i,_)) =
  match i with
  | Id("bit") -> string "vbit" 
  | Id i -> string (String.capitalize i)
  | DeIid x ->
      (* add an extra space through empty to avoid a closing-comment
       * token in case of x ending with star. *)
      parens (separate space [colon; string (String.capitalize x); empty])

let doc_typ_ocaml, doc_atomic_typ_ocaml =
  (* following the structure of parser for precedence *)
  let rec typ ty = fn_typ ty
  and fn_typ ((Typ_aux (t, _)) as ty) = match t with
  | Typ_fn(arg,ret,efct) ->
      separate space [tup_typ arg; arrow; fn_typ ret]
  | _ -> tup_typ ty
  and tup_typ ((Typ_aux (t, _)) as ty) = match t with
  | Typ_tup typs -> parens (separate_map star app_typ typs)
  | _ -> app_typ ty
  and app_typ ((Typ_aux (t, _)) as ty) = match t with
  | Typ_app(Id_aux (Id "vector", _), [
      Typ_arg_aux(Typ_arg_nexp n, _);
      Typ_arg_aux(Typ_arg_nexp m, _);
      Typ_arg_aux (Typ_arg_order ord, _);
      Typ_arg_aux (Typ_arg_typ typ, _)]) ->
    string "value"
  | Typ_app(Id_aux (Id "range", _), [
    Typ_arg_aux(Typ_arg_nexp n, _);
    Typ_arg_aux(Typ_arg_nexp m, _);]) ->
    (string "number")
  | Typ_app(Id_aux (Id "atom", _), [Typ_arg_aux(Typ_arg_nexp n,_)]) ->
    (string "number")
  | Typ_app(id,args) ->
      (separate_map space doc_typ_arg_ocaml args) ^^ (doc_id_ocaml_type id)
  | _ -> atomic_typ ty 
  and atomic_typ ((Typ_aux (t, _)) as ty) = match t with
  | Typ_id id  -> doc_id_ocaml_type id
  | Typ_var v  -> doc_var v
  | Typ_wild -> underscore
  | Typ_app _ | Typ_tup _ | Typ_fn _ ->
      (* exhaustiveness matters here to avoid infinite loops
       * if we add a new Typ constructor *)
      group (parens (typ ty))
  and doc_typ_arg_ocaml (Typ_arg_aux(t,_)) = match t with
  | Typ_arg_typ t -> app_typ t
  | Typ_arg_nexp n -> empty
  | Typ_arg_order o -> empty
  | Typ_arg_effect e -> empty
  in typ, atomic_typ

let doc_lit_ocaml (L_aux(l,_)) =
  utf8string (match l with
  | L_unit  -> "()"
  | L_zero  -> "0"
  | L_one   -> "1"
  | L_true  -> "1"
  | L_false -> "0"
  | L_num i -> string_of_int i
  | L_hex n -> "(num_to_vec" ^ ("0x" ^ n) ^ ")"
  | L_bin n -> "(num_to_vec" ^ ("0b" ^ n) ^ ")"
  | L_undef -> "2"
  | L_string s -> "\"" ^ s ^ "\"")

(* typ_doc is the doc for the type being quantified *)
let doc_typquant_ocaml (TypQ_aux(tq,_)) typ_doc = typ_doc

let doc_typscm_ocaml (TypSchm_aux(TypSchm_ts(tq,t),_)) =
  (doc_typquant tq (doc_typ_ocaml t))

(*Note: vector concatenation, literal vectors, indexed vectors, and record should 
  be removed prior to pp. The latter two have never yet been seen
*)
let doc_pat_ocaml, doc_atomic_pat_ocaml =
  let rec pat pa = app_pat pa
  and app_pat ((P_aux(p,l)) as pa) = match p with
  | P_app(id, ((_ :: _) as pats)) -> doc_unop (doc_id_ocaml_ctor id) (parens (separate_map comma_sp atomic_pat pats))
  | _ -> atomic_pat pa
  and atomic_pat ((P_aux(p,(l,annot))) as pa) = match p with
  | P_lit lit  -> doc_lit lit
  | P_wild -> underscore
  | P_id id -> doc_id id
  | P_as(p,id) -> parens (separate space [pat p; string "as"; doc_id_ocaml id])
  | P_typ(typ,p) -> doc_op colon (pat p) (doc_typ_ocaml typ) 
  | P_app(id,[]) -> doc_id_ocaml_ctor id
  | P_vector pats ->
    let non_bit_print () = parens (separate space [string "VvectorR"; squarebars (separate_map semi pat pats); underscore ; underscore]) in
    (match annot with
     | Base(([],t),_,_,_,_) ->
       if is_bit_vector t
       then parens (separate space [string "Vvector"; squarebars (separate_map semi pat pats); underscore ; underscore])
       else non_bit_print()
     | _ -> non_bit_print ())
  | P_tup pats  -> parens (separate_map comma_sp atomic_pat pats)
  | P_list pats -> brackets (separate_map semi pat pats) (*Never seen but easy in ocaml*)
  in pat, atomic_pat

let doc_exp_ocaml, doc_let_ocaml =
  let rec exp (E_aux (e, (_,annot))) =  match e with
    | E_assign((LEXP_aux(le_act,tannot) as le),e) ->
      (match annot with
       | Base(_,(Emp_local | Emp_set),_,_,_) ->
         (match le_act with
          | LEXP_id _ | LEXP_cast _ ->
            (*Setting local variable fully *)
            doc_op coloneq (doc_lexp_ocaml le) (exp e)
          | LEXP_vector _ ->
            doc_op (string "<-") (doc_lexp_ocaml le) (exp e)
          | LEXP_vector_range _ ->
            group ((string "set_vector_range") ^^ space ^^ (doc_lexp_ocaml le) ^^ space ^^ (exp e)))
       | _ ->
         (match le_act with
          | LEXP_vector _ | LEXP_vector_range _ | LEXP_cast _ | LEXP_field _ | LEXP_id _ ->
            (doc_lexp_rwrite le e)
          | LEXP_memory _ -> (doc_lexp_fcall le e)))
    | E_vector_append(l,r) ->
      group (parens (string "vector_append ") ^^ (exp l) ^^ space ^^ (exp r))
    | E_cons(l,r) -> doc_op (group (colon^^colon)) (exp l) (exp r)
    | E_if(c,t,E_aux(E_block [], _)) ->
      string "if" ^^ space ^^ string "to_bool" ^^  parens (exp c) ^/^
      string "then" ^^ space ^^ (exp t)
    | E_if(c,t,e) ->
      string "if" ^^ space ^^ string "to_bool" ^^ parens (exp c) ^/^
      string "then" ^^ space ^^ group (exp t) ^/^
      string "else" ^^ space ^^ group (exp e)
    | E_for(id,exp1,exp2,exp3,(Ord_aux(order,_)),exp4) ->
      let var= doc_id_ocaml id in
      let (compare,next) = if order = Ord_inc then string "<=",string "+" else string ">=",string "-" in
      let by = exp exp3 in
      let stop = exp exp2 in
      (*takes over two names but doesn't require building a closure*)
      parens
        (separate space [(string "let (__stop,__by) = ") ^^ (parens (doc_op comma stop by));
                             string "in" ^/^ empty;
                             string "let rec foreach";
                             var;
                             equals;
                             string "if";
                             parens (doc_op compare var (string "__stop") );
                             string "then";
                             parens (exp exp4 ^^ space ^^ semi ^^ (string "foreach") ^^
                                     parens (doc_op next var (string "__by")));
                             string "in";
                             string "foreach";
                             exp exp1])
        (*Requires fewer introduced names but introduces a closure*)
        (*let forL = if order = Ord_inc then string "foreach_inc" else string "foreach_dec" in
          forL ^^ space ^^ (group (exp exp1)) ^^ (group (exp exp2)) ^^ (group (exp full_exp3)) ^/^
          group ((string "fun") ^^ space ^^ (doc_id id) ^^ space ^^ arrow ^/^ (exp exp4))

        (* this way requires the following OCaml declarations first

         let rec foreach_inc i stop by body = 
           if i <= stop then (body i; foreach_inc (i + by) stop by body) else ()

         let rec foreach_dec i stop by body = 
           if i >= stop then (body i; foreach_dec (i - by) stop by body) else ()

         *)*)
    | E_let(leb,e) -> doc_op (string "in") (let_exp leb) (exp e)
    | E_app(f,args) ->
      let call = match annot with
        | Base(_,External (Some n),_,_,_) -> string n
        | Base(_,Constructor,_,_,_) -> doc_id_ocaml_ctor f
        | _ -> doc_id_ocaml f in
      parens (doc_unop call (parens (separate_map comma exp args)))
    | E_vector_access(v,e) ->
      let call = (match annot with
          | Base((_,t),_,_,_,_) ->
            (match t.t with
             | Tid "bit" | Tabbrev(_,{t=Tid "bit"}) -> (string "bit_vector_access")
             | _ -> (string "vector_access"))
          | _ -> (string "vector_access")) in
      parens (call ^^ space ^^ exp v ^^ space ^^ exp e)
    | E_vector_subrange(v,e1,e2) ->
      parens ((string "vector_subrange") ^^ space ^^ (exp v) ^^ space ^^ (exp e1) ^^ space ^^ (exp e2))
    | E_field((E_aux(_,(_,fannot)) as fexp),id) ->
      (match fannot with
       | Base((_,{t= Tapp("register",_)}),_,_,_,_) |
         Base((_,{t= Tabbrev(_,{t=Tapp("register",_)})}),_,_,_,_)->
        parens ((string "get_register_field") ^^ space ^^ (exp fexp) ^^ space ^^ string_lit (doc_id id))
      | _ -> exp fexp ^^ dot ^^ doc_id id)
    | E_block [] -> string "()"
    | E_block exps | E_nondet exps ->
      let exps_doc = separate_map (semi ^^ hardline) exp exps in
      surround 2 1 (string "begin") exps_doc (string "end")
    | E_id id ->
      (match annot with
      | Base((_, ({t = Tapp("reg",_)} | {t=Tabbrev(_,{t=Tapp("reg",_)})})),_,_,_,_) ->
        string "!" ^^ doc_id_ocaml id
      | Base(_,Alias alias_info,_,_,_) ->
        (match alias_info with
         | Alias_field(reg,field) -> parens (string "get_register_field" ^^ space ^^ string reg ^^ string_lit (string field))
         | Alias_extract(reg,start,stop) ->
           if start = stop
           then parens (string "bit_vector_access" ^^ space ^^ string reg ^^ space ^^ doc_int start)
           else parens (string "vector_subrange" ^^ space ^^ string reg ^^ space ^^ doc_int start ^^ space ^^ doc_int stop)
         | Alias_pair(reg1,reg2) ->
           parens (string "vector_append" ^^ space ^^ string reg1 ^^ space ^^ string reg2))        
      | _ -> doc_id_ocaml id)
    | E_lit lit -> doc_lit lit
    | E_cast(typ,e) -> (parens (doc_op colon (group (exp e)) (doc_typ typ)))
    | E_tuple exps ->
      parens (separate_map comma exp exps)
    | E_record(FES_aux(FES_Fexps(fexps,_),_)) ->
      braces (separate_map semi_sp doc_fexp fexps)
    | E_record_update(e,(FES_aux(FES_Fexps(fexps,_),_))) ->
      braces (doc_op (string "with") (exp e) (separate_map semi_sp doc_fexp fexps))
    | E_vector exps ->
      (match annot with
       | Base((_,t),_,_,_,_) ->
         match t.t with
         | Tapp("vector", [TA_nexp start; _; TA_ord order; _])
         | Tabbrev(_,{t= Tapp("vector", [TA_nexp start; _; TA_ord order; _])}) ->
           let call = if is_bit_vector t then (string "Vvector") else (string "VvectorR") in
           let dir,dir_out = match order.order with
             | Oinc -> true,"true"
             | _ -> false, "false" in
           let start = match start.nexp with
             | Nconst i -> string_of_big_int i
             | N2n(_,Some i) -> string_of_big_int i
             | _ -> if dir then "0" else string_of_int (List.length exps) in
           group (call ^^ space ^^ squarebars (separate_map semi exp exps) ^^ string start ^^ string dir_out))
    | E_vector_indexed (iexps, (Def_val_aux (default,_))) ->
      (match annot with
       | Base((_,t),_,_,_,_) ->
         match t.t with
         | Tapp("vector", [TA_nexp start; TA_nexp len; TA_ord order; _])
         | Tabbrev(_,{t= Tapp("vector", [TA_nexp start; TA_nexp len; TA_ord order; _])}) ->
           let call = if is_bit_vector t then (string "make_indexed_bitv") else (string "make_indexed_v") in
           let dir,dir_out = match order.order with
             | Oinc -> true,"true"
             | _ -> false, "false" in
           let start = match start.nexp with
             | Nconst i -> string_of_big_int i
             | N2n(_,Some i) -> string_of_big_int i
             | _ -> if dir then "0" else string_of_int (List.length iexps) in
           let size = match len.nexp with
             | Nconst i | N2n(_,Some i)-> string_of_big_int i in
           let default_string = 
             (match default with
              | Def_val_empty -> string "None" 
              | Def_val_dec e -> parens (string "Some " ^^ (exp e))) in 
           let iexp (i,e) = parens (separate_map comma_sp (fun x -> x) [(doc_int i); (exp e)]) in
           group (call ^^ (brackets (separate_map semi iexp iexps)) ^^ space ^^ default_string ^^ string start ^^ string size ^^ string dir_out))
  | E_vector_update(v,e1,e2) ->
    (*Has never happened to date*)
      brackets (doc_op (string "with") (exp v) (doc_op equals (exp e1) (exp e2)))
  | E_vector_update_subrange(v,e1,e2,e3) ->
    (*Has never happened to date*)
      brackets (
        doc_op (string "with") (exp v)
        (doc_op equals (exp e1 ^^ colon ^^ exp e2) (exp e3)))
  | E_list exps ->
      brackets (separate_map comma exp exps)
  | E_case(e,pexps) ->
      let opening = separate space [string "("; string "match"; exp e; string "with"] in
      let cases = separate_map (break 1) doc_case pexps in
      surround 2 1 opening cases rparen
  | E_exit e ->
    separate space [string "exit"; exp e;]
  | E_app_infix (e1,id,e2) ->
    let call = 
      match annot with
      | Base((_,t),External(Some name),_,_,_) -> string name
      | _ -> doc_id_ocaml id in
    separate space [call; parens (separate_map comma exp [e1;e2])]
  | E_internal_let(lexp, eq_exp, in_exp) ->
    separate space [string "let";
                    doc_lexp_ocaml lexp; (*Rewriter/typecheck should ensure this is only cast or id*)
                    equals;
                    string "ref";
                    exp eq_exp;
                    string "in";
                    exp in_exp]

  and let_exp (LB_aux(lb,_)) = match lb with
  | LB_val_explicit(ts,pat,e) ->
      prefix 2 1
        (separate space [string "let"; doc_atomic_pat_ocaml pat; equals])
        (exp e)
  | LB_val_implicit(pat,e) ->
      prefix 2 1
        (separate space [string "let"; doc_atomic_pat_ocaml pat; equals])
        (exp e)

  and doc_fexp (FE_aux(FE_Fexp(id,e),_)) = doc_op equals (doc_id_ocaml id) (exp e)

  and doc_case (Pat_aux(Pat_exp(pat,e),_)) =
    doc_op arrow (separate space [pipe; doc_atomic_pat_ocaml pat]) (group (exp e))

  and doc_lexp_ocaml ((LEXP_aux(lexp,(l,annot))) as le) = match lexp with
  | LEXP_vector(v,e) -> parens ((string "get_varray") ^^ space ^^ doc_lexp_ocaml v) ^^ dot ^^ parens (exp e)
  | LEXP_vector_range(v,e1,e2) ->
      parens ((string "vector_subrange") ^^ space ^^ doc_lexp_ocaml v ^^ space ^^ (exp e1) ^^ space ^^ (exp e2))
  | LEXP_field(v,id) -> doc_lexp_ocaml v ^^ dot ^^ doc_id_ocaml id
  | LEXP_id id -> doc_id_ocaml id
  | LEXP_cast(typ,id) -> (doc_id_ocaml id)

  and doc_lexp_rwrite ((LEXP_aux(lexp,(l,annot))) as le) e_new_v =
    match lexp with
    | LEXP_vector(v,e) ->
      doc_op (string "<-")
        (group (parens ((string "get_varray") ^^ space ^^ doc_lexp_ocaml v)) ^^ dot ^^ parens (exp e))
        (exp e_new_v)
    | LEXP_vector_range(v,e1,e2) ->
      parens ((string "set_vector_subrange") ^^ space ^^
              doc_lexp_ocaml v ^^ space ^^ exp e1 ^^ space ^^ exp e2 ^^ space ^^ exp e_new_v)
    | LEXP_field(v,id) ->
      parens ((string "set_register_field") ^^ space ^^
              doc_lexp_ocaml v ^^ space ^^string_lit (doc_id id) ^^ space ^^ exp e_new_v)
    | LEXP_id id | LEXP_cast (_,id) ->
      (match annot with
       | Base(_,Alias alias_info,_,_,_) ->
         (match alias_info with
          | Alias_field(reg,field) ->
            parens ((string "set_register_field") ^^ space ^^
                    string reg ^^ space ^^string_lit (string field) ^^ space ^^ exp e_new_v)
          | Alias_extract(reg,start,stop) ->
            if start = stop
            then
              doc_op (string "<-")
                (group (parens ((string "get_varray") ^^ space ^^ string reg)) ^^ dot ^^ parens (doc_int start))
                (exp e_new_v)
            else 
              parens ((string "set_vector_subrange") ^^ space ^^
                      string reg ^^ space ^^ doc_int start ^^ space ^^ doc_int stop ^^ space ^^ exp e_new_v)
          | Alias_pair(reg1,reg2) ->
            parens ((string "set_two_regs") ^^ space ^^ string reg1 ^^ space ^^ string reg2 ^^ space ^^ exp e_new_v))              
       | _ -> 
         doc_id_ocaml id) 

  and doc_lexp_fcall ((LEXP_aux(lexp,(l,annot))) as le) e_new_v = match lexp with
    | LEXP_memory(id,args) -> doc_id_ocaml id ^^ parens (separate_map comma exp (args@[e_new_v]))

  (* expose doc_exp and doc_let *)
  in exp, let_exp

(*TODO Upcase and downcase type and constructors as needed*)
let doc_type_union_ocaml (Tu_aux(typ_u,_)) = match typ_u with
  | Tu_ty_id(typ,id) -> separate space [pipe; doc_id_ocaml_ctor id; string "of"; doc_typ_ocaml typ;]
  | Tu_id id -> separate space [pipe; doc_id_ocaml_ctor id]

let rec doc_range_ocaml (BF_aux(r,_)) = match r with
  | BF_single i -> parens (doc_op comma (doc_int i) (doc_int i))
  | BF_range(i1,i2) -> parens (doc_op comma (doc_int i1) (doc_int i2))
  | BF_concat(ir1,ir2) -> (doc_range ir1) ^^ comma ^^ (doc_range ir2)

let doc_typdef_ocaml (TD_aux(td,_)) = match td with
  | TD_abbrev(id,nm,typschm) ->
      doc_op equals (concat [string "type"; space; doc_id_ocaml_type id;]) (doc_typscm_ocaml typschm)
  | TD_record(id,nm,typq,fs,_) ->
      let f_pp (typ,id) = concat [doc_id_ocaml_type id; space; colon; doc_typ_ocaml typ; semi] in
      let fs_doc = group (separate_map (break 1) f_pp fs) in
      doc_op equals
        (concat [string "type"; space; doc_id_ocaml_type id;]) (doc_typquant_ocaml typq (braces fs_doc))
  | TD_variant(id,nm,typq,ar,_) ->
      let ar_doc = group (separate_map (break 1) doc_type_union_ocaml ar) in
      doc_op equals
        (concat [string "type"; space; doc_id_ocaml_type id;])
        (doc_typquant_ocaml typq ar_doc)
  | TD_enum(id,nm,enums,_) ->
      let enums_doc = group (separate_map (break 1 ^^ pipe) doc_id_ocaml_ctor enums) in
      doc_op equals
        (concat [string "type"; space; doc_id_ocaml_type id;])
        (enums_doc)
  | TD_register(id,n1,n2,rs) ->
    let doc_rid (r,id) = separate comma_sp [string_lit (doc_id id); doc_range_ocaml r;] in
    let doc_rids = group (separate_map (break 1) doc_rid rs) in
    match n1,n2 with
    | Nexp_aux(Nexp_constant i1,_),Nexp_aux(Nexp_constant i2,_) ->
      let dir = i1 < i2 in                  
      doc_op equals
        ((string "let") ^^ space ^^ doc_id_ocaml id ^^ space ^^ (string "init_val"))
        (separate space [string "Vregister";
                         (parens (separate comma_sp [string "init_val";
                                                     doc_nexp n1;
                                                     string (if dir then "true" else "false");
                                                     brackets doc_rids]))])

let doc_rec_ocaml (Rec_aux(r,_)) = match r with
  | Rec_nonrec -> empty
  | Rec_rec -> string "rec" ^^ space

let doc_tannot_opt_ocaml (Typ_annot_opt_aux(t,_)) = match t with
  | Typ_annot_opt_some(tq,typ) -> doc_typquant_ocaml tq (doc_typ_ocaml typ)

let doc_funcl_ocaml (FCL_aux(FCL_Funcl(id,pat,exp),_)) =
  group (doc_op arrow (doc_pat_ocaml pat) (doc_exp_ocaml exp))

let get_id = function
  | [] -> failwith "FD_function with empty list"
  | (FCL_aux (FCL_Funcl (id,_,_),_))::_ -> id

let doc_fundef_ocaml (FD_aux(FD_function(r, typa, efa, fcls),_)) =
  match fcls with
  | [] -> failwith "FD_function with empty function list"
  | [FCL_aux (FCL_Funcl(id,pat,exp),_)] ->
     (separate space [(string "let"); (doc_rec_ocaml r); (doc_id_ocaml id); (doc_pat_ocaml pat); equals]) ^^ hardline ^^ (doc_exp_ocaml exp)
  | _ ->
    let id = get_id fcls in
    let sep = hardline ^^ pipe ^^ space in
    let clauses = separate_map sep doc_funcl fcls in
    separate space [string "let";
                    doc_rec_ocaml r;
                    doc_id_ocaml id;
                    equals;
                    (string "function");
                    clauses]

(*Aliases should be removed by here; registers not sure about*)
(*let doc_dec (DEC_aux (reg,_)) =
  match reg with
    | DEC_reg(typ,id) -> separate space [string "register"; doc_atomic_typ typ; doc_id id]
    | DEC_alias(id,alspec) ->
        doc_op equals (string "register alias" ^^ space ^^ doc_id id) (doc_alias alspec)
    | DEC_typ_alias(typ,id,alspec) -> 
        doc_op equals (string "register alias" ^^ space ^^ doc_atomic_typ typ) (doc_alias alspec)*)

let doc_def_ocaml def = group (match def with
  | DEF_default df -> empty
  | DEF_spec v_spec -> empty (*unless we want to have a separate pass to create mli files*)
  | DEF_type t_def -> doc_typdef_ocaml t_def
  | DEF_fundef f_def -> doc_fundef_ocaml f_def
  | DEF_val lbind -> doc_let_ocaml lbind
  | DEF_reg_dec dec -> empty (*unless we want to have something for the declaration of a register and guess a default init value*)
  | DEF_scattered sdef -> empty (*shoulnd't still be here*)
  ) ^^ hardline

let doc_defs_ocaml (Defs(defs)) =
  separate_map hardline doc_def_ocaml defs
let pp_defs_ocaml f d top_line opens =
  print f (string "(*" ^^ (string top_line) ^^ string "*)" ^/^
           (separate_map hardline (fun lib -> (string "open") ^^ space ^^ (string lib)) opens) ^/^ 
           (doc_defs_ocaml d))

(****************************************************************************
 * PPrint-based sail-to-lem pretty printer
****************************************************************************)


(*
  | E_for(id,exp1,exp2,exp3,(Ord_aux(order,_)),exp4) ->

     let updated_vars =
       let vars = List.map (function Id_aux (Id name,_) -> name
                                   | Id_aux (DeIid name,_) -> name)
                           (Analyser.find_updated_vars exp4) in
       "[" ^ String.concat ";" vars ^ "]" in
     
     let start = group (exp exp1) in
     let stop = group (exp exp2) in
     let by = group (exp exp3) in
     let var = doc_id_ocaml id in
     let body = exp exp4 in

     let forL = if order = Ord_inc then string "foreach_inc" else string "foreach_dec" in
     forL ^^ space ^^ start ^^ stop ^^ by ^/^
       group (
           (string "fun") ^^ space ^^ updated_vars ^^ space var ^^ space ^^ arrow ^/^
           body ^/^
           (string "return") ^^ space ^^ updated_vars
         )
             
        (* this way requires the following OCaml declarations first

         let rec foreach_inc i stop by body = 
           if i <= stop then (body i; foreach_inc (i + by) stop by body) else ()

         let rec foreach_dec i stop by body = 
           if i >= stop then (body i; foreach_dec (i - by) stop by body) else ()

         and we need to make sure not to use the "ignore bind" function >> for sequentially
         composing the for-loop with another expression, so we don't "forget" the updated
         variables
         *)
*)
