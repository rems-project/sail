open Ast

let rec list_format (sep : string) (fmt : 'a -> string) (ls : 'a list) : string =
  match ls with
  | [] -> ""
  | [a] -> fmt a
  | a::ls -> (fmt a) ^ sep ^ (list_format sep fmt ls)

let pp_format_id (Id_aux(i,_)) =
  match i with
  | Id(i) -> i
  | DeIid(x) -> "(:" ^ x ")"

let pp_format_bkind (BK_aux(k,_)) =
  match k with
  | BK_type -> "Type"
  | BK_nat -> "Nat"
  | BK_order -> "Order"
  | BK_effects -> "Effects"

let pp_format_kind (K_aux(K_kind(klst),_)) = 
  list_format " -> " pp_format_bkind klst
 
let rec pp_format_typ (Typ_aux(t,_)) =
  match t with
  | Typ_id(id) -> pp_format_id id
  | Typ_wild -> "_"
  | Typ_fn(arg,ret,efct) -> (pp_format_typ arg) ^ " -> " ^ 
                            (pp_format_typ ret) ^ " " ^
                            (pp_format_effect efct)
  | Typ_tup(typs) -> "(" ^ (list_format ", " pp_format_typ args) ^ ")"
  | Typ_app(id,args) -> (pp_format_id id) ^ (list_format " " pp_format_typ_arg args)
and pp_format_nexp (Nexp_aux(n,_)) = 
  match n with
  | Nexp_id(id) -> pp_format_id id
  | Nexp_constant(i) -> string_of_int i
  | Nexp_sum(n1,n2) -> "(" ^ (pp_format_nexp n1) ^ " + ^ " (pp_format_nexp n2) ^ ")"
  | Nexp_times(n1,n2) -> "(" ^  (pp_format_nexp n1) ^ " * " ^ (pp_format_nexp n2) ^ ")"
  | Nexp_exp(n1) -> "2** (" ^ (pp_format_nexp n1) ^ ")"
and pp_format_ord (Ord_aux(o,_)) = 
  match o with
  | Ord_id(id) -> pp_format_id id
  | Ord_inc -> "inc"
  | Ord_dec -> "dec"  
and pp_format_effect (Effects_aux(e,_)) =
  match e with
  | Effects_var(id) -> "effect " ^ pp_format id
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
	 efcts) " }"
and pp_format_typ_arg (Typ_arg_aux(t,_)) = 
  match t with
  | Typ_arg_typ(t) -> pp_format_typ t
  | Typ_arg_nexp(n) -> pp_format_nexp n
  | Typ_arg_order(o) -> pp_format_ord o
  | Typ_arg_Efct(e) -> pp_format_effects e

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

let pp_format_qi (QI_aux(qi,_)) =
  match qi with
  | QI_const(n_const) -> pp_format_nexp_constraint qi
  | QI_id(KOpt_aux(ki,_)) ->
    (match ki with
    | KOpt_none(id) -> pp_format_id id
    | KOpt_kind(k,id) -> pp_format_kind k ^ " " pp_format_id id)

let pp_format_typquant (TypQ_aux(tq,_)) =
  match tq with
  | TypQ_no_forall -> ""
  | TypQ_tq(qlist) ->
    "forall " ^ 
    (list_format ", " pp_format_qi qlist) ^
    ". "

let pp_format_typscm (TypSchm_aux(TypSchm_ts(tq,t),_)) =
  (pp_format_typquant tq) ^ pp_format_typ t
 
let pp_format_lit (L_aux(l,_)) =
  match l with
  | L_unit -> "()"
  | L_zero -> "0"
  | L_one -> "1"
  | L_true -> "true"
  | L_false -> "false"
  | L_num(i) -> string_of_int i
  | L_hex(n) | L_bin(n) -> n
  | L_string(s) -> "\"" ^ s "\"" 

let rec pp_format_pat (P_aux(p,l)) =
  match p with
  | P_lit(lit) -> pp_format_lit lit
  | P_wild -> "_"
  | P_id(id) -> pp_format_id id
  | P_as(pat,id) -> "(" ^ pp_format_pat pat ^ " as " ^ pp_format_id id ^ ")"
  | P_typ(typ,pat) -> "<" ^ pp_format_typ typ ^ "> " ^ pp_format_pat pat
  | P_app(id,pats) -> pp_format_id id ^ "(" ^
                      list_format ", " pp_format_pat pats ^ ")"
  | P_record(fpats) -> "{" ^
                       list_format "; " (fun (FP_aux(FP_Fpat(id,fpat),_)) -> 
			                  pp_format_id id ^ " = " pp_format_pat fpat) fpats
                       ^ "}"
  | P_vector(pats) -> "[" ^ list_format "; " pp_format_pats pats ^ "]"
  | P_vector_indexed(ipats) ->
    "[" ^ list_format "; " (fun (i,p) -> string_of_int i ^ " = " pp_format_pat p) ipats ^ "]"
  | P_vector_concat(pats) ->
    list_format " ^ " pp_format_pats pats
  | P_tup(pats) -> "(" ^ (list_format ", " pp_format_pats pats) ^ ")"
  | P_list(pats) -> "[|" ^ (list_format "; " pp_format_pats pats) ^ "|]"




let pp_format_ast defs = assert false
