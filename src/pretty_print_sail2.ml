
open Ast
open Ast_util
open PPrint

let doc_op symb a b = infix 2 1 symb a b

let doc_id (Id_aux (id_aux, _)) =
  string (match id_aux with
          | Id v -> v
          | DeIid op -> "op " ^ op)

let doc_kid kid = string (Ast_util.string_of_kid kid)

let doc_int n = string (string_of_int n)

let doc_ord (Ord_aux(o,_)) = match o with
  | Ord_var v -> doc_kid v
  | Ord_inc -> string "inc"
  | Ord_dec -> string "dec"

let rec doc_nexp (Nexp_aux (n_aux, _)) =
  match n_aux with
  | Nexp_constant c -> string (string_of_int c)
  | Nexp_id id -> doc_id id
  | Nexp_var kid -> doc_kid kid
  | _ -> string "NEXP"

let doc_nc =
  let rec atomic_nc (NC_aux (nc_aux, _) as nc) =
    match nc_aux with
    | NC_true -> string "true"
    | NC_false -> string "false"
    | NC_set (kid, ints) ->
       separate space [doc_kid kid; string "in"; braces (separate_map (comma ^^ space) doc_int ints)]
    | _ -> parens (nc0 nc)
  and nc0 (NC_aux (nc_aux, _)) = string "NC0"
  in
  atomic_nc

let rec doc_typ (Typ_aux (typ_aux, _)) =
  match typ_aux with
  | Typ_id id -> doc_id id
  | Typ_app (id, []) -> doc_id id
  | Typ_app (Id_aux (DeIid str, _), [x; y]) ->
     separate space [doc_typ_arg x; doc_typ_arg y]
  | Typ_app (id, typs) -> doc_id id ^^ parens (separate_map (string ", ") doc_typ_arg typs)
  | Typ_tup typs -> parens (separate_map (string ", ") doc_typ typs)
  | Typ_var kid -> doc_kid kid
  | Typ_wild -> assert false
  (* Resugar set types like {|1, 2, 3|} *)
  | Typ_exist ([kid1], NC_aux (NC_set (kid2, ints), _), Typ_aux (Typ_app (id, [Typ_arg_aux (Typ_arg_typ (Typ_aux (Typ_var kid3, _)), _)]), _))
         when Kid.compare kid1 kid2 == 0 && Kid.compare kid2 kid3 == 0 ->
     enclose (string "{|") (string "|}") (separate_map (string ", ") doc_int ints)
  | Typ_exist (kids, nc, typ) ->
     braces (separate_map space doc_kid kids ^^ comma ^^ space ^^ doc_nc nc ^^ dot ^^ space ^^ doc_typ typ)
  | Typ_fn (typ1, typ2, eff) ->
     separate space [doc_typ typ1; string "->"; doc_typ typ2]
and doc_typ_arg (Typ_arg_aux (ta_aux, _)) =
  match ta_aux with
  | Typ_arg_typ typ -> doc_typ typ
  | Typ_arg_nexp nexp -> doc_nexp nexp
  | Typ_arg_order o -> doc_ord o

let doc_typschm (TypSchm_aux (TypSchm_ts (TypQ_aux (tq_aux, _), typ), _)) =
  match tq_aux with
  | TypQ_no_forall -> doc_typ typ
  | TypQ_tq [] -> doc_typ typ
  | TypQ_tq qs -> string "QI" ^^ dot ^^ space ^^ doc_typ typ

let doc_typschm_typ (TypSchm_aux (TypSchm_ts (TypQ_aux (tq_aux, _), typ), _)) = doc_typ typ

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
  | L_real r -> r
  | L_undef -> "undefined"
  | L_string s -> "\"" ^ String.escaped s ^ "\"")

let rec doc_pat (P_aux (p_aux, _)) =
  match p_aux with
  | P_id id -> doc_id id
  | P_tup pats -> lparen ^^ separate_map (comma ^^ space) doc_pat pats ^^ rparen
  | P_app (id, pats) -> doc_id id ^^ lparen ^^ separate_map (comma ^^ space) doc_pat pats ^^ rparen
  | P_typ (typ, pat) -> separate space [doc_pat pat; colon; doc_typ typ]
  | P_lit lit -> doc_lit lit
  | P_var (pat, kid) -> separate space [doc_pat pat; string "as"; doc_kid kid]
  | P_vector_concat pats -> separate_map (space ^^ string "@" ^^ space) doc_pat pats
  | P_wild -> string "_"
  | _ -> string "PAT"

let rec doc_exp (E_aux (e_aux, _) as exp) =
 match e_aux with
  | E_block exps -> surround 2 0 lbrace (doc_block exps) rbrace
  | E_nondet exps -> assert false
  | E_id id -> doc_id id
  | E_lit lit -> doc_lit lit
  | E_cast (typ, exp) ->
     separate space [doc_exp exp; colon; doc_typ typ]
  | E_app (id, exps) -> assert false
  | E_app_infix (x, id, y) -> doc_op (doc_id id) (doc_exp x) (doc_exp y)
  | E_tuple exps -> assert false
  | E_if (if_exp, then_exp, else_exp) -> assert false
  | E_for (id, exp1, exp2, exp3, order, exp4) -> assert false
  | E_vector exps -> assert false
  | E_vector_access (exp1, exp2) -> assert false
  | E_vector_subrange (exp1, exp2, exp3) -> doc_exp exp1 ^^ brackets (separate space [doc_exp exp2; string ".."; doc_exp exp3])
  | E_vector_update (exp1, exp2, exp3) -> assert false
  | E_vector_update_subrange (exp1, exp2, exp3, exp4) -> assert false
  | E_list exps -> assert false
  | E_cons (exp1, exp2) -> assert false
  | E_record fexps -> assert false
  | E_record_update (exp, fexps) -> assert false
  | E_field (exp, id) -> assert false
  | E_case (exp, pexps) ->
     separate space [string "match"; doc_exp exp; doc_pexps pexps]
  | E_let (lb, exp) -> assert false
  | E_assign (lexp, exp) ->
     separate space [doc_lexp lexp; equals; doc_exp exp]
  | E_sizeof nexp -> assert false
  | E_constraint nc -> assert false
  | E_exit exp -> assert false
  | E_throw exp -> assert false
  | E_try (exp, pexps) -> assert false
  | E_return exp -> assert false
and doc_block = function
  | [] -> assert false
  | [exp] -> doc_exp exp
  | exp :: exps -> doc_exp exp ^^ semi ^^ break 1 ^^ doc_block exps
and doc_lexp (LEXP_aux (l_aux, _)) =
  match l_aux with
  | LEXP_id id -> doc_id id
  | LEXP_tup lexps -> lparen ^^ separate_map (comma ^^ space) doc_lexp lexps ^^ rparen
  | _ -> string "LEXP"
and doc_pexps pexps = surround 2 0 lbrace (separate_map (semi ^^ hardline) doc_pexp pexps) rbrace
and doc_pexp (Pat_aux (pat_aux, _)) =
  match pat_aux with
  | Pat_exp (pat, exp) -> separate space [doc_pat pat; string "=>"; doc_exp exp]
  | Pat_when (pat, wh, exp) ->
     separate space [doc_pat pat; string "if"; doc_exp wh; string "=>"; doc_exp exp]
and doc_letbind (LB_aux (lb_aux, _)) =
  match lb_aux with
  | LB_val (pat, exp) ->
     separate space [doc_pat pat; equals; doc_exp exp]

let doc_funcl funcl = string "FUNCL"

let doc_funcl (FCL_aux  (FCL_Funcl (id, pat, exp), _)) =
  group (separate space [doc_id id; doc_pat pat; equals; doc_exp exp])

let doc_default (DT_aux(df,_)) = match df with
  | DT_kind(bk,v) -> string "DT_kind" (* separate space [string "default"; doc_bkind bk; doc_var v] *)
  | DT_typ(ts,id) -> separate space [string "default"; doc_typschm ts; doc_id id]
  | DT_order(ord) -> separate space [string "default"; string "Order"; doc_ord ord]

let doc_fundef (FD_aux (FD_function (r, typa, efa, funcls), _)) =
  match funcls with
  | [] -> failwith "Empty function list"
  | _ ->
     let sep = hardline ^^ string "and" ^^ space in
     let clauses = separate_map sep doc_funcl funcls in
     string "function" ^^ space ^^ clauses

let doc_dec (DEC_aux (reg,_)) =
  match reg with
  | DEC_reg (typ, id) -> separate space [string "register"; doc_id id; colon; doc_typ typ]
  | DEC_alias(id,alspec) -> string "ALIAS"
  | DEC_typ_alias(typ,id,alspec) -> string "ALIAS"

let doc_typdef (TD_aux(td,_)) = match td with
  | TD_abbrev(id, _, typschm) ->
      doc_op equals (concat [string "type"; space; doc_id id]) (doc_typschm_typ typschm)
  | _ -> string "TYPEDEF"

let doc_spec (VS_aux(v,_)) = match v with
  | VS_val_spec(ts,id,_,_) ->
     separate space [string "val"; doc_id id; colon; doc_typschm ts]
  | _ -> string "VS?"
(*
  | VS_cast_spec (ts, id) ->
     separate space [string "val"; string "cast"; doc_typscm ts; doc_id id]
  | VS_extern_no_rename(ts,id) ->
     separate space [string "val"; string "extern"; doc_typscm ts; doc_id id]
  | VS_extern_spec(ts,id,s) ->
     separate space [string "val"; string "extern"; doc_typscm ts; doc_op equals (doc_id id) (dquotes (string s))]
               *)
let rec doc_def def = group (match def with
  | DEF_default df -> doc_default df
  | DEF_spec v_spec -> doc_spec v_spec
  | DEF_type t_def -> doc_typdef t_def
  | DEF_kind k_def -> string "TOPLEVEL"
  | DEF_fundef f_def -> doc_fundef f_def
  | DEF_val lbind -> string "let" ^^ space ^^ doc_letbind lbind
  | DEF_reg_dec dec -> doc_dec dec
  | DEF_scattered sdef -> string "TOPLEVEL"
  | DEF_overload (id, ids) ->
      string "TOPLEVEL"
  | DEF_comm (DC_comm s) -> string "TOPLEVEL"
  | DEF_comm (DC_comm_struct d) -> string "TOPLEVEL"
  ) ^^ hardline

let doc_defs (Defs(defs)) =
  separate_map hardline doc_def defs

let pp_defs f d = ToChannel.pretty 1. 120 f (doc_defs d)
