(**************************************************************************)
(*     Sail                                                               *)
(*                                                                        *)
(*  Copyright (c) 2013-2017                                               *)
(*    Kathyrn Gray                                                        *)
(*    Shaked Flur                                                         *)
(*    Stephen Kell                                                        *)
(*    Gabriel Kerneis                                                     *)
(*    Robert Norton-Wright                                                *)
(*    Christopher Pulte                                                   *)
(*    Peter Sewell                                                        *)
(*    Alasdair Armstrong                                                  *)
(*    Brian Campbell                                                      *)
(*    Thomas Bauereiss                                                    *)
(*    Anthony Fox                                                         *)
(*    Jon French                                                          *)
(*    Dominic Mulligan                                                    *)
(*    Stephen Kell                                                        *)
(*    Mark Wassell                                                        *)
(*                                                                        *)
(*  All rights reserved.                                                  *)
(*                                                                        *)
(*  This software was developed by the University of Cambridge Computer   *)
(*  Laboratory as part of the Rigorous Engineering of Mainstream Systems  *)
(*  (REMS) project, funded by EPSRC grant EP/K008528/1.                   *)
(*                                                                        *)
(*  Redistribution and use in source and binary forms, with or without    *)
(*  modification, are permitted provided that the following conditions    *)
(*  are met:                                                              *)
(*  1. Redistributions of source code must retain the above copyright     *)
(*     notice, this list of conditions and the following disclaimer.      *)
(*  2. Redistributions in binary form must reproduce the above copyright  *)
(*     notice, this list of conditions and the following disclaimer in    *)
(*     the documentation and/or other materials provided with the         *)
(*     distribution.                                                      *)
(*                                                                        *)
(*  THIS SOFTWARE IS PROVIDED BY THE AUTHOR AND CONTRIBUTORS ``AS IS''    *)
(*  AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED     *)
(*  TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A       *)
(*  PARTICULAR PURPOSE ARE DISCLAIMED.  IN NO EVENT SHALL THE AUTHOR OR   *)
(*  CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,          *)
(*  SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT      *)
(*  LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF      *)
(*  USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND   *)
(*  ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,    *)
(*  OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT    *)
(*  OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF    *)
(*  SUCH DAMAGE.                                                          *)
(**************************************************************************)

open Ast
open Ast_util
open PPrint

module Big_int = Nat_big_num

let doc_op symb a b = infix 2 1 symb a b

let doc_id (Id_aux (id_aux, _)) =
  string (match id_aux with
          | Id v -> v
          | DeIid op -> "operator " ^ op)

let doc_kid kid = string (Ast_util.string_of_kid kid)

let doc_int n = string (Big_int.to_string n)

let doc_ord (Ord_aux(o,_)) = match o with
  | Ord_var v -> doc_kid v
  | Ord_inc -> string "inc"
  | Ord_dec -> string "dec"

let rec doc_typ_pat (TP_aux (tpat_aux, _)) =
  match tpat_aux with
  | TP_wild -> string "_"
  | TP_var kid -> doc_kid kid
  | TP_app (f, tpats) -> doc_id f ^^ parens (separate_map (comma ^^ space) doc_typ_pat tpats)

let rec doc_nexp =
  let rec atomic_nexp (Nexp_aux (n_aux, _) as nexp) =
    match n_aux with
    | Nexp_constant c -> string (Big_int.to_string c)
    | Nexp_app (id, nexps) -> string (string_of_nexp nexp)
    (* This segfaults??!!!!
       doc_id id ^^ (parens (separate_map (comma ^^ space) doc_nexp nexps))
     *)
    | Nexp_id id -> doc_id id
    | Nexp_var kid -> doc_kid kid
    | _ -> parens (nexp0 nexp)
  and nexp0 (Nexp_aux (n_aux, _) as nexp) =
    match n_aux with
    | Nexp_sum (n1, Nexp_aux (Nexp_neg n2, _)) | Nexp_minus (n1, n2) ->
       separate space [nexp0 n1; string "-"; nexp1 n2]
    | Nexp_sum (n1, Nexp_aux (Nexp_constant c, _)) when Big_int.less c Big_int.zero ->
       separate space [nexp0 n1; string "-"; doc_int (Big_int.abs c)]
    | Nexp_sum (n1, n2) -> separate space [nexp0 n1; string "+"; nexp1 n2]
    | _ -> nexp1 nexp
  and nexp1 (Nexp_aux (n_aux, _) as nexp) =
    match n_aux with
    | Nexp_times (n1, n2) -> separate space [nexp1 n1; string "*"; nexp2 n2]
    | _ -> nexp2 nexp
  and nexp2 (Nexp_aux (n_aux, _) as nexp) =
    match n_aux with
    | Nexp_neg n -> separate space [string "-"; atomic_nexp n]
    | Nexp_exp n -> separate space [string "2"; string "^"; atomic_nexp n]
    | _ -> atomic_nexp nexp
  in
  nexp0

let doc_nc =
  let nc_op op n1 n2 = separate space [doc_nexp n1; string op; doc_nexp n2] in
  let rec atomic_nc (NC_aux (nc_aux, _) as nc) =
    match nc_aux with
    | NC_true -> string "true"
    | NC_false -> string "false"
    | NC_equal (n1, n2) -> nc_op "=" n1 n2
    | NC_not_equal (n1, n2) -> nc_op "!=" n1 n2
    | NC_bounded_ge (n1, n2) -> nc_op ">=" n1 n2
    | NC_bounded_le (n1, n2) -> nc_op "<=" n1 n2
    | NC_set (kid, ints) ->
       separate space [doc_kid kid; string "in"; braces (separate_map (comma ^^ space) doc_int ints)]
    | _ -> parens (nc0 nc)
  and nc0 (NC_aux (nc_aux, _) as nc) =
    match nc_aux with
    | NC_or (c1, c2) -> separate space [nc0 c1; string "|"; nc1 c2]
    | _ -> nc1 nc
  and nc1 (NC_aux (nc_aux, _) as nc) =
    match nc_aux with
    | NC_and (c1, c2) -> separate space [nc1 c1; string "&"; atomic_nc c2]
    | _ -> atomic_nc nc
  in
  nc0

let rec doc_typ (Typ_aux (typ_aux, _)) =
  match typ_aux with
  | Typ_id id -> doc_id id
  | Typ_app (id, []) -> doc_id id
  | Typ_app (Id_aux (DeIid str, _), [x; y]) ->
     separate space [doc_typ_arg x; doc_typ_arg y]
              (*
  | Typ_app (id, [_; len; _; Typ_arg_aux (Typ_arg_typ (Typ_aux (Typ_id tid, _)), _)]) when Id.compare (mk_id "vector") id == 0 && Id.compare (mk_id "bit") tid == 0->
     string "bits" ^^ parens (doc_typ_arg len)
               *)
  | Typ_app (id, typs) -> doc_id id ^^ parens (separate_map (string ", ") doc_typ_arg typs)
  | Typ_tup typs -> parens (separate_map (string ", ") doc_typ typs)
  | Typ_var kid -> doc_kid kid
  (* Resugar set types like {|1, 2, 3|} *)
  | Typ_exist ([kid1], NC_aux (NC_set (kid2, ints), _), Typ_aux (Typ_app (id, [Typ_arg_aux (Typ_arg_nexp (Nexp_aux (Nexp_var kid3, _)), _)]), _))
         when Kid.compare kid1 kid2 == 0 && Kid.compare kid2 kid3 == 0 && Id.compare (mk_id "atom") id == 0 ->
     enclose (string "{|") (string "|}") (separate_map (string ", ") doc_int ints)
  | Typ_exist (kids, nc, typ) ->
     braces (separate_map space doc_kid kids ^^ comma ^^ space ^^ doc_nc nc ^^ dot ^^ space ^^ doc_typ typ)
  | Typ_fn (typ1, typ2, Effect_aux (Effect_set [], _)) ->
     separate space [doc_typ typ1; string "->"; doc_typ typ2]
  | Typ_fn (typ1, typ2, Effect_aux (Effect_set effs, _)) ->
     let ocaml_eff = braces (separate (comma ^^ space) (List.map (fun be -> string (string_of_base_effect be)) effs)) in
     separate space [doc_typ typ1; string "->"; doc_typ typ2; string "effect"; ocaml_eff]
and doc_typ_arg (Typ_arg_aux (ta_aux, _)) =
  match ta_aux with
  | Typ_arg_typ typ -> doc_typ typ
  | Typ_arg_nexp nexp -> doc_nexp nexp
  | Typ_arg_order o -> doc_ord o

let doc_quants quants =
  let doc_qi_kopt (QI_aux (qi_aux, _)) =
    match qi_aux with
    | QI_id (KOpt_aux (KOpt_none kid, _)) -> [doc_kid kid]
    | QI_id kopt when is_nat_kopt kopt -> [parens (separate space [doc_kid (kopt_kid kopt); colon; string "Int"])]
    | QI_id kopt when is_typ_kopt kopt -> [parens (separate space [doc_kid (kopt_kid kopt); colon; string "Type"])]
    | QI_id kopt -> [parens (separate space [doc_kid (kopt_kid kopt); colon; string "Order"])]
    | QI_const nc -> []
  in
  let qi_nc (QI_aux (qi_aux, _)) =
    match qi_aux with
    | QI_const nc -> [nc]
    | _ -> []
  in
  let kdoc = separate space (List.concat (List.map doc_qi_kopt quants)) in
  let ncs = List.concat (List.map qi_nc quants) in
  match ncs with
  | [] -> kdoc
  | [nc] -> kdoc ^^ comma ^^ space ^^ doc_nc nc
  | nc :: ncs -> kdoc ^^ comma ^^ space ^^ doc_nc (List.fold_left nc_and nc ncs)



let doc_binding (TypQ_aux (tq_aux, _), typ) =
  match tq_aux with
  | TypQ_no_forall -> doc_typ typ
  | TypQ_tq [] -> doc_typ typ
  | TypQ_tq qs ->
     string "forall" ^^ space ^^ doc_quants qs ^^ dot ^//^ doc_typ typ

let doc_typschm (TypSchm_aux (TypSchm_ts (typq, typ), _)) = doc_binding (typq, typ)

let doc_typschm_typ (TypSchm_aux (TypSchm_ts (TypQ_aux (tq_aux, _), typ), _)) = doc_typ typ

let doc_typschm_quants (TypSchm_aux (TypSchm_ts (TypQ_aux (tq_aux, _), typ), _)) =
  match tq_aux with
  | TypQ_no_forall -> None
  | TypQ_tq [] -> None
  | TypQ_tq qs -> Some (doc_quants qs)

let doc_lit (L_aux(l,_)) =
  utf8string (match l with
  | L_unit  -> "()"
  | L_zero  -> "bitzero"
  | L_one   -> "bitone"
  | L_true  -> "true"
  | L_false -> "false"
  | L_num i -> Big_int.to_string i
  | L_hex n -> "0x" ^ n
  | L_bin n -> "0b" ^ n
  | L_real r -> r
  | L_undef -> "undefined"
  | L_string s -> "\"" ^ String.escaped s ^ "\"")

let rec doc_pat (P_aux (p_aux, _) as pat) =
  match p_aux with
  | P_id id -> doc_id id
  | P_tup pats -> lparen ^^ separate_map (comma ^^ space) doc_pat pats ^^ rparen
  | P_typ (typ, pat) -> separate space [doc_pat pat; colon; doc_typ typ]
  | P_lit lit -> doc_lit lit
  (* P_var short form sugar *)
  | P_var (P_aux (P_id id, _), TP_aux (TP_var kid, _)) when Id.compare (id_of_kid kid) id == 0 ->
     doc_kid kid
  | P_var (pat, tpat) -> separate space [doc_pat pat; string "as"; doc_typ_pat tpat]
  | P_vector pats -> brackets (separate_map (comma ^^ space) doc_pat pats)
  | P_vector_concat pats -> separate_map (space ^^ string "@" ^^ space) doc_pat pats
  | P_wild -> string "_"
  | P_as (pat, id) -> parens (separate space [doc_pat pat; string "as"; doc_id id])
  | P_app (id, pats) -> doc_id id ^^ parens (separate_map (comma ^^ space) doc_pat pats)
  | P_list pats -> string "[|" ^^ separate_map (comma ^^ space) doc_pat pats ^^ string "|]"
  | _ -> string (string_of_pat pat)

(* if_block_x is true if x should be printed like a block, i.e. with
   newlines. Blocks are automatically printed as blocks, so this
   returns false for them. *)
let if_block_then (E_aux (e_aux, _)) =
  match e_aux with
  | E_assign _ | E_if _ -> true
  | _ -> false

let if_block_else (E_aux (e_aux, _)) =
  match e_aux with
  | E_assign _ -> true
  | _ -> false

let fixities =
  let fixities' =
    List.fold_left
      (fun r (x, y) -> Bindings.add x y r)
      Bindings.empty
      [
        (mk_id "^", (InfixR, 8));
        (mk_id "*", (InfixL, 7));
        (mk_id "+", (InfixL, 6));
        (mk_id "-", (InfixL, 6));
        (mk_id "!=", (Infix, 4));
        (mk_id ">", (Infix, 4));
        (mk_id "<", (Infix, 4));
        (mk_id ">=", (Infix, 4));
        (mk_id "<=", (Infix, 4));
        (mk_id "&", (InfixR, 3));
        (mk_id "|", (InfixR, 2));
      ]
  in
  ref (fixities' : (prec * int) Bindings.t)

let rec doc_exp (E_aux (e_aux, _) as exp) =
  match e_aux with
  | E_block [] -> string "()"
  | E_block [exp] -> doc_exp exp
  | E_block exps -> surround 2 0 lbrace (doc_block exps) rbrace
  | E_nondet exps -> assert false
  (* This is mostly for the -convert option *)
  | E_app_infix (x, id, y) when Id.compare (mk_id "quot") id == 0 ->
     separate space [doc_atomic_exp x; string "/"; doc_atomic_exp y]
  | E_app_infix _ -> doc_infix 0 exp
  | E_tuple exps -> parens (separate_map (comma ^^ space) doc_exp exps)

  (* Various rules to try to format if blocks nicely based on content *)
  | E_if (if_exp, then_exp, else_exp) when if_block_then then_exp && if_block_else else_exp ->
     (separate space [string "if"; doc_exp if_exp; string "then"] ^//^ doc_exp then_exp)
     ^/^ (string "else" ^//^ doc_exp else_exp)
  | E_if (if_exp, then_exp, (E_aux (E_if _, _) as else_exp)) when if_block_then then_exp ->
     (separate space [string "if"; doc_exp if_exp; string "then"] ^//^ doc_exp then_exp)
     ^/^ (string "else" ^^ space ^^ doc_exp else_exp)
  | E_if (if_exp, then_exp, else_exp) when if_block_else else_exp ->
     (separate space [string "if"; doc_exp if_exp; string "then"; doc_exp then_exp])
     ^^ space ^^ (string "else" ^//^ doc_exp else_exp)
  | E_if (if_exp, then_exp, else_exp) when if_block_then then_exp ->
     (separate space [string "if"; doc_exp if_exp; string "then"] ^//^ doc_exp then_exp)
     ^/^ (string "else" ^^ space ^^ doc_exp else_exp)
  | E_if (if_exp, then_exp, else_exp) ->
     group (separate space [string "if"; doc_exp if_exp; string "then"; doc_exp then_exp; string "else"; doc_exp else_exp])

  | E_list exps -> string "[|" ^^ separate_map (comma ^^ space) doc_exp exps ^^ string "|]"
  | E_cons (exp1, exp2) -> doc_atomic_exp exp1 ^^ space ^^ string "::" ^^ space ^^ doc_exp exp2
  | E_record fexps -> separate space [string "struct"; string "{"; doc_fexps fexps; string "}"]
  | E_loop (While, cond, exp) ->
     separate space [string "while"; doc_exp cond; string "do"; doc_exp exp]
  | E_loop (Until, cond, exp) ->
     separate space [string "repeat"; doc_exp exp; string "until"; doc_exp cond]
  | E_record_update (exp, fexps) ->
     separate space [string "{"; doc_exp exp; string "with"; doc_fexps fexps; string "}"]
  | E_vector_append (exp1, exp2) -> separate space [doc_atomic_exp exp1; string "@"; doc_atomic_exp exp2]
  | E_case (exp, pexps) ->
     separate space [string "match"; doc_exp exp; doc_pexps pexps]
  | E_let (LB_aux (LB_val (pat, binding), _), exp) ->
     separate space [string "let"; doc_pat pat; equals; doc_exp binding; string "in"; doc_exp exp]
  | E_internal_plet (pat, exp1, exp2) ->
     let le =
       prefix 2 1
         (separate space [string "internal_plet"; doc_pat pat; equals])
         (doc_exp exp1) in
     doc_op (string "in") le (doc_exp exp2)
  | E_var (lexp, binding, exp) ->
     separate space [string "var"; doc_lexp lexp; equals; doc_exp binding; string "in"; doc_exp exp]
  | E_assign (lexp, exp) ->
     separate space [doc_lexp lexp; equals; doc_exp exp]
  | E_for (id, exp1, exp2, exp3, order, exp4) ->
     begin
       let header =
         string "foreach" ^^ space ^^
           group (parens (separate (break 1)
                                   [ doc_id id;
                                     string "from " ^^ doc_atomic_exp exp1;
                                     string "to " ^^ doc_atomic_exp exp2;
                                     string "by " ^^ doc_atomic_exp exp3;
                                     string "in " ^^ doc_ord order ]))
       in
       match exp4 with
       | E_aux (E_block [_], _) -> header ^//^ doc_exp exp4
       | E_aux (E_block _, _) -> header ^^ space ^^ doc_exp exp4
       | _ -> header ^//^ doc_exp exp4
     end
  (* Resugar an assert with an empty message *)
  | E_throw exp -> string "throw" ^^ parens (doc_exp exp)
  | E_try (exp, pexps) ->
     separate space [string "try"; doc_exp exp; string "catch"; doc_pexps pexps]
  | E_return exp -> string "return" ^^ parens (doc_exp exp)
  | E_internal_return exp -> string "internal_return" ^^ parens (doc_exp exp)
  | E_app (id, [exp]) when Id.compare (mk_id "pow2") id == 0 ->
     separate space [string "2"; string "^"; doc_atomic_exp exp]
  | _ -> doc_atomic_exp exp
and doc_infix n (E_aux (e_aux, _) as exp) =
  match e_aux with
  | E_app_infix (l, op, r) when n < 10 ->
     begin
       try
         match Bindings.find op !fixities with
         | (Infix, m) when m >= n -> separate space [doc_infix (m + 1) l; doc_id op; doc_infix (m + 1) r]
         | (Infix, m) when m < n -> parens (separate space [doc_infix (m + 1) l; doc_id op; doc_infix (m + 1) r])
         | (InfixL, m) when m >= n -> separate space [doc_infix m l; doc_id op; doc_infix (m + 1) r]
         | (InfixL, m) when m < n -> parens (separate space [doc_infix m l; doc_id op; doc_infix (m + 1) r])
         | (InfixR, m) when m >= n -> separate space [doc_infix (m + 1) l; doc_id op; doc_infix m r]
         | (InfixR, m) when m < n -> parens (separate space [doc_infix (m + 1) l; doc_id op; doc_infix m r])
         | _ -> assert false
       with
       | Not_found ->
          separate space [doc_atomic_exp l; doc_id op; doc_atomic_exp r]
     end
  | _ -> doc_atomic_exp exp
and doc_atomic_exp (E_aux (e_aux, _) as exp) =
  match e_aux with
  | E_cast (typ, exp) ->
     separate space [doc_atomic_exp exp; colon; doc_typ typ]
  | E_lit lit -> doc_lit lit
  | E_id id -> doc_id id
  | E_ref id -> string "ref" ^^ space ^^ doc_id id
  | E_field (exp, id) -> doc_atomic_exp exp ^^ dot ^^ doc_id id
  | E_sizeof (Nexp_aux (Nexp_var kid, _)) -> doc_kid kid
  | E_sizeof nexp -> string "sizeof" ^^ parens (doc_nexp nexp)
  (* Format a function with a unit argument as f() rather than f(()) *)
  | E_app (id, [E_aux (E_lit (L_aux (L_unit, _)), _)]) -> doc_id id ^^ string "()"
  | E_app (id, exps) -> doc_id id ^^ parens (separate_map (comma ^^ space) doc_exp exps)
  | E_constraint nc -> string "constraint" ^^ parens (doc_nc nc)
  | E_assert (exp1, E_aux (E_lit (L_aux (L_string "", _)), _)) -> string "assert" ^^ parens (doc_exp exp1)
  | E_assert (exp1, exp2) -> string "assert" ^^ parens (doc_exp exp1 ^^ comma ^^ space ^^ doc_exp exp2)
  | E_exit exp -> string "exit" ^^ parens (doc_exp exp)
  | E_vector_access (exp1, exp2) -> doc_atomic_exp exp1 ^^ brackets (doc_exp exp2)
  | E_vector_subrange (exp1, exp2, exp3) -> doc_atomic_exp exp1 ^^ brackets (separate space [doc_exp exp2; string ".."; doc_exp exp3])
  | E_vector exps -> brackets (separate_map (comma ^^ space) doc_exp exps)
  | E_vector_update (exp1, exp2, exp3) ->
     brackets (separate space [doc_exp exp1; string "with"; doc_atomic_exp exp2; equals; doc_exp exp3])
  | E_vector_update_subrange (exp1, exp2, exp3, exp4) ->
     brackets (separate space [doc_exp exp1; string "with"; doc_atomic_exp exp2; string ".."; doc_atomic_exp exp3; equals; doc_exp exp4])
  | E_internal_value v -> string (Value.string_of_value v |> Util.green |> Util.clear)
  | _ -> parens (doc_exp exp)
and doc_fexps (FES_aux (FES_Fexps (fexps, _), _)) =
  separate_map (comma ^^ space) doc_fexp fexps
and doc_fexp (FE_aux (FE_Fexp (id, exp), _)) =
  separate space [doc_id id; equals; doc_exp exp]
and doc_block = function
  | [] -> string "()"
  | [E_aux (E_let (LB_aux (LB_val (pat, binding), _), E_aux (E_block exps, _)), _)] ->
     separate space [string "let"; doc_pat pat; equals; doc_exp binding] ^^ semi ^^ hardline ^^ doc_block exps
  | [E_aux (E_var (lexp, binding, E_aux (E_block exps, _)), _)] ->
     separate space [string "var"; doc_lexp lexp; equals; doc_exp binding] ^^ semi ^^ hardline ^^ doc_block exps
  | [exp] -> doc_exp exp
  | exp :: exps -> doc_exp exp ^^ semi ^^ hardline ^^ doc_block exps
and doc_lexp (LEXP_aux (l_aux, _) as lexp) =
  match l_aux with
  | LEXP_cast (typ, id) -> separate space [doc_id id; colon; doc_typ typ]
  | _ -> doc_atomic_lexp lexp
and doc_atomic_lexp (LEXP_aux (l_aux, _) as lexp) =
  match l_aux with
  | LEXP_id id -> doc_id id
  | LEXP_deref exp -> lparen ^^ string "*" ^^ doc_atomic_exp exp ^^ rparen
  | LEXP_tup lexps -> lparen ^^ separate_map (comma ^^ space) doc_lexp lexps ^^ rparen
  | LEXP_field (lexp, id) -> doc_atomic_lexp lexp ^^ dot ^^ doc_id id
  | LEXP_vector (lexp, exp) -> doc_atomic_lexp lexp ^^ brackets (doc_exp exp)
  | LEXP_vector_range (lexp, exp1, exp2) -> doc_atomic_lexp lexp ^^ brackets (separate space [doc_exp exp1; string ".."; doc_exp exp2])
  | LEXP_memory (id, exps) -> doc_id id ^^ parens (separate_map (comma ^^ space) doc_exp exps)
  | _ -> parens (doc_lexp lexp)
and doc_pexps pexps = surround 2 0 lbrace (separate_map (comma ^^ hardline) doc_pexp pexps) rbrace
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

let doc_funcl (FCL_aux  (FCL_Funcl (id, Pat_aux (pexp,_)), _)) =
  match pexp with
  | Pat_exp (pat,exp) ->
     group (separate space [doc_id id; doc_pat pat; equals; doc_exp exp])
  | Pat_when (pat,wh,exp) ->
     group (separate space [doc_id id; parens (separate space [doc_pat pat; string "if"; doc_exp wh]); string "="; doc_exp exp])

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

let doc_field (typ, id) =
  separate space [doc_id id; colon; doc_typ typ]

let doc_union (Tu_aux (Tu_ty_id (typ, id), l)) = separate space [doc_id id; colon; doc_typ typ]

let doc_typdef (TD_aux(td,_)) = match td with
  | TD_abbrev (id, _, typschm) ->
     begin
       match doc_typschm_quants typschm with
       | Some qdoc ->
          doc_op equals (concat [string "type"; space; doc_id id; space; qdoc]) (doc_typschm_typ typschm)
       | None ->
          doc_op equals (concat [string "type"; space; doc_id id]) (doc_typschm_typ typschm)
     end
  | TD_enum (id, _, ids, _) ->
     separate space [string "enum"; doc_id id; equals; surround 2 0 lbrace (separate_map (comma ^^ break 1) doc_id ids) rbrace]
  | TD_record (id, _, TypQ_aux (TypQ_no_forall, _), fields, _) | TD_record (id, _, TypQ_aux (TypQ_tq [], _), fields, _) ->
     separate space [string "struct"; doc_id id; equals; surround 2 0 lbrace (separate_map (comma ^^ break 1) doc_field fields) rbrace]
  | TD_record (id, _, TypQ_aux (TypQ_tq qs, _), fields, _) ->
     separate space [string "struct"; doc_id id; doc_quants qs; equals;
                     surround 2 0 lbrace (separate_map (comma ^^ break 1) doc_field fields) rbrace]
  | TD_variant (id, _, TypQ_aux (TypQ_no_forall, _), unions, _) | TD_variant (id, _, TypQ_aux (TypQ_tq [], _), unions, _) ->
     separate space [string "union"; doc_id id; equals; surround 2 0 lbrace (separate_map (comma ^^ break 1) doc_union unions) rbrace]
  | TD_variant (id, _, TypQ_aux (TypQ_tq qs, _), unions, _) ->
     separate space [string "union"; doc_id id; doc_quants qs; equals;
                     surround 2 0 lbrace (separate_map (comma ^^ break 1) doc_union unions) rbrace]
  | _ -> string "TYPEDEF"


let doc_spec (VS_aux(v,_)) =
  let doc_extern ext =
    let doc_backend b = Util.option_map (fun id -> string (b ^ ":") ^^ space ^^
      utf8string ("\"" ^ String.escaped id ^  "\"")) (ext b) in
    let docs = Util.option_these (List.map doc_backend ["ocaml"; "lem"; "smt"; "interpreter"; "c"]) in
    if docs = [] then empty else equals ^^ space ^^ braces (separate (comma ^^ space) docs)
  in
  match v with
  | VS_val_spec(ts,id,ext,is_cast) ->
     string "val" ^^ space
     ^^ (if is_cast then (string "cast" ^^ space) else empty)
     ^^ doc_id id ^^ space
     ^^ doc_extern ext
     ^^ colon ^^ space
     ^^ doc_typschm ts

let doc_prec = function
  | Infix -> string "infix"
  | InfixL -> string "infixl"
  | InfixR -> string "infixr"

let doc_kind_def (KD_aux (KD_nabbrev (_, id, _, nexp), _)) =
  separate space [string "integer"; doc_id id; equals; doc_nexp nexp]

let rec doc_scattered (SD_aux (sd_aux, _)) =
  match sd_aux with
  | SD_scattered_function (_, _, _, id) ->
     string "scattered" ^^ space ^^ string "function" ^^ space ^^ doc_id id
  | SD_scattered_funcl funcl ->
     string "function" ^^ space ^^ string "clause" ^^ space ^^ doc_funcl funcl
  | SD_scattered_end id ->
     string "end" ^^ space ^^ doc_id id
  | _ -> string "SCATTERED"

let rec doc_def def = group (match def with
  | DEF_default df -> doc_default df
  | DEF_spec v_spec -> doc_spec v_spec
  | DEF_type t_def -> doc_typdef t_def
  | DEF_kind k_def -> doc_kind_def k_def
  | DEF_fundef f_def -> doc_fundef f_def
  | DEF_val lbind -> string "let" ^^ space ^^ doc_letbind lbind
  | DEF_internal_mutrec fundefs ->
     (string "mutual {" ^//^ separate_map (hardline ^^ hardline) doc_fundef fundefs)
     ^^ hardline ^^ string "}"
  | DEF_reg_dec dec -> doc_dec dec
  | DEF_scattered sdef -> doc_scattered sdef
  | DEF_fixity (prec, n, id) ->
     fixities := Bindings.add id (prec, Big_int.to_int n) !fixities;
     separate space [doc_prec prec; doc_int n; doc_id id]
  | DEF_overload (id, ids) ->
     separate space [string "overload"; doc_id id; equals; surround 2 0 lbrace (separate_map (comma ^^ break 1) doc_id ids) rbrace]
  | DEF_comm (DC_comm s) -> string "TOPLEVEL"
  | DEF_comm (DC_comm_struct d) -> string "TOPLEVEL"
  ) ^^ hardline

let doc_defs (Defs(defs)) =
  separate_map hardline doc_def defs

let pp_defs f d = ToChannel.pretty 1. 80 f (doc_defs d)

let pretty_sail f doc = ToChannel.pretty 1. 120 f doc

let to_string doc =
  let b = Buffer.create 120 in
  ToBuffer.pretty 1. 120 b doc;
  Buffer.contents b
