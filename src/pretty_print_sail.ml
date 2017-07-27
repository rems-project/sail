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
open PPrint
open Pretty_print_common

(****************************************************************************
 * PPrint-based source-to-source pretty printer
****************************************************************************)

let doc_bkind (BK_aux(k,_)) =
  string (match k with
  | BK_type -> "Type"
  | BK_nat -> "Nat"
  | BK_order -> "Order"
  | BK_effect -> "Effect")

let doc_kind (K_aux(K_kind(klst),_)) =
  separate_map (spaces arrow) doc_bkind klst

let doc_qi (QI_aux(qi,_)) = match qi with
  | QI_const n_const -> doc_nexp_constraint n_const
  | QI_id(KOpt_aux(ki,_)) ->
    match ki with
    | KOpt_none v -> doc_var v
    | KOpt_kind(k,v) -> separate space [doc_kind k; doc_var v]

(* typ_doc is the doc for the type being quantified *)
let doc_typquant (TypQ_aux(tq,_)) typ_doc = match tq with
  | TypQ_no_forall -> typ_doc
  | TypQ_tq [] -> typ_doc
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
  | L_real r -> r
  | L_undef -> "undefined"
  | L_string s -> "\"" ^ String.escaped s ^ "\"")

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
  | P_cons (pat1, pat2) -> separate space [atomic_pat pat1; string "::"; pat pat2]
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
      (doc_id f) ^^ (parens (separate_map comma exp args))
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
  | E_comment s -> string ("(*" ^ s ^ "*) ()")
  | E_comment_struc e -> string "(*" ^^ exp e ^^ string "*) ()"
  | E_id id -> doc_id id
  | E_lit lit -> doc_lit lit
  | E_cast(typ,e) -> prefix 2 1 (parens (doc_typ typ)) (group (atomic_exp e))
                            (*
  | E_internal_cast((_,NoTyp),e) -> atomic_exp e
  | E_internal_cast((_,Base((_,t),_,_,_,_,bindings)), (E_aux(_,(_,eannot)) as e)) ->
      (match t.t,eannot with
      (* XXX I don't understand why we can hide the internal cast here
         AAA Because an internal cast between vectors is only generated to reset the base access;
             the type checker generates far more than are needed and they're pruned off here, after constraint resolution *)
      | Tapp("vector",[TA_nexp n1;_;_;_]),Base((_,{t=Tapp("vector",[TA_nexp n2;_;_;_])}),_,_,_,_,_)
          when nexp_eq n1 n2 -> atomic_exp e
      | _ -> prefix 2 1 (parens (doc_typ (t_to_typ t))) (group (atomic_exp e)))
                             *)
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
  | E_sizeof n ->
     separate space [string "sizeof"; doc_nexp n]
  | E_constraint nc ->
     string "constraint" ^^ parens (doc_nexp_constraint nc)
  | E_exit e ->
    separate space [string "exit"; atomic_exp e;]
  | E_return e ->
    separate space [string "return"; atomic_exp e;]
  | E_assert(c,m) ->
    separate space [string "assert"; parens (separate comma [exp c; exp m])]
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
  | E_comment s -> comment (string s)
  | E_comment_struc e -> comment (exp e)
                                 (*
  | E_internal_exp((l, Base((_,t),_,_,_,_,bindings))) -> (*TODO use bindings, and other params*)
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
                                  *)
  and let_exp (LB_aux(lb,_)) = match lb with
    | LB_val_explicit(ts,pat,e) ->
      (match ts with
       | TypSchm_aux (TypSchm_ts (TypQ_aux (TypQ_no_forall,_),_),_) ->
         prefix 2 1
           (separate space [string "let"; parens (doc_typscm_atomic ts); doc_atomic_pat pat; equals])
           (atomic_exp e)
       | _ ->
         prefix 2 1
           (separate space [string "let"; doc_typscm_atomic ts; doc_atomic_pat pat; equals])
           (atomic_exp e))
  | LB_val_implicit(pat,e) ->
      prefix 2 1
        (separate space [string "let"; doc_atomic_pat pat; equals])
        (atomic_exp e)

  and doc_fexp (FE_aux(FE_Fexp(id,e),_)) = doc_op equals (doc_id id) (exp e)

  and doc_case (Pat_aux (pexp, _)) =
    match pexp with
    | Pat_exp(pat, e) ->
       doc_op arrow (separate space [string "case"; doc_atomic_pat pat]) (group (exp e))
    | Pat_when(pat, guard, e) ->
       doc_op arrow (separate space [string "case"; doc_atomic_pat pat; string "when"; exp guard]) (group (exp e))

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
  | LEXP_tup tups -> parens (separate_map comma doc_lexp tups)

  (* expose doc_exp and doc_let *)
  in exp, let_exp

let doc_default (DT_aux(df,_)) = match df with
  | DT_kind(bk,v) -> separate space [string "default"; doc_bkind bk; doc_var v]
  | DT_typ(ts,id) -> separate space [string "default"; doc_typscm ts; doc_id id]
  | DT_order(ord) -> separate space [string "default"; string "Order"; doc_ord ord]

let doc_spec (VS_aux(v,_)) = match v with
  | VS_val_spec(ts,id) ->
     separate space [string "val"; doc_typscm ts; doc_id id]
  | VS_cast_spec (ts, id) ->
     separate space [string "val"; string "cast"; doc_typscm ts; doc_id id]
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

let doc_kindef (KD_aux(kd,_)) = match kd with
  | KD_abbrev(kind,id,nm,typschm) ->
    doc_op equals (concat [string "def"; space; doc_kind kind; space; doc_id id; doc_namescm nm]) (doc_typscm typschm)
  | KD_nabbrev(kind,id,nm,n) ->
    doc_op equals (concat [string "def"; space; doc_kind kind; space; doc_id id; doc_namescm nm]) (doc_nexp n)
  | KD_record(kind,id,nm,typq,fs,_) ->
    let f_pp (typ,id) = concat [doc_typ typ; space; doc_id id; semi] in
    let fs_doc = group (separate_map (break 1) f_pp fs) in
    doc_op equals
      (concat [string "def"; space;doc_kind kind; space; doc_id id; doc_namescm nm])
      (string "const struct" ^^ space ^^ doc_typquant typq (braces fs_doc))
  | KD_variant(kind,id,nm,typq,ar,_) ->
    let ar_doc = group (separate_map (semi ^^ break 1) doc_type_union ar) in
    doc_op equals
      (concat [string "def"; space; doc_kind kind; space; doc_id id; doc_namescm nm])
      (string "const union" ^^ space ^^ doc_typquant typq (braces ar_doc))
  | KD_enum(kind,id,nm,enums,_) ->
      let enums_doc = group (separate_map (semi ^^ break 1) doc_id enums) in
      doc_op equals
        (concat [string "def"; space; doc_kind kind; space; doc_id id; doc_namescm nm])
        (string "enumerate" ^^ space ^^ braces enums_doc)
  | KD_register(kind,id,n1,n2,rs) ->
      let doc_rid (r,id) = separate space [doc_range r; colon; doc_id id] ^^ semi in
      let doc_rids = group (separate_map (break 1) doc_rid rs) in
      doc_op equals
        (string "def" ^^ space ^^ doc_kind kind ^^ space ^^ doc_id id)
        (separate space [
          string "register bits";
          brackets (doc_nexp n1 ^^ colon ^^ doc_nexp n2);
          braces doc_rids;
        ])


let doc_rec (Rec_aux(r,_)) = match r with
  | Rec_nonrec -> empty
  (* include trailing space because caller doesn't know if we return
   * empty *)
  | Rec_rec -> space ^^ string "rec"

let doc_tannot_opt (Typ_annot_opt_aux(t,_)) = match t with
  | Typ_annot_opt_some(tq,typ) -> space ^^ doc_typquant tq (doc_typ typ)
  | Typ_annot_opt_none -> empty

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
      separate space ([string "function" ^^ doc_rec r ^^ doc_tannot_opt typa]@
                      (match efa with
                       | Effect_opt_aux (Effect_opt_pure,_) -> []
                       | _ -> [string "effect";
                               doc_effects_opt efa;])
                      @[clauses])

let doc_alias (AL_aux (alspec,_)) =
  match alspec with
    | AL_subreg((RI_aux (RI_id id,_)),subid) -> doc_id id ^^ dot ^^ doc_id subid
    | AL_bit((RI_aux (RI_id id,_)),ac) -> doc_id id ^^ brackets (doc_exp ac)
    | AL_slice((RI_aux (RI_id id,_)),b,e) -> doc_id id ^^ brackets (doc_op dotdot (doc_exp b) (doc_exp e))
    | AL_concat((RI_aux (RI_id f,_)),(RI_aux (RI_id s,_))) -> doc_op colon (doc_id f) (doc_id s)

let doc_dec (DEC_aux (reg,_)) =
  match reg with
    | DEC_reg(typ,id) -> separate space [string "register"; doc_typ typ; doc_id id]
    | DEC_alias(id,alspec) ->
        doc_op equals (string "register alias" ^^ space ^^ doc_id id) (doc_alias alspec)
    | DEC_typ_alias(typ,id,alspec) ->
        doc_op equals (string "register alias" ^^ space ^^ doc_typ typ) (doc_alias alspec)

let doc_scattered (SD_aux (sdef, _)) = match sdef with
 | SD_scattered_function (r, typa, efa, id) ->
     separate space ([
       string "scattered function";
       doc_rec r ^^ doc_tannot_opt typa;]@
       (match efa with
        | Effect_opt_aux (Effect_opt_pure,_) -> []
        | _ -> [string "effect"; doc_effects_opt efa;])
         @[doc_id id])
 | SD_scattered_variant (id, ns, tq) ->
     doc_op equals
       (string "scattered typedef" ^^ space ^^ doc_id id ^^ doc_namescm ns)
       (string "const union" ^^ space ^^ (doc_typquant tq empty))
 | SD_scattered_funcl funcl ->
     string "function clause" ^^ space ^^ doc_funcl funcl
 | SD_scattered_unioncl (id, tu) ->
     separate space [string "union"; doc_id id;
     string "member"; doc_type_union tu]
 | SD_scattered_end id -> string "end" ^^ space ^^ doc_id id

let rec doc_def def = group (match def with
  | DEF_default df -> doc_default df
  | DEF_spec v_spec -> doc_spec v_spec
  | DEF_type t_def -> doc_typdef t_def
  | DEF_kind k_def -> doc_kindef k_def
  | DEF_fundef f_def -> doc_fundef f_def
  | DEF_val lbind -> doc_let lbind
  | DEF_reg_dec dec -> doc_dec dec
  | DEF_scattered sdef -> doc_scattered sdef
  | DEF_overload (id, ids) ->
      let ids_doc = group (separate_map (semi ^^ break 1) doc_id ids) in
      string "overload" ^^ space ^^ doc_id id ^^ space ^^ brackets ids_doc
  | DEF_comm (DC_comm s) -> comment (string s)
  | DEF_comm (DC_comm_struct d) -> comment (doc_def d)
  ) ^^ hardline

let doc_defs (Defs(defs)) =
  separate_map hardline doc_def defs

let pp_defs f d = print f (doc_defs d)
let pp_exp b e = to_buf b (doc_exp e)
let pat_to_string p =
  let b = Buffer.create 20 in
  to_buf b (doc_pat p);
  Buffer.contents b
