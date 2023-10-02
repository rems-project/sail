(****************************************************************************)
(*     Sail                                                                 *)
(*                                                                          *)
(*  Sail and the Sail architecture models here, comprising all files and    *)
(*  directories except the ASL-derived Sail code in the aarch64 directory,  *)
(*  are subject to the BSD two-clause licence below.                        *)
(*                                                                          *)
(*  The ASL derived parts of the ARMv8.3 specification in                   *)
(*  aarch64/no_vector and aarch64/full are copyright ARM Ltd.               *)
(*                                                                          *)
(*  Copyright (c) 2013-2021                                                 *)
(*    Kathyrn Gray                                                          *)
(*    Shaked Flur                                                           *)
(*    Stephen Kell                                                          *)
(*    Gabriel Kerneis                                                       *)
(*    Robert Norton-Wright                                                  *)
(*    Christopher Pulte                                                     *)
(*    Peter Sewell                                                          *)
(*    Alasdair Armstrong                                                    *)
(*    Brian Campbell                                                        *)
(*    Thomas Bauereiss                                                      *)
(*    Anthony Fox                                                           *)
(*    Jon French                                                            *)
(*    Dominic Mulligan                                                      *)
(*    Stephen Kell                                                          *)
(*    Mark Wassell                                                          *)
(*    Alastair Reid (Arm Ltd)                                               *)
(*                                                                          *)
(*  All rights reserved.                                                    *)
(*                                                                          *)
(*  This work was partially supported by EPSRC grant EP/K008528/1 <a        *)
(*  href="http://www.cl.cam.ac.uk/users/pes20/rems">REMS: Rigorous          *)
(*  Engineering for Mainstream Systems</a>, an ARM iCASE award, EPSRC IAA   *)
(*  KTF funding, and donations from Arm.  This project has received         *)
(*  funding from the European Research Council (ERC) under the European     *)
(*  Union’s Horizon 2020 research and innovation programme (grant           *)
(*  agreement No 789108, ELVER).                                            *)
(*                                                                          *)
(*  This software was developed by SRI International and the University of  *)
(*  Cambridge Computer Laboratory (Department of Computer Science and       *)
(*  Technology) under DARPA/AFRL contracts FA8650-18-C-7809 ("CIFV")        *)
(*  and FA8750-10-C-0237 ("CTSRD").                                         *)
(*                                                                          *)
(*  Redistribution and use in source and binary forms, with or without      *)
(*  modification, are permitted provided that the following conditions      *)
(*  are met:                                                                *)
(*  1. Redistributions of source code must retain the above copyright       *)
(*     notice, this list of conditions and the following disclaimer.        *)
(*  2. Redistributions in binary form must reproduce the above copyright    *)
(*     notice, this list of conditions and the following disclaimer in      *)
(*     the documentation and/or other materials provided with the           *)
(*     distribution.                                                        *)
(*                                                                          *)
(*  THIS SOFTWARE IS PROVIDED BY THE AUTHOR AND CONTRIBUTORS ``AS IS''      *)
(*  AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED       *)
(*  TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A         *)
(*  PARTICULAR PURPOSE ARE DISCLAIMED.  IN NO EVENT SHALL THE AUTHOR OR     *)
(*  CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,            *)
(*  SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT        *)
(*  LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF        *)
(*  USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND     *)
(*  ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,      *)
(*  OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT      *)
(*  OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF      *)
(*  SUCH DAMAGE.                                                            *)
(****************************************************************************)

open Ast
open Ast_defs
open Ast_util
open PPrint

let opt_use_heuristics = ref false
let opt_insert_braces = ref false

module Big_int = Nat_big_num

let doc_op symb a b = infix 2 1 symb a b

let doc_id (Id_aux (id_aux, _)) = string (match id_aux with Id v -> v | Operator op -> "operator " ^ op)

let doc_kid kid = string (Ast_util.string_of_kid kid)

let doc_attr attr arg =
  if arg = "" then Printf.ksprintf string "$[%s]" attr ^^ space else Printf.ksprintf string "$[%s %s]" attr arg ^^ space

let doc_def_annot def_annot =
  (match def_annot.doc_comment with Some str -> string "/*!" ^^ string str ^^ string "*/" ^^ hardline | _ -> empty)
  ^^
  match def_annot.attrs with
  | [] -> empty
  | attrs -> separate_map hardline (fun (_, attr, arg) -> doc_attr attr arg) attrs ^^ hardline

let doc_kopt_no_parens = function
  | kopt when is_int_kopt kopt -> doc_kid (kopt_kid kopt)
  | kopt when is_typ_kopt kopt -> separate space [doc_kid (kopt_kid kopt); colon; string "Type"]
  | kopt -> separate space [doc_kid (kopt_kid kopt); colon; string "Bool"]

let doc_kopt = function
  | kopt when is_int_kopt kopt -> doc_kopt_no_parens kopt
  | kopt -> parens (doc_kopt_no_parens kopt)

let doc_int n = string (Big_int.to_string n)

let doc_ord (Ord_aux (o, _)) = match o with Ord_inc -> string "inc" | Ord_dec -> string "dec"

let rec doc_typ_pat (TP_aux (tpat_aux, _)) =
  match tpat_aux with
  | TP_wild -> string "_"
  | TP_var kid -> doc_kid kid
  | TP_app (f, tpats) -> doc_id f ^^ parens (separate_map (comma ^^ space) doc_typ_pat tpats)

let doc_nexp nexp =
  let rec atomic_nexp (Nexp_aux (n_aux, _) as nexp) =
    match n_aux with
    | Nexp_constant c -> string (Big_int.to_string c)
    | Nexp_app (Id_aux (Operator op, _), [n1; n2]) -> separate space [atomic_nexp n1; string op; atomic_nexp n2]
    | Nexp_app (_id, _nexps) -> string (string_of_nexp nexp)
    (* This segfaults??!!!!
       doc_id id ^^ (parens (separate_map (comma ^^ space) doc_nexp nexps))
    *)
    | Nexp_id id -> doc_id id
    | Nexp_var kid -> doc_kid kid
    | _ -> parens (nexp0 nexp)
  and nexp0 (Nexp_aux (n_aux, _) as nexp) =
    match n_aux with
    | Nexp_sum (n1, Nexp_aux (Nexp_neg n2, _)) | Nexp_minus (n1, n2) -> separate space [nexp0 n1; string "-"; nexp1 n2]
    | Nexp_sum (n1, Nexp_aux (Nexp_constant c, _)) when Big_int.less c Big_int.zero ->
        separate space [nexp0 n1; string "-"; doc_int (Big_int.abs c)]
    | Nexp_sum (n1, n2) -> separate space [nexp0 n1; string "+"; nexp1 n2]
    | _ -> nexp1 nexp
  and nexp1 (Nexp_aux (n_aux, _) as nexp) =
    match n_aux with Nexp_times (n1, n2) -> separate space [nexp1 n1; string "*"; nexp2 n2] | _ -> nexp2 nexp
  and nexp2 (Nexp_aux (n_aux, _) as nexp) =
    match n_aux with
    | Nexp_neg n -> separate space [string "-"; atomic_nexp n]
    | Nexp_exp n -> separate space [string "2"; string "^"; atomic_nexp n]
    | _ -> atomic_nexp nexp
  in
  nexp0 nexp

let rec doc_nc nc =
  let nc_op op n1 n2 = separate space [doc_nexp n1; string op; doc_nexp n2] in
  let rec atomic_nc (NC_aux (nc_aux, _) as nc) =
    match nc_aux with
    | NC_true -> string "true"
    | NC_false -> string "false"
    | NC_equal (n1, n2) -> nc_op "==" n1 n2
    | NC_not_equal (n1, n2) -> nc_op "!=" n1 n2
    | NC_bounded_ge (n1, n2) -> nc_op ">=" n1 n2
    | NC_bounded_gt (n1, n2) -> nc_op ">" n1 n2
    | NC_bounded_le (n1, n2) -> nc_op "<=" n1 n2
    | NC_bounded_lt (n1, n2) -> nc_op "<" n1 n2
    | NC_set (kid, ints) ->
        separate space [doc_kid kid; string "in"; braces (separate_map (comma ^^ space) doc_int ints)]
    | NC_app (id, args) -> doc_id id ^^ parens (separate_map (comma ^^ space) doc_typ_arg args)
    | NC_var kid -> doc_kid kid
    | NC_or _ | NC_and _ -> nc0 ~parenthesize:true nc
  and nc0 ?(parenthesize = false) nc =
    (* Rather than parens (nc0 x) we use nc0 ~parenthesize:true x, because if
       we rewrite a disjunction as a set constraint, then we can
       always omit the parens. *)
    let parens' = if parenthesize then parens else fun x -> x in
    let disjs = constraint_disj nc in
    let collect_constants kid = function
      | NC_aux (NC_equal (Nexp_aux (Nexp_var kid', _), Nexp_aux (Nexp_constant c, _)), _) when Kid.compare kid kid' = 0
        ->
          Some c
      | _ -> None
    in
    match disjs with
    | NC_aux (NC_equal (Nexp_aux (Nexp_var kid, _), Nexp_aux (Nexp_constant c, _)), _) :: ncs -> begin
        match Util.option_all (List.map (collect_constants kid) ncs) with
        | None | Some [] -> parens' (separate_map (space ^^ bar ^^ space) nc1 disjs)
        | Some cs -> separate space [doc_kid kid; string "in"; braces (separate_map (comma ^^ space) doc_int (c :: cs))]
      end
    | _ -> parens' (separate_map (space ^^ bar ^^ space) nc1 disjs)
  and nc1 nc =
    let conjs = constraint_conj nc in
    separate_map (space ^^ string "&" ^^ space) atomic_nc conjs
  in
  atomic_nc (constraint_simp nc)

and doc_typ ?(simple = false) (Typ_aux (typ_aux, l)) =
  match typ_aux with
  | Typ_id id -> doc_id id
  | Typ_app (id, []) -> doc_id id
  | Typ_app (Id_aux (Operator str, _), [x; y]) -> separate space [doc_typ_arg x; string str; doc_typ_arg y]
  | Typ_app (id, typs) when Id.compare id (mk_id "atom") = 0 ->
      string "int" ^^ parens (separate_map (string ", ") doc_typ_arg typs)
  | Typ_app (id, typs) when Id.compare id (mk_id "atom_bool") = 0 ->
      string "bool" ^^ parens (separate_map (string ", ") doc_typ_arg typs)
  | Typ_app (id, typs) -> doc_id id ^^ parens (separate_map (string ", ") doc_typ_arg typs)
  | Typ_tuple typs -> parens (separate_map (string ", ") doc_typ typs)
  | Typ_var kid -> doc_kid kid
  (* Resugar set types like {|1, 2, 3|} *)
  | Typ_exist
      ( [kopt],
        NC_aux (NC_set (kid1, ints), _),
        Typ_aux (Typ_app (id, [A_aux (A_nexp (Nexp_aux (Nexp_var kid2, _)), _)]), _)
      )
    when Kid.compare (kopt_kid kopt) kid1 == 0 && Kid.compare kid1 kid2 == 0 && Id.compare (mk_id "atom") id == 0 ->
      enclose (char '{') (char '}') (separate_map (string ", ") doc_int ints)
  | Typ_exist (kopts, nc, typ) ->
      braces (separate_map space doc_kopt kopts ^^ comma ^^ space ^^ doc_nc nc ^^ dot ^^ space ^^ doc_typ typ)
  | Typ_fn ([Typ_aux (Typ_tuple typs, _)], typ) ->
      separate space [parens (doc_arg_typs typs); string "->"; doc_typ ~simple typ]
  | Typ_fn (typs, typ) -> separate space [doc_arg_typs typs; string "->"; doc_typ ~simple typ]
  | Typ_bidir (typ1, typ2) -> separate space [doc_typ typ1; string "<->"; doc_typ typ2]
  | Typ_internal_unknown -> raise (Reporting.err_unreachable l __POS__ "escaped Typ_internal_unknown")

and doc_typ_arg (A_aux (ta_aux, _)) =
  match ta_aux with A_typ typ -> doc_typ typ | A_nexp nexp -> doc_nexp nexp | A_bool nc -> doc_nc nc

and doc_arg_typs = function [typ] -> doc_typ typ | typs -> parens (separate_map (comma ^^ space) doc_typ typs)

let doc_subst (IS_aux (subst_aux, _)) =
  match subst_aux with
  | IS_typ (kid, typ) -> doc_kid kid ^^ space ^^ equals ^^ space ^^ doc_typ typ
  | IS_id (id1, id2) -> doc_id id1 ^^ space ^^ equals ^^ space ^^ doc_id id2

let doc_kind (K_aux (k, _)) = string (match k with K_int -> "Int" | K_type -> "Type" | K_bool -> "Bool")

let doc_kopts = separate_map space doc_kopt

let doc_quants quants =
  let rec get_kopts = function
    | QI_aux (QI_id kopt, _) :: qis -> kopt :: get_kopts qis
    | _ :: qis -> get_kopts qis
    | [] -> []
  in
  let qi_nc (QI_aux (qi_aux, _)) = match qi_aux with QI_constraint nc -> [nc] | _ -> [] in
  let kdoc = doc_kopts (get_kopts quants) in
  let ncs = List.concat (List.map qi_nc quants) in
  match ncs with
  | [] -> kdoc
  | [nc] -> kdoc ^^ comma ^^ space ^^ doc_nc nc
  | nc :: ncs -> kdoc ^^ comma ^^ space ^^ doc_nc (List.fold_left nc_and nc ncs)

let doc_param_quants quants =
  let doc_qi_kopt (QI_aux (qi_aux, _)) =
    match qi_aux with
    | QI_id kopt when is_int_kopt kopt -> [doc_kid (kopt_kid kopt) ^^ colon ^^ space ^^ string "Int"]
    | QI_id kopt when is_typ_kopt kopt -> [doc_kid (kopt_kid kopt) ^^ colon ^^ space ^^ string "Type"]
    | QI_id kopt -> [doc_kid (kopt_kid kopt) ^^ colon ^^ space ^^ string "Bool"]
    | QI_constraint _ -> []
  in
  let qi_nc (QI_aux (qi_aux, _)) = match qi_aux with QI_constraint nc -> [nc] | _ -> [] in
  let kdoc = separate (comma ^^ space) (List.concat (List.map doc_qi_kopt quants)) in
  let ncs = List.concat (List.map qi_nc quants) in
  match ncs with
  | [] -> parens kdoc
  | [nc] -> parens kdoc ^^ comma ^^ space ^^ doc_nc nc
  | nc :: ncs -> parens kdoc ^^ comma ^^ space ^^ doc_nc (List.fold_left nc_and nc ncs)

let doc_binding ?(simple = false) ((TypQ_aux (tq_aux, _) as typq), typ) =
  match tq_aux with
  | TypQ_no_forall -> doc_typ ~simple typ
  | TypQ_tq [] -> doc_typ ~simple typ
  | TypQ_tq qs ->
      if !opt_use_heuristics && String.length (string_of_typquant typq) > 60 then (
        let kopts, ncs = quant_split typq in
        if ncs = [] then string "forall" ^^ space ^^ separate_map space doc_kopt kopts ^^ dot ^//^ doc_typ ~simple typ
        else
          string "forall" ^^ space ^^ separate_map space doc_kopt kopts ^^ comma
          ^//^ separate_map (space ^^ string "&" ^^ space) doc_nc ncs
          ^^ dot ^^ hardline ^^ doc_typ ~simple typ
      )
      else string "forall" ^^ space ^^ doc_quants qs ^^ dot ^//^ doc_typ ~simple typ

let doc_typschm ?(simple = false) (TypSchm_aux (TypSchm_ts (typq, typ), _)) = doc_binding ~simple (typq, typ)

let doc_typschm_typ (TypSchm_aux (TypSchm_ts (_, typ), _)) = doc_typ typ

let doc_typquant (TypQ_aux (tq_aux, _)) =
  match tq_aux with TypQ_no_forall -> None | TypQ_tq [] -> None | TypQ_tq qs -> Some (doc_param_quants qs)

let doc_lit (L_aux (l, _)) =
  utf8string
    ( match l with
    | L_unit -> "()"
    | L_zero -> "bitzero"
    | L_one -> "bitone"
    | L_true -> "true"
    | L_false -> "false"
    | L_num i -> Big_int.to_string i
    | L_hex n -> "0x" ^ n
    | L_bin n -> "0b" ^ n
    | L_real r -> r
    | L_undef -> "undefined"
    | L_string s -> "\"" ^ String.escaped s ^ "\""
    )

let rec doc_pat (P_aux (p_aux, (_, uannot))) =
  let wrap, attrs_doc =
    match get_attributes uannot with
    | [] -> ((fun x -> x), empty)
    | _ -> (parens, concat_map (fun (_, attr, arg) -> doc_attr attr arg) (get_attributes uannot))
  in
  let pat_doc =
    match p_aux with
    | P_id id -> doc_id id
    | P_or (pat1, pat2) -> parens (doc_pat pat1 ^^ string " | " ^^ doc_pat pat2)
    | P_not pat -> string "~" ^^ parens (doc_pat pat)
    | P_tuple pats -> lparen ^^ separate_map (comma ^^ space) doc_pat pats ^^ rparen
    | P_typ (typ, pat) -> separate space [doc_pat pat; colon; doc_typ typ]
    | P_lit lit -> doc_lit lit
    (* P_var short form sugar *)
    | P_var (P_aux (P_id id, _), TP_aux (TP_var kid, _)) when Id.compare (id_of_kid kid) id == 0 -> doc_kid kid
    | P_var (pat, tpat) -> parens (separate space [doc_pat pat; string "as"; doc_typ_pat tpat])
    | P_vector pats -> brackets (separate_map (comma ^^ space) doc_pat pats)
    | P_vector_concat pats -> parens (separate_map (space ^^ string "@" ^^ space) doc_pat pats)
    | P_vector_subrange (id, n, m) ->
        if Big_int.equal n m then doc_id id ^^ brackets (string (Big_int.to_string n))
        else doc_id id ^^ brackets (string (Big_int.to_string n) ^^ string ".." ^^ string (Big_int.to_string m))
    | P_wild -> string "_"
    | P_as (pat, id) -> parens (separate space [doc_pat pat; string "as"; doc_id id])
    | P_app (id, pats) -> doc_id id ^^ parens (separate_map (comma ^^ space) doc_pat pats)
    | P_list pats -> string "[|" ^^ separate_map (comma ^^ space) doc_pat pats ^^ string "|]"
    | P_cons (hd_pat, tl_pat) -> parens (separate space [doc_pat hd_pat; string "::"; doc_pat tl_pat])
    | P_string_append [] -> string "\"\""
    | P_string_append pats -> parens (separate_map (string " ^ ") doc_pat pats)
    | P_struct (fpats, fwild) ->
        let fpats = List.map (fun (field, pat) -> separate space [doc_id field; equals; doc_pat pat]) fpats in
        let fwild = match fwild with FP_wild _ -> [string "_"] | FP_no_wild -> [] in
        let fpats = fpats @ fwild in
        separate space [string "struct"; lbrace; separate (comma ^^ space) fpats; rbrace]
  in
  wrap (attrs_doc ^^ pat_doc)

(* if_block_x is true if x should be printed like a block, i.e. with
   newlines. Blocks are automatically printed as blocks, so this
   returns false for them. *)
let if_block_then (E_aux (e_aux, _)) = match e_aux with E_assign _ | E_if _ -> true | _ -> false

let if_block_else (E_aux (e_aux, _)) = match e_aux with E_assign _ -> true | _ -> false

let fixities =
  let fixities' =
    List.fold_left
      (fun r (x, y) -> Bindings.add x y r)
      Bindings.empty
      [
        (mk_id "^", (InfixR, 8));
        (mk_id "*", (InfixL, 7));
        (mk_id "/", (InfixL, 7));
        (mk_id "%", (InfixL, 7));
        (mk_id "+", (InfixL, 6));
        (mk_id "-", (InfixL, 6));
        (mk_id "!=", (Infix, 4));
        (mk_id ">", (Infix, 4));
        (mk_id "<", (Infix, 4));
        (mk_id ">=", (Infix, 4));
        (mk_id "<=", (Infix, 4));
        (mk_id "==", (Infix, 4));
        (mk_id "&", (InfixR, 3));
        (mk_id "|", (InfixR, 2));
      ]
  in
  ref (fixities' : (prec * int) Bindings.t)

type 'a vector_update = VU_single of 'a exp * 'a exp | VU_range of 'a exp * 'a exp * 'a exp

let rec get_vector_updates (E_aux (e_aux, _) as exp) =
  match e_aux with
  | E_vector_update (exp1, exp2, exp3) ->
      let input, updates = get_vector_updates exp1 in
      (input, updates @ [VU_single (exp2, exp3)])
  | E_vector_update_subrange (exp1, exp2, exp3, exp4) ->
      let input, updates = get_vector_updates exp1 in
      (input, updates @ [VU_range (exp2, exp3, exp4)])
  | _ -> (exp, [])

let rec doc_exp (E_aux (e_aux, (_, uannot)) as exp) =
  concat_map (fun (_, attr, arg) -> doc_attr attr arg) (get_attributes uannot)
  ^^
  match e_aux with
  | E_block [] -> string "()"
  | E_block exps -> group (lbrace ^^ nest 4 (hardline ^^ doc_block exps) ^^ hardline ^^ rbrace)
  (* This is mostly for the -convert option *)
  | E_app_infix (x, id, y) when Id.compare (mk_id "quot") id == 0 ->
      separate space [doc_atomic_exp x; string "/"; doc_atomic_exp y]
  | E_app_infix _ -> doc_infix 0 exp
  | E_tuple exps -> parens (separate_map (comma ^^ space) doc_exp exps)
  | E_if (if_exp, then_exp, (E_aux (E_if (_, _, _), _) as else_exp)) when !opt_insert_braces ->
      separate space [string "if"; doc_exp if_exp; string "then"]
      ^^ space ^^ doc_exp_as_block then_exp ^^ space ^^ string "else" ^^ space ^^ doc_exp else_exp
  | E_if (if_exp, then_exp, else_exp) when !opt_insert_braces ->
      separate space [string "if"; doc_exp if_exp; string "then"]
      ^^ space ^^ doc_exp_as_block then_exp ^^ space ^^ string "else" ^^ space ^^ doc_exp_as_block else_exp
  (* Various rules to try to format if blocks nicely based on content.
     There's also an if rule in doc_block for { ... if . then .; ... } because it's
     unambiguous there. *)
  | E_if (if_exp, then_exp, else_exp) when if_block_then then_exp && if_block_else else_exp ->
      (separate space [string "if"; doc_exp if_exp; string "then"] ^//^ doc_exp then_exp)
      ^/^ string "else" ^//^ doc_exp else_exp
  | E_if (if_exp, then_exp, (E_aux (E_if _, _) as else_exp)) when if_block_then then_exp ->
      (separate space [string "if"; doc_exp if_exp; string "then"] ^//^ doc_exp then_exp)
      ^/^ string "else" ^^ space ^^ doc_exp else_exp
  | E_if (if_exp, then_exp, else_exp) when if_block_else else_exp ->
      separate space [string "if"; doc_exp if_exp; string "then"; doc_exp then_exp]
      ^^ space ^^ string "else" ^//^ doc_exp else_exp
  | E_if (if_exp, then_exp, else_exp) when if_block_then then_exp ->
      (separate space [string "if"; doc_exp if_exp; string "then"] ^//^ doc_exp then_exp)
      ^/^ string "else" ^^ space ^^ doc_exp else_exp
  | E_if (if_exp, E_aux (E_block (_ :: _ as then_exps), _), E_aux (E_block (_ :: _ as else_exps), _)) ->
      separate space [string "if"; doc_exp if_exp; string "then {"]
      ^^ group (nest 4 (hardline ^^ doc_block then_exps) ^^ hardline)
      ^^ string "} else {"
      ^^ group (nest 4 (hardline ^^ doc_block else_exps) ^^ hardline ^^ rbrace)
  | E_if (if_exp, E_aux (E_block (_ :: _ as then_exps), _), (E_aux (E_if _, _) as else_exp)) ->
      separate space [string "if"; doc_exp if_exp; string "then {"]
      ^^ group (nest 4 (hardline ^^ doc_block then_exps) ^^ hardline)
      ^^ string "} else " ^^ doc_exp else_exp
  | E_if (if_exp, E_aux (E_block (_ :: _ as then_exps), _), else_exp) ->
      separate space [string "if"; doc_exp if_exp; string "then {"]
      ^^ group (nest 4 (hardline ^^ doc_block then_exps) ^^ hardline)
      ^^ string "} else" ^//^ doc_exp else_exp
  | E_if (if_exp, then_exp, E_aux (E_block (_ :: _ as else_exps), _)) ->
      group ((separate space [string "if"; doc_exp if_exp; string "then"] ^//^ doc_exp then_exp) ^/^ string "else {")
      ^^ group (nest 4 (hardline ^^ doc_block else_exps) ^^ hardline ^^ rbrace)
  | E_if (if_exp, then_exp, else_exp) ->
      group ((separate space [string "if"; doc_exp if_exp; string "then"] ^//^ doc_exp then_exp) ^/^ string "else")
      ^//^ doc_exp else_exp
  | E_list exps -> string "[|" ^^ separate_map (comma ^^ space) doc_exp exps ^^ string "|]"
  | E_cons (exp1, exp2) -> doc_atomic_exp exp1 ^^ space ^^ string "::" ^^ space ^^ doc_exp exp2
  | E_struct fexps -> separate space [string "struct"; string "{"; doc_fexps fexps; string "}"]
  | E_loop (While, measure, cond, exp) ->
      separate space ([string "while"] @ doc_measure measure @ [doc_exp cond; string "do"; doc_exp exp])
  | E_loop (Until, measure, cond, exp) ->
      separate space ([string "repeat"] @ doc_measure measure @ [doc_exp exp; string "until"; doc_exp cond])
  | E_struct_update (exp, fexps) -> separate space [string "{"; doc_exp exp; string "with"; doc_fexps fexps; string "}"]
  | E_vector_append (exp1, exp2) -> separate space [doc_atomic_exp exp1; string "@"; doc_atomic_exp exp2]
  | E_match (exp, pexps) -> separate space [string "match"; doc_exp exp; doc_pexps pexps]
  | E_let (LB_aux (LB_val (pat, binding), _), exp) -> doc_let_style "let" (doc_pat pat) (doc_exp binding) exp
  | E_internal_plet (pat, exp1, exp2) -> doc_let_style "internal_plet" (doc_pat pat) (doc_exp exp1) exp2
  | E_var (lexp, binding, exp) -> doc_let_style "var" (doc_lexp lexp) (doc_exp binding) exp
  | E_assign (lexp, exp) -> separate space [doc_lexp lexp; equals; doc_exp exp]
  | E_for (id, exp1, exp2, exp3, order, exp4) ->
      let header =
        string "foreach" ^^ space
        ^^ group
             (parens
                (separate (break 1)
                   [
                     doc_id id;
                     string "from " ^^ doc_atomic_exp exp1;
                     string "to " ^^ doc_atomic_exp exp2;
                     string "by " ^^ doc_atomic_exp exp3;
                     string "in " ^^ doc_ord order;
                   ]
                )
             )
      in
      header ^^ space ^^ doc_exp exp4
  (* Resugar an assert with an empty message *)
  | E_throw exp -> string "throw" ^^ parens (doc_exp exp)
  | E_try (exp, pexps) -> separate space [string "try"; doc_exp exp; string "catch"; doc_pexps pexps]
  | E_return (E_aux (E_lit (L_aux (L_unit, _)), _)) -> string "return()"
  | E_return exp -> string "return" ^^ parens (doc_exp exp)
  | E_internal_return exp -> string "internal_return" ^^ parens (doc_exp exp)
  | E_app (id, [exp]) when Id.compare (mk_id "pow2") id == 0 ->
      separate space [string "2"; string "^"; doc_atomic_exp exp]
  | E_internal_assume (nc, exp) -> doc_let_style_general "internal_assume" (parens (doc_nc nc)) None exp
  | _ -> doc_atomic_exp exp

and doc_let_style keyword lhs rhs body = doc_let_style_general keyword lhs (Some rhs) body

and doc_let_style_general keyword lhs rhs body =
  (* Avoid staircases *)
  let ( ^///^ ) =
    match unaux_exp body with E_let _ | E_var _ | E_internal_plet _ | E_internal_assume _ -> ( ^/^ ) | _ -> ( ^//^ )
  in
  match rhs with
  | Some rhs -> group ((separate space [string keyword; lhs; equals] ^//^ rhs) ^/^ string "in") ^///^ doc_exp body
  | None -> group ((string keyword ^//^ lhs) ^/^ string "in") ^///^ doc_exp body

and doc_measure (Measure_aux (m_aux, _)) =
  match m_aux with Measure_none -> [] | Measure_some exp -> [string "termination_measure"; braces (doc_exp exp)]

and doc_infix n (E_aux (e_aux, _) as exp) =
  match e_aux with
  | E_app_infix (l, op, r) when n < 10 -> begin
      try
        match Bindings.find op !fixities with
        | Infix, m when m >= n -> separate space [doc_infix (m + 1) l; doc_id op; doc_infix (m + 1) r]
        | Infix, m -> parens (separate space [doc_infix (m + 1) l; doc_id op; doc_infix (m + 1) r])
        | InfixL, m when m >= n -> separate space [doc_infix m l; doc_id op; doc_infix (m + 1) r]
        | InfixL, m -> parens (separate space [doc_infix m l; doc_id op; doc_infix (m + 1) r])
        | InfixR, m when m >= n -> separate space [doc_infix (m + 1) l; doc_id op; doc_infix m r]
        | InfixR, m -> parens (separate space [doc_infix (m + 1) l; doc_id op; doc_infix m r])
      with Not_found -> parens (separate space [doc_atomic_exp l; doc_id op; doc_atomic_exp r])
    end
  | _ -> doc_atomic_exp exp

and doc_atomic_exp (E_aux (e_aux, _) as exp) =
  match e_aux with
  | E_typ (typ, exp) -> separate space [doc_atomic_exp exp; colon; doc_typ typ]
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
  | E_vector_subrange (exp1, exp2, exp3) ->
      doc_atomic_exp exp1 ^^ brackets (separate space [doc_exp exp2; string ".."; doc_exp exp3])
  | E_vector exps -> brackets (separate_map (comma ^^ space) doc_exp exps)
  | E_vector_update _ | E_vector_update_subrange _ ->
      let input, updates = get_vector_updates exp in
      let updates_doc = separate_map (comma ^^ space) doc_vector_update updates in
      brackets (separate space [doc_exp input; string "with"; updates_doc])
  | E_internal_value v ->
      if !Interactive.opt_interactive then string (Value.string_of_value v |> Util.green |> Util.clear)
      else string (Value.string_of_value v)
  | _ -> parens (doc_exp exp)

and doc_fexps fexps = separate_map (comma ^^ space) doc_fexp fexps

and doc_fexp (FE_aux (FE_fexp (id, exp), _)) = separate space [doc_id id; equals; doc_exp exp]

and doc_block = function
  | [] -> string "()"
  | [E_aux (E_let (LB_aux (LB_val (pat, binding), _), E_aux (E_block exps, _)), _)] ->
      separate space [string "let"; doc_pat pat; equals; doc_exp binding] ^^ semi ^^ hardline ^^ doc_block exps
  | [E_aux (E_let (LB_aux (LB_val (pat, binding), _), exp), _)] ->
      separate space [string "let"; doc_pat pat; equals; doc_exp binding] ^^ semi ^^ hardline ^^ doc_block [exp]
  | [E_aux (E_var (lexp, binding, E_aux (E_block exps, _)), _)] ->
      separate space [string "var"; doc_lexp lexp; equals; doc_exp binding] ^^ semi ^^ hardline ^^ doc_block exps
  | E_aux (E_if (if_exp, then_exp, E_aux ((E_lit (L_aux (L_unit, _)) | E_block []), _)), _) :: exps ->
      group (separate space [string "if"; doc_exp if_exp; string "then"; doc_exp then_exp])
      ^^ semi ^^ hardline ^^ doc_block exps
  | [exp] -> doc_exp exp
  | exp :: exps -> doc_exp exp ^^ semi ^^ hardline ^^ doc_block exps

and doc_lexp (LE_aux (l_aux, _) as lexp) =
  match l_aux with LE_typ (typ, id) -> separate space [doc_id id; colon; doc_typ typ] | _ -> doc_atomic_lexp lexp

and doc_atomic_lexp (LE_aux (l_aux, _) as lexp) =
  match l_aux with
  | LE_id id -> doc_id id
  | LE_deref exp -> lparen ^^ string "*" ^^ doc_atomic_exp exp ^^ rparen
  | LE_tuple lexps -> lparen ^^ separate_map (comma ^^ space) doc_lexp lexps ^^ rparen
  | LE_field (lexp, id) -> doc_atomic_lexp lexp ^^ dot ^^ doc_id id
  | LE_vector (lexp, exp) -> doc_atomic_lexp lexp ^^ brackets (doc_exp exp)
  | LE_vector_range (lexp, exp1, exp2) ->
      doc_atomic_lexp lexp ^^ brackets (separate space [doc_exp exp1; string ".."; doc_exp exp2])
  | LE_vector_concat lexps -> parens (separate_map (string " @ ") doc_lexp lexps)
  | LE_app (id, exps) -> doc_id id ^^ parens (separate_map (comma ^^ space) doc_exp exps)
  | _ -> parens (doc_lexp lexp)

and doc_pexps pexps = surround 2 0 lbrace (separate_map (comma ^^ hardline) doc_pexp pexps) rbrace

and doc_pexp (Pat_aux (pat_aux, _)) =
  match pat_aux with
  | Pat_exp (pat, exp) -> separate space [doc_pat pat; string "=>"; doc_exp exp]
  | Pat_when (pat, wh, exp) -> separate space [doc_pat pat; string "if"; doc_exp wh; string "=>"; doc_exp exp]

and doc_letbind (LB_aux (lb_aux, _)) =
  match lb_aux with LB_val (pat, exp) -> separate space [doc_pat pat; equals; doc_exp exp]

and doc_exp_as_block (E_aux (aux, _) as exp) =
  match aux with
  | E_block _ | E_lit _ -> doc_exp exp
  | _ when !opt_insert_braces -> group (lbrace ^^ nest 4 (hardline ^^ doc_block [exp]) ^^ hardline ^^ rbrace)
  | _ -> doc_exp exp

and doc_vector_update = function
  | VU_single (idx, value) -> begin
      match (unaux_exp idx, unaux_exp value) with
      | E_id id, E_id id' when Id.compare id id' == 0 -> doc_atomic_exp idx
      | _, _ -> separate space [doc_atomic_exp idx; equals; doc_exp value]
    end
  | VU_range (high, low, value) ->
      separate space [doc_atomic_exp high; string ".."; doc_atomic_exp low; equals; doc_exp value]

let doc_funcl (FCL_aux (FCL_funcl (id, Pat_aux (pexp, _)), (def_annot, _))) =
  doc_def_annot def_annot
  ^^
  match pexp with
  | Pat_exp (pat, exp) -> group (separate space [doc_id id; doc_pat pat; equals; doc_exp_as_block exp])
  | Pat_when (pat, wh, exp) ->
      group
        (separate space
           [doc_id id; parens (separate space [doc_pat pat; string "if"; doc_exp wh]); string "="; doc_exp_as_block exp]
        )

let doc_default (DT_aux (DT_order ord, _)) = separate space [string "default"; string "Order"; doc_ord ord]

let doc_rec (Rec_aux (r, _)) =
  match r with
  | Rec_nonrec | Rec_rec -> empty
  | Rec_measure (pat, exp) -> braces (doc_pat pat ^^ string " => " ^^ doc_exp exp) ^^ space

let doc_fundef (FD_aux (FD_function (r, _, funcls), _)) =
  match funcls with
  | [] -> failwith "Empty function list"
  | _ ->
      let rec_pp = doc_rec r in
      let sep = hardline ^^ string "and" ^^ space in
      let clauses = separate_map sep doc_funcl funcls in
      string "function" ^^ space ^^ rec_pp ^^ clauses

let rec doc_mpat (MP_aux (mp_aux, _) as mpat) =
  match mp_aux with
  | MP_id id -> doc_id id
  | MP_tuple pats -> lparen ^^ separate_map (comma ^^ space) doc_mpat pats ^^ rparen
  | MP_lit lit -> doc_lit lit
  | MP_vector pats -> brackets (separate_map (comma ^^ space) doc_mpat pats)
  | MP_vector_concat pats -> separate_map (space ^^ string "@" ^^ space) doc_mpat pats
  | MP_app (id, pats) -> doc_id id ^^ parens (separate_map (comma ^^ space) doc_mpat pats)
  | MP_list pats -> string "[|" ^^ separate_map (comma ^^ space) doc_mpat pats ^^ string "|]"
  | _ -> string (string_of_mpat mpat)

let doc_mpexp (MPat_aux (mpexp, _)) =
  match mpexp with
  | MPat_pat mpat -> doc_mpat mpat
  | MPat_when (mpat, guard) -> doc_mpat mpat ^^ space ^^ string "if" ^^ space ^^ doc_exp guard

let doc_mapcl (MCL_aux (cl, (def_annot, _))) =
  doc_def_annot def_annot
  ^^
  match cl with
  | MCL_bidir (mpexp1, mpexp2) ->
      let left = doc_mpexp mpexp1 in
      let right = doc_mpexp mpexp2 in
      separate space [left; string "<->"; right]
  | MCL_forwards (mpexp, exp) ->
      let left = doc_mpexp mpexp in
      let right = doc_exp exp in
      separate space [left; string "=>"; right]
  | MCL_backwards (mpexp, exp) ->
      let left = doc_mpexp mpexp in
      let right = doc_exp exp in
      separate space [left; string "<-"; right]

let doc_mapdef (MD_aux (MD_mapping (id, _, mapcls), _)) =
  match mapcls with
  | [] -> failwith "Empty mapping"
  | _ ->
      let sep = string "," ^^ hardline in
      let clauses = separate_map sep doc_mapcl mapcls in
      string "mapping" ^^ space ^^ doc_id id ^^ space ^^ string "=" ^^ space ^^ surround 2 0 lbrace clauses rbrace

let doc_dec (DEC_aux (reg, _)) =
  match reg with
  | DEC_reg (typ, id, opt_exp) -> (
      match opt_exp with
      | None -> separate space [string "register"; doc_id id; colon; doc_typ typ]
      | Some exp -> separate space [string "register"; doc_id id; colon; doc_typ typ; equals; doc_exp exp]
    )

let doc_field (typ, id) = separate space [doc_id id; colon; doc_typ typ]

let doc_union (Tu_aux (Tu_ty_id (typ, id), def_annot)) =
  doc_def_annot def_annot ^^ separate space [doc_id id; colon; doc_typ typ]

let rec doc_index_range (BF_aux (ir, _)) =
  match ir with
  | BF_single i -> doc_nexp i
  | BF_range (i, j) -> doc_nexp i ^^ string ".." ^^ doc_nexp j
  | BF_concat (i, j) -> parens (doc_index_range i ^^ space ^^ at ^^ space ^^ doc_index_range j)

let doc_typ_arg_kind sep (A_aux (aux, _)) =
  match aux with
  | A_nexp _ -> space ^^ string sep ^^ space ^^ string "Int"
  | A_bool _ -> space ^^ string sep ^^ space ^^ string "Bool"
  | A_typ _ -> empty

let doc_typdef (TD_aux (td, _)) =
  match td with
  | TD_abbrev (id, typq, typ_arg) -> begin
      match doc_typquant typq with
      | Some qdoc ->
          doc_op equals
            (concat [string "type"; space; doc_id id; qdoc; doc_typ_arg_kind "->" typ_arg])
            (doc_typ_arg typ_arg)
      | None ->
          doc_op equals (concat [string "type"; space; doc_id id; doc_typ_arg_kind ":" typ_arg]) (doc_typ_arg typ_arg)
    end
  | TD_enum (id, ids, _) ->
      separate space
        [string "enum"; doc_id id; equals; surround 2 0 lbrace (separate_map (comma ^^ break 1) doc_id ids) rbrace]
  | TD_record (id, TypQ_aux (TypQ_no_forall, _), fields, _) | TD_record (id, TypQ_aux (TypQ_tq [], _), fields, _) ->
      separate space
        [
          string "struct";
          doc_id id;
          equals;
          surround 2 0 lbrace (separate_map (comma ^^ break 1) doc_field fields) rbrace;
        ]
  | TD_record (id, TypQ_aux (TypQ_tq qs, _), fields, _) ->
      separate space
        [
          string "struct";
          doc_id id;
          doc_param_quants qs;
          equals;
          surround 2 0 lbrace (separate_map (comma ^^ break 1) doc_field fields) rbrace;
        ]
  | TD_variant (id, TypQ_aux (TypQ_no_forall, _), unions, _) | TD_variant (id, TypQ_aux (TypQ_tq [], _), unions, _) ->
      separate space
        [
          string "union";
          doc_id id;
          equals;
          surround 2 0 lbrace (separate_map (comma ^^ break 1) doc_union unions) rbrace;
        ]
  | TD_variant (id, TypQ_aux (TypQ_tq qs, _), unions, _) ->
      separate space
        [
          string "union";
          doc_id id;
          doc_param_quants qs;
          equals;
          surround 2 0 lbrace (separate_map (comma ^^ break 1) doc_union unions) rbrace;
        ]
  | TD_bitfield (id, typ, fields) ->
      let doc_field (id, range) = separate space [doc_id id; colon; doc_index_range range] in
      doc_op equals
        (separate space [string "bitfield"; doc_id id; colon; doc_typ typ])
        (surround 2 0 lbrace (separate_map (comma ^^ break 1) doc_field fields) rbrace)

let doc_spec =
  let doc_extern ext =
    match ext with
    | Some ext ->
        let purity = if ext.pure then string "pure" ^^ space else string "monadic" ^^ space in
        let docs =
          List.map
            (fun (backend, rep) -> string (backend ^ ":") ^^ space ^^ utf8string ("\"" ^ String.escaped rep ^ "\""))
            ext.bindings
        in
        equals ^^ space ^^ purity ^^ braces (separate (comma ^^ space) docs)
    | None -> empty
  in
  function
  | VS_aux (VS_val_spec (ts, id, ext), _) ->
      string "val" ^^ space ^^ doc_id id ^^ space ^^ doc_extern ext ^^ colon ^^ space ^^ doc_typschm ts

let doc_prec = function Infix -> string "infix" | InfixL -> string "infixl" | InfixR -> string "infixr"

let doc_loop_measures l =
  separate_map
    (comma ^^ break 1)
    (function Loop (l, e) -> string (match l with While -> "while" | Until -> "until") ^^ space ^^ doc_exp e)
    l

let doc_scattered (SD_aux (sd_aux, _)) =
  match sd_aux with
  | SD_function (_, _, id) -> string "scattered" ^^ space ^^ string "function" ^^ space ^^ doc_id id
  | SD_funcl funcl -> string "function" ^^ space ^^ string "clause" ^^ space ^^ doc_funcl funcl
  | SD_end id -> string "end" ^^ space ^^ doc_id id
  | SD_variant (id, TypQ_aux (TypQ_no_forall, _)) -> string "scattered" ^^ space ^^ string "union" ^^ space ^^ doc_id id
  | SD_variant (id, TypQ_aux (TypQ_tq quants, _)) ->
      string "scattered" ^^ space ^^ string "union" ^^ space ^^ doc_id id ^^ doc_param_quants quants
  | SD_mapcl (id, mapcl) -> separate space [string "mapping clause"; doc_id id; equals; doc_mapcl mapcl]
  | SD_mapping (id, Typ_annot_opt_aux (Typ_annot_opt_none, _)) -> separate space [string "scattered mapping"; doc_id id]
  | SD_mapping (id, Typ_annot_opt_aux (Typ_annot_opt_some (typq, typ), _)) ->
      separate space [string "scattered mapping"; doc_id id; colon; doc_binding (typq, typ)]
  | SD_unioncl (id, tu) -> separate space [string "union clause"; doc_id id; equals; doc_union tu]
  | SD_internal_unioncl_record (id, record_id, typq, fields) ->
      let prefix = separate space [string "internal_union_record clause"; doc_id id; doc_id record_id] in
      let params =
        match typq with
        | TypQ_aux (TypQ_no_forall, _) | TypQ_aux (TypQ_tq [], _) -> empty
        | TypQ_aux (TypQ_tq qs, _) -> doc_param_quants qs
      in
      separate space
        [prefix ^^ params; equals; surround 2 0 lbrace (separate_map (comma ^^ break 1) doc_field fields) rbrace]
  | SD_enum id -> separate space [string "scattered enum"; doc_id id]
  | SD_enumcl (id, member) -> separate space [string "enum clause"; doc_id id; equals; doc_id member]

let doc_filter = function
  | DEF_aux ((DEF_pragma ("file_start", _, _) | DEF_pragma ("file_end", _, _)), _) -> false
  | _ -> true

let rec doc_def_no_hardline (DEF_aux (aux, def_annot)) =
  doc_def_annot def_annot
  ^^
  match aux with
  | DEF_default df -> doc_default df
  | DEF_val v_spec -> doc_spec v_spec
  | DEF_type t_def -> doc_typdef t_def
  | DEF_fundef f_def -> doc_fundef f_def
  | DEF_mapdef m_def -> doc_mapdef m_def
  | DEF_outcome (OV_aux (OV_outcome (id, typschm, args), _), defs) -> (
      string "outcome" ^^ space ^^ doc_id id ^^ space ^^ colon ^^ space ^^ doc_typschm typschm ^^ break 1
      ^^ (string "with" ^//^ separate_map (comma ^^ break 1) doc_kopt_no_parens args)
      ^^
      match defs with
      | [] -> empty
      | _ -> break 1 ^^ (string "= {" ^//^ separate_map (hardline ^^ hardline) doc_def_no_hardline defs) ^/^ string "}"
    )
  | DEF_instantiation (IN_aux (IN_id id, _), substs) -> (
      string "instantiation" ^^ space ^^ doc_id id
      ^^
      match substs with
      | [] -> empty
      | _ -> (space ^^ string "with") ^//^ separate_map (comma ^^ break 1) doc_subst substs
    )
  | DEF_impl funcl -> string "impl" ^^ space ^^ doc_funcl funcl
  | DEF_let lbind -> string "let" ^^ space ^^ doc_letbind lbind
  | DEF_internal_mutrec fundefs ->
      (string "mutual {" ^//^ separate_map (hardline ^^ hardline) doc_fundef fundefs) ^^ hardline ^^ string "}"
  | DEF_register dec -> doc_dec dec
  | DEF_scattered sdef -> doc_scattered sdef
  | DEF_measure (id, pat, exp) ->
      string "termination_measure" ^^ space ^^ doc_id id ^/^ doc_pat pat ^^ space ^^ equals ^/^ doc_exp exp
  | DEF_loop_measures (id, measures) ->
      string "termination_measure" ^^ space ^^ doc_id id ^/^ doc_loop_measures measures
  | DEF_pragma (pragma, arg, _) -> string ("$" ^ pragma ^ " " ^ arg)
  | DEF_fixity (prec, n, id) ->
      fixities := Bindings.add id (prec, Big_int.to_int n) !fixities;
      separate space [doc_prec prec; doc_int n; doc_id id]
  | DEF_overload (id, ids) ->
      separate space
        [string "overload"; doc_id id; equals; surround 2 0 lbrace (separate_map (comma ^^ break 1) doc_id ids) rbrace]

and doc_def def = group (doc_def_no_hardline def ^^ hardline)

let doc_ast { defs; _ } = separate_map hardline doc_def (List.filter doc_filter defs)

(* This function is intended to reformat machine-generated Sail into
   something a bit more readable, it is not intended to be used as a
   general purpose formatter *)
let reformat dir { defs; _ } =
  let file_stack = ref [] in

  let pop () =
    match !file_stack with
    | [] -> Reporting.unreachable Parse_ast.Unknown __POS__ "Unbalanced file structure"
    | Some chan :: chans ->
        close_out chan;
        file_stack := chans
    | None :: chans -> file_stack := chans
  in

  let push = function
    | Some path -> file_stack := Some (open_out path) :: !file_stack
    | None -> file_stack := None :: !file_stack
  in

  let adjust_path path = Filename.concat (Filename.concat (Filename.dirname path) dir) (Filename.basename path) in

  let output_def def =
    match !file_stack with
    | Some chan :: _ -> ToChannel.pretty 1. 120 chan (hardline ^^ doc_def def)
    | None :: _ -> ()
    | [] -> Reporting.unreachable Parse_ast.Unknown __POS__ "No file for definition"
  in

  let output_include path =
    match !file_stack with
    | Some chan :: _ ->
        if Filename.is_relative path then Printf.fprintf chan "$include \"%s\"\n" path
        else Printf.fprintf chan "$include <%s>\n" (Filename.basename path)
    | None :: _ -> ()
    | [] -> Reporting.unreachable Parse_ast.Unknown __POS__ "No file for include"
  in

  let format_def = function
    | DEF_aux (DEF_pragma ("file_start", path, _), _) -> push (Some (adjust_path path))
    | DEF_aux (DEF_pragma ("file_end", _, _), _) -> pop ()
    | DEF_aux (DEF_pragma ("include_start", path, _), _) ->
        output_include path;
        if Filename.is_relative path then push (Some (adjust_path path)) else push None
    | DEF_aux (DEF_pragma ("include_end", _, _), _) -> pop ()
    | def -> output_def def
  in

  opt_insert_braces := true;
  List.iter format_def defs;
  opt_insert_braces := false

let pp_ast f d = ToChannel.pretty 1. 80 f (doc_ast d)

let pretty_sail f doc = ToChannel.pretty 1. 120 f doc

let to_string doc =
  let b = Buffer.create 120 in
  ToBuffer.pretty 1. 120 b doc;
  Buffer.contents b
