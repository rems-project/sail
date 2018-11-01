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

open Type_check
open Ast
open Ast_util
open Rewriter
open PPrint
open Pretty_print_common

type blocktype = Expression | Action | ActionValue | Recipe

type ctxt = {
  blocktype : blocktype;
  lvars : IdSet.t;
  return_sink : bool;
}

let empty_ctxt = { blocktype = Expression; lvars = IdSet.empty; return_sink = false; }

let keywords = ["signed"; "unsigned"]

let bsv_id cap id =
  let is_num_char c = let c = Char.code c in (c >= 48 && c <= 57) in
  let is_upper c = let c = Char.code c in (c >= 65 && c <= 90) in
  let is_lower c = let c = Char.code c in (c >= 97 && c <= 122) in
  let is_alpha c = is_upper c || is_lower c in
  let valid_char c = (c = '$' || c = '_' || is_alpha c || is_num_char c) in
  let rec valid_from idx =
    if idx < String.length id then
      let c = String.get id idx in
      valid_char c &&
      (idx > 0 || not (is_num_char c || if cap then (is_lower c || c = 'Z') else (is_upper c || c = 'z'))) &&
      valid_from (idx + 1)
    else true
  in
  let valid = valid_from 0 && not (List.mem id keywords) in
  (if valid then id else Util.zencode_string id)
  |> if cap then String.capitalize else String.uncapitalize

let bsv_kid kid =
  let (Kid_aux (Var kid,l)) = orig_kid kid in
  bsv_id false (String.map (function '#' -> '_' | '\'' -> '_' | c -> c) kid)

let doc_id cap (Id_aux (i, _)) =
  match i with
  | Id i -> string (bsv_id cap i)
  | DeIid x -> string (bsv_id cap ("op " ^ x))

let doc_typ_id id =
  match string_of_id id with
  | "bit" -> string "bit"
  | "bool" -> string "Bool"
  | "option" -> string "Maybe"
  | "list" -> string "List"
  | "unit" -> string "void"
  | "string" -> string "String"
  | "register" -> string "Reg"
  | "regstate" -> string "Regstate"
  | "register_value" -> string "RegisterValue"
  | _ -> doc_id true id

let doc_constr_id id =
  match string_of_id id with
  | "Some" -> string "Valid"
  | "None" -> string "Invalid"
  | _ -> doc_id true id

let doc_lit (L_aux (lit, _)) = match lit with
  | L_unit -> string "?"
  | L_zero -> string "1\'b0"
  | L_one -> string "1\'b1"
  | L_true -> string "True"
  | L_false -> string "False"
  | L_num i -> string (Big_int.to_string i)
  | L_hex h -> string ("\'h" ^ h)
  | L_bin b -> string ("\'b" ^ b)
  | L_string s -> dquotes (string s)
  | L_undef -> string "?"
  | L_real r -> string r

let has_mem_eff (Effect_aux (Effect_set effs, _)) =
  let mem_eff (BE_aux (be, _)) = match be with
    | BE_rmem | BE_rmemt | BE_wmem | BE_eamem | BE_exmem
    | BE_wmv | BE_wmvt | BE_barr -> true
    | _ -> false
  in
  List.exists mem_eff effs
let has_eff eff (Effect_aux (Effect_set effs, _)) =
  List.exists (fun (BE_aux (be, _)) -> eff = be) effs
let effectful_effs (Effect_aux (Effect_set effs, _)) = not (effs = [])
let effectful exp = effectful_effs (effect_of exp)
let effectful_pexp pexp = effectful_effs (effect_of_pexp pexp)
let is_enum id env = match Env.lookup_id id env with
  | Enum _ -> true
  | _ -> false

let doc_nexp nexp =
  let (Nexp_aux (nexp, l) as full_nexp) = nexp_simp nexp in
  match nexp with
  | Nexp_constant i -> string (Big_int.to_string i)
  | Nexp_var v -> string (bsv_kid v)
  | _ ->
     let rec mangle_nexp (Nexp_aux (nexp, _)) = begin
       match nexp with
       | Nexp_id id -> string_of_id id
       | Nexp_var kid -> bsv_kid kid
       | Nexp_constant i -> Big_int.to_string i
       | Nexp_times (n1, n2) -> mangle_nexp n1 ^ "_times_" ^ mangle_nexp n2
       | Nexp_sum (n1, n2) -> mangle_nexp n1 ^ "_plus_" ^ mangle_nexp n2
       | Nexp_minus (n1, n2) -> mangle_nexp n1 ^ "_minus_" ^ mangle_nexp n2
       | Nexp_exp n -> "exp_" ^ mangle_nexp n
       | Nexp_neg n -> "neg_" ^ mangle_nexp n
       | _ ->
          raise (Reporting.err_unreachable l __POS__
                  ("cannot pretty-print nexp \"" ^ string_of_nexp full_nexp ^ "\""))
     end in
     string (bsv_id false (mangle_nexp full_nexp))

let rec doc_typ (Typ_aux (taux, l) as typ) = match taux with
  | _ when is_number typ ->
     (* TODO Distinguish bounded number types *)
     string "Integer"
  | Typ_tup ts ->
     string ("Tuple" ^ string_of_int (List.length ts) ^ "#") ^^
     parens (separate_map comma_sp doc_typ ts)
  | Typ_exist (kids, nc, t) ->
     (* TODO Check that unsupported existentials don't escape into output *)
     doc_typ t
  | Typ_id id -> doc_typ_id id
  | Typ_var var -> string (bsv_kid var)
  | Typ_app (vector, _) when string_of_id vector = "vector" ->
     let len, ord, etyp = vector_typ_args_of typ in
     if is_bit_typ etyp then string "Bit#" ^^ parens (doc_nexp len)
     else string "List#" ^^ parens (doc_typ etyp)
  | Typ_app (id, args) ->
     doc_typ_id id ^^ string "#" ^^ parens (separate_map comma_sp doc_typ_arg args)
  | _ -> raise (Reporting.err_todo l ("Unprintable type " ^ string_of_typ typ))
and doc_typ_arg (Typ_arg_aux (targ, l)) = match targ with
  | Typ_arg_nexp nexp -> doc_nexp nexp
  | Typ_arg_typ typ -> doc_typ typ
  | Typ_arg_order _ ->
     raise (Reporting.err_unreachable l __POS__ ("Unprintable order type arg"))

let exp_uses_lvars ctxt exp =
  let used_vars =
    fold_exp
      { (pure_exp_alg IdSet.empty IdSet.union)
        with e_id = IdSet.singleton; lEXP_id = IdSet.singleton;
             lEXP_cast = (fun (_, id) -> IdSet.singleton id) }
      exp
  in
  IdSet.exists (fun id -> IdSet.mem id ctxt.lvars) used_vars

let lexp_assigns_lvars ctxt lexp =
  let assigned_vars =
    fold_lexp
      { (pure_exp_alg IdSet.empty IdSet.union)
        with lEXP_id = IdSet.singleton;
             lEXP_cast = (fun (_, id) -> IdSet.singleton id) }
      lexp
  in
  IdSet.exists (fun id -> IdSet.mem id ctxt.lvars) assigned_vars

let lexp_writes_registers lexp = has_eff BE_wreg (effect_of_lexp lexp)

let assign_op ctxt lhs rhs =
  if lexp_writes_registers lhs || lexp_assigns_lvars ctxt lhs then string "<="
  else if effectful rhs && not (is_unit_typ (typ_of rhs)) then string "<-"
  else string "="

let get_blocktype ctxt exp =
  let used_vars =
    fold_exp
      { (pure_exp_alg IdSet.empty IdSet.union)
        with e_id = IdSet.singleton; lEXP_id = IdSet.singleton;
             lEXP_cast = (fun (_, id) -> IdSet.singleton id) }
      exp
  in
  let uses_lvar = IdSet.exists (fun id -> IdSet.mem id ctxt.lvars) used_vars in
  if has_mem_eff (effect_of exp) then Recipe else
  if effectful exp || uses_lvar then
    if is_unit_typ (typ_of exp) then Action else ActionValue
  else Expression

let enclose_block bt doc =
  let dopen, dclose = match bt with
    | Expression -> ("begin", "end")
    | Action -> ("action", "endaction")
    | ActionValue -> ("actionvalue", "endactionvalue")
    | Recipe -> ("`FastSeq", "`End")
  in
  surround 2 1 (string dopen) doc (string dclose)

let is_actionvalue exp =
  effectful exp &&
  not (has_mem_eff (effect_of exp)) &&
  not (is_unit_typ (typ_of exp))
let is_seq exp = has_mem_eff (effect_of exp)

let rec map_last f f_last = function
  | [x] -> [f_last x]
  | x :: xs -> f x :: map_last f f_last xs
  | [] -> []

let rec doc_pat_combinator (P_aux (paux, (l, _)) as pat) = match paux with
  | P_lit lit -> string "litPat" ^^ parens (doc_lit lit), []
  | P_wild -> string "wildPat", []
  | P_as (p, id) ->
     let pdoc, vars = doc_pat_combinator p in
     string "bindPat" ^^ parens (pdoc), ((typ_of_pat pat, id) :: vars)
  | P_typ (_, pat) -> doc_pat_combinator pat
  | P_id id when is_enum id (env_of_pat pat) ->
     string "litPat" ^^ parens (doc_id false id), []
  | P_id id ->
     string "varPat", [(typ_of_pat pat, id)]
  | P_var (pat, _) -> doc_pat_combinator pat
  | P_app (id, ps) ->
     let pdoc, vars = match ps with
       | [] -> empty, []
       | [p] when is_unit_typ (typ_of_pat p) -> empty, []
       | _ ->
          let pdocs, vars = List.split (List.map doc_pat_combinator ps) in
          parens (separate comma_sp pdocs), List.concat vars
     in
     doc_id false (prepend_id "pat_" id) ^^ pdoc, vars
  | P_tup ps ->
     let pdocs, vars = List.split (List.map doc_pat_combinator ps) in
     string ("tup" ^ string_of_int (List.length ps)) ^^ parens (separate comma_sp pdocs),
     List.concat vars
  | _ -> raise (Reporting.err_todo l "doc_pat_combinator: not yet implemented")

let rec ensure_block (E_aux (eaux, a) as exp) =
  let rewrap e = E_aux (e, a) in
  match eaux with
  | E_block _ -> exp
  (* | E_if (i, t, e) -> rewrap (E_if (i, ensure_block t, ensure_block e)) *)
  | E_case (e, ps) ->
     let ensure_block_pexp pexp =
       let pat, guard, exp, a = destruct_pexp pexp in
       construct_pexp (pat, guard, ensure_block exp, a)
     in
     rewrap (E_case (e, List.map ensure_block_pexp ps))
  | _ -> E_aux (E_block [exp], a)

let rec doc_stmt ctxt (E_aux (eaux, (l, annot)) as exp) =
  match eaux with
  | E_if (i, t, E_aux (E_lit (L_aux (L_unit, _)), _)) when ctxt.blocktype <> ActionValue ->
     prefix 2 1 (string "if " ^^ parens (doc_exp ctxt i)) (doc_stmt ctxt t)
  | E_if (i, t, e) ->
     prefix 0 1
       (prefix 2 1 (string "if " ^^ parens (doc_exp ctxt i)) (doc_stmt ctxt t))
       (prefix 2 1 (string "else") (doc_stmt ctxt e))
  | E_case (e, ps) ->
     surround 2 1
       (surround 2 1 (string "case") (parens (doc_exp ctxt e)) (string "matches"))
       (separate_map hardline (doc_pexp ctxt) ps)
       (string "endcase")
  | E_assign (lhs, rhs)
    when exp_uses_lvars ctxt rhs ||
         (effectful rhs &&
          (lexp_writes_registers lhs || lexp_assigns_lvars ctxt lhs)) ->
     enclose_block Action
       (separate (break 1)
          [prefix 2 1 (string "let zresult <-") (doc_exp ctxt rhs) ^^ semi;
           infix 2 1 (string "<=") (doc_lexp ctxt lhs) (string "zresult") ^^ semi])
  | E_assign (lhs, rhs) ->
     separate space [doc_lexp ctxt lhs; assign_op ctxt lhs rhs; doc_exp ctxt rhs] ^^ semi
  | E_return e when ctxt.return_sink ->
     string "outsnk.put" ^^ parens (doc_exp ctxt exp) ^^ semi
  | E_return e when ctxt.blocktype = ActionValue ->
     prefix 2 1 (string "return") (doc_exp ctxt exp ^^ semi)
  | _ -> parens (doc_exp ctxt exp) ^^ semi
and doc_recipe ctxt (E_aux (eaux, (l, annot)) as exp) =
  match eaux with
  | E_block _ -> doc_exp ctxt exp
  | E_if (i, t, E_aux (E_lit (L_aux (L_unit, _)), _)) ->
     surround 2 1
       (string "`When" ^^ parens (doc_exp ctxt i))
       (doc_recipe ctxt t)
       (string "`End")
  | E_if (i, t, e) ->
     prefix 0 1
       (prefix 2 1 (string "`If" ^^ parens (doc_exp ctxt i)) (doc_recipe ctxt t))
       (surround 2 1 (string "`Else") (doc_recipe ctxt e) (string "`End"))
  | E_case (e, ps) ->
     let doc_p p tail =
       string "Cons" ^^ parens (doc_pexp_combinator ctxt p ^^ comma ^^ break 1 ^^ tail)
     in
     let doc_ps = List.fold_right doc_p ps (string "Nil") in
     prefix 2 1 (string "rCase(" ^^ parens (doc_exp ctxt e) ^^ comma) (doc_ps ^^ string ")")
  | E_assign (lhs, (E_aux (E_app (f, args), _) as rhs))
  | E_assign (lhs, (E_aux (E_app (f, args), _) as rhs))
    when has_mem_eff (effect_of rhs) ->
     let toRecipe doc =
       string "toRecipe" ^^
       parens (surround 2 1 (string "action") doc (string "endaction"))
     in
     let ifc = doc_id false (append_id f "_ifc") in
     let call =
       ifc ^^ string ".sink.put" ^^
       parens (doc_exp ctxt (E_aux (E_tuple args, (l, empty_tannot)))) ^^ semi in
     let resp =
       separate (break 1)
         [prefix 2 1 (string "let zresult <-") (ifc ^^ string ".source.get()") ^^ semi;
          infix 2 1 (string "<=") (doc_lexp ctxt lhs) (string "zresult") ^^ semi]
     in
     surround 2 1
       (string "`FastSeq")
       (separate (comma ^^ break 1) [toRecipe call; toRecipe resp])
       (string "`End")
  | E_app (f, args) when has_mem_eff (effect_of exp) ->
     doc_id false (append_id f "_ifc") ^^ string ".sink.put" ^^
     parens (doc_exp ctxt (E_aux (E_tuple args, (l, empty_tannot))))
  | E_return e when ctxt.return_sink ->
     string "toRecipe" ^^ parens (string "outsnk.put" ^^ parens (doc_exp ctxt exp))
  | _ ->
     string "toRecipe" ^^
     parens (doc_exp { ctxt with blocktype = Action; } (ensure_block exp))
and doc_exp ctxt (E_aux (eaux, (l, annot)) as exp) =
  match eaux with
  | E_block (_ :: _ as es) ->
     let ctxt' exp = { ctxt with blocktype = get_blocktype ctxt exp; } in
     let doc_butlast, doc_last, sep =
       if ctxt.blocktype = Recipe then
         (fun exp -> doc_recipe (ctxt' exp) exp), (doc_recipe ctxt), comma
       else
         (fun exp -> doc_stmt (ctxt' exp) exp), (doc_stmt ctxt), empty
     in
     let docs = map_last doc_butlast doc_last es in
     enclose_block ctxt.blocktype (separate (sep ^^ break 1) docs)
  | E_block [] -> enclose_block ctxt.blocktype empty
  | E_id id ->
     (if Env.is_register id (env_of exp) then string "z." else empty) ^^
     doc_id (is_enum id (env_of exp)) id ^^ (if IdSet.mem id ctxt.lvars then string "[1]" else empty)
  | E_lit lit -> doc_lit lit
  | E_cast (t, e) -> separate space [doc_typ t; string "\'"; parens (doc_exp ctxt e)]
  | E_app (id, es) ->
     let union = Env.is_union_constructor id (env_of exp) in
     let call = match destruct_tannot annot with
       | Some (env, _, _) when Env.is_extern id (env_of exp) "bsv" ->
          string (Env.get_extern id (env_of exp) "bsv")
       | _ when union -> doc_constr_id id
       | _ -> doc_id false id
     in
     let fun_effs =
       try
         match unaux_typ (snd (Env.get_val_spec_orig id (env_of exp))) with
         | Typ_fn (_, _, eff) -> eff
         | _ -> no_effect
       with _ -> no_effect
     in
     let state_arg = if effectful_effs fun_effs then [string "z"] else [] in
     let argstup = doc_exp ctxt (E_aux (E_tuple es, (l, empty_tannot))) in
     let argslist =
       match state_arg, es with
       | [], [] -> []
       | [], [e] when is_unit_typ (typ_of e) -> []
       | _, _ ->
          if union then
            [parens (doc_exp ctxt (E_aux (E_tuple es, (l, empty_tannot))))]
          else
            let doc_es = List.map (doc_exp ctxt) es in
            [parens (separate comma_sp (state_arg @ doc_es))]
     in
     if union then
       separate space (string "tagged" :: call :: argslist)
     else
       concat (call :: argslist)
  | E_tuple [] -> string "?"
  | E_tuple [e] -> doc_exp ctxt e
  | E_tuple es ->
     string ("tuple" ^ string_of_int (List.length es)) ^^ space ^^
     parens (separate_map comma_sp (doc_exp ctxt) es)
  | E_if (i, t, e) ->
     separate space [doc_exp ctxt i; string "?"; doc_exp ctxt t; string ":"; doc_exp ctxt e]
  | E_vector es when is_bitvector_typ (typ_of exp) ->
     braces (separate_map comma_sp (doc_exp ctxt) es)
  | E_list es -> braces (separate_map comma_sp (doc_exp ctxt) es)
  | E_case (e, ps) ->
     surround 2 1
       (surround 2 1 (string "case") (parens (doc_exp ctxt e)) (string "matches"))
       (separate_map hardline (doc_pexp ctxt) ps)
       (string "endcase")
  | E_let (lb, e) ->
     enclose_block ctxt.blocktype
       (prefix 0 1
         (doc_letbind ctxt lb ^^ semi)
         (doc_stmt ctxt e))
  | E_return e -> doc_exp ctxt e
  | E_assert (E_aux (E_constraint nc, _), msg) ->
     string "staticAssert" ^^ parens (separate comma_sp [Pretty_print_sail.doc_nc nc; doc_exp ctxt msg])
  | E_assert (c, msg) ->
     string "dynamicAssert" ^^ parens (separate comma_sp [doc_exp ctxt c; doc_exp ctxt msg])
  (* TODO *)
  | _ -> raise (Reporting.err_todo l "not implemented")
and doc_pat (P_aux (p_aux, (l, annot)) as pat) =
  match p_aux with
  | P_lit lit -> doc_lit lit
  | P_wild -> string ".*"
  | P_id id ->
     let enum = is_enum id (env_of_pat pat) in
     (if enum then empty else string ".") ^^ doc_id enum id
  | P_app (id, ps) when Env.is_union_constructor id (env_of_pat pat) ->
     let doc_ps = match ps with
       | [] -> []
       | [p] when is_unit_typ (typ_of_pat p) -> []
       | [p] -> [doc_pat p]
       | _ -> [braces (separate_map comma_sp doc_pat ps)]
     in
     separate space (string "tagged" :: doc_constr_id id :: doc_ps)
  | P_tup ps -> braces (separate_map comma_sp doc_pat ps)
  | P_var (pat, _) | P_typ (_, pat) -> doc_pat pat
  (* TODO *)
  | _ -> raise (Reporting.err_todo l "not implemented")
and doc_pexp ctxt pexp =
  let pat, guard, exp, _ = destruct_pexp pexp in
  let gdoc = match guard with
    | Some wh -> [string "&&&"; doc_exp ctxt wh]
    | None -> []
  in
  prefix 2 1
    (separate space (doc_pat pat :: gdoc @ [string ":"]))
    (doc_stmt ctxt exp)
and doc_pexp_combinator ctxt pexp =
  let pat, guard, exp, _ = destruct_pexp pexp in
  let pdoc, vars = doc_pat_combinator pat in
  let gdoc = match guard with
    | Some wh -> string "guarded" ^^ parens (doc_exp ctxt wh ^^ comma_sp ^^ pdoc)
    | None -> pdoc
  in
  let vdoc (typ, id) = doc_typ typ ^^ space ^^ doc_id false id in
  let varsdoc = parens (separate_map comma_sp vdoc vars) in
  let fdoc =
    prefix 2 1
      (string "function Recipe f " ^^ varsdoc ^^ string " =")
      (doc_recipe ctxt exp ^^ semi)
  in
  let ldoc =
    surround 2 1
      (string "begin")
      (separate hardline [fdoc; string "f;"])
      (string "end")
  in
  prefix 2 1 (string "when(" ^^ gdoc ^^ comma) (ldoc ^^ string ")")
and doc_letbind ctxt (LB_aux (LB_val (p, e), _)) =
  match untyp_pat p with
  | P_aux (P_id id, _), _ when IdSet.mem id ctxt.lvars ->
     separate space
       [doc_id false id ^^ string "[0]";
        string (if has_mem_eff (effect_of e) then "<-" else "<=");
        doc_exp ctxt e]
  | P_aux (P_id id, _), Some typ when not (effectful e) ->
     separate space [doc_typ typ; doc_id false id; string "="; doc_exp ctxt e]
  | P_aux (P_id id, _), _ ->
     separate space
       [string "let";
        doc_id false id;
        string (if effectful e then "<-" else "=");
        doc_exp ctxt e]
  | _, _ ->
     separate space [string "match"; doc_pat p; string "="; doc_exp ctxt e]
and doc_lexp ctxt (LEXP_aux (l_aux, (l, a)) as lexp) =
  let env = env_of_annot (l, a) in
  match l_aux with
  | LEXP_cast (_, id) | LEXP_id id ->
     let state_prefix = if Env.is_register id env then string "z." else empty in
     let typdecl, creg_suffix =
       if IdSet.mem id ctxt.lvars then
         empty, string "[0]"
       else if Env.lookup_id id env = Unbound then
         doc_typ (typ_of_annot (l, a)) ^^ space, empty
       else empty, empty
     in
     typdecl ^^ state_prefix ^^ doc_id false id ^^ creg_suffix
  | LEXP_field (lexp, id) -> doc_lexp ctxt lexp ^^ dot ^^ doc_id false id
  | _ -> raise (Reporting.err_todo l "Unsupported lexp")

let doc_fundef (FD_aux (FD_function (r, typa, efa, funcls), (l, _))) =
  match funcls with
  | [] -> failwith "Empty function clause list"
  | [FCL_aux (FCL_Funcl (id, Pat_aux (pexp, _)), (l, annot)) as funcl] ->
     if Env.is_extern id (env_of_annot (l, annot)) "bsv" then empty else
     begin
       match pexp, destruct_tannot annot with
       | Pat_exp (pat, exp), Some (env, funcl_typ, _) ->
          let typ = try snd (Env.get_val_spec_orig id env) with | _ -> funcl_typ in
          let targs, tret, eff = match unaux_typ typ with
            | Typ_fn (targs, tret, eff) -> targs, tret, eff
            | _ -> raise (Reporting.err_unreachable l __POS__ "Unexpected function clause type")
          in
          let lvars_pat pat = fst (fold_pat
            { (compute_pat_alg Bindings.empty (Bindings.union (fun _ _ r -> Some r))) with
              p_aux = (fun ((v, p), annot) ->
                match p with
                | P_id id when Env.lookup_id id (env_of_annot annot) = Unbound ->
                   Bindings.add id (typ_of_annot annot) v, P_aux (p, annot)
                | _ -> v, P_aux (p, annot))
            } pat)
          in
          let lvars = fst (fold_exp
            { (compute_exp_alg Bindings.empty (Bindings.union (fun _ _ r -> Some r))) with
              lEXP_aux = (fun ((v, le), annot) ->
                match le with
                | LEXP_id id | LEXP_cast (_, id)
                  when Env.lookup_id id (env_of_annot annot) = Unbound ->
                   Bindings.add id (typ_of_annot annot) v, LEXP_aux (le, annot)
                | _ -> v, LEXP_aux (le, annot));
              e_let = (fun ((v1, lb), (v2, e)) ->
                let (LB_aux (LB_val (pat, _), _)) = lb in
                Bindings.union (fun _ _ r -> Some r)
                  (Bindings.union (fun _ _ r -> Some r) v1 (lvars_pat pat))
                  v2,
                E_let (lb, e))
            } exp)
          in
          let ctxt =
            { lvars =
                if has_mem_eff eff
                then IdSet.of_list (List.map fst (Bindings.bindings lvars))
                else IdSet.empty;
              return_sink = has_mem_eff eff;
              blocktype = get_blocktype empty_ctxt exp;
            }
          in
          let state_arg =
            if effectful_effs eff && not (has_mem_eff eff)
            then [string "Regstate z"]
            else []
          in
          let retsnk_arg =
            if ctxt.return_sink
            then [string "Sink#" ^^ parens (doc_typ tret) ^^ string " outsnk"]
            else []
          in
          let formals =
            (* TODO Map constraints to provisos *)
            match unaux_pat (fst (untyp_pat pat)), targs with
            | P_tup ps, _ ->
               let doc p t =
                 match fst (untyp_pat p) with
                 | P_aux (P_id id, _) when Env.lookup_id id env = Unbound ->
                    doc_typ t ^^ space ^^ doc_id false id
                 | _ ->
                    raise (Reporting.err_unreachable l __POS__ "Unsupported function parameter")
               in
               List.map2 doc ps targs
            | P_id id, _ | P_var (P_aux (P_id id, _), _), _
              when Env.lookup_id id env = Unbound ->
               let targ = match targs with
                 | [targ] -> targ
                 | targs -> mk_typ (Typ_tup targs)
               in
               [doc_typ targ ^^ space ^^ doc_id false id]
            | _, [targ] when is_unit_typ targ ->
               []
            | _ -> raise (Reporting.err_unreachable l __POS__ "Unsupported function parameters")
          in
          let formals_doc = parens (separate comma_sp (state_arg @ formals @ retsnk_arg)) in
          let tret_doc =
            if has_mem_eff eff then string "Recipe"
            else if effectful_effs eff then
              if is_unit_typ tret
              then string "Action"
              else string "ActionValue#" ^^ parens (doc_typ tret)
            else doc_typ tret
          in
          let fun_doc =
              prefix 2 1
                (separate space [string "function"; tret_doc; doc_id false id; formals_doc; equals])
                (doc_exp ctxt (if effectful_effs eff then ensure_block exp else exp) ^^ semi)
          in
          if has_mem_eff eff then
            let called_ifcs = fst (fold_exp
              { (compute_exp_alg Bindings.empty (Bindings.union (fun _ _ r -> Some r))) with
                e_aux = (fun ((v, e), annot) ->
                  match e with
                  | E_app (id, es) ->
                     let fun_eff =
                       try
                         match unaux_typ (snd (Env.get_val_spec_orig id (env_of_annot annot))) with
                         | Typ_fn (_, _, eff) -> eff
                         | _ -> no_effect
                       with
                       | _ -> no_effect
                     in
                     if has_mem_eff fun_eff then
                       (* TODO Distinguish different type instantiations of function *)
                       let targ = mk_typ (Typ_tup (List.map typ_of es)) in
                       let tret = typ_of_annot annot in
                       Bindings.add id (targ, tret) v, E_aux (e, annot)
                     else v, E_aux (e, annot)
                  | _ -> v, E_aux (e, annot))
              } exp)
            in
            let doc_ifc (id, (targ, tret)) =
              separate space
                [string "Slave#" ^^ parens (separate comma_sp [doc_typ targ; doc_typ tret]);
                 doc_id false (append_id id "_ifc"); string "<-";
                 doc_id false (prepend_id "mk_" id) ^^ parens (string "z") ^^ semi]
            in
            let doc_ifcs = separate_map hardline doc_ifc (Bindings.bindings called_ifcs) in
            let doc_lvar (id, typ) =
              separate space [string "Reg#" ^^ parens (doc_typ typ);
              doc_id false id ^^ string "[2]"; string "<- mkCRegU(2)" ^^ semi]
            in
            let doc_lvars = separate_map hardline doc_lvar (Bindings.bindings lvars) in
            let indent doc = string "  " ^^ align doc in
            separate hardline
              [string "module[Module] " ^^ doc_id false (prepend_id "mk_" id) ^^
                 string " (Regstate z, Slave#(" ^^
                 doc_typ (mk_typ (Typ_tup targs)) ^^ comma_sp ^^ doc_typ tret ^^
                 string ") ifc);";
               indent doc_lvars; empty;
               indent doc_ifcs; empty;
               indent fun_doc; empty;
               indent (string "let ifc <- mkRecipeFSMSlave(" ^^ doc_id false id ^^ string ");");
               indent (string "return ifc;");
               string "endmodule"]
          else
            fun_doc
       | _ -> raise (Reporting.err_unreachable l __POS__ "Unsupported function clause")
     end
  | _ -> raise (Reporting.err_unreachable l __POS__ "Multiple function clauses should have been merged")

let doc_kopt k_id =
  if is_nat_kopt k_id then [string ("numeric type " ^ bsv_kid (kopt_kid k_id))]
  else if is_typ_kopt k_id then [string ("type " ^ bsv_kid (kopt_kid k_id))]
  else []

let doc_tq tq =
  if quant_items tq = [] then empty
  else begin
    let qis = quant_kopts tq |> List.map doc_kopt |> List.concat |> separate comma_sp in
    string "#" ^^ parens qis
  end

let doc_union_pat_combinator tid tq members =
  let doc_mem (Tu_aux (Tu_ty_id (typ, cid), _)) =
    let argtyps = match typ with
      | Typ_aux (Typ_tup typs, _) -> typs
      | _ -> [typ]
    in
    let var p i = string (p ^ string_of_int i) in
    let pat_typ typ i j = string "Pat#" ^^ parens (separate comma_sp [typ; var "t" i; var "t" j]) in
    let doc_arg i typ = pat_typ (doc_typ typ) i (i + 1) ^^ space ^^ var "p" i in
    let doc_pats = match argtyps with
      | [] -> empty
      | _ -> braces (separate comma_sp (List.mapi (fun i _ -> dot ^^ var "x" i) argtyps))
    in
    let app i v = var "p" i ^^ parens v in
    let rec doc_app = function
      | [(i, v)] -> app i v
      | (i, v) :: vs -> string "app" ^^ parens (app i v ^^ comma_sp ^^ doc_app vs)
      | [] -> string "none"
    in
    let doc_apps = doc_app (List.mapi (fun i _ -> (i, var "x" i)) argtyps) in
    let doc_apps_undef = doc_app (List.mapi (fun i _ -> (i, string "?")) argtyps) in
    let cont =
      prefix 2 1
        (separate space
          [string "function";
           string "Cont#" ^^ parens (var "t" 0 ^^ comma_sp ^^ var "t" (List.length argtyps));
           string "k" ^^ parens (doc_typ_id tid ^^ doc_tq tq ^^ space ^^ string "s");
           equals])
        (surround 2 1
          (string "case (s) matches")
          (separate space [string "tagged"; doc_constr_id cid; doc_pats; colon; doc_apps ^^ semi] ^^
           break 1 ^^
           separate space [string ".*"; colon; string "fail" ^^ parens (doc_apps_undef) ^^ semi])
          (string "endcase;"))
    in
    surround 2 1
      (separate space
        [string "function";
         pat_typ (doc_typ_id tid ^^ doc_tq tq) 0 (List.length argtyps);
         doc_id false (prepend_id "pat_" cid);
         parens (separate comma_sp (List.mapi doc_arg argtyps)) ^^ semi])
      (cont ^^ break 1 ^^ string "return k;")
      (string "endfunction")
  in
  separate_map (hardline) doc_mem members

let doc_typdef (TD_aux (td, _)) =
  let builtins = ["option"] in
  match td with
  | TD_abbrev (id, _, TypSchm_aux (TypSchm_ts (tq, typ), _))
    when not (List.mem (string_of_id id) builtins) ->
     separate space [string "typedef"; doc_typ typ; doc_typ_id id ^^ doc_tq tq] ^^ semi
  | TD_record (id, _, tq, fields, _)
    when not (List.mem (string_of_id id) builtins) ->
     let regstate = string_of_id id = "regstate" in
     let doc_field (typ, id) =
       let typ =
         if regstate
         then app_typ (mk_id "register") [mk_typ_arg (Typ_arg_typ typ)]
         else typ
       in
       doc_typ typ ^^ space ^^ doc_id false id ^^ semi
     in
     let doc_fields = group (separate_map (break 1) doc_field fields) in
     surround 2 1
       (string "typedef struct {")
       (align doc_fields)
       (string "} " ^^ doc_typ_id id ^^ doc_tq tq) ^^ semi
  | TD_variant (id, _, tq, members, _)
    when not (List.mem (string_of_id id) builtins) ->
     let doc_mem (Tu_aux (Tu_ty_id (typ, id), _)) =
       doc_typ typ ^^ space ^^ doc_constr_id id ^^ semi
     in
     let doc_members = group (separate_map (break 1) doc_mem members) in
     surround 2 1
       (string "typedef union tagged {")
       (align doc_members)
       (string "} " ^^ doc_typ_id id ^^ doc_tq tq) ^^ semi ^^
     hardline ^^
     doc_union_pat_combinator id tq members
  | TD_enum (id, _, members, _)
    when not (List.mem (string_of_id id) builtins) ->
     separate space
       [string "typedef enum {";
        separate_map comma_sp doc_typ_id members;
        string "}"; doc_typ_id id] ^^ semi
  | _ -> empty

let doc_def = function
  | DEF_fundef fd -> doc_fundef fd
  | DEF_type td -> doc_typdef td
  | _ -> empty

let doc_defs (Defs defs) =
  let is_typdef = function | DEF_type _ -> true | _ -> false in
  let typdefs, defs = List.partition is_typdef defs in
  separate hardline [
    string "import List :: *;";
    string "import Assert :: *;";
    string "import BitPat :: *;";
    string "import MasterSlave :: *;";
    string "import SourceSink :: *;";
    string "import Recipe :: *;";
    string "import Sail :: *;";
    string "`include \"RecipeMacros.inc\"";
    empty;
    separate_map hardline doc_def typdefs;
    separate_map hardline doc_def defs;
    empty;
    string "module top (Empty);";
    string " // TODO";
    string "endmodule";
    empty
  ]

let pp_defs out defs = ToChannel.pretty 1. 80 out (doc_defs defs)
