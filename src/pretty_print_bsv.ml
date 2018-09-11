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
  (if valid_from 0 then id else Util.zencode_string id)
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
          raise (Reporting_basic.err_unreachable l __POS__
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
  | Typ_app (id, args) ->
     if is_vector_typ typ then
       let len, ord, etyp = vector_typ_args_of typ in
       if is_bit_typ etyp then string "Bit#" ^^ parens (doc_nexp len)
       else string "List#" ^^ parens (doc_typ etyp)
     else
       doc_typ_id id ^^ string "#" ^^ parens (separate_map comma_sp doc_typ_arg args)
  | _ -> raise (Reporting_basic.err_todo l ("Unprintable type " ^ string_of_typ typ))
and doc_typ_arg (Typ_arg_aux (targ, l)) = match targ with
  | Typ_arg_nexp nexp -> doc_nexp nexp
  | Typ_arg_typ typ -> doc_typ typ
  | Typ_arg_order _ ->
     raise (Reporting_basic.err_unreachable l __POS__ ("Unprintable order type arg"))

let enclose_block tannot doc =
  let dopen, dclose = match destruct_tannot tannot with
    | Some (env, typ, eff) when effectful_effs eff ->
       if has_mem_eff eff then ("seq", "endseq")
       else if is_unit_typ typ then ("action", "endaction")
       else ("actionvalue", "endactionvalue")
    | _ -> ("begin", "end")
  in
  surround 2 1 (string dopen) doc (string dclose)

let assign_op lhs rhs =
  if has_eff BE_wreg (effect_of_lexp lhs) then string "<="
  else if effectful rhs then string "<-" else string "="

let rec doc_exp stmt (E_aux (eaux, (l, annot)) as exp) =
  let stmt_semi = if stmt then semi else empty in
  match eaux with
  | E_block es ->
     enclose_block annot (separate_map (break 1) (doc_exp true) es)
  | E_id id ->
     (if Env.is_register id (env_of exp) then string "z." else empty) ^^
     doc_id (is_enum id (env_of exp)) id ^^ stmt_semi
  | E_lit lit -> doc_lit lit ^^ stmt_semi
  | E_cast (t, e) -> separate space [doc_typ t; string "\'"; parens (doc_exp false e)] ^^ stmt_semi
  | E_app (id, es) ->
     let union = Env.is_union_constructor id (env_of exp) in
     let state_arg =
       try
         match unaux_typ (snd (Env.get_val_spec_orig id (env_of exp))) with
         | Typ_fn (_, _, eff) when effectful_effs eff -> [string "z"]
         | _ -> []
       with _ -> []
     in
     let args =
       match state_arg, es with
       | [], [] -> []
       | [], [e] when is_unit_typ (typ_of e) -> []
       | [], es when union ->
          [parens (doc_exp false (E_aux (E_tuple es, (l, empty_tannot))))]
       | _, _ ->
          let doc_es = List.map (doc_exp false) es in
          [parens (separate comma_sp (state_arg @ doc_es))]
     in
     if union then
       separate space (string "tagged" :: doc_constr_id id :: args) ^^ stmt_semi
     else
       concat (doc_id false id :: args) ^^ stmt_semi
  | E_tuple [] -> string "?" ^^ stmt_semi
  | E_tuple [e] -> doc_exp false e ^^ stmt_semi
  | E_tuple es ->
     string ("tuple" ^ string_of_int (List.length es)) ^^ space ^^
     parens (separate_map comma_sp (doc_exp false) es) ^^ stmt_semi
  | E_if (i, t, E_aux (E_lit (L_aux (L_unit, _)), _)) when stmt ->
     prefix 2 1 (string "if " ^^ parens (doc_exp false i)) (doc_exp true t)
  | E_if (i, t, e) ->
     if stmt then
       prefix 0 1
         (prefix 2 1 (string "if " ^^ parens (doc_exp false i)) (doc_exp true t))
         (prefix 2 1 (string "else") (doc_exp true e))
     else
       separate space [doc_exp false i; string "?"; doc_exp false t; string ":"; doc_exp false e]
  | E_vector es when is_bitvector_typ (typ_of exp) ->
     braces (separate_map comma_sp (doc_exp false) es) ^^ stmt_semi
  | E_list es -> braces (separate_map comma_sp (doc_exp false) es) ^^ stmt_semi
  | E_case (e, ps) ->
     surround 2 1
       (surround 2 1 (string "case") (parens (doc_exp false e)) (string "matches"))
       (separate_map hardline (doc_pexp stmt) ps)
       (string "endcase")
  | E_let (lb, e) ->
     enclose_block annot
       (prefix 0 1
         (doc_letbind lb ^^ semi)
         (doc_exp true e))
  | E_assign (LEXP_aux (LEXP_id id, _) as lhs, rhs)
    when Env.lookup_id id (env_of exp) = Unbound ->
     separate space [string "let"; doc_id false id; assign_op lhs rhs; doc_exp false rhs] ^^ stmt_semi
  | E_assign (LEXP_aux (LEXP_cast (typ, id), _) as lhs, rhs)
    when Env.lookup_id id (env_of exp) = Unbound ->
     separate space [doc_typ typ; doc_id false id; assign_op lhs rhs; doc_exp false rhs] ^^ stmt_semi
  | E_assign (lhs, rhs) ->
     separate space [doc_lexp lhs; assign_op lhs rhs; doc_exp false rhs] ^^ stmt_semi
  | E_assert (E_aux (E_constraint nc, _), msg) ->
     string "staticAssert" ^^ parens (separate comma_sp [Pretty_print_sail.doc_nc nc; doc_exp false msg]) ^^ stmt_semi
  | E_assert (c, msg) ->
     string "dynamicAssert" ^^ parens (separate comma_sp [doc_exp false c; doc_exp false msg]) ^^ stmt_semi
  (* TODO *)
  | _ -> Pretty_print_sail.doc_exp exp
and doc_pat (P_aux (p_aux, (l, annot)) as pat) =
  match p_aux with
  | P_lit lit -> doc_lit lit
  | P_wild -> string ".*"
  | P_id id ->
     let enum = is_enum id (pat_env_of pat) in
     (if enum then empty else string ".") ^^ doc_id enum id
  | P_app (id, ps) when Env.is_union_constructor id (pat_env_of pat) ->
     let doc_ps = match ps with
       | [] -> []
       | [p] when is_unit_typ (pat_typ_of p) -> []
       | [p] -> [doc_pat p]
       | _ -> [braces (separate_map comma_sp doc_pat ps)]
     in
     separate space (string "tagged" :: doc_constr_id id :: doc_ps)
  | P_tup ps -> braces (separate_map comma_sp doc_pat ps)
  | P_var (pat, _) | P_typ (_, pat) -> doc_pat pat
  (* TODO *)
  | _ -> Pretty_print_sail.doc_pat pat
and doc_pexp stmt pexp =
  let pat, guard, exp, _ = destruct_pexp pexp in
  let gdoc = match guard with
    | Some wh -> [string "&&&"; doc_exp false wh]
    | None -> []
  in
  prefix 2 1
    (separate space (doc_pat pat :: gdoc @ [string ":"]))
    (doc_exp stmt exp)
and doc_letbind (LB_aux (LB_val (p, e), _)) =
  match untyp_pat p with
  | P_aux (P_id id, _), Some typ ->
     separate space [doc_typ typ; doc_id false id; string "="; doc_exp false e]
  | P_aux (P_id id, _), None ->
     let assign = if effectful e then "<-" else "=" in
     separate space [string "let"; doc_id false id; string assign; doc_exp false e]
  | _, _ ->
     separate space [string "match"; doc_pat p; string "="; doc_exp false e]
and doc_lexp (LEXP_aux (l_aux, (l, a)) as lexp) =
  match l_aux with
  | LEXP_cast (_, id) | LEXP_id id ->
     (if Env.is_register id (env_of_annot (l, a)) then string "z." else empty) ^^
     doc_id false id
  | LEXP_field (lexp, id) -> doc_lexp lexp ^^ dot ^^ doc_id false id
  | _ -> raise (Reporting_basic.err_todo l "Unsupported lexp")

let doc_fundef (FD_aux (FD_function (r, typa, efa, funcls), (l, _))) =
  match funcls with
  | [] -> failwith "Empty function clause list"
  | [FCL_aux (FCL_Funcl (id, Pat_aux (pexp, _)), (l, annot)) as funcl] ->
     begin
       match pexp, destruct_tannot annot with
       | Pat_exp (pat, exp), Some (env, funcl_typ, _) ->
          let typ = try snd (Env.get_val_spec_orig id env) with | _ -> funcl_typ in
          let state_arg = match unaux_typ typ with
            | Typ_fn (_, _, eff) when effectful_effs eff -> [string "Regstate z"]
            | _ -> []
          in
          let formals =
            (* TODO Map constraints to provisos *)
            match unaux_pat (fst (untyp_pat pat)), unaux_typ typ with
            | P_tup ps, Typ_fn (Typ_aux (Typ_tup ts, _), _, _) ->
               let doc p t =
                 match fst (untyp_pat p) with
                 | P_aux (P_id id, _) when Env.lookup_id id env = Unbound ->
                    doc_typ t ^^ space ^^ doc_id false id
                 | _ ->
                    raise (Reporting_basic.err_unreachable l __POS__ "Unsupported function parameter")
               in
               List.map2 doc ps ts
            | P_id id, Typ_fn (t, _, _) when Env.lookup_id id env = Unbound ->
               [doc_typ t ^^ space ^^ doc_id false id]
            | _, Typ_fn (t, _, _) when is_unit_typ t ->
               []
            | _ -> raise (Reporting_basic.err_unreachable l __POS__ "Unsupported function parameters")
          in
          let formals_list = parens (separate comma_sp (state_arg @ formals)) in
          let ret_typ =
            match unaux_typ typ with
            | Typ_fn (_, tret, eff) ->
               if has_mem_eff eff then string "RStmt#" ^^ parens (doc_typ tret)
               else if effectful_effs eff then
                 if is_unit_typ tret
                 then string "Action"
                 else string "ActionValue#" ^^ parens (doc_typ tret)
               else doc_typ tret
            | _ -> raise (Reporting_basic.err_unreachable l __POS__ "Unsupported function type")
          in
          surround 2 1
            (separate space [string "function"; ret_typ; doc_id false id; formals_list] ^^ semi)
            (doc_exp true exp)
            (string "endfunction")
       | _ -> raise (Reporting_basic.err_unreachable l __POS__ "Unsupported function clause")
     end
  | _ -> raise (Reporting_basic.err_unreachable l __POS__ "Multiple function clauses should have been merged")

let doc_typdef (TD_aux (td, _)) =
  let doc_kopt k_id =
    if is_nat_kopt k_id then [string ("numeric type " ^ bsv_kid (kopt_kid k_id))]
    else if is_typ_kopt k_id then [string ("type " ^ bsv_kid (kopt_kid k_id))]
    else []
  in
  let doc_tq tq =
    if quant_items tq = [] then empty
    else begin
      let qis = quant_kopts tq |> List.map doc_kopt |> List.concat |> separate comma_sp in
      string "#" ^^ parens qis
    end
  in
  let builtins = ["option"] in
  match td with
  | TD_abbrev (id, _, TypSchm_aux (TypSchm_ts (tq, typ), _))
    when not (List.mem (string_of_id id) builtins) ->
     separate space [string "typedef"; doc_typ typ; doc_typ_id id ^^ doc_tq tq] ^^ semi
  | TD_record (id, _, tq, fields, _)
    when not (List.mem (string_of_id id) builtins) ->
     let doc_field (typ, id) = doc_typ typ ^^ space ^^ doc_id false id ^^ semi in
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
       (string "} " ^^ doc_typ_id id ^^ doc_tq tq) ^^ semi
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
  separate_map hardline doc_def typdefs ^^ hardline ^^
  separate_map hardline doc_def defs ^^ hardline

let pp_defs out defs = ToChannel.pretty 1. 80 out (doc_defs defs)
