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
      (idx > 0 || not (is_num_char c || if cap then is_lower c else is_upper c)) &&
      valid_from (idx + 1)
    else true
  in
  (if valid_from 0 then id else Util.zencode_string id)
  |> if cap then String.capitalize else String.uncapitalize

let doc_id cap (Id_aux (i, _)) =
  match i with
  | Id i -> string (bsv_id cap i)
  | DeIid x -> string (bsv_id cap ("op " ^ x))

let doc_typ_id id =
  match string_of_id id with
  | "bit" -> string "bit"
  | "bool" -> string "Bool"
  | "option" -> string "Maybe"
  | "unit" -> string "void"
  | "string" -> string "String"
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

let has_mem_eff  (Effect_aux (Effect_set effs, _)) =
  let mem_eff (BE_aux (be, _)) = match be with
    | BE_rmem | BE_rmemt | BE_wmem | BE_eamem | BE_exmem
    | BE_wmv | BE_wmvt | BE_barr -> true
    | _ -> false
  in
  List.exists mem_eff effs
let effectful_effs (Effect_aux (Effect_set effs, _)) = not (effs = [])
let effectful exp = effectful_effs (effect_of exp)
let effectful_pexp pexp = effectful_effs (effect_of_pexp pexp)
let is_enum id env = match Env.lookup_id id env with
  | Enum _ -> true
  | _ -> false

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
  | Typ_var var -> doc_id false (id_of_kid var)
  | Typ_app (id, args) ->
     if is_vector_typ typ then
       let len, ord, etyp = vector_typ_args_of typ in
       if is_bit_typ etyp then string "Bit#" ^^ parens (Pretty_print_sail.doc_nexp len)
       else string "List#" ^^ parens (doc_typ etyp)
     else
       doc_typ_id id ^^ string "#" ^^ parens (separate_map comma_sp doc_typ_arg args)
  | _ -> raise (Reporting_basic.err_todo l ("Unprintable type " ^ string_of_typ typ))
and doc_typ_arg (Typ_arg_aux (targ, l)) = match targ with
  | Typ_arg_nexp nexp -> Pretty_print_sail.doc_nexp nexp
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

let rec doc_exp stmt (E_aux (eaux, (l, annot)) as exp) =
  match eaux with
  | E_block es ->
     enclose_block annot (separate_map (semi ^^ break 1) (doc_exp true) es)
  | E_id id -> doc_id (is_enum id (env_of exp)) id
  | E_lit lit -> doc_lit lit
  | E_cast (t, e) -> separate space [doc_typ t; string "\'"; parens (doc_exp stmt e)]
  | E_app (id, es) ->
     let union = Env.is_union_constructor id (env_of exp) in
     let args =
       match es with
       | [] -> []
       | [e] when is_unit_typ (typ_of e) -> []
       | es ->
          if union then [parens (doc_exp false (E_aux (E_tuple es, (l, empty_tannot))))]
          else [parens (separate_map comma_sp (doc_exp false) es)]
     in
     if union then
       separate space (string "tagged" :: doc_constr_id id :: args)
     else
       concat (doc_id false id :: args)
  | E_tuple [] -> string "?"
  | E_tuple [e] -> doc_exp stmt e
  | E_tuple es ->
     string ("tuple" ^ string_of_int (List.length es)) ^^ space ^^
     parens (separate_map comma_sp (doc_exp false) es)
  | E_if (i, t, e) ->
     if stmt then
       prefix 0 1
         (prefix 2 1 (string "if " ^^ parens (doc_exp false i)) (doc_exp true t))
         (prefix 2 1 (string "else") (doc_exp true t))
     else
       separate space [doc_exp false i; string "?"; doc_exp false t; string ":"; doc_exp false e]
  | E_vector es when is_bitvector_typ (typ_of exp) ->
     braces (separate_map comma_sp (doc_exp false) es)
  | E_list es -> braces (separate_map comma_sp (doc_exp false) es)
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
  | E_assert (E_aux (E_constraint nc, _), msg) ->
     string "staticAssert" ^^ parens (separate comma_sp [Pretty_print_sail.doc_nc nc; doc_exp false msg])
  | E_assert (c, msg) ->
     string "dynamicAssert" ^^ parens (separate comma_sp [doc_exp false c; doc_exp false msg])
  (* TODO *)
  | _ -> Pretty_print_sail.doc_exp exp
and doc_pat (P_aux (p_aux, (l, annot)) as pat) =
  match p_aux with
  | P_lit lit -> doc_lit lit
  | P_wild -> string ".*"
  | P_id id ->
     let enum = is_enum id (pat_env_of pat) in
     (if enum then empty else string ".") ^^ doc_id enum id
  | P_app (id, ps) ->
     let union = Env.is_union_constructor id (pat_env_of pat) in
     (if union then string "tagged " else empty) ^^
     doc_id union id ^^ parens (separate_map comma_sp doc_pat ps)
  | P_tup ps -> braces (separate_map comma_sp doc_pat ps)
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

let doc_fundef (FD_aux (FD_function (r, typa, efa, funcls), (l, _))) =
  match funcls with
  | [] -> failwith "Empty function clause list"
  | [FCL_aux (FCL_Funcl (id, Pat_aux (pexp, _)), (l, annot)) as funcl] ->
     begin
       match pexp, destruct_tannot annot with
       | Pat_exp (pat, exp), Some (env, funcl_typ, _) ->
          let typ = try snd (Env.get_val_spec_orig id env) with | _ -> funcl_typ in
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
               parens (separate comma_sp (List.map2 doc ps ts))
            | P_id id, Typ_fn (t, _, _) when Env.lookup_id id env = Unbound ->
               parens (doc_typ t ^^ space ^^ doc_id false id)
            | _, Typ_fn (t, _, _) when is_unit_typ t ->
               string "()"
            | _ -> raise (Reporting_basic.err_unreachable l __POS__ "Unsupported function parameters")
          in
          let ret_typ =
            match unaux_typ typ with
            | Typ_fn (_, tret, eff) ->
               if effectful_effs eff then
                 if is_unit_typ tret
                 then string "Action"
                 else string "ActionValue#" ^^ parens (doc_typ tret)
               else doc_typ tret
            | _ -> raise (Reporting_basic.err_unreachable l __POS__ "Unsupported function type")
          in
          surround 2 1
            (separate space [string "function"; ret_typ; doc_id false id; formals] ^^ semi)
            (doc_exp true exp)
            (string "endfunction")
       | _ -> raise (Reporting_basic.err_unreachable l __POS__ "Unsupported function clause")
     end
  | _ -> raise (Reporting_basic.err_unreachable l __POS__ "Multiple function clauses should have been merged")

let doc_def = function
  | DEF_fundef fd -> doc_fundef fd
  | _ -> empty

let doc_defs (Defs defs) = separate_map hardline doc_def defs ^^ hardline

let pp_defs out defs = ToChannel.pretty 1. 80 out (doc_defs defs)
