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

(* XXX this is copy-pasted from pretty_printer.ml with the following
 * changes:
 * - open Interp_ast instead of Ast; don't open Type_internals
 * - string_of_big_int instead of string_of_int
 * - annot does not contain type annotations anymore, so E_internal_cast
 *   is ignored
 * - don't print E_typ either by default (controlled by ignore_casts)
 * - special case for holes in doc_id
 * - pp_exp returns a string instead of working on a buffer (should
 *   change this in the original as well, probably)
 * - pp_defs deleted
 * - the pretty-printer does not support DeIid; here, we add a
 *   work-around to make it work, converting back to Id with parens,
 *   because the stack/continuation contains operators in DeIid form.
 *   Should maybe backport this one to the original p-p.
 *)

open Interp_ast
open Format
open Nat_big_num

let ignore_casts = ref true

let zero_big = of_int 0
let one_big = of_int 1

let pp_format_id (Id_aux (i, _)) = match i with Id i -> i | DeIid x -> "(deinfix " ^ x ^ ")"

let lit_to_string = function
  | L_unit -> "unit"
  | L_zero -> "0b0"
  | L_one -> "0b1"
  | L_true -> "true"
  | L_false -> "false"
  | L_num n -> Nat_big_num.to_string n
  | L_hex s -> "0x" ^ s
  | L_bin s -> "0b" ^ s
  | L_undef -> "undefined"
  | L_string s -> "\"" ^ s ^ "\""

let id_to_string = function Id_aux (Id s, _) | Id_aux (DeIid s, _) -> s

let rec loc_to_string = function
  | Unknown -> "location unknown"
  | Int (s, _) -> s
  | Generated l -> "Generated near " ^ loc_to_string l
  | Range (s, fline, fchar, tline, tchar) ->
      if fline = tline then sprintf "%s:%d:%d" s fline fchar else sprintf "%s:%d:%d-%d:%d" s fline fchar tline tchar

let collapse_leading s =
  if String.length s <= 8 then s
  else (
    let first_bit = s.[0] in
    let templ = sprintf "%c...%c" first_bit first_bit in

    let rec find_first_diff str cha pos =
      if pos >= String.length str then None else if str.[pos] != cha then Some pos else find_first_diff str cha (pos + 1)
    in

    match find_first_diff s first_bit 0 with
    | None -> templ
    | Some pos when pos > 4 -> templ ^ String.sub s pos (String.length s - pos)
    | _ -> s
  )

(* pp the bytes of a Bytevector as a hex value *)

let bitvec_to_string l =
  "0b"
  ^ collapse_leading
      (String.concat ""
         (List.map
            (function
              | Interp_ast.V_lit (L_aux (L_zero, _)) -> "0"
              | Interp_ast.V_lit (L_aux (L_one, _)) -> "1"
              | Interp_ast.V_lit (L_aux (L_undef, _)) -> "u"
              | Interp_ast.V_unknown -> "?"
              | v ->
                  Printf.printf "bitvec found a non bit %s%!\n" (Interp.string_of_value v);
                  assert false
              )
            (List.map Interp.detaint l)
         )
      )

(****************************************************************************
 * PPrint-based source-to-source pretty printer
****************************************************************************)

open PPrint

let doc_id (Id_aux (i, _)) =
  match i with
  | Id "0" -> string "\x1b[1;31m[_]\x1b[m" (* internal representation of a hole *)
  | Id i -> string i
  | DeIid x ->
      (* add an extra space through empty to avoid a closing-comment
       * token in case of x ending with star. *)
      parens (separate space [string "deinfix"; string x; empty])

let doc_var (Kid_aux (Var v, _)) = string v

let doc_int i = string (to_string i)

let doc_bkind (BK_aux (k, _)) = string (match k with BK_type -> "Type" | BK_int -> "Int" | BK_order -> "Order")

let doc_op symb a b = infix 2 1 symb a b
let doc_unop symb a = prefix 2 1 symb a

let arrow = string "->"
let dotdot = string ".."
let coloneq = string ":="
let lsquarebar = string "[|"
let rsquarebar = string "|]"
let squarebars = enclose lsquarebar rsquarebar
let lsquarebarbar = string "[||"
let rsquarebarbar = string "||]"
let squarebarbars = enclose lsquarebarbar rsquarebarbar
let spaces op = enclose space space op
let semi_sp = semi ^^ space
let comma_sp = comma ^^ space
let colon_sp = spaces colon

let doc_kind (K_aux (K_kind klst, _)) = separate_map (spaces arrow) doc_bkind klst

let doc_effect (BE_aux (e, _)) =
  string
    ( match e with
    | BE_rreg -> "rreg"
    | BE_wreg -> "wreg"
    | BE_rmem -> "rmem"
    | BE_wmem -> "wmem"
    | BE_wmv -> "wmv"
    | BE_eamem -> "eamem"
    | BE_exmem -> "exmem"
    | BE_barr -> "barr"
    | BE_depend -> "depend"
    | BE_undef -> "undef"
    | BE_unspec -> "unspec"
    | BE_escape -> "escape"
    | BE_nondet -> "nondet"
    | BE_lset -> "(*lset*)"
    | BE_lret -> "(*lret*)"
    )

let doc_effects (Effect_aux (e, _)) =
  match e with
  | Effect_var v -> doc_var v
  | Effect_set [] -> string "pure"
  | Effect_set s -> braces (separate_map comma_sp doc_effect s)

let doc_ord (Ord_aux (o, _)) = match o with Ord_var v -> doc_var v | Ord_inc -> string "inc" | Ord_dec -> string "dec"

let doc_typ, doc_atomic_typ, doc_nexp =
  (* following the structure of parser for precedence *)
  let rec typ ty = fn_typ ty
  and fn_typ (Typ_aux (t, _) as ty) =
    match t with
    | Typ_fn (arg, ret, efct) -> separate space [tup_typ arg; arrow; fn_typ ret; string "effect"; doc_effects efct]
    | _ -> tup_typ ty
  and tup_typ (Typ_aux (t, _) as ty) =
    match t with Typ_tuple typs -> parens (separate_map comma_sp app_typ typs) | _ -> app_typ ty
  and app_typ (Typ_aux (t, _) as ty) =
    match t with
    | Typ_app
        ( Id_aux (Id "vector", _),
          [
            Typ_arg_aux (Typ_arg_nexp (Nexp_aux (Nexp_constant n, _)), _);
            Typ_arg_aux (Typ_arg_nexp (Nexp_aux (Nexp_constant m, _)), _);
            Typ_arg_aux (Typ_arg_order (Ord_aux (Ord_inc, _)), _);
            Typ_arg_aux (Typ_arg_typ (Typ_aux (Typ_id id, _)), _);
          ]
        ) ->
        doc_id id
        ^^ brackets (if equal n zero_big then doc_int m else doc_op colon (doc_int n) (doc_int (add n (sub m one_big))))
    | Typ_app
        ( Id_aux (Id "range", _),
          [Typ_arg_aux (Typ_arg_nexp (Nexp_aux (Nexp_constant n, _)), _); Typ_arg_aux (Typ_arg_nexp m, _)]
        ) ->
        squarebars (if equal n zero_big then nexp m else doc_op colon (doc_int n) (nexp m))
    | Typ_app (id, args) ->
        (* trailing space to avoid >> token in case of nested app types *)
        doc_id id ^^ angles (separate_map comma_sp doc_typ_arg args) ^^ space
    | _ -> atomic_typ ty
  and atomic_typ (Typ_aux (t, _) as ty) =
    match t with
    | Typ_id id -> doc_id id
    | Typ_var v -> doc_var v
    | Typ_app _ | Typ_tuple _ | Typ_fn _ ->
        (* exhaustiveness matters here to avoid infinite loops
         * if we add a new Typ constructor *)
        group (parens (typ ty))
  and doc_typ_arg (Typ_arg_aux (t, _)) =
    match t with
    (* Be careful here because typ_arg is implemented as nexp in the
     * parser - in practice falling through app_typ after all the proper nexp
     * cases; so Typ_arg_typ has the same precedence as a Typ_app *)
    | Typ_arg_typ t -> app_typ t
    | Typ_arg_nexp n -> nexp n
    | Typ_arg_order o -> doc_ord o
  (* same trick to handle precedence of nexp *)
  and nexp ne = sum_typ ne
  and sum_typ (Nexp_aux (n, _) as ne) =
    match n with
    | Nexp_sum (n1, n2) -> doc_op plus (sum_typ n1) (star_typ n2)
    | Nexp_minus (n1, n2) -> doc_op minus (sum_typ n1) (star_typ n2)
    | _ -> star_typ ne
  and star_typ (Nexp_aux (n, _) as ne) =
    match n with Nexp_times (n1, n2) -> doc_op star (star_typ n1) (exp_typ n2) | _ -> exp_typ ne
  and exp_typ (Nexp_aux (n, _) as ne) =
    match n with Nexp_exp n1 -> doc_unop (string "2**") (atomic_nexp_typ n1) | _ -> neg_typ ne
  and neg_typ (Nexp_aux (n, _) as ne) =
    match n with
    | Nexp_neg n1 ->
        (* XXX this is not valid Sail, only an internal representation -
         * work around by commenting it *)
        let minus = concat [string "(*"; minus; string "*)"] in
        minus ^^ atomic_nexp_typ n1
    | _ -> atomic_nexp_typ ne
  and atomic_nexp_typ (Nexp_aux (n, _) as ne) =
    match n with
    | Nexp_id id -> doc_id id
    | Nexp_var v -> doc_var v
    | Nexp_constant i -> doc_int i
    | Nexp_neg _ | Nexp_exp _ | Nexp_times _ | Nexp_sum _ | Nexp_minus _ -> group (parens (nexp ne))
    (* expose doc_typ, doc_atomic_typ and doc_nexp *)
  in

  (typ, atomic_typ, nexp)

let doc_nexp_constraint (NC_aux (nc, _)) =
  match nc with
  | NC_equal (n1, n2) -> doc_op equals (doc_nexp n1) (doc_nexp n2)
  | NC_bounded_ge (n1, n2) -> doc_op (string ">=") (doc_nexp n1) (doc_nexp n2)
  | NC_bounded_le (n1, n2) -> doc_op (string "<=") (doc_nexp n1) (doc_nexp n2)
  | NC_set (v, bounds) -> doc_op (string "IN") (doc_var v) (braces (separate_map comma_sp doc_int bounds))

let doc_qi (QI_aux (qi, _)) =
  match qi with
  | QI_const n_const -> doc_nexp_constraint n_const
  | QI_id (KOpt_aux (ki, _)) -> (
      match ki with KOpt_none v -> doc_var v | KOpt_kind (k, v) -> separate space [doc_kind k; doc_var v]
    )

(* typ_doc is the doc for the type being quantified *)
let doc_typquant (TypQ_aux (tq, _)) typ_doc =
  match tq with
  | TypQ_no_forall -> typ_doc
  | TypQ_tq [] -> failwith "TypQ_tq with empty list"
  | TypQ_tq qlist ->
      (* include trailing break because the caller doesn't know if tq is empty *)
      doc_op dot (separate space [string "forall"; separate_map comma_sp doc_qi qlist]) typ_doc

let doc_typscm (TypSchm_aux (TypSchm_ts (tq, t), _)) = doc_typquant tq (doc_typ t)

let doc_typscm_atomic (TypSchm_aux (TypSchm_ts (tq, t), _)) = doc_typquant tq (doc_atomic_typ t)

let doc_lit (L_aux (l, _)) =
  utf8string
    ( match l with
    | L_unit -> "()"
    | L_zero -> "bitzero"
    | L_one -> "bitone"
    | L_true -> "true"
    | L_false -> "false"
    | L_num i -> to_string i
    | L_hex n -> "0x" ^ n
    | L_bin n -> "0b" ^ n
    | L_undef -> "undefined"
    | L_string s -> "\"" ^ s ^ "\""
    )

let doc_pat, doc_atomic_pat =
  let rec pat pa = pat_colons pa
  and pat_colons (P_aux (p, l) as pa) =
    match p with P_vector_concat pats -> separate_map colon_sp atomic_pat pats | _ -> app_pat pa
  and app_pat (P_aux (p, l) as pa) =
    match p with
    | P_app (id, (_ :: _ as pats)) -> doc_unop (doc_id id) (parens (separate_map comma_sp atomic_pat pats))
    | _ -> atomic_pat pa
  and atomic_pat (P_aux (p, l) as pa) =
    match p with
    | P_lit lit -> doc_lit lit
    | P_wild -> underscore
    | P_id id -> doc_id id
    | P_as (p, id) -> parens (separate space [pat p; string "as"; doc_id id])
    | P_typ (typ, p) -> separate space [parens (doc_typ typ); atomic_pat p]
    | P_app (id, []) -> doc_id id
    | P_record (fpats, _) -> braces (separate_map semi_sp fpat fpats)
    | P_vector pats -> brackets (separate_map comma_sp atomic_pat pats)
    | P_tuple pats -> parens (separate_map comma_sp atomic_pat pats)
    | P_list pats -> squarebarbars (separate_map semi_sp atomic_pat pats)
    | P_app (_, _ :: _) | P_vector_concat _ -> group (parens (pat pa))
  and fpat (FP_aux (FP_Fpat (id, fpat), _)) = doc_op equals (doc_id id) (pat fpat)
  and npat (i, p) = doc_op equals (doc_int i) (pat p) (* expose doc_pat and doc_atomic_pat *) in

  (pat, atomic_pat)

let doc_exp, doc_let =
  let rec exp env mem add_red show_hole_contents e = group (or_exp env mem add_red show_hole_contents e)
  and or_exp env mem add_red show_hole_contents (E_aux (e, _) as expr) =
    match e with
    | E_app_infix (l, (Id_aux (Id ("|" | "||"), _) as op), r) ->
        doc_op (doc_id op) (and_exp env mem add_red show_hole_contents l) (or_exp env mem add_red show_hole_contents r)
    | _ -> and_exp env mem add_red show_hole_contents expr
  and and_exp env mem add_red show_hole_contents (E_aux (e, _) as expr) =
    match e with
    | E_app_infix (l, (Id_aux (Id ("&" | "&&"), _) as op), r) ->
        doc_op (doc_id op) (eq_exp env mem add_red show_hole_contents l) (and_exp env mem add_red show_hole_contents r)
    | _ -> eq_exp env mem add_red show_hole_contents expr
  and eq_exp env mem add_red show_hole_contents (E_aux (e, _) as expr) =
    match e with
    | E_app_infix
        ( l,
          ( Id_aux
              ( Id
                  (* XXX this is not very consistent - is the parser bogus here? *)
                  ( "=" | "==" | "!=" | ">=" | ">=_s" | ">=_u" | ">" | ">_s" | ">_u" | "<=" | "<=_s" | "<" | "<_s"
                  | "<_si" | "<_u" ),
                _
              ) as op
          ),
          r
        ) ->
        doc_op (doc_id op) (eq_exp env mem add_red show_hole_contents l) (at_exp env mem add_red show_hole_contents r)
    (* XXX assignment should not have the same precedence as equal etc. *)
    | E_assign (le, exp) ->
        doc_op coloneq (doc_lexp env mem add_red show_hole_contents le) (at_exp env mem add_red show_hole_contents exp)
    | _ -> at_exp env mem add_red show_hole_contents expr
  and at_exp env mem add_red show_hole_contents (E_aux (e, _) as expr) =
    match e with
    | E_app_infix (l, (Id_aux (Id ("@" | "^^" | "^" | "~^"), _) as op), r) ->
        doc_op (doc_id op) (cons_exp env mem add_red show_hole_contents l) (at_exp env mem add_red show_hole_contents r)
    | _ -> cons_exp env mem add_red show_hole_contents expr
  and cons_exp env mem add_red show_hole_contents (E_aux (e, _) as expr) =
    match e with
    | E_vector_append (l, r) ->
        doc_op colon (shift_exp env mem add_red show_hole_contents l) (cons_exp env mem add_red show_hole_contents r)
    | E_cons (l, r) ->
        doc_op colon (shift_exp env mem add_red show_hole_contents l) (cons_exp env mem add_red show_hole_contents r)
    | _ -> shift_exp env mem add_red show_hole_contents expr
  and shift_exp env mem add_red show_hole_contents (E_aux (e, _) as expr) =
    match e with
    | E_app_infix (l, (Id_aux (Id (">>" | ">>>" | "<<" | "<<<"), _) as op), r) ->
        doc_op (doc_id op)
          (shift_exp env mem add_red show_hole_contents l)
          (plus_exp env mem add_red show_hole_contents r)
    | _ -> plus_exp env mem add_red show_hole_contents expr
  and plus_exp env mem add_red show_hole_contents (E_aux (e, _) as expr) =
    match e with
    | E_app_infix (l, (Id_aux (Id ("+" | "-" | "+_s" | "-_s"), _) as op), r) ->
        doc_op (doc_id op)
          (plus_exp env mem add_red show_hole_contents l)
          (star_exp env mem add_red show_hole_contents r)
    | _ -> star_exp env mem add_red show_hole_contents expr
  and star_exp env mem add_red show_hole_contents (E_aux (e, _) as expr) =
    match e with
    | E_app_infix
        ( l,
          ( Id_aux
              (Id ("*" | "/" | "div" | "quot" | "rem" | "mod" | "quot_s" | "mod_s" | "*_s" | "*_si" | "*_u" | "*_ui"), _)
            as op
          ),
          r
        ) ->
        doc_op (doc_id op)
          (star_exp env mem add_red show_hole_contents l)
          (starstar_exp env mem add_red show_hole_contents r)
    | _ -> starstar_exp env mem add_red show_hole_contents expr
  and starstar_exp env mem add_red show_hole_contents (E_aux (e, _) as expr) =
    match e with
    | E_app_infix (l, (Id_aux (Id "**", _) as op), r) ->
        doc_op (doc_id op)
          (starstar_exp env mem add_red show_hole_contents l)
          (app_exp env mem add_red show_hole_contents r)
    | E_if _ | E_for _ | E_let _ -> right_atomic_exp env mem add_red show_hole_contents expr
    | _ -> app_exp env mem add_red show_hole_contents expr
  and right_atomic_exp env mem add_red show_hole_contents (E_aux (e, _) as expr) =
    match e with
    (* Special case: omit "else ()" when the else branch is empty. *)
    | E_if (c, t, E_aux (E_block [], _)) ->
        string "if" ^^ space
        ^^ group (exp env mem add_red show_hole_contents c)
        ^/^ string "then" ^^ space
        ^^ group (exp env mem add_red show_hole_contents t)
    | E_if (c, t, e) ->
        string "if" ^^ space
        ^^ group (exp env mem add_red show_hole_contents c)
        ^/^ string "then" ^^ space
        ^^ group (exp env mem add_red show_hole_contents t)
        ^/^ string "else" ^^ space
        ^^ group (exp env mem add_red show_hole_contents e)
    | E_for (id, exp1, exp2, exp3, order, exp4) ->
        string "foreach" ^^ space
        ^^ group
             (parens
                (separate (break 1)
                   [
                     doc_id id;
                     string "from " ^^ atomic_exp env mem add_red show_hole_contents exp1;
                     string "to " ^^ atomic_exp env mem add_red show_hole_contents exp2;
                     string "by " ^^ atomic_exp env mem add_red show_hole_contents exp3;
                     string "in " ^^ doc_ord order;
                   ]
                )
             )
        ^/^ exp env mem add_red show_hole_contents exp4
    | E_let (leb, e) ->
        doc_op (string "in") (let_exp env mem add_red show_hole_contents leb) (exp env mem add_red show_hole_contents e)
    | _ -> group (parens (exp env mem add_red show_hole_contents expr))
  and app_exp env mem add_red show_hole_contents (E_aux (e, _) as expr) =
    match e with
    | E_app (f, args) -> doc_unop (doc_id f) (parens (separate_map comma (exp env mem add_red show_hole_contents) args))
    | _ -> vaccess_exp env mem add_red show_hole_contents expr
  and vaccess_exp env mem add_red show_hole_contents (E_aux (e, _) as expr) =
    match e with
    | E_vector_access (v, e) ->
        atomic_exp env mem add_red show_hole_contents v ^^ brackets (exp env mem add_red show_hole_contents e)
    | E_vector_subrange (v, e1, e2) ->
        atomic_exp env mem add_red show_hole_contents v
        ^^ brackets
             (doc_op dotdot (exp env mem add_red show_hole_contents e1) (exp env mem add_red show_hole_contents e2))
    | _ -> field_exp env mem add_red show_hole_contents expr
  and field_exp env mem add_red show_hole_contents (E_aux (e, _) as expr) =
    match e with
    | E_field (fexp, id) -> atomic_exp env mem add_red show_hole_contents fexp ^^ dot ^^ doc_id id
    | _ -> atomic_exp env mem add_red show_hole_contents expr
  and atomic_exp env mem add_red (show_hole_contents : bool) (E_aux (e, annot) as expr) =
    match e with
    (* Special case: an empty block is equivalent to unit, but { } is a syntactic struct *)
    | E_block [] -> string "()"
    | E_block exps ->
        let exps_doc = separate_map (semi ^^ hardline) (exp env mem add_red show_hole_contents) exps in
        surround 2 1 lbrace exps_doc rbrace
    | E_nondet exps ->
        let exps_doc = separate_map (semi ^^ hardline) (exp env mem add_red show_hole_contents) exps in
        string "nondet" ^^ space ^^ surround 2 1 lbrace exps_doc rbrace
    | E_id id -> (
        match id with
        | Id_aux (Id "0", _) -> (
            match Interp.in_lenv env id with
            | Interp_ast.V_unknown -> string (add_red "[_]")
            | v -> if show_hole_contents then string (add_red (Interp.string_of_value v)) else string (add_red "[_]")
          )
        | _ -> doc_id id
      )
    | E_lit lit -> doc_lit lit
    | E_typ (typ, e) ->
        if !ignore_casts then atomic_exp env mem add_red show_hole_contents e
        else prefix 2 1 (parens (doc_typ typ)) (group (atomic_exp env mem add_red show_hole_contents e))
    | E_internal_cast (_, e) ->
        (* XXX ignore internal casts in the interpreter *)
        atomic_exp env mem add_red show_hole_contents e
    | E_tuple exps -> parens (separate_map comma (exp env mem add_red show_hole_contents) exps)
    | E_struct (FES_aux (FES_fexps (fexps, _), _)) ->
        braces (separate_map semi_sp (doc_fexp env mem add_red show_hole_contents) fexps)
    | E_struct_update (e, FES_aux (FES_fexps (fexps, _), _)) ->
        braces
          (doc_op (string "with")
             (exp env mem add_red show_hole_contents e)
             (separate_map semi_sp (doc_fexp env mem add_red show_hole_contents) fexps)
          )
    | E_vector exps -> (
        let default_print _ = brackets (separate_map comma (exp env mem add_red show_hole_contents) exps) in
        match exps with
        | [] -> default_print ()
        | es ->
            if
              List.for_all
                (fun e -> match e with E_aux (E_lit (L_aux ((L_one | L_zero | L_undef), _)), _) -> true | _ -> false)
                es
            then
              utf8string
                ("0b"
                ^ List.fold_right
                    (fun (E_aux (e, _)) rst ->
                      match e with
                      | E_lit (L_aux (l, _)) -> (
                          match l with
                          | L_one -> "1" ^ rst
                          | L_zero -> "0" ^ rst
                          | L_undef -> "u" ^ rst
                          | _ -> failwith "bit vector not just bit values"
                        )
                      | _ -> failwith "bit vector not all lits"
                    )
                    exps ""
                )
            else default_print ()
      )
    | E_vector_update (v, e1, e2) ->
        brackets
          (doc_op (string "with")
             (exp env mem add_red show_hole_contents v)
             (doc_op equals
                (atomic_exp env mem add_red show_hole_contents e1)
                (exp env mem add_red show_hole_contents e2)
             )
          )
    | E_vector_update_subrange (v, e1, e2, e3) ->
        brackets
          (doc_op (string "with")
             (exp env mem add_red show_hole_contents v)
             (doc_op equals
                (atomic_exp env mem add_red show_hole_contents e1
                ^^ colon
                ^^ atomic_exp env mem add_red show_hole_contents e2
                )
                (exp env mem add_red show_hole_contents e3)
             )
          )
    | E_list exps -> squarebarbars (separate_map comma (exp env mem add_red show_hole_contents) exps)
    | E_match (e, pexps) ->
        let opening = separate space [string "switch"; exp env mem add_red show_hole_contents e; lbrace] in
        let cases = separate_map (break 1) (doc_case env mem add_red show_hole_contents) pexps in
        surround 2 1 opening cases rbrace
    | E_exit e -> separate space [string "exit"; exp env mem add_red show_hole_contents e]
    | E_return e -> separate space [string "return"; exp env mem add_red show_hole_contents e]
    | E_assert (e, msg) ->
        string "assert" ^^ parens (separate_map comma (exp env mem add_red show_hole_contents) [e; msg])
    (* adding parens and loop for lower precedence *)
    | E_app (_, _)
    | E_vector_access (_, _)
    | E_vector_subrange (_, _, _)
    | E_cons (_, _)
    | E_field (_, _)
    | E_assign (_, _)
    | E_if _ | E_for _ | E_let _ | E_vector_append _
    | E_app_infix
        ( _,
          (* for every app_infix operator caught at a higher precedence,
           * we need to wrap around with parens *)
          Id_aux
            ( Id
                ( "|" | "||" | "&" | "&&" | "=" | "==" | "!=" | ">=" | ">=_s" | ">=_u" | ">" | ">_s" | ">_u" | "<="
                | "<=_s" | "<" | "<_s" | "<_si" | "<_u" | "@" | "^^" | "^" | "~^" | ">>" | ">>>" | "<<" | "<<<" | "+"
                | "+_s" | "-" | "-_s" | "*" | "/" | "div" | "quot" | "quot_s" | "rem" | "mod" | "mod_s" | "*_s" | "*_si"
                | "*_u" | "*_ui" | "**" ),
              _
            ),
          _
        ) ->
        group (parens (exp env mem add_red show_hole_contents expr))
    (* XXX fixup deinfix into infix ones *)
    | E_app_infix (l, Id_aux (DeIid op, annot'), r) ->
        group
          (parens (exp env mem add_red show_hole_contents (E_aux (E_app_infix (l, Id_aux (Id op, annot'), r), annot))))
    (* XXX default precedence for app_infix? *)
    | E_app_infix (l, op, r) -> failwith ("unexpected app_infix operator " ^ pp_format_id op)
    (* doc_op (doc_id op) (exp l) (exp r) *)
    (* XXX missing case *)
    | E_comment _ | E_comment_struc _ -> string ""
    | E_internal_value v -> string (Interp.string_of_value v)
    | _ -> failwith "internal expression escaped"
  and let_exp env mem add_red show_hole_contents (LB_aux (lb, _)) =
    match lb with
    | LB_val (pat, e) ->
        prefix 2 1 (separate space [string "let"; doc_atomic_pat pat; equals]) (exp env mem add_red show_hole_contents e)
  and doc_fexp env mem add_red show_hole_contents (FE_aux (FE_fexp (id, e), _)) =
    doc_op equals (doc_id id) (exp env mem add_red show_hole_contents e)
  and doc_case env mem add_red show_hole_contents (Pat_aux (Pat_exp (pat, e), _)) =
    doc_op arrow (separate space [string "case"; doc_atomic_pat pat]) (group (exp env mem add_red show_hole_contents e))
  (* lexps are parsed as eq_exp - we need to duplicate the precedence
   * structure for them *)
  and doc_lexp env mem add_red show_hole_contents le = app_lexp env mem add_red show_hole_contents le
  and app_lexp env mem add_red show_hole_contents (LE_aux (lexp, _) as le) =
    match lexp with
    | LE_app (id, args) -> doc_id id ^^ parens (separate_map comma (exp env mem add_red show_hole_contents) args)
    | _ -> vaccess_lexp env mem add_red show_hole_contents le
  and vaccess_lexp env mem add_red show_hole_contents (LE_aux (lexp, _) as le) =
    match lexp with
    | LE_vector (v, e) ->
        atomic_lexp env mem add_red show_hole_contents v ^^ brackets (exp env mem add_red show_hole_contents e)
    | LE_vector_range (v, e1, e2) ->
        atomic_lexp env mem add_red show_hole_contents v
        ^^ brackets (exp env mem add_red show_hole_contents e1 ^^ dotdot ^^ exp env mem add_red show_hole_contents e2)
    | _ -> field_lexp env mem add_red show_hole_contents le
  and field_lexp env mem add_red show_hole_contents (LE_aux (lexp, _) as le) =
    match lexp with
    | LE_field (v, id) -> atomic_lexp env mem add_red show_hole_contents v ^^ dot ^^ doc_id id
    | _ -> atomic_lexp env mem add_red show_hole_contents le
  and atomic_lexp env mem add_red show_hole_contents (LE_aux (lexp, _) as le) =
    match lexp with
    | LE_id id -> doc_id id
    | LE_typ (typ, id) -> prefix 2 1 (parens (doc_typ typ)) (doc_id id)
    | LE_tuple lexps -> group (parens (separate_map comma (doc_lexp env mem add_red show_hole_contents) lexps))
    | LE_app _ | LE_vector _ | LE_vector_range _ | LE_field _ ->
        group (parens (doc_lexp env mem add_red show_hole_contents le))
    (* expose doc_exp and doc_let *)
  in

  (exp, let_exp)

let doc_default (DT_aux (df, _)) =
  match df with
  | DT_kind (bk, v) -> separate space [string "default"; doc_bkind bk; doc_var v]
  | DT_typ (ts, id) -> separate space [string "default"; doc_typscm ts; doc_id id]
  | DT_order o -> separate space [string "default"; string "Order"; doc_ord o]

let doc_spec (VS_aux (v, _)) =
  match v with VS_val_spec (ts, id, _, _) -> separate space [string "val"; doc_typscm ts; doc_id id]

let doc_namescm (Name_sect_aux (ns, _)) =
  match ns with
  | Name_sect_none -> empty
  (* include leading space because the caller doesn't know if ns is
   * empty, and trailing break already added by the following equals *)
  | Name_sect_some s -> space ^^ brackets (doc_op equals (string "name") (dquotes (string s)))

let rec doc_range (BF_aux (r, _)) =
  match r with
  | BF_single i -> doc_int i
  | BF_range (i1, i2) -> doc_op dotdot (doc_int i1) (doc_int i2)
  | BF_concat (ir1, ir2) -> doc_range ir1 ^^ comma ^^ doc_range ir2

let doc_type_union (Tu_aux (typ_u, _)) =
  match typ_u with Tu_ty_id (typ, id) -> separate space [doc_typ typ; doc_id id] | Tu_id id -> doc_id id

let doc_typdef (TD_aux (td, _)) =
  match td with
  | TD_abbrev (id, nm, typschm) ->
      doc_op equals (concat [string "typedef"; space; doc_id id; doc_namescm nm]) (doc_typscm typschm)
  | TD_record (id, nm, typq, fs, _) ->
      let f_pp (typ, id) = concat [doc_typ typ; space; doc_id id; semi] in
      let fs_doc = group (separate_map (break 1) f_pp fs) in
      doc_op equals
        (concat [string "typedef"; space; doc_id id; doc_namescm nm])
        (string "const struct" ^^ space ^^ doc_typquant typq (braces fs_doc))
  | TD_variant (id, nm, typq, ar, _) ->
      let ar_doc = group (separate_map (semi ^^ break 1) doc_type_union ar) in
      doc_op equals
        (concat [string "typedef"; space; doc_id id; doc_namescm nm])
        (string "const union" ^^ space ^^ doc_typquant typq (braces ar_doc))
  | TD_enum (id, nm, enums, _) ->
      let enums_doc = group (separate_map (semi ^^ break 1) doc_id enums) in
      doc_op equals
        (concat [string "typedef"; space; doc_id id; doc_namescm nm])
        (string "enumerate" ^^ space ^^ braces enums_doc)
  | TD_register (id, n1, n2, rs) ->
      let doc_rid (r, id) = separate space [doc_range r; colon; doc_id id] ^^ semi in
      let doc_rids = group (separate_map (break 1) doc_rid rs) in
      doc_op equals
        (string "typedef" ^^ space ^^ doc_id id)
        (separate space [string "register bits"; brackets (doc_nexp n1 ^^ colon ^^ doc_nexp n2); braces doc_rids])

let doc_rec (Rec_aux (r, _)) =
  match r with
  | Rec_nonrec -> empty
  (* include trailing space because caller doesn't know if we return
   * empty *)
  | Rec_rec -> string "rec" ^^ space

let doc_tannot_opt (Typ_annot_opt_aux (t, _)) =
  match t with Typ_annot_opt_some (tq, typ) -> doc_typquant tq (doc_typ typ)

let doc_effects_opt (Effect_opt_aux (e, _)) =
  match e with Effect_opt_pure -> string "pure" | Effect_opt_effect e -> doc_effects e

let doc_funcl env mem add_red (FCL_aux (FCL_funcl (id, Pat_aux (Pat_exp (pat, exp), _)), _)) =
  group (doc_op equals (separate space [doc_id id; doc_atomic_pat pat]) (doc_exp env mem add_red false exp))

let doc_fundef env mem add_red (FD_aux (FD_function (r, typa, efa, fcls), _)) =
  match fcls with
  | [] -> failwith "FD_function with empty function list"
  | _ ->
      let sep = hardline ^^ string "and" ^^ space in
      let clauses = separate_map sep (doc_funcl env mem add_red) fcls in
      separate space
        [string "function"; doc_rec r ^^ doc_tannot_opt typa; string "effect"; doc_effects_opt efa; clauses]

let doc_dec (DEC_aux (d, _)) =
  match d with
  | DEC_reg (typ, id) -> separate space [string "register"; doc_atomic_typ typ; doc_id id]
  | _ -> failwith "interpreter printing out declarations unexpectedly"

let doc_scattered env mem add_red (SD_aux (sdef, _)) =
  match sdef with
  | SD_scattered_function (r, typa, efa, id) ->
      separate space
        [string "scattered function"; doc_rec r ^^ doc_tannot_opt typa; string "effect"; doc_effects_opt efa; doc_id id]
  | SD_scattered_variant (id, ns, tq) ->
      doc_op equals (string "scattered typedef" ^^ space ^^ doc_id id ^^ doc_namescm ns) (doc_typquant tq empty)
  | SD_scattered_funcl funcl -> string "function clause" ^^ space ^^ doc_funcl env mem add_red funcl
  | SD_scattered_unioncl (id, tu) -> separate space [string "union"; doc_id id; string "member"; doc_type_union tu]
  | SD_scattered_end id -> string "end" ^^ space ^^ doc_id id

let rec doc_def env mem add_red def =
  group
    ( match def with
    | DEF_default df -> doc_default df
    | DEF_val v_spec -> doc_spec v_spec
    | DEF_type t_def -> doc_typdef t_def
    | DEF_kind k_def -> failwith "interpreter unexpectedly printing kind def"
    | DEF_fundef f_def -> doc_fundef env mem add_red f_def
    | DEF_let lbind -> doc_let env mem add_red false lbind
    | DEF_register dec -> doc_dec dec
    | DEF_scattered sdef -> doc_scattered env mem add_red sdef
    | DEF_comm comm_dec -> string "(*" ^^ doc_comm_dec env mem add_red comm_dec ^^ string "*)"
    )
  ^^ hardline

and doc_comm_dec env mem add_red dec =
  match dec with DC_comm s -> string s | DC_comm_struct d -> doc_def env mem add_red d

let doc_defs env mem add_red (Defs defs) = separate_map hardline (doc_def env mem add_red) defs

let print ?(len = 80) channel doc = ToChannel.pretty 1. len channel doc
let to_buf ?(len = 80) buf doc = ToBuffer.pretty 1. len buf doc

let pp_exp env mem add_red show_hole_contents e =
  let b = Buffer.create 20 in
  to_buf b (doc_exp env mem add_red show_hole_contents e);
  Buffer.contents b
