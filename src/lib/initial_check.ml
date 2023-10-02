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
open Util
open Printf
module Big_int = Nat_big_num

module P = Parse_ast

(* See mli file for details on what these flags do *)
let opt_undefined_gen = ref false
let opt_fast_undefined = ref false
let opt_magic_hash = ref false

module StringSet = Set.Make (String)
module StringMap = Map.Make (String)

(* These are types that are defined in Sail, but we rely on them
   having specific definitions, so we only allow them to be defined in
   $sail_internal marked files in the prelude. *)
let reserved_type_ids = IdSet.of_list [mk_id "result"; mk_id "option"]

type type_constructor = kind_aux option list

type ctx = {
  kinds : kind_aux KBindings.t;
  type_constructors : type_constructor Bindings.t;
  scattereds : (P.typquant * ctx) Bindings.t;
  fixities : (prec * int) Bindings.t;
  internal_files : StringSet.t;
  target_sets : string list StringMap.t;
}

let rec equal_ctx ctx1 ctx2 =
  KBindings.equal ( = ) ctx1.kinds ctx2.kinds
  && Bindings.equal ( = ) ctx1.type_constructors ctx2.type_constructors
  && Bindings.equal
       (fun (typq1, ctx1) (typq2, ctx2) -> typq1 = typq2 && equal_ctx ctx1 ctx2)
       ctx1.scattereds ctx2.scattereds
  && Bindings.equal ( = ) ctx1.fixities ctx2.fixities
  && StringSet.equal ctx1.internal_files ctx2.internal_files
  && StringMap.equal ( = ) ctx1.target_sets ctx2.target_sets

let merge_ctx l ctx1 ctx2 =
  let compatible equal err k x y =
    match (x, y) with
    | None, None -> None
    | Some x, None -> Some x
    | None, Some y -> Some y
    | Some x, Some y -> if equal x y then Some x else raise (Reporting.err_general l (err k))
  in
  {
    kinds =
      KBindings.merge
        (compatible ( = ) (fun v -> "Mismatching kinds for type variable " ^ string_of_kid v))
        ctx1.kinds ctx2.kinds;
    type_constructors =
      Bindings.merge
        (compatible ( = ) (fun id -> "Different definitions for type constructor " ^ string_of_id id ^ " found"))
        ctx1.type_constructors ctx2.type_constructors;
    scattereds =
      Bindings.merge
        (compatible
           (fun (typq1, ctx1) (typq2, ctx2) -> typq1 = typq2 && equal_ctx ctx1 ctx2)
           (fun id -> "Scattered definition " ^ string_of_id id ^ " found with mismatching context")
        )
        ctx1.scattereds ctx2.scattereds;
    fixities =
      Bindings.merge
        (compatible ( = ) (fun id -> "Operator " ^ string_of_id id ^ " declared with multiple fixities"))
        ctx1.fixities ctx2.fixities;
    internal_files = StringSet.union ctx1.internal_files ctx2.internal_files;
    target_sets =
      StringMap.merge
        (compatible ( = ) (fun s -> "Mismatching target set " ^ s ^ " found"))
        ctx1.target_sets ctx2.target_sets;
  }

let string_of_parse_id_aux = function P.Id v -> v | P.Operator v -> v

let string_of_parse_id (P.Id_aux (id, l)) = string_of_parse_id_aux id

let parse_id_loc (P.Id_aux (_, l)) = l

let string_contains str char =
  try
    ignore (String.index str char);
    true
  with Not_found -> false

let to_ast_kind (P.K_aux (k, l)) =
  match k with
  | P.K_type -> Some (K_aux (K_type, l))
  | P.K_int -> Some (K_aux (K_int, l))
  | P.K_order -> None
  | P.K_bool -> Some (K_aux (K_bool, l))

let to_ast_id ctx (P.Id_aux (id, l)) =
  let to_ast_id' id = Id_aux ((match id with P.Id x -> Id x | P.Operator x -> Operator x), l) in
  if string_contains (string_of_parse_id_aux id) '#' then begin
    match Reporting.loc_file l with
    | Some file when !opt_magic_hash || StringSet.mem file ctx.internal_files -> to_ast_id' id
    | None -> to_ast_id' id
    | _ -> raise (Reporting.err_general l "Identifier contains hash character and -dmagic_hash is unset")
  end
  else to_ast_id' id

let to_infix_parser_op =
  let open Infix_parser in
  function
  | Infix, 0, x -> Op0 x
  | InfixL, 0, x -> Op0l x
  | InfixR, 0, x -> Op0r x
  | Infix, 1, x -> Op1 x
  | InfixL, 1, x -> Op1l x
  | InfixR, 1, x -> Op1r x
  | Infix, 2, x -> Op2 x
  | InfixL, 2, x -> Op2l x
  | InfixR, 2, x -> Op2r x
  | Infix, 3, x -> Op3 x
  | InfixL, 3, x -> Op3l x
  | InfixR, 3, x -> Op3r x
  | Infix, 4, x -> Op4 x
  | InfixL, 4, x -> Op4l x
  | InfixR, 4, x -> Op4r x
  | Infix, 5, x -> Op5 x
  | InfixL, 5, x -> Op5l x
  | InfixR, 5, x -> Op5r x
  | Infix, 6, x -> Op6 x
  | InfixL, 6, x -> Op6l x
  | InfixR, 6, x -> Op6r x
  | Infix, 7, x -> Op7 x
  | InfixL, 7, x -> Op7l x
  | InfixR, 7, x -> Op7r x
  | Infix, 8, x -> Op8 x
  | InfixL, 8, x -> Op8l x
  | InfixR, 8, x -> Op8r x
  | Infix, 9, x -> Op9 x
  | InfixL, 9, x -> Op9l x
  | InfixR, 9, x -> Op9r x
  | _ -> Reporting.unreachable P.Unknown __POS__ "Invalid fixity"

let parse_infix :
      'a 'b.
      P.l ->
      ctx ->
      ('a P.infix_token * Lexing.position * Lexing.position) list ->
      ('a -> Infix_parser.token) ->
      'b Infix_parser.MenhirInterpreter.checkpoint ->
      'b =
 fun l ctx infix_tokens mk_primary checkpoint ->
  let open Infix_parser in
  let tokens =
    ref
      (List.map
         (function
           | P.IT_primary x, s, e -> (mk_primary x, s, e)
           | P.IT_prefix id, s, e -> (
               match id with
               | Id_aux (Id "pow2", _) -> (TwoCaret, s, e)
               | Id_aux (Id "negate", _) -> (Minus, s, e)
               | Id_aux (Id "__deref", _) -> (Star, s, e)
               | _ -> raise (Reporting.err_general (P.Range (s, e)) "Unknown prefix operator")
             )
           | P.IT_op id, s, e -> (
               match id with
               | Id_aux (Id "+", _) -> (Plus, s, e)
               | Id_aux (Id "-", _) -> (Minus, s, e)
               | Id_aux (Id "*", _) -> (Star, s, e)
               | Id_aux (Id "<", _) -> (Lt, s, e)
               | Id_aux (Id ">", _) -> (Gt, s, e)
               | Id_aux (Id "<=", _) -> (LtEq, s, e)
               | Id_aux (Id ">=", _) -> (GtEq, s, e)
               | Id_aux (Id "::", _) -> (ColonColon, s, e)
               | Id_aux (Id "@", _) -> (At, s, e)
               | Id_aux (Id "in", _) -> (In, s, e)
               | _ -> (
                   match Bindings.find_opt (to_ast_id ctx id) ctx.fixities with
                   | Some (prec, level) -> (to_infix_parser_op (prec, level, id), s, e)
                   | None ->
                       raise
                         (Reporting.err_general
                            (P.Range (s, e))
                            ("Undeclared fixity for operator " ^ string_of_parse_id id)
                         )
                 )
             )
           )
         infix_tokens
      )
  in
  let supplier () : token * Lexing.position * Lexing.position =
    match !tokens with
    | [((_, _, e) as token)] ->
        tokens := [(Infix_parser.Eof, e, e)];
        token
    | token :: rest ->
        tokens := rest;
        token
    | [] -> assert false
  in
  try MenhirInterpreter.loop supplier checkpoint
  with Infix_parser.Error -> raise (Reporting.err_syntax_loc l "Failed to parse infix expression")

let parse_infix_exp ctx = function
  | P.E_aux (P.E_infix infix_tokens, l) -> (
      match infix_tokens with
      | (_, s, _) :: _ ->
          parse_infix l ctx infix_tokens (fun exp -> Infix_parser.Exp exp) (Infix_parser.Incremental.exp_eof s)
      | [] -> Reporting.unreachable l __POS__ "Found empty infix expression"
    )
  | exp -> exp

let parse_infix_atyp ctx = function
  | P.ATyp_aux (P.ATyp_infix infix_tokens, l) -> (
      match infix_tokens with
      | (_, s, _) :: _ ->
          parse_infix l ctx infix_tokens (fun typ -> Infix_parser.Typ typ) (Infix_parser.Incremental.typ_eof s)
      | [] -> Reporting.unreachable l __POS__ "Found empty infix type"
    )
  | atyp -> atyp

let to_ast_var (P.Kid_aux (P.Var v, l)) = Kid_aux (Var v, l)

(* Used for error messages involving lists of kinds *)
let format_kind_aux_list = function
  | [kind] -> string_of_kind_aux kind
  | kinds -> "(" ^ Util.string_of_list ", " string_of_kind_aux kinds ^ ")"

let to_ast_kopts ctx (P.KOpt_aux (aux, l)) =
  let mk_kopt v k =
    let v = to_ast_var v in
    Option.map
      (fun k -> (KOpt_aux (KOpt_kind (k, v), l), { ctx with kinds = KBindings.add v (unaux_kind k) ctx.kinds }))
      (to_ast_kind k)
  in
  match aux with
  | P.KOpt_kind (attr, vs, None) ->
      let k = P.K_aux (P.K_int, gen_loc l) in
      ( List.fold_left
          (fun (kopts, ctx) v ->
            match mk_kopt v k with Some (kopt, ctx) -> (kopt :: kopts, ctx) | None -> (kopts, ctx)
          )
          ([], ctx) vs,
        attr
      )
  | P.KOpt_kind (attr, vs, Some k) ->
      ( List.fold_left
          (fun (kopts, ctx) v ->
            match mk_kopt v k with Some (kopt, ctx) -> (kopt :: kopts, ctx) | None -> (kopts, ctx)
          )
          ([], ctx) vs,
        attr
      )

let rec to_ast_typ ctx atyp =
  let (P.ATyp_aux (aux, l)) = parse_infix_atyp ctx atyp in
  match aux with
  | P.ATyp_id id -> Typ_aux (Typ_id (to_ast_id ctx id), l)
  | P.ATyp_var v -> Typ_aux (Typ_var (to_ast_var v), l)
  | P.ATyp_fn (from_typ, to_typ, _) ->
      let from_typs =
        match from_typ with
        | P.ATyp_aux (P.ATyp_tuple typs, _) -> List.map (to_ast_typ ctx) typs
        | _ -> [to_ast_typ ctx from_typ]
      in
      Typ_aux (Typ_fn (from_typs, to_ast_typ ctx to_typ), l)
  | P.ATyp_bidir (typ1, typ2, _) -> Typ_aux (Typ_bidir (to_ast_typ ctx typ1, to_ast_typ ctx typ2), l)
  | P.ATyp_nset nums ->
      let n = Kid_aux (Var "'n", gen_loc l) in
      Typ_aux (Typ_exist ([mk_kopt ~loc:l K_int n], nc_set n nums, atom_typ (nvar n)), l)
  | P.ATyp_tuple typs -> Typ_aux (Typ_tuple (List.map (to_ast_typ ctx) typs), l)
  | P.ATyp_app (P.Id_aux (P.Id "int", il), [n]) ->
      Typ_aux (Typ_app (Id_aux (Id "atom", il), [to_ast_typ_arg ctx n K_int]), l)
  | P.ATyp_app (P.Id_aux (P.Id "bool", il), [n]) ->
      Typ_aux (Typ_app (Id_aux (Id "atom_bool", il), [to_ast_typ_arg ctx n K_bool]), l)
  | P.ATyp_app (id, args) ->
      let id = to_ast_id ctx id in
      begin
        match Bindings.find_opt id ctx.type_constructors with
        | None -> raise (Reporting.err_typ l (sprintf "Could not find type constructor %s" (string_of_id id)))
        | Some kinds ->
            let non_order_kinds = Util.option_these kinds in
            let args_len = List.length args in
            if args_len = List.length non_order_kinds then
              Typ_aux (Typ_app (id, List.map2 (to_ast_typ_arg ctx) args non_order_kinds), l)
            else if args_len = List.length kinds then
              Typ_aux
                ( Typ_app (id, Util.option_these (List.map2 (fun arg -> Option.map (to_ast_typ_arg ctx arg)) args kinds)),
                  l
                )
            else
              raise
                (Reporting.err_typ l
                   (sprintf "%s : %s -> Type expected %d arguments, given %d" (string_of_id id)
                      (format_kind_aux_list non_order_kinds) (List.length kinds) (List.length args)
                   )
                )
      end
  | P.ATyp_exist (kopts, nc, atyp) ->
      let kopts, ctx =
        List.fold_right
          (fun kopt (kopts, ctx) ->
            let (kopts', ctx), attr = to_ast_kopts ctx kopt in
            match attr with
            | None -> (kopts' @ kopts, ctx)
            | Some attr ->
                raise (Reporting.err_typ l (sprintf "Attribute %s cannot appear within an existential type" attr))
          )
          kopts ([], ctx)
      in
      Typ_aux (Typ_exist (kopts, to_ast_constraint ctx nc, to_ast_typ ctx atyp), l)
  | P.ATyp_parens atyp -> to_ast_typ ctx atyp
  | _ -> raise (Reporting.err_typ l "Invalid type")

and to_ast_typ_arg ctx (ATyp_aux (_, l) as atyp) = function
  | K_type -> A_aux (A_typ (to_ast_typ ctx atyp), l)
  | K_int -> A_aux (A_nexp (to_ast_nexp ctx atyp), l)
  | K_bool -> A_aux (A_bool (to_ast_constraint ctx atyp), l)

and to_ast_nexp ctx atyp =
  let (P.ATyp_aux (aux, l)) = parse_infix_atyp ctx atyp in
  match aux with
  | P.ATyp_id id -> Nexp_aux (Nexp_id (to_ast_id ctx id), l)
  | P.ATyp_var v -> Nexp_aux (Nexp_var (to_ast_var v), l)
  | P.ATyp_lit (P.L_aux (P.L_num c, _)) -> Nexp_aux (Nexp_constant c, l)
  | P.ATyp_sum (t1, t2) -> Nexp_aux (Nexp_sum (to_ast_nexp ctx t1, to_ast_nexp ctx t2), l)
  | P.ATyp_exp t1 -> Nexp_aux (Nexp_exp (to_ast_nexp ctx t1), l)
  | P.ATyp_neg t1 -> Nexp_aux (Nexp_neg (to_ast_nexp ctx t1), l)
  | P.ATyp_times (t1, t2) -> Nexp_aux (Nexp_times (to_ast_nexp ctx t1, to_ast_nexp ctx t2), l)
  | P.ATyp_minus (t1, t2) -> Nexp_aux (Nexp_minus (to_ast_nexp ctx t1, to_ast_nexp ctx t2), l)
  | P.ATyp_app (id, ts) -> Nexp_aux (Nexp_app (to_ast_id ctx id, List.map (to_ast_nexp ctx) ts), l)
  | P.ATyp_parens atyp -> to_ast_nexp ctx atyp
  | _ -> raise (Reporting.err_typ l "Invalid numeric expression in type")

and to_ast_bitfield_index_nexp ctx atyp =
  let (P.ATyp_aux (aux, l)) = parse_infix_atyp ctx atyp in
  match aux with
  | P.ATyp_id id -> Nexp_aux (Nexp_id (to_ast_id ctx id), l)
  | P.ATyp_lit (P.L_aux (P.L_num c, _)) -> Nexp_aux (Nexp_constant c, l)
  | P.ATyp_sum (t1, t2) -> Nexp_aux (Nexp_sum (to_ast_bitfield_index_nexp ctx t1, to_ast_bitfield_index_nexp ctx t2), l)
  | P.ATyp_exp t1 -> Nexp_aux (Nexp_exp (to_ast_bitfield_index_nexp ctx t1), l)
  | P.ATyp_neg t1 -> Nexp_aux (Nexp_neg (to_ast_bitfield_index_nexp ctx t1), l)
  | P.ATyp_times (t1, t2) ->
      Nexp_aux (Nexp_times (to_ast_bitfield_index_nexp ctx t1, to_ast_bitfield_index_nexp ctx t2), l)
  | P.ATyp_minus (t1, t2) ->
      Nexp_aux (Nexp_minus (to_ast_bitfield_index_nexp ctx t1, to_ast_bitfield_index_nexp ctx t2), l)
  | P.ATyp_app (id, ts) -> Nexp_aux (Nexp_app (to_ast_id ctx id, List.map (to_ast_bitfield_index_nexp ctx) ts), l)
  | P.ATyp_parens atyp -> to_ast_bitfield_index_nexp ctx atyp
  | _ -> raise (Reporting.err_typ l "Invalid numeric expression in field index")

and to_ast_order ctx (P.ATyp_aux (aux, l)) =
  match aux with
  | P.ATyp_inc -> Ord_aux (Ord_inc, l)
  | P.ATyp_dec -> Ord_aux (Ord_dec, l)
  | P.ATyp_parens atyp -> to_ast_order ctx atyp
  | _ -> raise (Reporting.err_typ l "Invalid order in type")

and to_ast_constraint ctx atyp =
  let (P.ATyp_aux (aux, l)) = parse_infix_atyp ctx atyp in
  match aux with
  | P.ATyp_parens atyp -> to_ast_constraint ctx atyp
  | _ ->
      let aux =
        match aux with
        | P.ATyp_app ((Id_aux (Operator op, _) as id), [t1; t2]) -> begin
            match op with
            | "==" -> NC_equal (to_ast_nexp ctx t1, to_ast_nexp ctx t2)
            | "!=" -> NC_not_equal (to_ast_nexp ctx t1, to_ast_nexp ctx t2)
            | ">=" -> NC_bounded_ge (to_ast_nexp ctx t1, to_ast_nexp ctx t2)
            | "<=" -> NC_bounded_le (to_ast_nexp ctx t1, to_ast_nexp ctx t2)
            | ">" -> NC_bounded_gt (to_ast_nexp ctx t1, to_ast_nexp ctx t2)
            | "<" -> NC_bounded_lt (to_ast_nexp ctx t1, to_ast_nexp ctx t2)
            | "&" -> NC_and (to_ast_constraint ctx t1, to_ast_constraint ctx t2)
            | "|" -> NC_or (to_ast_constraint ctx t1, to_ast_constraint ctx t2)
            | _ -> (
                let id = to_ast_id ctx id in
                match Bindings.find_opt id ctx.type_constructors with
                | None -> raise (Reporting.err_typ l (sprintf "Could not find type constructor %s" (string_of_id id)))
                | Some kinds ->
                    let non_order_kinds = Util.option_these kinds in
                    if List.length non_order_kinds = 2 then
                      NC_app (id, List.map2 (to_ast_typ_arg ctx) [t1; t2] non_order_kinds)
                    else
                      raise
                        (Reporting.err_typ l
                           (sprintf "%s : %s -> Bool expected %d arguments, given 2" (string_of_id id)
                              (format_kind_aux_list non_order_kinds) (List.length non_order_kinds)
                           )
                        )
              )
          end
        | P.ATyp_app (id, args) ->
            let id = to_ast_id ctx id in
            begin
              match Bindings.find_opt id ctx.type_constructors with
              | None -> raise (Reporting.err_typ l (sprintf "Could not find type constructor %s" (string_of_id id)))
              | Some kinds ->
                  let non_order_kinds = Util.option_these kinds in
                  if List.length args = List.length non_order_kinds then
                    NC_app (id, List.map2 (to_ast_typ_arg ctx) args non_order_kinds)
                  else
                    raise
                      (Reporting.err_typ l
                         (sprintf "%s : %s -> Bool expected %d arguments, given %d" (string_of_id id)
                            (format_kind_aux_list non_order_kinds) (List.length non_order_kinds) (List.length args)
                         )
                      )
            end
        | P.ATyp_var v -> NC_var (to_ast_var v)
        | P.ATyp_lit (P.L_aux (P.L_true, _)) -> NC_true
        | P.ATyp_lit (P.L_aux (P.L_false, _)) -> NC_false
        | P.ATyp_in (P.ATyp_aux (P.ATyp_var v, _), P.ATyp_aux (P.ATyp_nset bounds, _)) -> NC_set (to_ast_var v, bounds)
        | _ -> raise (Reporting.err_typ l "Invalid constraint")
      in
      NC_aux (aux, l)

let to_ast_quant_items ctx (P.QI_aux (aux, l)) =
  match aux with
  | P.QI_constraint nc -> ([QI_aux (QI_constraint (to_ast_constraint ctx nc), l)], ctx)
  | P.QI_id kopt -> (
      let (kopts, ctx), attr = to_ast_kopts ctx kopt in
      match attr with
      | Some "constant" ->
          Reporting.warn "Deprecated" l "constant type variable attribute no longer used";
          (List.map (fun kopt -> QI_aux (QI_id kopt, l)) kopts, ctx)
      | Some attr -> raise (Reporting.err_typ l (sprintf "Unknown attribute %s" attr))
      | None -> (List.map (fun kopt -> QI_aux (QI_id kopt, l)) kopts, ctx)
    )

let to_ast_typquant ctx (P.TypQ_aux (aux, l)) =
  match aux with
  | P.TypQ_no_forall -> (TypQ_aux (TypQ_no_forall, l), ctx)
  | P.TypQ_tq quants ->
      let quants, ctx =
        List.fold_left
          (fun (qis, ctx) qi ->
            let qis', ctx = to_ast_quant_items ctx qi in
            (qis' @ qis, ctx)
          )
          ([], ctx) quants
      in
      (TypQ_aux (TypQ_tq (List.rev quants), l), ctx)

let to_ast_typschm ctx (P.TypSchm_aux (P.TypSchm_ts (typq, typ), l)) =
  let typq, ctx = to_ast_typquant ctx typq in
  let typ = to_ast_typ ctx typ in
  (TypSchm_aux (TypSchm_ts (typq, typ), l), ctx)

let to_ast_lit (P.L_aux (lit, l)) =
  L_aux
    ( ( match lit with
      | P.L_unit -> L_unit
      | P.L_zero -> L_zero
      | P.L_one -> L_one
      | P.L_true -> L_true
      | P.L_false -> L_false
      | P.L_undef -> L_undef
      | P.L_num i -> L_num i
      | P.L_hex h -> L_hex h
      | P.L_bin b -> L_bin b
      | P.L_real r -> L_real r
      | P.L_string s -> L_string s
      ),
      l
    )

let rec to_ast_typ_pat ctx (P.ATyp_aux (aux, l)) =
  match aux with
  | P.ATyp_wild -> TP_aux (TP_wild, l)
  | P.ATyp_var kid -> TP_aux (TP_var (to_ast_var kid), l)
  | P.ATyp_app (P.Id_aux (P.Id "int", il), typs) ->
      TP_aux (TP_app (Id_aux (Id "atom", il), List.map (to_ast_typ_pat ctx) typs), l)
  | P.ATyp_app (P.Id_aux (P.Id "bool", il), typs) ->
      TP_aux (TP_app (Id_aux (Id "atom_bool", il), List.map (to_ast_typ_pat ctx) typs), l)
  | P.ATyp_app (f, typs) -> TP_aux (TP_app (to_ast_id ctx f, List.map (to_ast_typ_pat ctx) typs), l)
  | _ -> raise (Reporting.err_typ l "Unexpected type in type pattern")

let is_wild_fpat = function P.FP_aux (P.FP_wild, _) -> true | _ -> false

let check_duplicate_fields ~error ~field_id fields =
  List.fold_left
    (fun seen field ->
      let id = field_id field in
      match IdSet.find_opt id seen with
      | Some seen_id ->
          raise
            (Reporting.err_general (Hint ("Previous field here", id_loc seen_id, id_loc id)) (error (string_of_id id)))
      | None -> IdSet.add id seen
    )
    IdSet.empty fields
  |> ignore

let rec to_ast_pat ctx (P.P_aux (aux, l)) =
  match aux with
  | P.P_attribute (attr, arg, pat) ->
      let (P_aux (aux, (pat_l, annot))) = to_ast_pat ctx pat in
      (* The location of an E_attribute node is just the attribute by itself *)
      let annot = add_attribute l attr arg annot in
      P_aux (aux, (pat_l, annot))
  | _ ->
      let aux =
        match aux with
        | P.P_attribute _ -> assert false
        | P.P_lit lit -> P_lit (to_ast_lit lit)
        | P.P_wild -> P_wild
        | P.P_var (pat, P.ATyp_aux (P.ATyp_id id, _)) -> P_as (to_ast_pat ctx pat, to_ast_id ctx id)
        | P.P_typ (typ, pat) -> P_typ (to_ast_typ ctx typ, to_ast_pat ctx pat)
        | P.P_id id -> P_id (to_ast_id ctx id)
        | P.P_var (pat, typ) -> P_var (to_ast_pat ctx pat, to_ast_typ_pat ctx typ)
        | P.P_app (id, []) -> P_id (to_ast_id ctx id)
        | P.P_app (id, pats) ->
            if List.length pats == 1 && string_of_parse_id id = "~" then P_not (to_ast_pat ctx (List.hd pats))
            else P_app (to_ast_id ctx id, List.map (to_ast_pat ctx) pats)
        | P.P_vector pats -> P_vector (List.map (to_ast_pat ctx) pats)
        | P.P_vector_concat pats -> P_vector_concat (List.map (to_ast_pat ctx) pats)
        | P.P_vector_subrange (id, n, m) -> P_vector_subrange (to_ast_id ctx id, n, m)
        | P.P_tuple pats -> P_tuple (List.map (to_ast_pat ctx) pats)
        | P.P_list pats -> P_list (List.map (to_ast_pat ctx) pats)
        | P.P_cons (pat1, pat2) -> P_cons (to_ast_pat ctx pat1, to_ast_pat ctx pat2)
        | P.P_string_append pats -> P_string_append (List.map (to_ast_pat ctx) pats)
        | P.P_struct fpats ->
            let wild_fpats, fpats = List.partition is_wild_fpat fpats in
            let field_wildcard =
              match wild_fpats with
              | FP_aux (_, l1) :: FP_aux (_, l2) :: _ ->
                  raise
                    (Reporting.err_general
                       (Parse_ast.Hint ("previous field wildcard here", l1, l2))
                       "Duplicate field wildcards in struct pattern"
                    )
              | [FP_aux (_, l)] -> FP_wild l
              | [] -> FP_no_wild
            in
            let fpats = List.map (to_ast_fpat ctx) fpats in
            check_duplicate_fields ~error:(fun f -> "Duplicate field " ^ f ^ " in struct pattern") ~field_id:fst fpats;
            P_struct (fpats, field_wildcard)
      in
      P_aux (aux, (l, empty_uannot))

and to_ast_fpat ctx (P.FP_aux (aux, l)) =
  match aux with
  | FP_field (field, pat) -> (to_ast_id ctx field, to_ast_pat ctx pat)
  | FP_wild -> Reporting.unreachable l __POS__ "Unexpected field wildcard"

let rec to_ast_letbind ctx (P.LB_aux (lb, l) : P.letbind) : uannot letbind =
  LB_aux ((match lb with P.LB_val (pat, exp) -> LB_val (to_ast_pat ctx pat, to_ast_exp ctx exp)), (l, empty_uannot))

and to_ast_exp ctx exp =
  let (P.E_aux (exp, l)) = parse_infix_exp ctx exp in
  match exp with
  | P.E_attribute (attr, arg, exp) ->
      let (E_aux (exp, (exp_l, annot))) = to_ast_exp ctx exp in
      (* The location of an E_attribute node is just the attribute itself *)
      let annot = add_attribute l attr arg annot in
      E_aux (exp, (exp_l, annot))
  | _ ->
      let aux =
        match exp with
        | P.E_attribute _ | P.E_infix _ -> assert false
        | P.E_block exps -> (
            match to_ast_fexps false ctx exps with
            | Some fexps -> E_struct fexps
            | None -> E_block (List.map (to_ast_exp ctx) exps)
          )
        | P.E_id id ->
            (* We support identifiers the same as __LOC__, __FILE__ and
               __LINE__ in the OCaml standard library, and similar
               constructs in C *)
            let id_str = string_of_parse_id id in
            if id_str = "__LOC__" then E_lit (L_aux (L_string (Reporting.short_loc_to_string l), l))
            else if id_str = "__FILE__" then (
              let file = match Reporting.simp_loc l with Some (p, _) -> p.pos_fname | None -> "unknown file" in
              E_lit (L_aux (L_string file, l))
            )
            else if id_str = "__LINE__" then (
              let lnum = match Reporting.simp_loc l with Some (p, _) -> p.pos_lnum | None -> -1 in
              E_lit (L_aux (L_num (Big_int.of_int lnum), l))
            )
            else E_id (to_ast_id ctx id)
        | P.E_ref id -> E_ref (to_ast_id ctx id)
        | P.E_lit lit -> E_lit (to_ast_lit lit)
        | P.E_typ (typ, exp) -> E_typ (to_ast_typ ctx typ, to_ast_exp ctx exp)
        | P.E_app (f, args) -> (
            match List.map (to_ast_exp ctx) args with
            | [] -> E_app (to_ast_id ctx f, [])
            | exps -> E_app (to_ast_id ctx f, exps)
          )
        | P.E_app_infix (left, op, right) -> E_app_infix (to_ast_exp ctx left, to_ast_id ctx op, to_ast_exp ctx right)
        | P.E_tuple exps -> E_tuple (List.map (to_ast_exp ctx) exps)
        | P.E_if (e1, e2, e3, _) -> E_if (to_ast_exp ctx e1, to_ast_exp ctx e2, to_ast_exp ctx e3)
        | P.E_for (id, e1, e2, e3, atyp, e4) ->
            E_for
              ( to_ast_id ctx id,
                to_ast_exp ctx e1,
                to_ast_exp ctx e2,
                to_ast_exp ctx e3,
                to_ast_order ctx atyp,
                to_ast_exp ctx e4
              )
        | P.E_loop (P.While, m, e1, e2) -> E_loop (While, to_ast_measure ctx m, to_ast_exp ctx e1, to_ast_exp ctx e2)
        | P.E_loop (P.Until, m, e1, e2) -> E_loop (Until, to_ast_measure ctx m, to_ast_exp ctx e1, to_ast_exp ctx e2)
        | P.E_vector exps -> E_vector (List.map (to_ast_exp ctx) exps)
        | P.E_vector_access (vexp, exp) -> E_vector_access (to_ast_exp ctx vexp, to_ast_exp ctx exp)
        | P.E_vector_subrange (vex, exp1, exp2) ->
            E_vector_subrange (to_ast_exp ctx vex, to_ast_exp ctx exp1, to_ast_exp ctx exp2)
        | P.E_vector_update (vex, exp1, exp2) ->
            E_vector_update (to_ast_exp ctx vex, to_ast_exp ctx exp1, to_ast_exp ctx exp2)
        | P.E_vector_update_subrange (vex, e1, e2, e3) ->
            E_vector_update_subrange (to_ast_exp ctx vex, to_ast_exp ctx e1, to_ast_exp ctx e2, to_ast_exp ctx e3)
        | P.E_vector_append (e1, e2) -> E_vector_append (to_ast_exp ctx e1, to_ast_exp ctx e2)
        | P.E_list exps -> E_list (List.map (to_ast_exp ctx) exps)
        | P.E_cons (e1, e2) -> E_cons (to_ast_exp ctx e1, to_ast_exp ctx e2)
        | P.E_struct fexps -> (
            match to_ast_fexps true ctx fexps with
            | Some fexps -> E_struct fexps
            | None -> raise (Reporting.err_unreachable l __POS__ "to_ast_fexps with true returned none")
          )
        | P.E_struct_update (exp, fexps) -> (
            match to_ast_fexps true ctx fexps with
            | Some fexps -> E_struct_update (to_ast_exp ctx exp, fexps)
            | _ -> raise (Reporting.err_unreachable l __POS__ "to_ast_fexps with true returned none")
          )
        | P.E_field (exp, id) -> E_field (to_ast_exp ctx exp, to_ast_id ctx id)
        | P.E_match (exp, pexps) -> E_match (to_ast_exp ctx exp, List.map (to_ast_case ctx) pexps)
        | P.E_try (exp, pexps) -> E_try (to_ast_exp ctx exp, List.map (to_ast_case ctx) pexps)
        | P.E_let (leb, exp) -> E_let (to_ast_letbind ctx leb, to_ast_exp ctx exp)
        | P.E_assign (lexp, exp) -> E_assign (to_ast_lexp ctx lexp, to_ast_exp ctx exp)
        | P.E_var (lexp, exp1, exp2) -> E_var (to_ast_lexp ctx lexp, to_ast_exp ctx exp1, to_ast_exp ctx exp2)
        | P.E_sizeof nexp -> E_sizeof (to_ast_nexp ctx nexp)
        | P.E_constraint nc -> E_constraint (to_ast_constraint ctx nc)
        | P.E_exit exp -> E_exit (to_ast_exp ctx exp)
        | P.E_throw exp -> E_throw (to_ast_exp ctx exp)
        | P.E_return exp -> E_return (to_ast_exp ctx exp)
        | P.E_assert (cond, msg) -> E_assert (to_ast_exp ctx cond, to_ast_exp ctx msg)
        | P.E_internal_plet (pat, exp1, exp2) ->
            if !opt_magic_hash then E_internal_plet (to_ast_pat ctx pat, to_ast_exp ctx exp1, to_ast_exp ctx exp2)
            else raise (Reporting.err_general l "Internal plet construct found without -dmagic_hash")
        | P.E_internal_return exp ->
            if !opt_magic_hash then E_internal_return (to_ast_exp ctx exp)
            else raise (Reporting.err_general l "Internal return construct found without -dmagic_hash")
        | P.E_internal_assume (nc, exp) ->
            if !opt_magic_hash then E_internal_assume (to_ast_constraint ctx nc, to_ast_exp ctx exp)
            else raise (Reporting.err_general l "Internal assume construct found without -dmagic_hash")
        | P.E_deref exp -> E_app (Id_aux (Id "__deref", l), [to_ast_exp ctx exp])
      in
      E_aux (aux, (l, empty_uannot))

and to_ast_measure ctx (P.Measure_aux (m, l)) : uannot internal_loop_measure =
  let m =
    match m with
    | P.Measure_none -> Measure_none
    | P.Measure_some exp ->
        if !opt_magic_hash then Measure_some (to_ast_exp ctx exp)
        else raise (Reporting.err_general l "Internal loop termination measure found without -dmagic_hash")
  in
  Measure_aux (m, l)

and to_ast_lexp ctx exp =
  let (P.E_aux (exp, l)) = parse_infix_exp ctx exp in
  let lexp =
    match exp with
    | P.E_id id -> LE_id (to_ast_id ctx id)
    | P.E_deref exp -> LE_deref (to_ast_exp ctx exp)
    | P.E_typ (typ, P.E_aux (P.E_id id, l')) -> LE_typ (to_ast_typ ctx typ, to_ast_id ctx id)
    | P.E_tuple tups ->
        let ltups = List.map (to_ast_lexp ctx) tups in
        let is_ok_in_tup (LE_aux (le, (l, _))) =
          match le with
          | LE_id _ | LE_typ _ | LE_vector _ | LE_vector_concat _ | LE_field _ | LE_vector_range _ | LE_tuple _ -> ()
          | LE_app _ | LE_deref _ ->
              raise (Reporting.err_typ l "only identifiers, fields, and vectors may be set in a tuple")
        in
        List.iter is_ok_in_tup ltups;
        LE_tuple ltups
    | P.E_app ((P.Id_aux (f, l') as f'), args) -> begin
        match f with
        | P.Id id -> (
            match List.map (to_ast_exp ctx) args with
            | [E_aux (E_lit (L_aux (L_unit, _)), _)] -> LE_app (to_ast_id ctx f', [])
            | [E_aux (E_tuple exps, _)] -> LE_app (to_ast_id ctx f', exps)
            | args -> LE_app (to_ast_id ctx f', args)
          )
        | _ -> raise (Reporting.err_typ l' "memory call on lefthand side of assignment must begin with an id")
      end
    | P.E_vector_append (exp1, exp2) -> LE_vector_concat (to_ast_lexp ctx exp1 :: to_ast_lexp_vector_concat ctx exp2)
    | P.E_vector_access (vexp, exp) -> LE_vector (to_ast_lexp ctx vexp, to_ast_exp ctx exp)
    | P.E_vector_subrange (vexp, exp1, exp2) ->
        LE_vector_range (to_ast_lexp ctx vexp, to_ast_exp ctx exp1, to_ast_exp ctx exp2)
    | P.E_field (fexp, id) -> LE_field (to_ast_lexp ctx fexp, to_ast_id ctx id)
    | _ ->
        raise
          (Reporting.err_typ l
             "Only identifiers, cast identifiers, vector accesses, vector slices, and fields can be on the lefthand \
              side of an assignment"
          )
  in
  LE_aux (lexp, (l, empty_uannot))

and to_ast_lexp_vector_concat ctx (P.E_aux (exp_aux, l) as exp) =
  match exp_aux with
  | P.E_vector_append (exp1, exp2) -> to_ast_lexp ctx exp1 :: to_ast_lexp_vector_concat ctx exp2
  | _ -> [to_ast_lexp ctx exp]

and to_ast_case ctx (P.Pat_aux (pex, l) : P.pexp) : uannot pexp =
  match pex with
  | P.Pat_exp (pat, exp) -> Pat_aux (Pat_exp (to_ast_pat ctx pat, to_ast_exp ctx exp), (l, empty_uannot))
  | P.Pat_when (pat, guard, exp) ->
      Pat_aux (Pat_when (to_ast_pat ctx pat, to_ast_exp ctx guard, to_ast_exp ctx exp), (l, empty_uannot))

and to_ast_fexps (fail_on_error : bool) ctx (exps : P.exp list) : uannot fexp list option =
  match exps with
  | [] -> Some []
  | fexp :: exps -> (
      let maybe_fexp, maybe_error = to_ast_record_try ctx fexp in
      match (maybe_fexp, maybe_error) with
      | Some fexp, None -> (
          match to_ast_fexps fail_on_error ctx exps with Some fexps -> Some (fexp :: fexps) | _ -> None
        )
      | None, Some (l, msg) -> if fail_on_error then raise (Reporting.err_typ l msg) else None
      | _ -> None
    )

and to_ast_record_try ctx (P.E_aux (exp, l) : P.exp) : uannot fexp option * (l * string) option =
  match exp with
  | P.E_app_infix (left, op, r) -> (
      match (left, op) with
      | P.E_aux (P.E_id id, li), P.Id_aux (P.Id "=", leq) ->
          (Some (FE_aux (FE_fexp (to_ast_id ctx id, to_ast_exp ctx r), (l, empty_uannot))), None)
      | P.E_aux (_, li), P.Id_aux (P.Id "=", leq) ->
          (None, Some (li, "Expected an identifier to begin this field assignment"))
      | P.E_aux (P.E_id id, li), P.Id_aux (_, leq) ->
          (None, Some (leq, "Expected a field assignment to be identifier = expression"))
      | P.E_aux (_, li), P.Id_aux (_, leq) ->
          (None, Some (l, "Expected a field assignment to be identifier = expression"))
    )
  | _ -> (None, Some (l, "Expected a field assignment to be identifier = expression"))

type 'a ctx_out = 'a * ctx

let to_ast_default ctx (default : P.default_typing_spec) : default_spec ctx_out =
  match default with
  | P.DT_aux (P.DT_order (P.K_aux (P.K_order, _), o), l) -> (
      match o with
      | P.ATyp_aux (P.ATyp_inc, lo) ->
          let default_order = Ord_aux (Ord_inc, lo) in
          (DT_aux (DT_order default_order, l), ctx)
      | P.ATyp_aux (P.ATyp_dec, lo) ->
          let default_order = Ord_aux (Ord_dec, lo) in
          (DT_aux (DT_order default_order, l), ctx)
      | _ -> raise (Reporting.err_typ l "default Order must be inc or dec")
    )
  | P.DT_aux (_, l) -> raise (Reporting.err_typ l "default must specify Order")

let to_ast_extern (ext : P.extern) : extern = { pure = ext.pure; bindings = ext.bindings }

let to_ast_spec ctx (vs : P.val_spec) : uannot val_spec ctx_out =
  match vs with
  | P.VS_aux (vs, l) -> (
      match vs with
      | P.VS_val_spec (ts, id, ext) ->
          let typschm, _ = to_ast_typschm ctx ts in
          let ext = Option.map to_ast_extern ext in
          (VS_aux (VS_val_spec (typschm, to_ast_id ctx id, ext), (l, empty_uannot)), ctx)
    )

let to_ast_outcome ctx (ev : P.outcome_spec) : outcome_spec ctx_out =
  match ev with
  | P.OV_aux (P.OV_outcome (id, typschm, outcome_args), l) ->
      let outcome_args, inner_ctx =
        List.fold_left
          (fun (args, ctx) arg ->
            let (arg, ctx), _ = to_ast_kopts ctx arg in
            (arg @ args, ctx)
          )
          ([], ctx) outcome_args
      in
      let typschm, _ = to_ast_typschm inner_ctx typschm in
      (OV_aux (OV_outcome (to_ast_id ctx id, typschm, List.rev outcome_args), l), inner_ctx)

let rec to_ast_range ctx (P.BF_aux (r, l)) =
  (* TODO add check that ranges are sensible for some definition of sensible *)
  BF_aux
    ( ( match r with
      | P.BF_single i -> BF_single (to_ast_bitfield_index_nexp ctx i)
      | P.BF_range (i1, i2) -> BF_range (to_ast_bitfield_index_nexp ctx i1, to_ast_bitfield_index_nexp ctx i2)
      | P.BF_concat (ir1, ir2) -> BF_concat (to_ast_range ctx ir1, to_ast_range ctx ir2)
      ),
      l
    )

let rec to_ast_type_union doc attrs ctx = function
  | P.Tu_aux (P.Tu_doc (doc_comment, tu), l) -> begin
      match doc with
      | Some _ -> raise (Reporting.err_general l "Union constructor has multiple documentation comments")
      | None -> to_ast_type_union (Some doc_comment) attrs ctx tu
    end
  | P.Tu_aux (P.Tu_attribute (attr, arg, tu), l) -> to_ast_type_union doc (attrs @ [(l, attr, arg)]) ctx tu
  | P.Tu_aux (P.Tu_ty_id (atyp, id), l) ->
      let typ = to_ast_typ ctx atyp in
      Tu_aux (Tu_ty_id (typ, to_ast_id ctx id), mk_def_annot ?doc ~attrs l)
  | P.Tu_aux (_, l) ->
      raise (Reporting.err_unreachable l __POS__ "Anonymous record type should have been rewritten by now")

let add_constructor id typq ctx =
  let kinds = List.map (fun kopt -> Some (unaux_kind (kopt_kind kopt))) (quant_kopts typq) in
  { ctx with type_constructors = Bindings.add id kinds ctx.type_constructors }

let anon_rec_constructor_typ record_id = function
  | P.TypQ_aux (P.TypQ_no_forall, l) -> P.ATyp_aux (P.ATyp_id record_id, Generated l)
  | P.TypQ_aux (P.TypQ_tq quants, l) -> (
      let quant_arg = function
        | P.QI_aux (P.QI_id (P.KOpt_aux (P.KOpt_kind (_, vs, _), l)), _) ->
            List.map (fun v -> P.ATyp_aux (P.ATyp_var v, Generated l)) vs
        | P.QI_aux (P.QI_constraint _, _) -> []
      in
      match List.concat (List.map quant_arg quants) with
      | [] -> P.ATyp_aux (P.ATyp_id record_id, Generated l)
      | args -> P.ATyp_aux (P.ATyp_app (record_id, args), Generated l)
    )

(* Strip attributes and doc comment from a type union *)
let rec type_union_strip = function
  | P.Tu_aux (P.Tu_attribute (attr, arg, tu), l) ->
      let unstrip, tu = type_union_strip tu in
      ((fun tu -> P.Tu_aux (P.Tu_attribute (attr, arg, unstrip tu), l)), tu)
  | P.Tu_aux (P.Tu_doc (doc, tu), l) ->
      let unstrip, tu = type_union_strip tu in
      ((fun tu -> P.Tu_aux (P.Tu_doc (doc, unstrip tu), l)), tu)
  | tu -> ((fun tu -> tu), tu)

let realize_union_anon_rec_arm union_id typq (P.Tu_aux (_, l) as tu) =
  match type_union_strip tu with
  | unstrip, (P.Tu_aux (P.Tu_ty_id _, _) as arm) -> (None, unstrip arm)
  | unstrip, P.Tu_aux (P.Tu_ty_anon_rec (fields, id), l) ->
      let open Parse_ast in
      let record_str = "_" ^ string_of_parse_id union_id ^ "_" ^ string_of_parse_id id ^ "_record" in
      let record_id = Id_aux (Id record_str, Generated l) in
      let new_arm = Tu_aux (Tu_ty_id (anon_rec_constructor_typ record_id typq, id), Generated l) in
      (Some (record_id, fields, l), unstrip new_arm)
  | _, _ -> Reporting.unreachable l __POS__ "Impossible base type union case"

let rec realize_union_anon_rec_types orig_union arms =
  match orig_union with
  | P.TD_variant (union_id, typq, _) -> begin
      match arms with
      | [] -> []
      | arm :: arms ->
          let realized =
            match realize_union_anon_rec_arm union_id typq arm with
            | Some (record_id, fields, l), new_arm ->
                (Some (P.TD_aux (P.TD_record (record_id, typq, fields), Generated l)), new_arm)
            | None, arm -> (None, arm)
          in
          realized :: realize_union_anon_rec_types orig_union arms
    end
  | _ ->
      raise
        (Reporting.err_unreachable Parse_ast.Unknown __POS__
           "Non union type-definition passed to realise_union_anon_rec_typs"
        )

let generate_enum_functions l ctx enum_id fns exps =
  let get_exp i = function
    | Some (P.E_aux (P.E_tuple exps, _)) -> List.nth exps i
    | Some exp -> exp
    | None -> Reporting.unreachable l __POS__ "get_exp called without expression"
  in
  let num_exps = function Some (P.E_aux (P.E_tuple exps, _)) -> List.length exps | Some _ -> 1 | None -> 0 in
  let num_fns = List.length fns in
  List.iter
    (fun (id, exp) ->
      let n = num_exps exp in
      if n <> num_fns then (
        let l = match exp with Some (P.E_aux (_, l)) -> l | None -> parse_id_loc id in
        raise
          (Reporting.err_general l
             (sprintf
                "Each enumeration clause for %s must define exactly %d expressions for the functions %s\n\
                 %s expressions have been given here" (string_of_id enum_id) num_fns
                (string_of_list ", " string_of_parse_id (List.map fst fns))
                (if n = 0 then "No" else if n > num_fns then "Too many" else "Too few")
             )
          )
      )
    )
    exps;
  List.mapi
    (fun i (id, typ) ->
      let typ = to_ast_typ ctx typ in
      let name = mk_id (string_of_id enum_id ^ "_" ^ string_of_parse_id id) in
      [
        mk_fundef
          [
            mk_funcl name
              (mk_pat (P_id (mk_id "arg#")))
              (mk_exp
                 (E_match
                    ( mk_exp (E_id (mk_id "arg#")),
                      List.map
                        (fun (id, exps) ->
                          let id = to_ast_id ctx id in
                          let exp = to_ast_exp ctx (get_exp i exps) in
                          mk_pexp (Pat_exp (mk_pat (P_id id), exp))
                        )
                        exps
                    )
                 )
              );
          ];
        mk_val_spec (VS_val_spec (mk_typschm (mk_typquant []) (function_typ [mk_id_typ enum_id] typ), name, None));
      ]
    )
    fns
  |> List.concat

(* When desugaring a type definition, we check that the type does not have a reserved name *)
let to_ast_reserved_type_id ctx id =
  let id = to_ast_id ctx id in
  if IdSet.mem id reserved_type_ids then begin
    match Reporting.loc_file (id_loc id) with
    | Some file when !opt_magic_hash || StringSet.mem file ctx.internal_files -> id
    | None -> id
    | Some file -> raise (Reporting.err_general (id_loc id) (sprintf "The type name %s is reserved" (string_of_id id)))
  end
  else id

let to_ast_record ctx id typq fields =
  let id = to_ast_reserved_type_id ctx id in
  let typq, typq_ctx = to_ast_typquant ctx typq in
  let fields = List.map (fun (atyp, id) -> (to_ast_typ typq_ctx atyp, to_ast_id ctx id)) fields in
  (id, typq, fields, add_constructor id typq ctx)

let rec to_ast_typedef ctx def_annot (P.TD_aux (aux, l) : P.type_def) : uannot def list ctx_out =
  match aux with
  | P.TD_abbrev (id, typq, kind, typ_arg) ->
      let id = to_ast_reserved_type_id ctx id in
      let typq, typq_ctx = to_ast_typquant ctx typq in
      begin
        match to_ast_kind kind with
        | Some kind ->
            let typ_arg = to_ast_typ_arg typq_ctx typ_arg (unaux_kind kind) in
            ( [DEF_aux (DEF_type (TD_aux (TD_abbrev (id, typq, typ_arg), (l, empty_uannot))), def_annot)],
              add_constructor id typq ctx
            )
        | None -> ([], ctx)
      end
  | P.TD_record (id, typq, fields) ->
      let id, typq, fields, ctx = to_ast_record ctx id typq fields in
      ([DEF_aux (DEF_type (TD_aux (TD_record (id, typq, fields, false), (l, empty_uannot))), def_annot)], ctx)
  | P.TD_variant (id, typq, arms) as union ->
      (* First generate auxilliary record types for anonymous records in constructors *)
      let records_and_arms = realize_union_anon_rec_types union arms in
      let rec filter_records = function
        | [] -> []
        | Some x :: xs -> x :: filter_records xs
        | None :: xs -> filter_records xs
      in
      let generated_records = filter_records (List.map fst records_and_arms) in
      let generated_records, ctx =
        List.fold_left
          (fun (prev, ctx) td ->
            let td, ctx = to_ast_typedef ctx (mk_def_annot (gen_loc l)) td in
            (prev @ td, ctx)
          )
          ([], ctx) generated_records
      in
      let arms = List.map snd records_and_arms in
      (* Now generate the AST union type *)
      let id = to_ast_reserved_type_id ctx id in
      let typq, typq_ctx = to_ast_typquant ctx typq in
      let arms = List.map (to_ast_type_union None [] (add_constructor id typq typq_ctx)) arms in
      ( [DEF_aux (DEF_type (TD_aux (TD_variant (id, typq, arms, false), (l, empty_uannot))), def_annot)]
        @ generated_records,
        add_constructor id typq ctx
      )
  | P.TD_enum (id, fns, enums) ->
      let id = to_ast_reserved_type_id ctx id in
      let fns = generate_enum_functions l ctx id fns enums in
      let enums = List.map (fun e -> to_ast_id ctx (fst e)) enums in
      ( fns @ [DEF_aux (DEF_type (TD_aux (TD_enum (id, enums, false), (l, empty_uannot))), def_annot)],
        { ctx with type_constructors = Bindings.add id [] ctx.type_constructors }
      )
  | P.TD_bitfield (id, typ, ranges) ->
      let id = to_ast_reserved_type_id ctx id in
      let typ = to_ast_typ ctx typ in
      let ranges = List.map (fun (id, range) -> (to_ast_id ctx id, to_ast_range ctx range)) ranges in
      ( [DEF_aux (DEF_type (TD_aux (TD_bitfield (id, typ, ranges), (l, empty_uannot))), def_annot)],
        { ctx with type_constructors = Bindings.add id [] ctx.type_constructors }
      )

let to_ast_rec ctx (P.Rec_aux (r, l) : P.rec_opt) : uannot rec_opt =
  Rec_aux
    ( ( match r with
      | P.Rec_none -> Rec_nonrec
      | P.Rec_measure (p, e) -> Rec_measure (to_ast_pat ctx p, to_ast_exp ctx e)
      ),
      l
    )

let to_ast_tannot_opt ctx (P.Typ_annot_opt_aux (tp, l)) : tannot_opt ctx_out =
  match tp with
  | P.Typ_annot_opt_none -> (Typ_annot_opt_aux (Typ_annot_opt_none, l), ctx)
  | P.Typ_annot_opt_some (tq, typ) ->
      let typq, ctx = to_ast_typquant ctx tq in
      (Typ_annot_opt_aux (Typ_annot_opt_some (typq, to_ast_typ ctx typ), l), ctx)

let to_ast_typschm_opt ctx (P.TypSchm_opt_aux (aux, l)) : tannot_opt ctx_out =
  match aux with
  | P.TypSchm_opt_none -> (Typ_annot_opt_aux (Typ_annot_opt_none, l), ctx)
  | P.TypSchm_opt_some (P.TypSchm_aux (P.TypSchm_ts (tq, typ), l)) ->
      let typq, ctx = to_ast_typquant ctx tq in
      (Typ_annot_opt_aux (Typ_annot_opt_some (typq, to_ast_typ ctx typ), l), ctx)

let rec to_ast_funcl doc attrs ctx (P.FCL_aux (fcl, l) : P.funcl) : uannot funcl =
  match fcl with
  | P.FCL_attribute (attr, arg, fcl) -> to_ast_funcl doc (attrs @ [(l, attr, arg)]) ctx fcl
  | P.FCL_doc (doc_comment, fcl) -> begin
      match doc with
      | Some _ -> raise (Reporting.err_general l "Function clause has multiple documentation comments")
      | None -> to_ast_funcl (Some doc_comment) attrs ctx fcl
    end
  | P.FCL_funcl (id, pexp) ->
      FCL_aux (FCL_funcl (to_ast_id ctx id, to_ast_case ctx pexp), (mk_def_annot ?doc ~attrs l, empty_uannot))

let to_ast_impl_funcls ctx (P.FCL_aux (fcl, l) : P.funcl) : uannot funcl list =
  match fcl with
  | P.FCL_funcl (id, pexp) -> (
      match StringMap.find_opt (string_of_parse_id id) ctx.target_sets with
      | Some targets ->
          List.map
            (fun target ->
              FCL_aux
                (FCL_funcl (Id_aux (Id target, parse_id_loc id), to_ast_case ctx pexp), (mk_def_annot l, empty_uannot))
            )
            targets
      | None -> [FCL_aux (FCL_funcl (to_ast_id ctx id, to_ast_case ctx pexp), (mk_def_annot l, empty_uannot))]
    )
  | _ -> raise (Reporting.err_general l "Attributes or documentation comment not permitted here")

let to_ast_fundef ctx (P.FD_aux (fd, l) : P.fundef) : uannot fundef =
  match fd with
  | P.FD_function (rec_opt, tannot_opt, _, funcls) ->
      let tannot_opt, ctx = to_ast_tannot_opt ctx tannot_opt in
      FD_aux
        (FD_function (to_ast_rec ctx rec_opt, tannot_opt, List.map (to_ast_funcl None [] ctx) funcls), (l, empty_uannot))

let rec to_ast_mpat ctx (P.MP_aux (mpat, l)) =
  MP_aux
    ( ( match mpat with
      | P.MP_lit lit -> MP_lit (to_ast_lit lit)
      | P.MP_id id -> MP_id (to_ast_id ctx id)
      | P.MP_as (mpat, id) -> MP_as (to_ast_mpat ctx mpat, to_ast_id ctx id)
      | P.MP_app (id, mpats) ->
          if mpats = [] then MP_id (to_ast_id ctx id) else MP_app (to_ast_id ctx id, List.map (to_ast_mpat ctx) mpats)
      | P.MP_vector mpats -> MP_vector (List.map (to_ast_mpat ctx) mpats)
      | P.MP_vector_concat mpats -> MP_vector_concat (List.map (to_ast_mpat ctx) mpats)
      | P.MP_vector_subrange (id, n, m) -> MP_vector_subrange (to_ast_id ctx id, n, m)
      | P.MP_tuple mpats -> MP_tuple (List.map (to_ast_mpat ctx) mpats)
      | P.MP_list mpats -> MP_list (List.map (to_ast_mpat ctx) mpats)
      | P.MP_cons (pat1, pat2) -> MP_cons (to_ast_mpat ctx pat1, to_ast_mpat ctx pat2)
      | P.MP_string_append pats -> MP_string_append (List.map (to_ast_mpat ctx) pats)
      | P.MP_typ (mpat, typ) -> MP_typ (to_ast_mpat ctx mpat, to_ast_typ ctx typ)
      | P.MP_struct fmpats ->
          MP_struct (List.map (fun (field, mpat) -> (to_ast_id ctx field, to_ast_mpat ctx mpat)) fmpats)
      ),
      (l, empty_uannot)
    )

let to_ast_mpexp ctx (P.MPat_aux (mpexp, l)) =
  match mpexp with
  | P.MPat_pat mpat -> MPat_aux (MPat_pat (to_ast_mpat ctx mpat), (l, empty_uannot))
  | P.MPat_when (mpat, exp) -> MPat_aux (MPat_when (to_ast_mpat ctx mpat, to_ast_exp ctx exp), (l, empty_uannot))

let rec to_ast_mapcl doc attrs ctx (P.MCL_aux (mapcl, l)) =
  match mapcl with
  | P.MCL_attribute (attr, arg, mcl) -> to_ast_mapcl doc (attrs @ [(l, attr, arg)]) ctx mcl
  | P.MCL_doc (doc_comment, mcl) -> begin
      match doc with
      | Some _ -> raise (Reporting.err_general l "Function clause has multiple documentation comments")
      | None -> to_ast_mapcl (Some doc_comment) attrs ctx mcl
    end
  | P.MCL_bidir (mpexp1, mpexp2) ->
      MCL_aux (MCL_bidir (to_ast_mpexp ctx mpexp1, to_ast_mpexp ctx mpexp2), (mk_def_annot ?doc ~attrs l, empty_uannot))
  | P.MCL_forwards (mpexp, exp) ->
      MCL_aux (MCL_forwards (to_ast_mpexp ctx mpexp, to_ast_exp ctx exp), (mk_def_annot ?doc ~attrs l, empty_uannot))
  | P.MCL_backwards (mpexp, exp) ->
      MCL_aux (MCL_backwards (to_ast_mpexp ctx mpexp, to_ast_exp ctx exp), (mk_def_annot ?doc ~attrs l, empty_uannot))

let to_ast_mapdef ctx (P.MD_aux (md, l) : P.mapdef) : uannot mapdef =
  match md with
  | P.MD_mapping (id, typschm_opt, mapcls) ->
      let tannot_opt, ctx = to_ast_typschm_opt ctx typschm_opt in
      MD_aux (MD_mapping (to_ast_id ctx id, tannot_opt, List.map (to_ast_mapcl None [] ctx) mapcls), (l, empty_uannot))

let to_ast_dec ctx (P.DEC_aux (regdec, l)) =
  DEC_aux
    ( ( match regdec with
      | P.DEC_reg (typ, id, opt_exp) ->
          let opt_exp = match opt_exp with None -> None | Some exp -> Some (to_ast_exp ctx exp) in
          DEC_reg (to_ast_typ ctx typ, to_ast_id ctx id, opt_exp)
      ),
      (l, empty_uannot)
    )

let to_ast_scattered ctx (P.SD_aux (aux, l)) =
  let extra_def, aux, ctx =
    match aux with
    | P.SD_function (rec_opt, tannot_opt, _, id) ->
        let tannot_opt, _ = to_ast_tannot_opt ctx tannot_opt in
        (None, SD_function (to_ast_rec ctx rec_opt, tannot_opt, to_ast_id ctx id), ctx)
    | P.SD_funcl funcl -> (None, SD_funcl (to_ast_funcl None [] ctx funcl), ctx)
    | P.SD_variant (id, parse_typq) ->
        let id = to_ast_id ctx id in
        let typq, typq_ctx = to_ast_typquant ctx parse_typq in
        ( None,
          SD_variant (id, typq),
          add_constructor id typq { ctx with scattereds = Bindings.add id (parse_typq, typq_ctx) ctx.scattereds }
        )
    | P.SD_unioncl (union_id, tu) ->
        let id = to_ast_id ctx union_id in
        begin
          match Bindings.find_opt id ctx.scattereds with
          | Some (typq, scattered_ctx) ->
              let anon_rec_opt, tu = realize_union_anon_rec_arm union_id typq tu in
              let extra_def, scattered_ctx =
                match anon_rec_opt with
                | Some (record_id, fields, l) ->
                    let l = gen_loc l in
                    let record_id, typq, fields, scattered_ctx = to_ast_record scattered_ctx record_id typq fields in
                    ( Some
                        (DEF_aux
                           ( DEF_scattered
                               (SD_aux (SD_internal_unioncl_record (id, record_id, typq, fields), (l, empty_uannot))),
                             mk_def_annot l
                           )
                        ),
                      scattered_ctx
                    )
                | None -> (None, scattered_ctx)
              in
              let tu = to_ast_type_union None [] scattered_ctx tu in
              (extra_def, SD_unioncl (id, tu), ctx)
          | None -> raise (Reporting.err_typ l ("No scattered union declaration found for " ^ string_of_id id))
        end
    | P.SD_end id -> (None, SD_end (to_ast_id ctx id), ctx)
    | P.SD_mapping (id, tannot_opt) ->
        let id = to_ast_id ctx id in
        let tannot_opt, _ = to_ast_tannot_opt ctx tannot_opt in
        (None, SD_mapping (id, tannot_opt), ctx)
    | P.SD_mapcl (id, mapcl) ->
        let id = to_ast_id ctx id in
        let mapcl = to_ast_mapcl None [] ctx mapcl in
        (None, SD_mapcl (id, mapcl), ctx)
    | P.SD_enum id ->
        let id = to_ast_id ctx id in
        (None, SD_enum id, ctx)
    | P.SD_enumcl (id, member) ->
        let id = to_ast_id ctx id in
        let member = to_ast_id ctx member in
        (None, SD_enumcl (id, member), ctx)
  in
  (extra_def, SD_aux (aux, (l, empty_uannot)), ctx)

let to_ast_prec = function P.Infix -> Infix | P.InfixL -> InfixL | P.InfixR -> InfixR

let to_ast_subst ctx = function
  | P.IS_aux (P.IS_id (id_from, id_to), l) -> IS_aux (IS_id (to_ast_id ctx id_from, to_ast_id ctx id_to), l)
  | P.IS_aux (P.IS_typ (kid, typ), l) -> IS_aux (IS_typ (to_ast_var kid, to_ast_typ ctx typ), l)

let to_ast_loop_measure ctx = function
  | P.Loop (P.While, exp) -> Loop (While, to_ast_exp ctx exp)
  | P.Loop (P.Until, exp) -> Loop (Until, to_ast_exp ctx exp)

(* Annotations on some scattered constructs will not be preserved after de-scattering, so warn about this *)
let check_annotation (DEF_aux (aux, def_annot)) =
  if Option.is_some def_annot.doc_comment || not (Util.list_empty def_annot.attrs) then (
    match aux with
    | DEF_scattered (SD_aux ((SD_function _ | SD_mapping _ | SD_end _), _)) ->
        Reporting.warn "" def_annot.loc "Documentation comments and attributes will not be preserved on this definition"
    | _ -> ()
  )

let rec to_ast_def doc attrs ctx (P.DEF_aux (def, l)) : uannot def list ctx_out =
  let annot = mk_def_annot ?doc ~attrs l in
  match def with
  | P.DEF_attribute (attr, arg, def) -> to_ast_def doc (attrs @ [(l, attr, arg)]) ctx def
  | P.DEF_doc (doc_comment, def) -> begin
      match doc with
      | Some _ -> raise (Reporting.err_general l "Toplevel definition has multiple documentation comments")
      | None -> to_ast_def (Some doc_comment) attrs ctx def
    end
  | P.DEF_overload (id, ids) -> ([DEF_aux (DEF_overload (to_ast_id ctx id, List.map (to_ast_id ctx) ids), annot)], ctx)
  | P.DEF_fixity (prec, n, op) ->
      let op = to_ast_id ctx op in
      let prec = to_ast_prec prec in
      ( [DEF_aux (DEF_fixity (prec, n, op), annot)],
        { ctx with fixities = Bindings.add op (prec, Big_int.to_int n) ctx.fixities }
      )
  | P.DEF_type t_def -> to_ast_typedef ctx annot t_def
  | P.DEF_fundef f_def ->
      let fd = to_ast_fundef ctx f_def in
      ([DEF_aux (DEF_fundef fd, annot)], ctx)
  | P.DEF_mapdef m_def ->
      let md = to_ast_mapdef ctx m_def in
      ([DEF_aux (DEF_mapdef md, annot)], ctx)
  | P.DEF_impl funcl ->
      let funcls = to_ast_impl_funcls ctx funcl in
      (List.map (fun funcl -> DEF_aux (DEF_impl funcl, annot)) funcls, ctx)
  | P.DEF_let lb ->
      let lb = to_ast_letbind ctx lb in
      ([DEF_aux (DEF_let lb, annot)], ctx)
  | P.DEF_val val_spec ->
      let vs, ctx = to_ast_spec ctx val_spec in
      ([DEF_aux (DEF_val vs, annot)], ctx)
  | P.DEF_outcome (outcome_spec, defs) ->
      let outcome_spec, inner_ctx = to_ast_outcome ctx outcome_spec in
      let defs, _ =
        List.fold_left
          (fun (defs, ctx) def ->
            let def, ctx = to_ast_def doc attrs ctx def in
            (def @ defs, ctx)
          )
          ([], inner_ctx) defs
      in
      ([DEF_aux (DEF_outcome (outcome_spec, List.rev defs), annot)], ctx)
  | P.DEF_instantiation (id, substs) ->
      let id = to_ast_id ctx id in
      ( [
          DEF_aux
            (DEF_instantiation (IN_aux (IN_id id, (id_loc id, empty_uannot)), List.map (to_ast_subst ctx) substs), annot);
        ],
        ctx
      )
  | P.DEF_default typ_spec ->
      let default, ctx = to_ast_default ctx typ_spec in
      ([DEF_aux (DEF_default default, annot)], ctx)
  | P.DEF_register dec ->
      let d = to_ast_dec ctx dec in
      ([DEF_aux (DEF_register d, annot)], ctx)
  | P.DEF_pragma ("sail_internal", arg) -> begin
      match Reporting.loc_file l with
      | Some file ->
          ( [DEF_aux (DEF_pragma ("sail_internal", arg, l), annot)],
            { ctx with internal_files = StringSet.add file ctx.internal_files }
          )
      | None -> ([DEF_aux (DEF_pragma ("sail_internal", arg, l), annot)], ctx)
    end
  | P.DEF_pragma ("target_set", arg) ->
      let args = String.split_on_char ' ' arg |> List.filter (fun s -> String.length s > 0) in
      begin
        match args with
        | set :: targets ->
            ( [DEF_aux (DEF_pragma ("target_set", arg, l), annot)],
              { ctx with target_sets = StringMap.add set targets ctx.target_sets }
            )
        | [] -> raise (Reporting.err_general l "No arguments provided to target set directive")
      end
  | P.DEF_pragma (pragma, arg) -> ([DEF_aux (DEF_pragma (pragma, arg, l), annot)], ctx)
  | P.DEF_internal_mutrec _ ->
      (* Should never occur because of remove_mutrec *)
      raise (Reporting.err_unreachable l __POS__ "Internal mutual block found when processing scattered defs")
  | P.DEF_scattered sdef ->
      let extra_def, sdef, ctx = to_ast_scattered ctx sdef in
      ([DEF_aux (DEF_scattered sdef, annot)] @ Option.to_list extra_def, ctx)
  | P.DEF_measure (id, pat, exp) ->
      ([DEF_aux (DEF_measure (to_ast_id ctx id, to_ast_pat ctx pat, to_ast_exp ctx exp), annot)], ctx)
  | P.DEF_loop_measures (id, measures) ->
      ([DEF_aux (DEF_loop_measures (to_ast_id ctx id, List.map (to_ast_loop_measure ctx) measures), annot)], ctx)

let rec remove_mutrec = function
  | [] -> []
  | P.DEF_aux (P.DEF_internal_mutrec fundefs, _) :: defs ->
      List.map (fun (P.FD_aux (_, l) as fdef) -> P.DEF_aux (P.DEF_fundef fdef, l)) fundefs @ remove_mutrec defs
  | def :: defs -> def :: remove_mutrec defs

let to_ast ctx (P.Defs files) =
  let to_ast_defs ctx (_, defs) =
    let defs = remove_mutrec defs in
    let defs, ctx =
      List.fold_left
        (fun (defs, ctx) def ->
          let new_defs, ctx = to_ast_def None [] ctx def in
          List.iter check_annotation new_defs;
          (new_defs @ defs, ctx)
        )
        ([], ctx) defs
    in
    (List.rev defs, ctx)
  in
  let wrap_file file defs =
    [mk_def (DEF_pragma ("file_start", file, P.Unknown))] @ defs @ [mk_def (DEF_pragma ("file_end", file, P.Unknown))]
  in
  let defs, ctx =
    List.fold_left
      (fun (defs, ctx) file ->
        let defs', ctx = to_ast_defs ctx file in
        (defs @ wrap_file (fst file) defs', ctx)
      )
      ([], ctx) files
  in
  ({ defs; comments = [] }, ctx)

let initial_ctx =
  {
    type_constructors =
      List.fold_left
        (fun m (k, v) -> Bindings.add (mk_id k) v m)
        Bindings.empty
        [
          ("bool", []);
          ("nat", []);
          ("int", []);
          ("unit", []);
          ("bit", []);
          ("string", []);
          ("real", []);
          ("list", [Some K_type]);
          ("register", [Some K_type]);
          ("range", [Some K_int; Some K_int]);
          ("bitvector", [Some K_int; None]);
          ("vector", [Some K_int; None; Some K_type]);
          ("atom", [Some K_int]);
          ("implicit", [Some K_int]);
          ("itself", [Some K_int]);
          ("not", [Some K_bool]);
        ];
    kinds = KBindings.empty;
    scattereds = Bindings.empty;
    fixities =
      List.fold_left
        (fun m (k, prec, level) -> Bindings.add (mk_id k) (prec, level) m)
        Bindings.empty
        [
          ("^", InfixR, 8);
          ("|", InfixR, 2);
          ("&", InfixR, 3);
          ("==", Infix, 4);
          ("!=", Infix, 4);
          ("/", InfixL, 7);
          ("%", InfixL, 7);
        ];
    internal_files = StringSet.empty;
    target_sets = StringMap.empty;
  }

let exp_of_string str =
  try
    let exp = Parser.exp_eof Lexer.token (Lexing.from_string str) in
    to_ast_exp initial_ctx exp
  with Parser.Error -> Reporting.unreachable Parse_ast.Unknown __POS__ ("Failed to parse " ^ str)

let typschm_of_string str =
  try
    let typschm = Parser.typschm_eof Lexer.token (Lexing.from_string str) in
    let typschm, _ = to_ast_typschm initial_ctx typschm in
    typschm
  with Parser.Error -> Reporting.unreachable Parse_ast.Unknown __POS__ ("Failed to parse " ^ str)

let typ_of_string str =
  try
    let typ = Parser.typ_eof Lexer.token (Lexing.from_string str) in
    let typ = to_ast_typ initial_ctx typ in
    typ
  with Parser.Error -> Reporting.unreachable Parse_ast.Unknown __POS__ ("Failed to parse " ^ str)

let constraint_of_string str =
  try
    let atyp = Parser.typ_eof Lexer.token (Lexing.from_string str) in
    to_ast_constraint initial_ctx atyp
  with Parser.Error -> Reporting.unreachable Parse_ast.Unknown __POS__ ("Failed to parse " ^ str)

let extern_of_string ?(pure = false) id str =
  VS_val_spec (typschm_of_string str, id, Some { pure; bindings = [("_", string_of_id id)] }) |> mk_val_spec

let val_spec_of_string id str = mk_val_spec (VS_val_spec (typschm_of_string str, id, None))

let quant_item_param = function
  | QI_aux (QI_id kopt, _) when is_int_kopt kopt -> [prepend_id "atom_" (id_of_kid (kopt_kid kopt))]
  | QI_aux (QI_id kopt, _) when is_typ_kopt kopt -> [prepend_id "typ_" (id_of_kid (kopt_kid kopt))]
  | _ -> []
let quant_item_typ = function
  | QI_aux (QI_id kopt, _) when is_int_kopt kopt -> [atom_typ (nvar (kopt_kid kopt))]
  | QI_aux (QI_id kopt, _) when is_typ_kopt kopt -> [mk_typ (Typ_var (kopt_kid kopt))]
  | _ -> []
let quant_item_arg = function
  | QI_aux (QI_id kopt, _) when is_int_kopt kopt -> [mk_typ_arg (A_nexp (nvar (kopt_kid kopt)))]
  | QI_aux (QI_id kopt, _) when is_typ_kopt kopt -> [mk_typ_arg (A_typ (mk_typ (Typ_var (kopt_kid kopt))))]
  | _ -> []
let undefined_typschm id typq =
  let qis = quant_items typq in
  if qis = [] then mk_typschm typq (function_typ [unit_typ] (mk_typ (Typ_id id)))
  else (
    let arg_typs = List.concat (List.map quant_item_typ qis) in
    let ret_typ = app_typ id (List.concat (List.map quant_item_arg qis)) in
    mk_typschm typq (function_typ arg_typs ret_typ)
  )

let have_undefined_builtins = ref false

let undefined_builtin_val_specs =
  [
    extern_of_string (mk_id "internal_pick") "forall ('a:Type). list('a) -> 'a";
    extern_of_string (mk_id "undefined_bool") "unit -> bool";
    extern_of_string (mk_id "undefined_bit") "unit -> bit";
    extern_of_string (mk_id "undefined_int") "unit -> int";
    extern_of_string (mk_id "undefined_nat") "unit -> nat";
    extern_of_string (mk_id "undefined_real") "unit -> real";
    extern_of_string (mk_id "undefined_string") "unit -> string";
    extern_of_string (mk_id "undefined_list") "forall ('a:Type). 'a -> list('a)";
    extern_of_string (mk_id "undefined_range") "forall 'n 'm. (atom('n), atom('m)) -> range('n,'m)";
    extern_of_string (mk_id "undefined_vector")
      "forall 'n ('a:Type) ('ord : Order). (atom('n), 'a) -> vector('n, 'ord,'a)";
    extern_of_string (mk_id "undefined_bitvector") "forall 'n. atom('n) -> bitvector('n)";
    extern_of_string (mk_id "undefined_unit") "unit -> unit";
  ]

let generate_undefineds vs_ids defs =
  let undefined_builtins =
    if !have_undefined_builtins then []
    else begin
      have_undefined_builtins := true;
      List.filter (fun def -> IdSet.is_empty (IdSet.inter vs_ids (ids_of_def def))) undefined_builtin_val_specs
    end
  in
  let undefined_tu = function
    | Tu_aux (Tu_ty_id (Typ_aux (Typ_tuple typs, _), id), _) ->
        mk_exp (E_app (id, List.map (fun typ -> mk_exp (E_typ (typ, mk_lit_exp L_undef))) typs))
    | Tu_aux (Tu_ty_id (typ, id), _) -> mk_exp (E_app (id, [mk_exp (E_typ (typ, mk_lit_exp L_undef))]))
  in
  let p_tup = function [pat] -> pat | pats -> mk_pat (P_tuple pats) in
  let undefined_union id typq tus =
    let pat =
      p_tup (quant_items typq |> List.map quant_item_param |> List.concat |> List.map (fun id -> mk_pat (P_id id)))
    in
    let body =
      if !opt_fast_undefined && List.length tus > 0 then undefined_tu (List.hd tus)
      else (
        (* Deduplicate arguments for each constructor to keep definitions
           manageable. *)
        let extract_tu = function
          | Tu_aux (Tu_ty_id (Typ_aux (Typ_tuple typs, _), id), _) -> (id, typs)
          | Tu_aux (Tu_ty_id (typ, id), _) -> (id, [typ])
        in
        let record_arg_typs m (_, typs) =
          let m' =
            List.fold_left
              (fun m typ -> TypMap.add typ (1 + try TypMap.find typ m with Not_found -> 0) m)
              TypMap.empty typs
          in
          TypMap.merge
            (fun _ x y -> match (x, y) with Some m, Some n -> Some (max m n) | None, x -> x | x, None -> x)
            m m'
        in
        let make_undef_var typ n (i, lbs, m) =
          let j = i + n in
          let rec aux k =
            if k = j then []
            else (
              let v = mk_id ("u_" ^ string_of_int k) in
              mk_letbind (mk_pat (P_typ (typ, mk_pat (P_id v)))) (mk_lit_exp L_undef) :: aux (k + 1)
            )
          in
          (j, aux i @ lbs, TypMap.add typ i m)
        in
        let make_constr m (id, typs) =
          let args, _ =
            List.fold_right
              (fun typ (acc, m) ->
                let i = TypMap.find typ m in
                (mk_exp (E_id (mk_id ("u_" ^ string_of_int i))) :: acc, TypMap.add typ (i + 1) m)
              )
              typs ([], m)
          in
          mk_exp (E_app (id, args))
        in
        let constr_args = List.map extract_tu tus in
        let typs_needed = List.fold_left record_arg_typs TypMap.empty constr_args in
        let _, letbinds, typ_to_var = TypMap.fold make_undef_var typs_needed (0, [], TypMap.empty) in
        List.fold_left
          (fun e lb -> mk_exp (E_let (lb, e)))
          (mk_exp (E_app (mk_id "internal_pick", [mk_exp (E_list (List.map (make_constr typ_to_var) constr_args))])))
          letbinds
      )
    in
    ( mk_val_spec (VS_val_spec (undefined_typschm id typq, prepend_id "undefined_" id, None)),
      mk_fundef [mk_funcl (prepend_id "undefined_" id) pat body]
    )
  in
  let undefined_td = function
    | TD_enum (id, ids, _) when not (IdSet.mem (prepend_id "undefined_" id) vs_ids) ->
        let typschm = typschm_of_string ("unit -> " ^ string_of_id id) in
        [
          mk_val_spec (VS_val_spec (typschm, prepend_id "undefined_" id, None));
          mk_fundef
            [
              mk_funcl (prepend_id "undefined_" id)
                (mk_pat (P_lit (mk_lit L_unit)))
                ( if !opt_fast_undefined && List.length ids > 0 then mk_exp (E_id (List.hd ids))
                  else
                    mk_exp (E_app (mk_id "internal_pick", [mk_exp (E_list (List.map (fun id -> mk_exp (E_id id)) ids))]))
                );
            ];
        ]
    | TD_record (id, typq, fields, _) when not (IdSet.mem (prepend_id "undefined_" id) vs_ids) ->
        let pat =
          p_tup (quant_items typq |> List.map quant_item_param |> List.concat |> List.map (fun id -> mk_pat (P_id id)))
        in
        [
          mk_val_spec (VS_val_spec (undefined_typschm id typq, prepend_id "undefined_" id, None));
          mk_fundef
            [
              mk_funcl (prepend_id "undefined_" id) pat
                (mk_exp (E_struct (List.map (fun (_, id) -> mk_fexp id (mk_lit_exp L_undef)) fields)));
            ];
        ]
    | TD_variant (id, typq, tus, _) when not (IdSet.mem (prepend_id "undefined_" id) vs_ids) ->
        let vs, def = undefined_union id typq tus in
        [vs; def]
    | _ -> []
  in
  let undefined_scattered id typq =
    let tus = get_scattered_union_clauses id defs in
    undefined_union id typq tus
  in
  let rec undefined_defs = function
    | (DEF_aux (DEF_type (TD_aux (td_aux, _)), _) as def) :: defs -> (def :: undefined_td td_aux) @ undefined_defs defs
    (* The function definition must come after the scattered type definition is complete, so put it at the end. *)
    | (DEF_aux (DEF_scattered (SD_aux (SD_variant (id, typq), _)), _) as def) :: defs ->
        let vs, fn = undefined_scattered id typq in
        (def :: vs :: undefined_defs defs) @ [fn]
    | (DEF_aux (DEF_scattered (SD_aux (SD_internal_unioncl_record (_, id, typq, fields), _)), _) as def) :: defs
      when not (IdSet.mem (prepend_id "undefined_" id) vs_ids) ->
        let pat =
          p_tup (quant_items typq |> List.map quant_item_param |> List.concat |> List.map (fun id -> mk_pat (P_id id)))
        in
        let vs = mk_val_spec (VS_val_spec (undefined_typschm id typq, prepend_id "undefined_" id, None)) in
        let fn =
          mk_fundef
            [
              mk_funcl (prepend_id "undefined_" id) pat
                (mk_exp (E_struct (List.map (fun (_, id) -> mk_fexp id (mk_lit_exp L_undef)) fields)));
            ]
        in
        def :: vs :: fn :: undefined_defs defs
    | def :: defs -> def :: undefined_defs defs
    | [] -> []
  in
  undefined_builtins @ undefined_defs defs

let rec get_uninitialized_registers = function
  | DEF_aux (DEF_register (DEC_aux (DEC_reg (typ, id, None), _)), _) :: defs ->
      (typ, id) :: get_uninitialized_registers defs
  | _ :: defs -> get_uninitialized_registers defs
  | [] -> []

let generate_initialize_registers vs_ids defs =
  let regs = get_uninitialized_registers defs in
  let initialize_registers =
    if IdSet.mem (mk_id "initialize_registers") vs_ids then []
    else if regs = [] then
      [
        val_spec_of_string (mk_id "initialize_registers") "unit -> unit";
        mk_fundef
          [mk_funcl (mk_id "initialize_registers") (mk_pat (P_lit (mk_lit L_unit))) (mk_exp (E_lit (mk_lit L_unit)))];
      ]
    else
      [
        val_spec_of_string (mk_id "initialize_registers") "unit -> unit";
        mk_fundef
          [
            mk_funcl (mk_id "initialize_registers")
              (mk_pat (P_lit (mk_lit L_unit)))
              (mk_exp
                 (E_block (List.map (fun (typ, id) -> mk_exp (E_assign (mk_lexp (LE_id id), mk_lit_exp L_undef))) regs))
              );
          ];
      ]
  in
  defs @ initialize_registers

let generate_enum_functions vs_ids defs =
  let rec gen_enums acc = function
    | (DEF_aux (DEF_type (TD_aux (TD_enum (id, elems, _), _)), def_annot) as enum) :: defs -> begin
        match get_def_attribute "no_enum_functions" def_annot with
        | Some _ -> gen_enums (enum :: acc) defs
        | None ->
            let enum_val_spec name quants typ =
              mk_val_spec (VS_val_spec (mk_typschm (mk_typquant quants) typ, name, None))
            in
            let range_constraint kid =
              nc_and (nc_lteq (nint 0) (nvar kid)) (nc_lteq (nvar kid) (nint (List.length elems - 1)))
            in

            (* Create a function that converts a number to an enum. *)
            let to_enum =
              let kid = mk_kid "e" in
              let name = append_id id "_of_num" in
              let pexp n id =
                let pat =
                  if n = List.length elems - 1 then mk_pat P_wild else mk_pat (P_lit (mk_lit (L_num (Big_int.of_int n))))
                in
                mk_pexp (Pat_exp (pat, mk_exp (E_id id)))
              in
              let funcl =
                mk_funcl name
                  (mk_pat (P_id (mk_id "arg#")))
                  (mk_exp (E_match (mk_exp (E_id (mk_id "arg#")), List.mapi pexp elems)))
              in
              if IdSet.mem name vs_ids then []
              else
                [
                  enum_val_spec name
                    [mk_qi_id K_int kid; mk_qi_nc (range_constraint kid)]
                    (function_typ [atom_typ (nvar kid)] (mk_typ (Typ_id id)));
                  mk_fundef [funcl];
                ]
            in

            (* Create a function that converts from an enum to a number. *)
            let from_enum =
              let kid = mk_kid "e" in
              let to_typ = mk_typ (Typ_exist ([mk_kopt K_int kid], range_constraint kid, atom_typ (nvar kid))) in
              let name = prepend_id "num_of_" id in
              let pexp n id = mk_pexp (Pat_exp (mk_pat (P_id id), mk_lit_exp (L_num (Big_int.of_int n)))) in
              let funcl =
                mk_funcl name
                  (mk_pat (P_id (mk_id "arg#")))
                  (mk_exp (E_match (mk_exp (E_id (mk_id "arg#")), List.mapi pexp elems)))
              in
              if IdSet.mem name vs_ids then []
              else [enum_val_spec name [] (function_typ [mk_typ (Typ_id id)] to_typ); mk_fundef [funcl]]
            in
            gen_enums (List.rev ((enum :: to_enum) @ from_enum) @ acc) defs
      end
    | def :: defs -> gen_enums (def :: acc) defs
    | [] -> List.rev acc
  in
  gen_enums [] defs

let incremental_ctx = ref initial_ctx

let process_ast ?(generate = true) ast =
  let ast, ctx = to_ast !incremental_ctx ast in
  incremental_ctx := ctx;
  let vs_ids = val_spec_ids ast.defs in
  if (not !opt_undefined_gen) && generate then { ast with defs = generate_enum_functions vs_ids ast.defs }
  else if generate then
    {
      ast with
      defs =
        ast.defs |> generate_undefineds vs_ids |> generate_enum_functions vs_ids |> generate_initialize_registers vs_ids;
    }
  else ast

let ast_of_def_string_with ocaml_pos f str =
  let lexbuf = Lexing.from_string str in
  let internal = !opt_magic_hash in
  opt_magic_hash := true;
  lexbuf.lex_curr_p <- { pos_fname = ""; pos_lnum = 1; pos_bol = 0; pos_cnum = 0 };
  let def = Parser.def_eof Lexer.token lexbuf in
  let ast = Reporting.forbid_errors ocaml_pos (fun ast -> process_ast ~generate:false ast) (P.Defs [("", f [def])]) in
  opt_magic_hash := internal;
  ast

let ast_of_def_string ocaml_pos str = ast_of_def_string_with ocaml_pos (fun x -> x) str

let defs_of_string ocaml_pos str = (ast_of_def_string ocaml_pos str).defs

let get_lexbuf f =
  let in_chan = open_in f in
  let lexbuf = Lexing.from_channel in_chan in
  lexbuf.Lexing.lex_curr_p <- { Lexing.pos_fname = f; Lexing.pos_lnum = 1; Lexing.pos_bol = 0; Lexing.pos_cnum = 0 };
  (lexbuf, in_chan)

let parse_file ?loc:(l = Parse_ast.Unknown) (f : string) : Lexer.comment list * Parse_ast.def list =
  try
    let lexbuf, in_chan = get_lexbuf f in
    begin
      try
        Lexer.comments := [];
        let defs = Parser.file Lexer.token lexbuf in
        close_in in_chan;
        (!Lexer.comments, defs)
      with Parser.Error ->
        let pos = Lexing.lexeme_start_p lexbuf in
        let tok = Lexing.lexeme lexbuf in
        raise (Reporting.err_syntax pos ("current token: " ^ tok))
    end
  with Sys_error err -> raise (Reporting.err_general l err)

let get_lexbuf_from_string f s =
  let lexbuf = Lexing.from_string s in
  lexbuf.Lexing.lex_curr_p <- { Lexing.pos_fname = f; Lexing.pos_lnum = 1; Lexing.pos_bol = 0; Lexing.pos_cnum = 0 };
  lexbuf

let parse_file_from_string ~filename:f ~contents:s =
  let lexbuf = get_lexbuf_from_string f s in
  try
    Lexer.comments := [];
    let defs = Parser.file Lexer.token lexbuf in
    (!Lexer.comments, defs)
  with Parser.Error ->
    let pos = Lexing.lexeme_start_p lexbuf in
    let tok = Lexing.lexeme lexbuf in
    raise (Reporting.err_syntax pos ("current token: " ^ tok))
