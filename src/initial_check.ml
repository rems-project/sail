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
let opt_enum_casts = ref false

type ctx = {
    kinds : kind_aux KBindings.t;
    type_constructors : (kind_aux list) Bindings.t;
    scattereds : ctx Bindings.t;
  }

let string_of_parse_id_aux = function
  | P.Id v -> v
  | P.Operator v -> v

let string_of_parse_id (P.Id_aux (id, l)) = string_of_parse_id_aux id

let parse_id_loc (P.Id_aux (_, l)) = l

let string_contains str char =
  try (ignore (String.index str char); true) with
  | Not_found -> false

let to_ast_var (P.Kid_aux (P.Var v, l)) = Kid_aux (Var v, l)

let to_ast_kind (P.K_aux (k, l)) =
  match k with
  | P.K_type  -> K_aux (K_type, l)
  | P.K_int   -> K_aux (K_int, l)
  | P.K_order -> K_aux (K_order, l)
  | P.K_bool  -> K_aux (K_bool, l)

let to_ast_id (P.Id_aux(id, l)) =
  if string_contains (string_of_parse_id_aux id) '#' && not (!opt_magic_hash) then
    raise (Reporting.err_general l "Identifier contains hash character and -dmagic_hash is unset")
  else
    Id_aux ((match id with
             | P.Id x -> Id x
             | P.Operator x -> Operator x),
            l)

let to_ast_var (P.Kid_aux (P.Var v, l)) = Kid_aux (Var v, l)

let to_ast_effects = function
  | P.ATyp_aux (P.ATyp_set effects, l) ->
     let to_effect (P.BE_aux (e, l)) =
       BE_aux ((match e with
                | P.BE_barr   -> BE_barr
                | P.BE_rreg   -> BE_rreg
                | P.BE_wreg   -> BE_wreg
                | P.BE_rmem   -> BE_rmem
                | P.BE_rmemt  -> BE_rmemt
                | P.BE_wmem   -> BE_wmem
                | P.BE_wmv    -> BE_wmv
                | P.BE_wmvt   -> BE_wmvt
                | P.BE_eamem  -> BE_eamem
                | P.BE_exmem  -> BE_exmem
                | P.BE_depend -> BE_depend
                | P.BE_undef  -> BE_undef
                | P.BE_unspec -> BE_unspec
                | P.BE_nondet -> BE_nondet
                | P.BE_escape -> BE_escape
                | P.BE_config -> BE_config),
               l)
     in
     Effect_aux (Effect_set (List.map to_effect effects), l)
  | P.ATyp_aux (_, l) ->
     raise (Reporting.err_typ l "Invalid effect set")

(* Used for error messages involving lists of kinds *)
let format_kind_aux_list = function
  | [kind] -> string_of_kind_aux kind
  | kinds -> "(" ^ Util.string_of_list ", " string_of_kind_aux kinds ^ ")"

let to_ast_kopts ctx (P.KOpt_aux (aux, l)) =
  let mk_kopt v k =
    let v = to_ast_var v in
    let k = to_ast_kind k in
    KOpt_aux (KOpt_kind (k, v), l), { ctx with kinds = KBindings.add v (unaux_kind k) ctx.kinds }
  in
  match aux with
  | P.KOpt_kind (attr, vs, None) ->
     let k = P.K_aux (P.K_int, gen_loc l) in
     List.fold_left (fun (kopts, ctx) v -> let kopt, ctx = mk_kopt v k in (kopt :: kopts, ctx)) ([], ctx) vs, attr
  | P.KOpt_kind (attr, vs, Some k) ->
     List.fold_left (fun (kopts, ctx) v -> let kopt, ctx = mk_kopt v k in (kopt :: kopts, ctx)) ([], ctx) vs, attr

let rec to_ast_typ ctx (P.ATyp_aux (aux, l)) =
  let aux = match aux with
    | P.ATyp_id id -> Typ_id (to_ast_id id)
    | P.ATyp_var v -> Typ_var (to_ast_var v)
    | P.ATyp_fn (from_typ, to_typ, effects) ->
       let from_typs = match from_typ with
         | P.ATyp_aux (P.ATyp_tup typs, _) ->
            List.map (to_ast_typ ctx) typs
         | _ -> [to_ast_typ ctx from_typ]
       in
       Typ_fn (from_typs, to_ast_typ ctx to_typ, to_ast_effects effects)
    | P.ATyp_bidir (typ1, typ2, effects) -> Typ_bidir (to_ast_typ ctx typ1, to_ast_typ ctx typ2, to_ast_effects effects)
    | P.ATyp_tup typs -> Typ_tup (List.map (to_ast_typ ctx) typs)
    | P.ATyp_app (P.Id_aux (P.Id "int", il), [n]) ->
       Typ_app (Id_aux (Id "atom", il), [to_ast_typ_arg ctx n K_int])
    | P.ATyp_app (P.Id_aux (P.Id "bool", il), [n]) ->
       Typ_app (Id_aux (Id "atom_bool", il), [to_ast_typ_arg ctx n K_bool])
    | P.ATyp_app (id, args) ->
       let id = to_ast_id id in
       begin match Bindings.find_opt id ctx.type_constructors with
       | None -> raise (Reporting.err_typ l (sprintf "Could not find type constructor %s" (string_of_id id)))
       | Some kinds when List.length args <> List.length kinds ->
          raise (Reporting.err_typ l (sprintf "%s : %s -> Type expected %d arguments, given %d"
                                              (string_of_id id) (format_kind_aux_list kinds)
                                              (List.length kinds) (List.length args)))
       | Some kinds ->
          Typ_app (id, List.map2 (to_ast_typ_arg ctx) args kinds)
       end
    | P.ATyp_exist (kopts, nc, atyp) ->
       let kopts, ctx =
         List.fold_right (fun kopt (kopts, ctx) ->
             let (kopts', ctx), attr = to_ast_kopts ctx kopt in
             match attr with
             | None ->
                kopts' @ kopts, ctx
             | Some attr ->
                raise (Reporting.err_typ l (sprintf "Attribute %s cannot appear within an existential type" attr))
           ) kopts ([], ctx)
       in
       Typ_exist (kopts, to_ast_constraint ctx nc, to_ast_typ ctx atyp)
    | P.ATyp_base (id, kind, nc) ->
       raise (Reporting.err_unreachable l __POS__ "TODO")
    | _ -> raise (Reporting.err_typ l "Invalid type")
  in
  Typ_aux (aux, l)

and to_ast_typ_arg ctx (ATyp_aux (_, l) as atyp) = function
  | K_type  -> A_aux (A_typ (to_ast_typ ctx atyp), l)
  | K_int   -> A_aux (A_nexp (to_ast_nexp ctx atyp), l)
  | K_order -> A_aux (A_order (to_ast_order ctx atyp), l)
  | K_bool  -> A_aux (A_bool (to_ast_constraint ctx atyp), l)

and to_ast_nexp ctx (P.ATyp_aux (aux, l)) =
  let aux = match aux with
    | P.ATyp_id id -> Nexp_id (to_ast_id id)
    | P.ATyp_var v -> Nexp_var (to_ast_var v)
    | P.ATyp_lit (P.L_aux (P.L_num c, _)) -> Nexp_constant c
    | P.ATyp_sum (t1, t2) -> Nexp_sum (to_ast_nexp ctx t1, to_ast_nexp ctx t2)
    | P.ATyp_exp t1 -> Nexp_exp (to_ast_nexp ctx t1)
    | P.ATyp_neg t1 -> Nexp_neg (to_ast_nexp ctx t1)
    | P.ATyp_times (t1, t2) -> Nexp_times (to_ast_nexp ctx t1, to_ast_nexp ctx t2)
    | P.ATyp_minus (t1, t2) -> Nexp_minus (to_ast_nexp ctx t1, to_ast_nexp ctx t2)
    | P.ATyp_app (id, ts) -> Nexp_app (to_ast_id id, List.map (to_ast_nexp ctx) ts)
    | _ -> raise (Reporting.err_typ l "Invalid numeric expression in type")
  in
  Nexp_aux (aux, l)

and to_ast_bitfield_index_nexp (P.ATyp_aux (aux, l)) =
  let aux = match aux with
    | P.ATyp_id id -> Nexp_id (to_ast_id id)
    | P.ATyp_lit (P.L_aux (P.L_num c, _)) -> Nexp_constant c
    | P.ATyp_sum (t1, t2) -> Nexp_sum (to_ast_bitfield_index_nexp t1, to_ast_bitfield_index_nexp t2)
    | P.ATyp_exp t1 -> Nexp_exp (to_ast_bitfield_index_nexp t1)
    | P.ATyp_neg t1 -> Nexp_neg (to_ast_bitfield_index_nexp t1)
    | P.ATyp_times (t1, t2) -> Nexp_times (to_ast_bitfield_index_nexp t1, to_ast_bitfield_index_nexp t2)
    | P.ATyp_minus (t1, t2) -> Nexp_minus (to_ast_bitfield_index_nexp t1, to_ast_bitfield_index_nexp t2)
    | P.ATyp_app (id, ts) -> Nexp_app (to_ast_id id, List.map (to_ast_bitfield_index_nexp) ts)
    | _ -> raise (Reporting.err_typ l "Invalid numeric expression in field index")
  in
  Nexp_aux (aux, l)

and to_ast_order ctx (P.ATyp_aux (aux, l)) =
  match aux with
  | ATyp_var v -> Ord_aux (Ord_var (to_ast_var v), l)
  | ATyp_inc -> Ord_aux (Ord_inc, l)
  | ATyp_dec -> Ord_aux (Ord_dec, l)
  | _ -> raise (Reporting.err_typ l "Invalid order in type")

and to_ast_constraint ctx (P.ATyp_aux (aux, l) as atyp) =
  let aux = match aux with
    | P.ATyp_app (Id_aux (Operator op, _) as id, [t1; t2]) ->
       begin match op with
       | "==" -> NC_equal (to_ast_nexp ctx t1, to_ast_nexp ctx t2)
       | "!=" -> NC_not_equal (to_ast_nexp ctx t1, to_ast_nexp ctx t2)
       | ">=" -> NC_bounded_ge (to_ast_nexp ctx t1, to_ast_nexp ctx t2)
       | "<=" -> NC_bounded_le (to_ast_nexp ctx t1, to_ast_nexp ctx t2)
       | ">" -> NC_bounded_gt (to_ast_nexp ctx t1, to_ast_nexp ctx t2)
       | "<" -> NC_bounded_lt (to_ast_nexp ctx t1, to_ast_nexp ctx t2)
       | "&" -> NC_and (to_ast_constraint ctx t1, to_ast_constraint ctx t2)
       | "|" -> NC_or (to_ast_constraint ctx t1, to_ast_constraint ctx t2)
       | _ ->
          let id = to_ast_id id in
          match Bindings.find_opt id ctx.type_constructors with
          | None -> raise (Reporting.err_typ l (sprintf "Could not find type constructor %s" (string_of_id id)))
          | Some kinds when List.length kinds <> 2 ->
             raise (Reporting.err_typ l (sprintf "%s : %s -> Bool expected %d arguments, given 2"
                                                 (string_of_id id) (format_kind_aux_list kinds)
                                                 (List.length kinds)))
          | Some kinds -> NC_app (id, List.map2 (to_ast_typ_arg ctx) [t1; t2] kinds)
       end
    | P.ATyp_app (id, args) ->
       let id = to_ast_id id in
       begin match Bindings.find_opt id ctx.type_constructors with
       | None -> raise (Reporting.err_typ l (sprintf "Could not find type constructor %s" (string_of_id id)))
       | Some kinds when List.length args <> List.length kinds ->
          raise (Reporting.err_typ l (sprintf "%s : %s -> Bool expected %d arguments, given %d"
                                              (string_of_id id) (format_kind_aux_list kinds)
                                              (List.length kinds) (List.length args)))
       | Some kinds -> NC_app (id, List.map2 (to_ast_typ_arg ctx) args kinds)
       end
    | P.ATyp_var v -> NC_var (to_ast_var v)
    | P.ATyp_lit (P.L_aux (P.L_true, _)) -> NC_true
    | P.ATyp_lit (P.L_aux (P.L_false, _)) -> NC_false
    | P.ATyp_nset (id, bounds) -> NC_set (to_ast_var id, bounds)
    | _ -> raise (Reporting.err_typ l "Invalid constraint")
  in
  NC_aux (aux, l)

let to_ast_quant_items ctx (P.QI_aux (aux, l)) =
  match aux with
  | P.QI_constraint nc -> [QI_aux (QI_constraint (to_ast_constraint ctx nc), l)], ctx
  | P.QI_id kopt ->
     let (kopts, ctx), attr = to_ast_kopts ctx kopt in
     match attr with
     | Some "constant" ->
        QI_aux (QI_constant kopts, l) :: List.map (fun kopt -> QI_aux (QI_id kopt, l)) kopts, ctx
     | Some attr ->
        raise (Reporting.err_typ l (sprintf "Unknown attribute %s" attr))
     | None ->
        List.map (fun kopt -> QI_aux (QI_id kopt, l)) kopts, ctx

let to_ast_typquant ctx (P.TypQ_aux (aux, l)) =
  match aux with
  | P.TypQ_no_forall -> TypQ_aux (TypQ_no_forall, l), ctx
  | P.TypQ_tq quants ->
     let quants, ctx =
       List.fold_left (fun (qis, ctx) qi -> let qis', ctx = to_ast_quant_items ctx qi in qis' @ qis, ctx) ([], ctx) quants
     in
     TypQ_aux (TypQ_tq (List.rev quants), l), ctx

let to_ast_typschm ctx (P.TypSchm_aux (P.TypSchm_ts (typq, typ), l)) =
  let typq, ctx = to_ast_typquant ctx typq in
  let typ = to_ast_typ ctx typ in
  TypSchm_aux (TypSchm_ts (typq, typ), l), ctx

let to_ast_lit (P.L_aux (lit, l)) =
  L_aux ((match lit with
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
          | P.L_string s -> L_string s)
        ,l)

let rec to_ast_typ_pat (P.ATyp_aux (aux, l)) =
  match aux with
  | P.ATyp_wild -> TP_aux (TP_wild, l)
  | P.ATyp_var kid -> TP_aux (TP_var (to_ast_var kid), l)
  | P.ATyp_app (P.Id_aux (P.Id "int", il), typs) ->
     TP_aux (TP_app (Id_aux (Id "atom", il), List.map to_ast_typ_pat typs), l)
  | P.ATyp_app (f, typs) ->
     TP_aux (TP_app (to_ast_id f, List.map to_ast_typ_pat typs), l)
  | _ -> raise (Reporting.err_typ l "Unexpected type in type pattern")

let rec to_ast_pat ctx (P.P_aux (pat, l)) =
  P_aux ((match pat with
          | P.P_lit lit -> P_lit (to_ast_lit lit)
          | P.P_wild -> P_wild
          | P.P_or (pat1, pat2) ->
             P_or (to_ast_pat ctx pat1, to_ast_pat ctx pat2)
          | P.P_var (pat, P.ATyp_aux (P.ATyp_id id, _)) ->
             P_as (to_ast_pat ctx pat, to_ast_id id)
          | P.P_typ (typ, pat) -> P_typ (to_ast_typ ctx typ, to_ast_pat ctx pat)
          | P.P_id id -> P_id (to_ast_id id)
          | P.P_var (pat, typ) -> P_var (to_ast_pat ctx pat, to_ast_typ_pat typ)
          | P.P_app (id, []) -> P_id (to_ast_id id)
          | P.P_app (id, pats) ->
             if List.length pats == 1 && string_of_parse_id id = "~"
             then P_not (to_ast_pat ctx (List.hd pats))
             else P_app (to_ast_id id, List.map (to_ast_pat ctx) pats)
          | P.P_vector(pats) -> P_vector(List.map (to_ast_pat ctx) pats)
          | P.P_vector_concat(pats) -> P_vector_concat(List.map (to_ast_pat ctx) pats)
          | P.P_tup(pats) -> P_tup(List.map (to_ast_pat ctx) pats)
          | P.P_list(pats) -> P_list(List.map (to_ast_pat ctx) pats)
          | P.P_cons(pat1, pat2) -> P_cons (to_ast_pat ctx pat1, to_ast_pat ctx pat2)
          | P.P_string_append pats -> P_string_append (List.map (to_ast_pat ctx) pats)
         ), (l,()))

let rec to_ast_letbind ctx (P.LB_aux(lb,l) : P.letbind) : unit letbind =
  LB_aux(
    (match lb with
    | P.LB_val(pat,exp) ->
      LB_val(to_ast_pat ctx pat, to_ast_exp ctx exp)
    ), (l,()))

and to_ast_exp ctx (P.E_aux(exp,l) : P.exp) =
  E_aux(
    (match exp with
    | P.E_block(exps) ->
      (match to_ast_fexps false ctx exps with
      | Some(fexps) -> E_record(fexps)
      | None -> E_block(List.map (to_ast_exp ctx) exps))
    | P.E_id(id) -> E_id(to_ast_id id)
    | P.E_ref(id) -> E_ref(to_ast_id id)
    | P.E_lit(lit) -> E_lit(to_ast_lit lit)
    | P.E_cast(typ,exp) -> E_cast(to_ast_typ ctx typ, to_ast_exp ctx exp)
    | P.E_app(f,args) ->
      (match List.map (to_ast_exp ctx) args with
	| [] -> E_app(to_ast_id f, [])
        | exps -> E_app(to_ast_id f, exps))
    | P.E_app_infix(left,op,right) ->
      E_app_infix(to_ast_exp ctx left, to_ast_id op, to_ast_exp ctx right)
    | P.E_tuple(exps) -> E_tuple(List.map (to_ast_exp ctx) exps)
    | P.E_if(e1,e2,e3) -> E_if(to_ast_exp ctx e1, to_ast_exp ctx e2, to_ast_exp ctx e3)
    | P.E_for(id,e1,e2,e3,atyp,e4) ->
      E_for(to_ast_id id,to_ast_exp ctx e1, to_ast_exp ctx e2,
            to_ast_exp ctx e3,to_ast_order ctx atyp, to_ast_exp ctx e4)
    | P.E_loop (P.While, m, e1, e2) -> E_loop (While, to_ast_measure ctx m, to_ast_exp ctx e1, to_ast_exp ctx e2)
    | P.E_loop (P.Until, m, e1, e2) -> E_loop (Until, to_ast_measure ctx m, to_ast_exp ctx e1, to_ast_exp ctx e2)
    | P.E_vector(exps) -> E_vector(List.map (to_ast_exp ctx) exps)
    | P.E_vector_access(vexp,exp) -> E_vector_access(to_ast_exp ctx vexp, to_ast_exp ctx exp)
    | P.E_vector_subrange(vex,exp1,exp2) ->
      E_vector_subrange(to_ast_exp ctx vex, to_ast_exp ctx exp1, to_ast_exp ctx exp2)
    | P.E_vector_update(vex,exp1,exp2) ->
      E_vector_update(to_ast_exp ctx vex, to_ast_exp ctx exp1, to_ast_exp ctx exp2)
    | P.E_vector_update_subrange(vex,e1,e2,e3) ->
      E_vector_update_subrange(to_ast_exp ctx vex, to_ast_exp ctx e1,
			       to_ast_exp ctx e2, to_ast_exp ctx e3)
    | P.E_vector_append(e1,e2) -> E_vector_append(to_ast_exp ctx e1,to_ast_exp ctx e2)
    | P.E_list(exps) -> E_list(List.map (to_ast_exp ctx) exps)
    | P.E_cons(e1,e2) -> E_cons(to_ast_exp ctx e1, to_ast_exp ctx e2)
    | P.E_record fexps ->
       (match to_ast_fexps true ctx fexps with
        | Some fexps -> E_record fexps
        | None -> raise (Reporting.err_unreachable l __POS__ "to_ast_fexps with true returned none"))
    | P.E_record_update(exp,fexps) ->
      (match to_ast_fexps true ctx fexps with
      | Some(fexps) -> E_record_update(to_ast_exp ctx exp, fexps)
      | _ -> raise (Reporting.err_unreachable l __POS__ "to_ast_fexps with true returned none"))
    | P.E_field(exp,id) -> E_field(to_ast_exp ctx exp, to_ast_id id)
    | P.E_case(exp,pexps) -> E_case(to_ast_exp ctx exp, List.map (to_ast_case ctx) pexps)
    | P.E_try (exp, pexps) -> E_try (to_ast_exp ctx exp, List.map (to_ast_case ctx) pexps)
    | P.E_let(leb,exp) -> E_let(to_ast_letbind ctx leb, to_ast_exp ctx exp)
    | P.E_assign(lexp,exp) -> E_assign(to_ast_lexp ctx lexp, to_ast_exp ctx exp)
    | P.E_var(lexp,exp1,exp2) -> E_var(to_ast_lexp ctx lexp, to_ast_exp ctx exp1, to_ast_exp ctx exp2)
    | P.E_sizeof(nexp) -> E_sizeof(to_ast_nexp ctx nexp)
    | P.E_constraint nc -> E_constraint (to_ast_constraint ctx nc)
    | P.E_exit exp -> E_exit(to_ast_exp ctx exp)
    | P.E_throw exp -> E_throw (to_ast_exp ctx exp)
    | P.E_return exp -> E_return(to_ast_exp ctx exp)
    | P.E_assert(cond,msg) -> E_assert(to_ast_exp ctx cond, to_ast_exp ctx msg)
    | P.E_internal_plet(pat,exp1,exp2) ->
       if !opt_magic_hash then
         E_internal_plet(to_ast_pat ctx pat, to_ast_exp ctx exp1, to_ast_exp ctx exp2)
       else
         raise (Reporting.err_general l "Internal plet construct found without -dmagic_hash")
    | P.E_internal_return(exp) ->
       if !opt_magic_hash then
         E_internal_return(to_ast_exp ctx exp)
       else
         raise (Reporting.err_general l "Internal return construct found without -dmagic_hash")
    | P.E_deref exp ->
       E_app (Id_aux (Id "__deref", l), [to_ast_exp ctx exp])
    ), (l,()))

and to_ast_measure ctx (P.Measure_aux(m,l)) : unit internal_loop_measure =
  let m = match m with
    | P.Measure_none -> Measure_none
    | P.Measure_some exp ->
       if !opt_magic_hash then
         Measure_some (to_ast_exp ctx exp)
       else
         raise (Reporting.err_general l "Internal loop termination measure found without -dmagic_hash")
  in Measure_aux (m,l)

and to_ast_lexp ctx (P.E_aux(exp,l) : P.exp) : unit lexp =
  let lexp = match exp with
    | P.E_id id -> LEXP_id (to_ast_id id)
    | P.E_deref exp -> LEXP_deref (to_ast_exp ctx exp)
    | P.E_cast (typ, P.E_aux (P.E_id id, l')) ->
       LEXP_cast (to_ast_typ ctx typ, to_ast_id id)
    | P.E_tuple tups ->
       let ltups = List.map (to_ast_lexp ctx) tups in
       let is_ok_in_tup (LEXP_aux (le, (l, _))) =
         match le with
         | LEXP_id _ | LEXP_cast _ | LEXP_vector _ | LEXP_vector_concat _ | LEXP_field _ | LEXP_vector_range _ | LEXP_tup _ -> ()
         | LEXP_memory _ | LEXP_deref _ ->
            raise (Reporting.err_typ l "only identifiers, fields, and vectors may be set in a tuple")
       in
       List.iter is_ok_in_tup ltups;
       LEXP_tup ltups
    | P.E_app ((P.Id_aux (f, l') as f'), args) ->
       begin match f with
       | P.Id(id) ->
          (match List.map (to_ast_exp ctx) args with
           | [E_aux (E_lit (L_aux (L_unit, _)), _)] -> LEXP_memory (to_ast_id f', [])
           | [E_aux (E_tuple exps,_)] -> LEXP_memory (to_ast_id f', exps)
           | args -> LEXP_memory(to_ast_id f', args))
       | _ -> raise (Reporting.err_typ l' "memory call on lefthand side of assignment must begin with an id")
       end
    | P.E_vector_append (exp1, exp2) ->
       LEXP_vector_concat (to_ast_lexp ctx exp1 :: to_ast_lexp_vector_concat ctx exp2)
    | P.E_vector_access (vexp, exp) -> LEXP_vector (to_ast_lexp ctx vexp, to_ast_exp ctx exp)
    | P.E_vector_subrange (vexp, exp1, exp2) ->
       LEXP_vector_range (to_ast_lexp ctx vexp, to_ast_exp ctx exp1, to_ast_exp ctx exp2)
    | P.E_field (fexp, id) -> LEXP_field (to_ast_lexp ctx fexp, to_ast_id id)
    | _ -> raise (Reporting.err_typ l "Only identifiers, cast identifiers, vector accesses, vector slices, and fields can be on the lefthand side of an assignment")
  in
  LEXP_aux (lexp, (l, ()))

and to_ast_lexp_vector_concat ctx (P.E_aux (exp_aux, l) as exp) =
  match exp_aux with
  | P.E_vector_append (exp1, exp2) ->
     to_ast_lexp ctx exp1 :: to_ast_lexp_vector_concat ctx exp2
  | _ -> [to_ast_lexp ctx exp]

and to_ast_case ctx (P.Pat_aux(pex,l) : P.pexp) : unit pexp =
  match pex with
  | P.Pat_exp(pat,exp) -> Pat_aux(Pat_exp(to_ast_pat ctx pat, to_ast_exp ctx exp),(l,()))
  | P.Pat_when(pat,guard,exp) ->
     Pat_aux (Pat_when (to_ast_pat ctx pat, to_ast_exp ctx guard, to_ast_exp ctx exp), (l, ()))

and to_ast_fexps (fail_on_error:bool) ctx (exps : P.exp list) : unit fexp list option =
  match exps with
  | [] -> Some []
  | fexp::exps -> let maybe_fexp,maybe_error = to_ast_record_try ctx fexp in
                  (match maybe_fexp,maybe_error with
                  | Some(fexp),None ->
                    (match (to_ast_fexps fail_on_error ctx exps) with
                    | Some(fexps) -> Some(fexp::fexps)
                    | _  -> None)
                  | None,Some(l,msg) ->
                    if fail_on_error
                    then raise (Reporting.err_typ l msg)
                    else None
                  | _ -> None)

and to_ast_record_try ctx (P.E_aux(exp,l):P.exp): unit fexp option * (l * string) option =
  match exp with
  | P.E_app_infix(left,op,r) ->
    (match left, op with
    | P.E_aux(P.E_id(id),li), P.Id_aux(P.Id("="),leq) ->
      Some(FE_aux(FE_Fexp(to_ast_id id, to_ast_exp ctx r), (l,()))),None
    | P.E_aux(_,li) , P.Id_aux(P.Id("="),leq) ->
      None,Some(li,"Expected an identifier to begin this field assignment")
    | P.E_aux(P.E_id(id),li), P.Id_aux(_,leq) ->
      None,Some(leq,"Expected a field assignment to be identifier = expression")
    | P.E_aux(_,li),P.Id_aux(_,leq) ->
      None,Some(l,"Expected a field assignment to be identifier = expression"))
  | _ ->
     None,Some(l, "Expected a field assignment to be identifier = expression")

type 'a ctx_out = 'a * ctx

let to_ast_default ctx (default : P.default_typing_spec) : default_spec ctx_out =
  match default with
  | P.DT_aux(P.DT_order(k,o),l) ->
     let k = to_ast_kind k in
     match (k,o) with
     | K_aux(K_order, _), P.ATyp_aux(P.ATyp_inc,lo) ->
        let default_order = Ord_aux(Ord_inc,lo) in
        DT_aux(DT_order default_order,l),ctx
     | K_aux(K_order, _), P.ATyp_aux(P.ATyp_dec,lo) ->
        let default_order = Ord_aux(Ord_dec,lo) in
        DT_aux(DT_order default_order,l),ctx
     | _ -> raise (Reporting.err_typ l "Inc and Dec must have kind Order")

let to_ast_spec ctx (val_:P.val_spec) : (unit val_spec) ctx_out =
  match val_ with
  | P.VS_aux(vs,l) ->
    (match vs with
    | P.VS_val_spec(ts,id,ext,is_cast) ->
      let typschm, _ = to_ast_typschm ctx ts in
      VS_aux(VS_val_spec(typschm,to_ast_id id,ext,is_cast),(l,())),ctx)

let rec to_ast_range (P.BF_aux(r,l)) = (* TODO add check that ranges are sensible for some definition of sensible *)
  BF_aux(
    (match r with
    | P.BF_single(i) -> BF_single(to_ast_bitfield_index_nexp i)
    | P.BF_range(i1,i2) -> BF_range(to_ast_bitfield_index_nexp i1,to_ast_bitfield_index_nexp i2)
    | P.BF_concat(ir1,ir2) -> BF_concat(to_ast_range ir1, to_ast_range ir2)),
    l)

let to_ast_type_union ctx = function
  | P.Tu_aux (P.Tu_ty_id (atyp, id), l) ->
     let typ = to_ast_typ ctx atyp in
     Tu_aux (Tu_ty_id (typ, to_ast_id id), l)
  | P.Tu_aux (_, l) ->
     raise (Reporting.err_unreachable l __POS__ "Anonymous record type should have been rewritten by now")

let add_constructor id typq ctx =
  let kinds = List.map (fun kopt -> unaux_kind (kopt_kind kopt)) (quant_kopts typq) in
  { ctx with type_constructors = Bindings.add id kinds ctx.type_constructors }

let anon_rec_constructor_typ record_id = function
  | P.TypQ_aux (P.TypQ_no_forall, l) -> P.ATyp_aux (P.ATyp_id record_id, Generated l)
  | P.TypQ_aux (P.TypQ_tq quants, l) ->
     let rec quant_arg = function
       | P.QI_aux (P.QI_id (P.KOpt_aux (P.KOpt_kind (_, vs, _), l)), _) ->
          List.map (fun v -> P.ATyp_aux (P.ATyp_var v, Generated l)) vs
       | P.QI_aux (P.QI_constraint _, _) -> []
     in
     match List.concat (List.map quant_arg quants) with
     | [] -> P.ATyp_aux (P.ATyp_id record_id, Generated l)
     | args -> P.ATyp_aux (P.ATyp_app (record_id, args), Generated l)

let rec realise_union_anon_rec_types orig_union arms =
  match orig_union with
  | P.TD_variant (union_id, typq, _, flag) ->
     begin match arms with
     | [] -> []
     | arm :: arms ->
        match arm with
        | (P.Tu_aux ((P.Tu_ty_id _), _)) -> (None, arm) :: realise_union_anon_rec_types orig_union arms
        | (P.Tu_aux ((P.Tu_ty_anon_rec (fields, id)), l)) ->
           let open Parse_ast in
           let record_str = "_" ^ string_of_parse_id union_id ^ "_" ^ string_of_parse_id id ^ "_record" in
           let record_id = Id_aux (Id record_str, Generated l) in
           let new_arm = Tu_aux (Tu_ty_id (anon_rec_constructor_typ record_id typq, id), Generated l) in
           let new_rec_def = TD_aux (TD_record (record_id, typq, fields, flag), Generated l) in
           (Some new_rec_def, new_arm) :: (realise_union_anon_rec_types orig_union arms)
     end
  | _ ->
     raise (Reporting.err_unreachable Parse_ast.Unknown __POS__ "Non union type-definition passed to realise_union_anon_rec_typs")

let generate_enum_functions l ctx enum_id fns exps =
  let get_exp i = function
    | Some (P.E_aux (P.E_tuple exps, _)) -> List.nth exps i 
    | Some exp -> exp
    | None -> Reporting.unreachable l __POS__ "get_exp called without expression"
  in
  let num_exps = function
    | Some (P.E_aux (P.E_tuple exps, _)) -> List.length exps
    | Some _ -> 1
    | None -> 0
  in
  let num_fns = List.length fns in
  List.iter (fun (id, exp) ->
      let n = num_exps exp in
      if n <> num_fns then (
        let l = (match exp with Some (P.E_aux (_, l)) -> l | None -> parse_id_loc id) in
        raise (Reporting.err_general l
                 (sprintf "Each enumeration clause for %s must define exactly %d expressions for the functions %s\n\
                           %s expressions have been given here"
                    (string_of_id enum_id)
                    num_fns
                    (string_of_list ", " string_of_parse_id (List.map fst fns))
                    (if n = 0 then "No" else if n > num_fns then "Too many" else "Too few")))
      )
    ) exps;
  List.mapi (fun i (id, typ) ->
      let typ = to_ast_typ ctx typ in
      let name = mk_id (string_of_id enum_id ^ "_" ^ string_of_parse_id id) in
      [mk_fundef [
           mk_funcl name (mk_pat (P_id (mk_id "arg#")))
             (mk_exp (E_case (mk_exp (E_id (mk_id "arg#")),
                              List.map (fun (id, exps) ->
                                  let id = to_ast_id id in
                                  let exp = to_ast_exp ctx (get_exp i exps) in
                                  mk_pexp (Pat_exp (mk_pat (P_id id), exp))
                                ) exps)))
         ];
       mk_val_spec (VS_val_spec (mk_typschm (mk_typquant []) (function_typ [mk_id_typ enum_id] typ no_effect),
                                 name,
                                 [],
                                 false))]
    ) fns
  |> List.concat

let rec to_ast_typedef ctx (P.TD_aux (aux, l) : P.type_def) : unit def list ctx_out =
  match aux with
  | P.TD_abbrev (id, typq, kind, typ_arg) ->
     let id = to_ast_id id in
     let typq, typq_ctx = to_ast_typquant ctx typq in
     let kind = to_ast_kind kind in
     let typ_arg = to_ast_typ_arg typq_ctx typ_arg (unaux_kind kind) in
     [DEF_type (TD_aux (TD_abbrev (id, typq, typ_arg), (l, ())))],
     add_constructor id typq ctx

  | P.TD_record (id, typq, fields, _) ->
     let id = to_ast_id id in
     let typq, typq_ctx = to_ast_typquant ctx typq in
     let fields = List.map (fun (atyp, id) -> to_ast_typ typq_ctx atyp, to_ast_id id) fields in
     [DEF_type (TD_aux (TD_record (id, typq, fields, false), (l, ())))],
     add_constructor id typq ctx

  | P.TD_variant (id, typq, arms, _) as union ->
     (* First generate auxilliary record types for anonymous records in constructors *)
     let records_and_arms = realise_union_anon_rec_types union arms in
     let rec filter_records = function
       | [] -> []
       | Some x :: xs -> x :: filter_records xs
       | None :: xs -> filter_records xs
     in
     let generated_records = filter_records (List.map fst records_and_arms) in
     let generated_records, ctx =
       List.fold_left (fun (prev, ctx) td -> let td, ctx = to_ast_typedef ctx td in prev @ td, ctx)
         ([], ctx)
         generated_records
     in
     let arms = List.map snd records_and_arms in
     let union = Parse_ast.TD_variant (id, typq, arms, false) in
     (* Now generate the AST union type *)
     let id = to_ast_id id in
     let typq, typq_ctx = to_ast_typquant ctx typq in
     let arms = List.map (to_ast_type_union typq_ctx) arms in
     [DEF_type (TD_aux (TD_variant (id, typq, arms, false), (l, ())))] @ generated_records,
     add_constructor id typq ctx

  | P.TD_enum (id, fns, enums, _) ->
     let id = to_ast_id id in
     let fns = generate_enum_functions l ctx id fns enums in
     let enums = List.map (fun e -> to_ast_id (fst e)) enums in
     fns @ [DEF_type (TD_aux (TD_enum (id, enums, false), (l, ())))],
     { ctx with type_constructors = Bindings.add id [] ctx.type_constructors }

  | P.TD_bitfield (id, typ, ranges) ->
     let id = to_ast_id id in
     let typ = to_ast_typ ctx typ in
     let ranges = List.map (fun (id, range) -> (to_ast_id id, to_ast_range range)) ranges in
     [DEF_type (TD_aux (TD_bitfield (id, typ, ranges), (l, ())))],
     { ctx with type_constructors = Bindings.add id [] ctx.type_constructors }

let to_ast_rec ctx (P.Rec_aux(r,l): P.rec_opt) : unit rec_opt =
  Rec_aux((match r with
  | P.Rec_nonrec -> Rec_nonrec
  | P.Rec_rec -> Rec_rec
  | P.Rec_measure (p,e) ->
     Rec_measure (to_ast_pat ctx p, to_ast_exp ctx e)
  ),l)

let to_ast_tannot_opt ctx (P.Typ_annot_opt_aux(tp,l)) : tannot_opt ctx_out =
  match tp with
  | P.Typ_annot_opt_none ->
     Typ_annot_opt_aux (Typ_annot_opt_none, l), ctx
  | P.Typ_annot_opt_some(tq,typ) ->
    let typq, ctx = to_ast_typquant ctx tq in
    Typ_annot_opt_aux (Typ_annot_opt_some(typq,to_ast_typ ctx typ),l),ctx

let to_ast_typschm_opt ctx (P.TypSchm_opt_aux(aux,l)) : tannot_opt ctx_out =
  match aux with
  | P.TypSchm_opt_none ->
     Typ_annot_opt_aux (Typ_annot_opt_none, l), ctx
  | P.TypSchm_opt_some (P.TypSchm_aux (P.TypSchm_ts (tq, typ), l)) ->
     let typq, ctx = to_ast_typquant ctx tq in
     Typ_annot_opt_aux (Typ_annot_opt_some (typq, to_ast_typ ctx typ), l), ctx

let to_ast_effects_opt (P.Effect_opt_aux(e,l)) : effect_opt =
  match e with
  | P.Effect_opt_none -> Effect_opt_aux(Effect_opt_none,l)
  | P.Effect_opt_effect(typ) -> Effect_opt_aux(Effect_opt_effect(to_ast_effects typ),l)

let to_ast_funcl ctx (P.FCL_aux(fcl,l) : P.funcl) : (unit funcl) =
  match fcl with
  | P.FCL_Funcl(id,pexp) ->
    FCL_aux(FCL_Funcl(to_ast_id id, to_ast_case ctx pexp),(l,()))

let to_ast_fundef ctx (P.FD_aux(fd,l):P.fundef) : unit fundef =
  match fd with
  | P.FD_function(rec_opt,tannot_opt,effects_opt,funcls) ->
    let tannot_opt, ctx = to_ast_tannot_opt ctx tannot_opt in
    FD_aux(FD_function(to_ast_rec ctx rec_opt, tannot_opt, to_ast_effects_opt effects_opt, List.map (to_ast_funcl ctx) funcls), (l,()))

let rec to_ast_mpat ctx (P.MP_aux(mpat,l)) =
  MP_aux(
    (match mpat with
    | P.MP_lit(lit) -> MP_lit(to_ast_lit lit)
    | P.MP_id(id) -> MP_id(to_ast_id id)
    | P.MP_as (mpat, id) -> MP_as (to_ast_mpat ctx mpat, to_ast_id id)
    | P.MP_app(id,mpats) ->
      if mpats = []
      then MP_id (to_ast_id id)
      else MP_app(to_ast_id id, List.map (to_ast_mpat ctx) mpats)
    | P.MP_vector(mpats) -> MP_vector(List.map (to_ast_mpat ctx) mpats)
    | P.MP_vector_concat(mpats) -> MP_vector_concat(List.map (to_ast_mpat ctx) mpats)
    | P.MP_tup(mpats) -> MP_tup(List.map (to_ast_mpat ctx) mpats)
    | P.MP_list(mpats) -> MP_list(List.map (to_ast_mpat ctx) mpats)
    | P.MP_cons(pat1, pat2) -> MP_cons (to_ast_mpat ctx pat1, to_ast_mpat ctx pat2)
    | P.MP_string_append pats -> MP_string_append (List.map (to_ast_mpat ctx) pats)
    | P.MP_typ (mpat, typ) -> MP_typ (to_ast_mpat ctx mpat, to_ast_typ ctx typ)
    ), (l,()))

let to_ast_mpexp ctx (P.MPat_aux(mpexp, l)) =
  match mpexp with
  | P.MPat_pat mpat -> MPat_aux (MPat_pat (to_ast_mpat ctx mpat), (l, ()))
  | P.MPat_when (mpat, exp) -> MPat_aux (MPat_when (to_ast_mpat ctx mpat, to_ast_exp ctx exp), (l, ()))

let to_ast_mapcl ctx (P.MCL_aux(mapcl, l)) =
  match mapcl with
  | P.MCL_bidir (mpexp1, mpexp2) -> MCL_aux (MCL_bidir (to_ast_mpexp ctx mpexp1, to_ast_mpexp ctx mpexp2), (l, ()))
  | P.MCL_forwards (mpexp, exp) -> MCL_aux (MCL_forwards (to_ast_mpexp ctx mpexp, to_ast_exp ctx exp), (l, ()))
  | P.MCL_backwards (mpexp, exp) -> MCL_aux (MCL_backwards (to_ast_mpexp ctx mpexp, to_ast_exp ctx exp), (l, ()))

let to_ast_mapdef ctx (P.MD_aux(md,l):P.mapdef) : unit mapdef =
  match md with
  | P.MD_mapping(id, typschm_opt, mapcls) ->
     let tannot_opt, ctx = to_ast_typschm_opt ctx typschm_opt in
     MD_aux(MD_mapping(to_ast_id id, tannot_opt, List.map (to_ast_mapcl ctx) mapcls), (l,()))

let to_ast_alias_spec ctx (P.E_aux(e, l)) =
  AL_aux((match e with
          | P.E_field (P.E_aux (P.E_id id, li), field) ->
             AL_subreg (RI_aux (RI_id (to_ast_id id), (li, ())), to_ast_id field)
          | P.E_vector_access (P.E_aux (P.E_id id, li), range) ->
             AL_bit (RI_aux (RI_id (to_ast_id id), (li, ())), to_ast_exp ctx range)
          | P.E_vector_subrange(P.E_aux(P.E_id id,li),base,stop) ->
             AL_slice (RI_aux (RI_id (to_ast_id id), (li,())), to_ast_exp ctx base, to_ast_exp ctx stop)
          | P.E_vector_append (P.E_aux (P.E_id first, lf), P.E_aux (P.E_id second, ls)) ->
             AL_concat (RI_aux (RI_id (to_ast_id first), (lf, ())),
                        RI_aux (RI_id (to_ast_id second), (ls, ())))
          | _ -> raise (Reporting.err_unreachable l __POS__ "Found an expression not supported by parser in to_ast_alias_spec")
         ), (l, ()))

let to_ast_dec ctx (P.DEC_aux(regdec,l)) =
  DEC_aux((match regdec with
           | P.DEC_reg (reffect, weffect, typ, id) ->
              DEC_reg (to_ast_effects reffect, to_ast_effects weffect, to_ast_typ ctx typ, to_ast_id id)
           | P.DEC_config (id, typ, exp) ->
              DEC_config (to_ast_id id, to_ast_typ ctx typ, to_ast_exp ctx exp)
           | P.DEC_alias (id,e) ->
              DEC_alias (to_ast_id id, to_ast_alias_spec ctx e)
           | P.DEC_typ_alias (typ,id,e) ->
              DEC_typ_alias (to_ast_typ ctx typ, to_ast_id id, to_ast_alias_spec ctx e)
          ),(l,()))

let to_ast_scattered ctx (P.SD_aux (aux, l)) =
  let aux, ctx = match aux with
    | P.SD_function (rec_opt, tannot_opt, effect_opt, id) ->
       let tannot_opt, _ = to_ast_tannot_opt ctx tannot_opt in
       let effect_opt = to_ast_effects_opt effect_opt in
       SD_function (to_ast_rec ctx rec_opt, tannot_opt, effect_opt, to_ast_id id), ctx
    | P.SD_funcl funcl ->
       SD_funcl (to_ast_funcl ctx funcl), ctx
    | P.SD_variant (id, typq) ->
       let id = to_ast_id id in
       let typq, typq_ctx = to_ast_typquant ctx typq in
       SD_variant (id, typq),
       add_constructor id typq { ctx with scattereds = Bindings.add id typq_ctx ctx.scattereds }
    | P.SD_unioncl (id, tu) ->
       let id = to_ast_id id in
       begin match Bindings.find_opt id ctx.scattereds with
       | Some typq_ctx ->
          let tu = to_ast_type_union typq_ctx tu in
          SD_unioncl (id, tu), ctx
       | None -> raise (Reporting.err_typ l ("No scattered union declaration found for " ^ string_of_id id))
       end
    | P.SD_end id -> SD_end (to_ast_id id), ctx
    | P.SD_mapping (id, tannot_opt) ->
       let id = to_ast_id id in
       let tannot_opt, _ = to_ast_tannot_opt ctx tannot_opt in
       SD_mapping (id, tannot_opt), ctx
    | P.SD_mapcl (id, mapcl) ->
       let id = to_ast_id id in
       let mapcl = to_ast_mapcl ctx mapcl in
       SD_mapcl (id, mapcl), ctx
  in
  SD_aux (aux, (l, ())), ctx

let to_ast_prec = function
  | P.Infix -> Infix
  | P.InfixL -> InfixL
  | P.InfixR -> InfixR

let to_ast_loop_measure ctx = function
  | P.Loop (P.While, exp) -> Loop (While, to_ast_exp ctx exp)
  | P.Loop (P.Until, exp) -> Loop (Until, to_ast_exp ctx exp)

let to_ast_def ctx def : unit def list ctx_out =
  match def with
  | P.DEF_overload (id, ids) ->
     [DEF_overload (to_ast_id id, List.map to_ast_id ids)], ctx
  | P.DEF_fixity (prec, n, op) ->
     [DEF_fixity (to_ast_prec prec, n, to_ast_id op)], ctx
  | P.DEF_type(t_def) ->
     to_ast_typedef ctx t_def
  | P.DEF_fundef(f_def) ->
     let fd = to_ast_fundef ctx f_def in
     [DEF_fundef fd], ctx
  | P.DEF_mapdef(m_def) ->
     let md = to_ast_mapdef ctx m_def in
     [DEF_mapdef md], ctx
  | P.DEF_val(lbind) ->
     let lb = to_ast_letbind ctx lbind in
     [DEF_val lb], ctx
  | P.DEF_spec(val_spec) ->
     let vs,ctx = to_ast_spec ctx val_spec in
     [DEF_spec vs], ctx
  | P.DEF_default(typ_spec) ->
     let default,ctx = to_ast_default ctx typ_spec in
     [DEF_default default], ctx
  | P.DEF_reg_dec dec ->
     let d = to_ast_dec ctx dec in
     [DEF_reg_dec d], ctx
  | P.DEF_pragma (pragma, arg, l) ->
     [DEF_pragma (pragma, arg, l)], ctx
  | P.DEF_internal_mutrec _ ->
     (* Should never occur because of remove_mutrec *)
     raise (Reporting.err_unreachable P.Unknown __POS__
                                      "Internal mutual block found when processing scattered defs")
  | P.DEF_scattered sdef ->
     let sdef, ctx = to_ast_scattered ctx sdef in
     [DEF_scattered sdef], ctx
  | P.DEF_measure (id, pat, exp) ->
     [DEF_measure (to_ast_id id, to_ast_pat ctx pat, to_ast_exp ctx exp)], ctx
  | P.DEF_loop_measures (id, measures) ->
     [DEF_loop_measures (to_ast_id id, List.map (to_ast_loop_measure ctx) measures)], ctx

let rec remove_mutrec = function
  | [] -> []
  | P.DEF_internal_mutrec fundefs :: defs ->
     List.map (fun fdef -> P.DEF_fundef fdef) fundefs @ remove_mutrec defs
  | def :: defs ->
     def :: remove_mutrec defs

let to_ast ctx (P.Defs files) =
  let to_ast_defs ctx (_, defs) =
    let defs = remove_mutrec defs in
    let defs, ctx =
      List.fold_left (fun (defs, ctx) def -> let def, ctx = to_ast_def ctx def in (def @ defs, ctx)) ([], ctx) defs
    in
    List.rev defs, ctx
  in
  let wrap_file file defs =
    [DEF_pragma ("file_start", file, P.Unknown)]
    @ defs
    @ [DEF_pragma ("file_end", file, P.Unknown)]
  in
  let defs, ctx =
    List.fold_left (fun (defs, ctx) file ->
        let defs', ctx = to_ast_defs ctx file in (defs @ wrap_file (fst file) defs', ctx)
      ) ([], ctx) files
  in
  { defs = defs; comments = [] }, ctx

let initial_ctx = {
    type_constructors =
      List.fold_left (fun m (k, v) -> Bindings.add (mk_id k) v m) Bindings.empty
        [ ("bool", []);
          ("nat", []);
          ("int", []);
          ("unit", []);
          ("bit", []);
          ("string", []);
          ("real", []);
          ("list", [K_type]);
          ("register", [K_type]);
          ("range", [K_int; K_int]);
          ("bitvector", [K_int; K_order]);
          ("vector", [K_int; K_order; K_type]);
          ("atom", [K_int]);
          ("implicit", [K_int]);
          ("itself", [K_int]);
          ("not", [K_bool]);
        ];
    kinds = KBindings.empty;
    scattereds = Bindings.empty;
  }

let exp_of_string str =
  let exp = Parser.exp_eof Lexer.token (Lexing.from_string str) in
  to_ast_exp initial_ctx exp

let typschm_of_string str =
  let typschm = Parser.typschm_eof Lexer.token (Lexing.from_string str) in
  let typschm, _ = to_ast_typschm initial_ctx typschm in
  typschm

let typ_of_string str =
  let typ = Parser.typ_eof Lexer.token (Lexing.from_string str) in
  let typ = to_ast_typ initial_ctx typ in
  typ

let constraint_of_string str =
  let atyp = Parser.typ_eof Lexer.token (Lexing.from_string str) in
  to_ast_constraint initial_ctx atyp

let extern_of_string id str = mk_val_spec (VS_val_spec (typschm_of_string str, id, [("_", string_of_id id)], false))
let val_spec_of_string id str = mk_val_spec (VS_val_spec (typschm_of_string str, id, [], false))

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
  if qis = [] then
    mk_typschm typq (function_typ [unit_typ] (mk_typ (Typ_id id)) (mk_effect [BE_undef]))
  else
    let arg_typs = List.concat (List.map quant_item_typ qis) in
    let ret_typ = app_typ id (List.concat (List.map quant_item_arg qis)) in
    mk_typschm typq (function_typ arg_typs ret_typ (mk_effect [BE_undef]))

let have_undefined_builtins = ref false

let undefined_builtin_val_specs =
  [extern_of_string (mk_id "internal_pick") "forall ('a:Type). list('a) -> 'a effect {undef}";
   extern_of_string (mk_id "undefined_bool") "unit -> bool effect {undef}";
   extern_of_string (mk_id "undefined_bit") "unit -> bit effect {undef}";
   extern_of_string (mk_id "undefined_int") "unit -> int effect {undef}";
   extern_of_string (mk_id "undefined_nat") "unit -> nat effect {undef}";
   extern_of_string (mk_id "undefined_real") "unit -> real effect {undef}";
   extern_of_string (mk_id "undefined_string") "unit -> string effect {undef}";
   extern_of_string (mk_id "undefined_list") "forall ('a:Type). 'a -> list('a) effect {undef}";
   extern_of_string (mk_id "undefined_range") "forall 'n 'm. (atom('n), atom('m)) -> range('n,'m) effect {undef}";
   extern_of_string (mk_id "undefined_vector") "forall 'n ('a:Type) ('ord : Order). (atom('n), 'a) -> vector('n, 'ord,'a) effect {undef}";
   extern_of_string (mk_id "undefined_bitvector") "forall 'n. atom('n) -> bitvector('n, dec) effect {undef}";
   extern_of_string (mk_id "undefined_unit") "unit -> unit effect {undef}"]

let generate_undefineds vs_ids defs =
  let undefined_builtins =
    if !have_undefined_builtins then
      []
    else
      begin
        have_undefined_builtins := true;
        List.filter
          (fun def -> IdSet.is_empty (IdSet.inter vs_ids (ids_of_def def)))
          undefined_builtin_val_specs
      end
  in
  let undefined_tu = function
    | Tu_aux (Tu_ty_id (Typ_aux (Typ_tup typs, _), id), _) ->
       mk_exp (E_app (id, List.map (fun typ -> mk_exp (E_cast (typ, mk_lit_exp L_undef))) typs))
    | Tu_aux (Tu_ty_id (typ, id), _) -> mk_exp (E_app (id, [mk_exp (E_cast (typ, mk_lit_exp L_undef))]))
  in
  let p_tup = function
    | [pat] -> pat
    | pats -> mk_pat (P_tup pats)
  in
  let undefined_td = function
    | TD_enum (id, ids, _) when not (IdSet.mem (prepend_id "undefined_" id) vs_ids) ->
       let typschm = typschm_of_string ("unit -> " ^ string_of_id id ^ " effect {undef}") in
       [mk_val_spec (VS_val_spec (typschm, prepend_id "undefined_" id, [], false));
        mk_fundef [mk_funcl (prepend_id "undefined_" id)
                            (mk_pat (P_lit (mk_lit L_unit)))
                            (if !opt_fast_undefined && List.length ids > 0 then
                               mk_exp (E_id (List.hd ids))
                             else
                               mk_exp (E_app (mk_id "internal_pick",
                                              [mk_exp (E_list (List.map (fun id -> mk_exp (E_id id)) ids))])))]]
    | TD_record (id, typq, fields, _) when not (IdSet.mem (prepend_id "undefined_" id) vs_ids) ->
       let pat = p_tup (quant_items typq |> List.map quant_item_param |> List.concat |> List.map (fun id -> mk_pat (P_id id))) in
       [mk_val_spec (VS_val_spec (undefined_typschm id typq, prepend_id "undefined_" id, [], false));
        mk_fundef [mk_funcl (prepend_id "undefined_" id)
                            pat
                            (mk_exp (E_record (List.map (fun (_, id) -> mk_fexp id (mk_lit_exp L_undef)) fields)))]]
    | TD_variant (id, typq, tus, _) when not (IdSet.mem (prepend_id "undefined_" id) vs_ids) ->
       let pat = p_tup (quant_items typq |> List.map quant_item_param |> List.concat |> List.map (fun id -> mk_pat (P_id id))) in
       let body =
         if !opt_fast_undefined && List.length tus > 0 then
           undefined_tu (List.hd tus)
         else
           (* Deduplicate arguments for each constructor to keep definitions
              manageable. *)
           let extract_tu = function
             | Tu_aux (Tu_ty_id (Typ_aux (Typ_tup typs, _), id), _) -> (id, typs)
             | Tu_aux (Tu_ty_id (typ, id), _) -> (id, [typ])
           in
           let record_arg_typs m (_,typs) =
             let m' =
               List.fold_left (fun m typ ->
                 TypMap.add typ (1 + try TypMap.find typ m with Not_found -> 0) m) TypMap.empty typs in
             TypMap.merge (fun _ x y -> match x,y with Some m, Some n -> Some (max m n)
             | None, x -> x
             | x, None -> x) m m'
           in
           let make_undef_var typ n (i,lbs,m) =
             let j = i+n in
             let rec aux k =
               if k = j then [] else
                 let v = mk_id ("u_" ^ string_of_int k) in
                 (mk_letbind (mk_pat (P_typ (typ,mk_pat (P_id v)))) (mk_lit_exp L_undef))::
                   (aux (k+1))
             in
             (j, aux i @ lbs, TypMap.add typ i m)
           in
           let make_constr m (id,typs) =
             let args, _ = List.fold_right (fun typ (acc,m) ->
               let i = TypMap.find typ m in
               (mk_exp (E_id (mk_id ("u_" ^ string_of_int i)))::acc,
                TypMap.add typ (i+1) m)) typs ([],m) in
             mk_exp (E_app (id, args))
           in
           let constr_args = List.map extract_tu tus in
           let typs_needed = List.fold_left record_arg_typs TypMap.empty constr_args in
           let (_,letbinds,typ_to_var) = TypMap.fold make_undef_var typs_needed (0,[],TypMap.empty) in
           List.fold_left (fun e lb -> mk_exp (E_let (lb,e)))
             (mk_exp (E_app (mk_id "internal_pick",
                             [mk_exp (E_list (List.map (make_constr typ_to_var) constr_args))]))) letbinds
       in
       [mk_val_spec (VS_val_spec (undefined_typschm id typq, prepend_id "undefined_" id, [], false));
        mk_fundef [mk_funcl (prepend_id "undefined_" id)
                      pat
                      body]]
    | _ -> []
  in
  let rec undefined_defs = function
    | DEF_type (TD_aux (td_aux, _)) as def :: defs ->
       def :: undefined_td td_aux @ undefined_defs defs
    | def :: defs ->
       def :: undefined_defs defs
    | [] -> []
  in
  undefined_builtins @ undefined_defs defs

let rec get_registers = function
  | DEF_reg_dec (DEC_aux (DEC_reg (_, _, typ, id), _)) :: defs -> (typ, id) :: get_registers defs
  | _ :: defs -> get_registers defs
  | [] -> []

let generate_initialize_registers vs_ids defs =
  let regs = get_registers defs in
  let initialize_registers =
    if IdSet.mem (mk_id "initialize_registers") vs_ids || regs = [] then []
    else
      [val_spec_of_string (mk_id "initialize_registers") "unit -> unit effect {undef, wreg}";
       mk_fundef [mk_funcl (mk_id "initialize_registers")
                           (mk_pat (P_lit (mk_lit L_unit)))
                           (mk_exp (E_block (List.map (fun (typ, id) -> mk_exp (E_assign (mk_lexp (LEXP_cast (typ, id)), mk_lit_exp L_undef))) regs)))]]
  in
  defs @ initialize_registers

let generate_enum_functions vs_ids defs =
  let rec gen_enums = function
    | DEF_type (TD_aux (TD_enum (id, elems, _), _)) as enum :: defs ->
       let enum_val_spec name quants typ =
         mk_val_spec (VS_val_spec (mk_typschm (mk_typquant quants) typ, name, [], !opt_enum_casts))
       in
       let range_constraint kid = nc_and (nc_lteq (nint 0) (nvar kid)) (nc_lteq (nvar kid) (nint (List.length elems - 1))) in

       (* Create a function that converts a number to an enum. *)
       let to_enum =
         let kid = mk_kid "e" in
         let name = append_id id "_of_num" in
         let pexp n id =
           let pat =
             if n = List.length elems - 1 then
               mk_pat (P_wild)
             else
               mk_pat (P_lit (mk_lit (L_num (Big_int.of_int n))))
           in
           mk_pexp (Pat_exp (pat, mk_exp (E_id id)))
         in
         let funcl =
           mk_funcl name
             (mk_pat (P_id (mk_id "arg#")))
             (mk_exp (E_case (mk_exp (E_id (mk_id "arg#")), List.mapi pexp elems)))
         in
         let range = range_typ (nint 0) (nint (List.length elems - 1)) in
         if IdSet.mem name vs_ids then []
         else
           [ enum_val_spec name
              [mk_qi_id K_int kid; mk_qi_nc (range_constraint kid)]
              (function_typ [atom_typ (nvar kid)] (mk_typ (Typ_id id)) no_effect);
             mk_fundef [funcl] ]
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
             (mk_exp (E_case (mk_exp (E_id (mk_id "arg#")), List.mapi pexp elems)))
         in
         if IdSet.mem name vs_ids then []
         else
           [ enum_val_spec name [] (function_typ [mk_typ (Typ_id id)] to_typ no_effect);
             mk_fundef [funcl] ]
       in
       enum :: to_enum @ from_enum @ gen_enums defs

    | def :: defs -> def :: gen_enums defs
    | [] -> []
  in
  gen_enums defs

let incremental_ctx = ref initial_ctx

let process_ast ?generate:(generate=true) ast =
  let ast, ctx = to_ast !incremental_ctx ast in
  incremental_ctx := ctx;
  let vs_ids = val_spec_ids ast.defs in
  if not !opt_undefined_gen && generate then
    { ast with defs = generate_enum_functions vs_ids ast.defs }
  else if generate then
    { ast with
      defs = ast.defs
             |> generate_undefineds vs_ids
             |> generate_enum_functions vs_ids
             |> generate_initialize_registers vs_ids
    }
  else
    ast

let ast_of_def_string_with f str =
  let def = Parser.def_eof Lexer.token (Lexing.from_string str) in
  process_ast (P.Defs [("", f [def])])

  
let ast_of_def_string str =
  let def = Parser.def_eof Lexer.token (Lexing.from_string str) in
  process_ast (P.Defs [("", [def])])

let defs_of_string str =
  let def = Parser.def_eof Lexer.token (Lexing.from_string str) in
  (process_ast (P.Defs [("", [def])])).defs
