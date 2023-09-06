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

open Libsail
open Ast
open Ast_defs
open Ast_util
open PPrint
open Type_check
open Util

module Big_int = Nat_big_num

(* Option to turn tracing features on or off *)
let opt_trace_ocaml = ref false

(* Option to not build generated ocaml by default *)
let opt_ocaml_nobuild = ref false
let opt_ocaml_coverage = ref false
let opt_ocaml_build_dir = ref "_sbuild"

(* OCaml variant type can have at most 246 non-constant
   constructors. *)
let ocaml_variant_max_constructors = 246

type ctx = { register_inits : tannot exp list; externs : id Bindings.t; val_specs : typ Bindings.t; records : IdSet.t }

let empty_ctx = { register_inits = []; externs = Bindings.empty; val_specs = Bindings.empty; records = IdSet.empty }

let gensym_counter = ref 0

let gensym () =
  let gs = "gs" ^ string_of_int !gensym_counter in
  incr gensym_counter;
  string gs

let zencode ctx id =
  try string (string_of_id (Bindings.find id ctx.externs)) with Not_found -> string (zencode_string (string_of_id id))

let zencode_upper ctx id =
  try string (string_of_id (Bindings.find id ctx.externs))
  with Not_found -> string (zencode_upper_string (string_of_id id))

let zencode_kid kid = string ("'" ^ zencode_string (string_of_id (id_of_kid kid)))

let ocaml_string_of id = string ("string_of_" ^ zencode_string (string_of_id id))

let ocaml_string_parens inside = string "\"(\" ^ " ^^ inside ^^ string " ^ \")\""

let ocaml_string_comma = string " ^ \", \" ^ "

let rec ocaml_string_typ (Typ_aux (typ_aux, l)) arg =
  match typ_aux with
  | Typ_id id when string_of_id id = "exception" -> string "Printexc.to_string" ^^ space ^^ arg
  | Typ_id id -> ocaml_string_of id ^^ space ^^ arg
  | Typ_app (id, []) -> ocaml_string_of id ^^ space ^^ arg
  | Typ_app (id, [A_aux (A_typ (Typ_aux (Typ_id eid, _)), _)]) when string_of_id id = "list" && string_of_id eid = "bit"
    ->
      string "string_of_bits" ^^ space ^^ arg
  | Typ_app (id, [A_aux (A_typ typ, _)]) when string_of_id id = "list" ->
      let farg = gensym () in
      separate space
        [
          string "string_of_list \", \"";
          parens (separate space [string "fun"; farg; string "->"; ocaml_string_typ typ farg]);
          arg;
        ]
  | Typ_app (_, _) -> string "\"APP\""
  | Typ_tuple typs ->
      let args = List.map (fun _ -> gensym ()) typs in
      let body =
        ocaml_string_parens
          (separate_map ocaml_string_comma (fun (typ, arg) -> ocaml_string_typ typ arg) (List.combine typs args))
      in
      parens (separate space [string "fun"; parens (separate (comma ^^ space) args); string "->"; body]) ^^ space ^^ arg
  | Typ_fn (typ1, typ2) -> string "\"FN\""
  | Typ_bidir (t1, t2) -> string "\"BIDIR\""
  | Typ_var kid -> string "\"VAR\""
  | Typ_exist _ -> assert false
  | Typ_internal_unknown -> raise (Reporting.err_unreachable l __POS__ "escaped Typ_internal_unknown")

let ocaml_typ_id ctx = function
  | id when Id.compare id (mk_id "string") = 0 -> string "string"
  | id when Id.compare id (mk_id "list") = 0 -> string "list"
  | id when Id.compare id (mk_id "bit") = 0 -> string "bit"
  | id when Id.compare id (mk_id "int") = 0 -> string "Big_int.num"
  | id when Id.compare id (mk_id "implicit") = 0 -> string "Big_int.num"
  | id when Id.compare id (mk_id "nat") = 0 -> string "Big_int.num"
  | id when Id.compare id (mk_id "bool") = 0 -> string "bool"
  | id when Id.compare id (mk_id "unit") = 0 -> string "unit"
  | id when Id.compare id (mk_id "real") = 0 -> string "Rational.t"
  | id when Id.compare id (mk_id "exception") = 0 -> string "exn"
  | id when Id.compare id (mk_id "register") = 0 -> string "ref"
  | id when IdSet.mem id ctx.records -> zencode_upper ctx id ^^ dot ^^ zencode ctx id
  | id -> zencode ctx id

let rec ocaml_typ ctx (Typ_aux (typ_aux, l)) =
  match typ_aux with
  | Typ_id id -> ocaml_typ_id ctx id
  | Typ_app (id, []) -> ocaml_typ_id ctx id
  | Typ_app (id, typs) -> parens (separate_map (string ", ") (ocaml_typ_arg ctx) typs) ^^ space ^^ ocaml_typ_id ctx id
  | Typ_tuple typs -> parens (separate_map (string " * ") (ocaml_typ ctx) typs)
  | Typ_fn (typs, typ) -> separate space [ocaml_typ ctx (Typ_aux (Typ_tuple typs, l)); string "->"; ocaml_typ ctx typ]
  | Typ_bidir _ -> raise (Reporting.err_general l "Ocaml doesn't support bidir types")
  | Typ_var kid -> zencode_kid kid
  | Typ_exist _ -> assert false
  | Typ_internal_unknown -> raise (Reporting.err_unreachable l __POS__ "escaped Typ_internal_unknown")

and ocaml_typ_arg ctx (A_aux (typ_arg_aux, _) as typ_arg) =
  match typ_arg_aux with
  | A_typ typ -> ocaml_typ ctx typ
  | _ -> failwith ("OCaml: unexpected type argument " ^ string_of_typ_arg typ_arg)

let ocaml_typquant (TypQ_aux (_, l) as typq) =
  let ocaml_qi = function
    | QI_aux (QI_id kopt, _) -> zencode_kid (kopt_kid kopt)
    | QI_aux (QI_constraint _, _) ->
        raise (Reporting.err_general l "Ocaml: type quantifiers should no longer contain constraints")
  in
  match quant_items typq with
  | [] -> empty
  | [qi] -> ocaml_qi qi
  | qis -> parens (separate_map (string ", ") ocaml_qi qis)

let string_lit str = dquotes (string (String.escaped str))

let ocaml_lit (L_aux (lit_aux, _)) =
  match lit_aux with
  | L_unit -> string "()"
  | L_zero -> string "B0"
  | L_one -> string "B1"
  | L_true -> string "true"
  | L_false -> string "false"
  | L_num n ->
      if Big_int.equal n Big_int.zero then string "Big_int.zero"
      else if Big_int.less_equal (Big_int.of_int min_int) n && Big_int.less_equal n (Big_int.of_int max_int) then
        parens (string "Big_int.of_int" ^^ space ^^ parens (string (Big_int.to_string n)))
      else parens (string "Big_int.of_string" ^^ space ^^ dquotes (string (Big_int.to_string n)))
  | L_undef -> failwith "undefined should have been re-written prior to ocaml backend"
  | L_string str -> string_lit str
  | L_real str -> parens (string "real_of_string" ^^ space ^^ dquotes (string (String.escaped str)))
  | _ -> string "LIT"

let pat_record_id l pat =
  match typ_of_pat pat with
  | Typ_aux (Typ_id id, _) when Env.is_record id (env_of_pat pat) -> id
  | Typ_aux (Typ_app (id, _), _) when Env.is_record id (env_of_pat pat) -> id
  | typ ->
      Reporting.unreachable l __POS__
        ("Found a struct without a record type when generating OCaml. Type found: " ^ string_of_typ typ)

let rec ocaml_pat ctx (P_aux (pat_aux, (l, _)) as pat) =
  match pat_aux with
  | P_id id -> begin
      match Env.lookup_id id (env_of_pat pat) with
      | Local (_, _) | Unbound _ -> zencode ctx id
      | Enum _ -> zencode_upper ctx id
      | _ -> failwith ("Ocaml: Cannot pattern match on register: " ^ string_of_pat pat)
    end
  | P_lit lit -> ocaml_lit lit
  | P_typ (_, pat) -> ocaml_pat ctx pat
  | P_tuple pats -> parens (separate_map (comma ^^ space) (ocaml_pat ctx) pats)
  | P_list pats -> brackets (separate_map (semi ^^ space) (ocaml_pat ctx) pats)
  | P_wild -> string "_"
  | P_as (pat, id) -> separate space [ocaml_pat ctx pat; string "as"; zencode ctx id]
  | P_app (id, pats) -> begin
      match Env.union_constructor_info id (env_of_pat pat) with
      | Some (_, m, _, _) when m > ocaml_variant_max_constructors ->
          (string "`" ^^ zencode_upper ctx id) ^^ space ^^ parens (separate_map (comma ^^ space) (ocaml_pat ctx) pats)
      | _ -> zencode_upper ctx id ^^ space ^^ parens (separate_map (comma ^^ space) (ocaml_pat ctx) pats)
    end
  | P_cons (hd_pat, tl_pat) -> ocaml_pat ctx hd_pat ^^ string " :: " ^^ ocaml_pat ctx tl_pat
  | P_struct (fpats, FP_no_wild) ->
      lbrace ^^ space
      ^^ separate_map (semi ^^ space) (fun (field, p) -> ocaml_fpat (pat_record_id l pat) ctx field p) fpats
      ^^ space ^^ rbrace
  | _ -> string ("PAT<" ^ string_of_pat pat ^ ">")

and ocaml_fpat record_id ctx id pat =
  separate space [zencode_upper ctx record_id ^^ dot ^^ zencode ctx id; equals; ocaml_pat ctx pat]

let begin_end doc = group (string "begin" ^^ nest 2 (break 1 ^^ doc) ^/^ string "end")

(* Returns true if a type is a register being passed by name *)
let is_passed_by_name = function Typ_aux (Typ_app (tid, _), _) -> string_of_id tid = "register" | _ -> false

let record_id l exp =
  match typ_of exp with
  | Typ_aux (Typ_id id, _) when Env.is_record id (env_of exp) -> id
  | Typ_aux (Typ_app (id, _), _) when Env.is_record id (env_of exp) -> id
  | typ ->
      Reporting.unreachable l __POS__
        ("Found a struct without a record type when generating OCaml. Type found: " ^ string_of_typ typ)

let rec ocaml_exp ctx (E_aux (exp_aux, (l, _)) as exp) =
  match exp_aux with
  | E_app (f, xs) -> begin
      match Env.union_constructor_info f (env_of exp) with
      | Some (_, m, _, _) ->
          let name =
            if m > ocaml_variant_max_constructors then string "`" ^^ zencode_upper ctx f else zencode_upper ctx f
          in
          begin
            match xs with
            | [x] -> name ^^ space ^^ ocaml_atomic_exp ctx x
            | xs -> name ^^ space ^^ parens (separate_map (comma ^^ space) (ocaml_atomic_exp ctx) xs)
          end
      | None -> begin
          match xs with
          | [x] -> zencode ctx f ^^ space ^^ ocaml_atomic_exp ctx x
          (* Make sure we get the correct short circuiting semantics for and and or *)
          | [x; y] when string_of_id f = "and_bool" ->
              separate space [ocaml_atomic_exp ctx x; string "&&"; ocaml_atomic_exp ctx y]
          | [x; y] when string_of_id f = "or_bool" ->
              separate space [ocaml_atomic_exp ctx x; string "||"; ocaml_atomic_exp ctx y]
          | xs -> zencode ctx f ^^ space ^^ parens (separate_map (comma ^^ space) (ocaml_atomic_exp ctx) xs)
        end
    end
  | E_vector_subrange (exp1, exp2, exp3) -> begin
      match Env.get_default_order_opt (env_of exp) with
      | Some (Ord_aux (Ord_inc, _)) ->
          string "subrange_inc" ^^ space
          ^^ parens (separate_map (comma ^^ space) (ocaml_atomic_exp ctx) [exp1; exp2; exp3])
      | _ ->
          string "subrange" ^^ space ^^ parens (separate_map (comma ^^ space) (ocaml_atomic_exp ctx) [exp1; exp2; exp3])
    end
  | E_return exp -> separate space [string "r.return"; ocaml_atomic_exp ctx exp]
  | E_assert (exp, _) -> separate space [string "assert"; ocaml_atomic_exp ctx exp]
  | E_typ (_, exp) -> ocaml_exp ctx exp
  | E_block [exp] -> ocaml_exp ctx exp
  | E_block [] -> string "()"
  | E_block exps -> begin_end (ocaml_block ctx exps)
  | E_field (exp, id) -> ocaml_atomic_exp ctx exp ^^ dot ^^ zencode ctx id
  | E_exit exp -> string "exit 0"
  | E_throw exp -> string "raise" ^^ space ^^ ocaml_atomic_exp ctx exp
  | E_match (exp, pexps) ->
      begin_end (separate space [string "match"; ocaml_atomic_exp ctx exp; string "with"] ^/^ ocaml_pexps ctx pexps)
  | E_try (exp, pexps) ->
      begin_end (separate space [string "try"; ocaml_atomic_exp ctx exp; string "with"] ^/^ ocaml_pexps ctx pexps)
  | E_assign (lexp, exp) -> ocaml_assignment ctx lexp exp
  | E_if (c, t, e) ->
      separate space
        [
          string "if";
          ocaml_atomic_exp ctx c;
          string "then";
          ocaml_atomic_exp ctx t;
          string "else";
          ocaml_atomic_exp ctx e;
        ]
  | E_struct fexps ->
      enclose lbrace rbrace (group (separate_map (semi ^^ break 1) (ocaml_fexp (record_id l exp) ctx) fexps))
  | E_struct_update (exp, fexps) ->
      enclose lbrace rbrace
        (separate space
           [
             ocaml_atomic_exp ctx exp;
             string "with";
             separate_map (semi ^^ space) (ocaml_fexp (record_id l exp) ctx) fexps;
           ]
        )
  | E_let (lb, exp) -> separate space [string "let"; ocaml_letbind ctx lb; string "in"] ^/^ ocaml_exp ctx exp
  | E_var (lexp, exp1, exp2) ->
      separate space
        [
          string "let";
          ocaml_atomic_lexp ctx lexp;
          equals;
          string "ref";
          parens
            (ocaml_atomic_exp ctx exp1 ^^ space ^^ colon ^^ space ^^ ocaml_typ ctx (Rewrites.simple_typ (typ_of exp1)));
          string "in";
        ]
      ^/^ ocaml_exp ctx exp2
  | E_loop (Until, _, cond, body) ->
      let loop_body =
        (ocaml_atomic_exp ctx body ^^ semi)
        ^/^ separate space [string "if"; ocaml_atomic_exp ctx cond; string "then ()"; string "else loop ()"]
      in
      (string "let rec loop () =" ^//^ loop_body) ^/^ string "in" ^/^ string "loop ()"
  | E_loop (While, _, cond, body) ->
      let loop_body =
        separate space
          [
            string "if";
            ocaml_atomic_exp ctx cond;
            string "then";
            parens (ocaml_atomic_exp ctx body ^^ semi ^^ space ^^ string "loop ()");
            string "else ()";
          ]
      in
      (string "let rec loop () =" ^//^ loop_body) ^/^ string "in" ^/^ string "loop ()"
  | E_lit _ | E_list _ | E_id _ | E_tuple _ | E_ref _ -> ocaml_atomic_exp ctx exp
  | E_for (id, exp_from, exp_to, exp_step, ord, exp_body) ->
      let loop_var =
        separate space [string "let"; zencode ctx id; equals; string "ref"; ocaml_atomic_exp ctx exp_from; string "in"]
      in
      let loop_mod =
        match ord with
        | Ord_aux (Ord_inc, _) ->
            string "Big_int.add" ^^ space ^^ zencode ctx id ^^ space ^^ ocaml_atomic_exp ctx exp_step
        | Ord_aux (Ord_dec, _) ->
            string "Big_int.sub" ^^ space ^^ zencode ctx id ^^ space ^^ ocaml_atomic_exp ctx exp_step
      in
      let loop_compare =
        match ord with
        | Ord_aux (Ord_inc, _) -> string "Big_int.less_equal"
        | Ord_aux (Ord_dec, _) -> string "Big_int.greater_equal"
      in
      let loop_body =
        separate space [string "if"; loop_compare; zencode ctx id; ocaml_atomic_exp ctx exp_to]
        ^/^ separate space
              [
                string "then";
                parens (ocaml_atomic_exp ctx exp_body ^^ semi ^^ space ^^ string "loop" ^^ space ^^ parens loop_mod);
              ]
        ^/^ string "else ()"
      in
      (string ("let rec loop " ^ zencode_string (string_of_id id) ^ " =") ^//^ loop_body)
      ^/^ string "in" ^/^ string "loop" ^^ space ^^ ocaml_atomic_exp ctx exp_from
  | E_cons (x, xs) -> ocaml_exp ctx x ^^ string " :: " ^^ ocaml_exp ctx xs
  | _ -> string ("EXP(" ^ string_of_exp exp ^ ")")

and ocaml_letbind ctx (LB_aux (lb_aux, _)) =
  match lb_aux with LB_val (pat, exp) -> separate space [ocaml_pat ctx pat; equals; ocaml_atomic_exp ctx exp]

and ocaml_pexps ctx = function
  | [pexp] -> ocaml_pexp ctx pexp
  | pexp :: pexps -> ocaml_pexp ctx pexp ^/^ ocaml_pexps ctx pexps
  | [] -> empty

and ocaml_pexp ctx = function
  | Pat_aux (Pat_exp (pat, exp), _) ->
      separate space [bar; ocaml_pat ctx pat; string "->"] ^//^ group (ocaml_exp ctx exp)
  | Pat_aux (Pat_when (pat, wh, exp), _) ->
      separate space [bar; ocaml_pat ctx pat; string "when"; ocaml_atomic_exp ctx wh; string "->"]
      ^//^ group (ocaml_exp ctx exp)

and ocaml_block ctx = function
  | [exp] -> ocaml_exp ctx exp
  | (E_aux (E_let _, _) as exp) :: exps -> ocaml_atomic_exp ctx exp ^^ semi ^/^ ocaml_block ctx exps
  | exp :: exps -> ocaml_exp ctx exp ^^ semi ^/^ ocaml_block ctx exps
  | _ -> assert false

and ocaml_fexp record_id ctx (FE_aux (FE_fexp (id, exp), _)) =
  separate space [zencode_upper ctx record_id ^^ dot ^^ zencode ctx id; equals; ocaml_exp ctx exp]

and ocaml_atomic_exp ctx (E_aux (exp_aux, _) as exp) =
  match exp_aux with
  | E_lit lit -> ocaml_lit lit
  | E_ref id -> zencode ctx id
  | E_id id -> begin
      match Env.lookup_id id (env_of exp) with
      | Local (Immutable, _) | Unbound _ -> zencode ctx id
      | Enum _ -> zencode_upper ctx id
      | Register _ when is_passed_by_name (typ_of exp) -> zencode ctx id
      | Register typ ->
          if !opt_trace_ocaml then (
            let var = gensym () in
            let str_typ = parens (ocaml_string_typ (Rewrites.simple_typ typ) var) in
            parens
              (separate space
                 [
                   string "let";
                   var;
                   equals;
                   bang ^^ zencode ctx id;
                   string "in";
                   string "trace_read" ^^ space ^^ string_lit (string_of_id id) ^^ space ^^ str_typ ^^ semi;
                   var;
                 ]
              )
          )
          else bang ^^ zencode ctx id
      | Local (Mutable, _) -> bang ^^ zencode ctx id
    end
  | E_list exps -> enclose lbracket rbracket (separate_map (semi ^^ space) (ocaml_exp ctx) exps)
  | E_tuple exps -> parens (separate_map (comma ^^ space) (ocaml_exp ctx) exps)
  | _ -> parens (ocaml_exp ctx exp)

and ocaml_assignment ctx (LE_aux (lexp_aux, _) as lexp) exp =
  match lexp_aux with
  | LE_typ (_, id) | LE_id id -> begin
      match Env.lookup_id id (env_of exp) with
      | Register typ ->
          let var = gensym () in
          let traced_exp =
            if !opt_trace_ocaml then (
              let var = gensym () in
              let str_typ = parens (ocaml_string_typ (Rewrites.simple_typ typ) var) in
              parens
                (separate space
                   [
                     string "let";
                     var;
                     equals;
                     ocaml_atomic_exp ctx exp;
                     string "in";
                     string "trace_write" ^^ space ^^ string_lit (string_of_id id) ^^ space ^^ str_typ ^^ semi;
                     var;
                   ]
                )
            )
            else ocaml_atomic_exp ctx exp
          in
          separate space [zencode ctx id; string ":="; traced_exp]
      | _ -> separate space [zencode ctx id; string ":="; parens (ocaml_exp ctx exp)]
    end
  | LE_deref ref_exp -> separate space [ocaml_atomic_exp ctx ref_exp; string ":="; parens (ocaml_exp ctx exp)]
  | _ -> string ("LEXP<" ^ string_of_lexp lexp ^ ">")

and ocaml_lexp ctx (LE_aux (lexp_aux, _) as lexp) =
  match lexp_aux with
  | LE_typ _ | LE_id _ -> ocaml_atomic_lexp ctx lexp
  | LE_deref exp -> ocaml_exp ctx exp
  | _ -> string ("LEXP<" ^ string_of_lexp lexp ^ ">")

and ocaml_atomic_lexp ctx (LE_aux (lexp_aux, _) as lexp) =
  match lexp_aux with LE_typ (_, id) -> zencode ctx id | LE_id id -> zencode ctx id | _ -> parens (ocaml_lexp ctx lexp)

let rec get_initialize_registers = function
  | DEF_aux
      ( DEF_fundef
          (FD_aux
            (FD_function (_, _, [FCL_aux (FCL_funcl (id, Pat_aux (Pat_exp (_, E_aux (E_block inits, _)), _)), _)]), _)
            ),
        _
      )
    :: defs
    when Id.compare id (mk_id "initialize_registers") = 0 ->
      inits
  | _ :: defs -> get_initialize_registers defs
  | [] -> []

let initial_value_for id inits =
  let find_reg = function
    | E_aux (E_assign (LE_aux (LE_id reg_id, _), init), _) when Id.compare id reg_id = 0 -> Some init
    | _ -> None
  in
  match Util.option_first find_reg inits with
  | Some init -> init
  | None -> failwith ("No assignment to register ^ " ^ string_of_id id ^ " in initialize_registers")

let ocaml_dec_spec ctx (DEC_aux (reg, _)) =
  match reg with
  | DEC_reg (typ, id, None) ->
      separate space
        [
          string "let";
          zencode ctx id;
          colon;
          parens (ocaml_typ ctx typ);
          string "ref";
          equals;
          string "ref";
          parens (ocaml_exp ctx (initial_value_for id ctx.register_inits));
        ]
  | DEC_reg (typ, id, Some exp) ->
      separate space
        [
          string "let";
          zencode ctx id;
          colon;
          parens (ocaml_typ ctx typ);
          string "ref";
          equals;
          string "ref";
          parens (ocaml_exp ctx exp);
        ]

let first_function = ref true

let function_header () =
  if !first_function then (
    first_function := false;
    string "let rec"
  )
  else string "and"

let funcls_id = function [] -> failwith "Ocaml: empty function" | FCL_aux (FCL_funcl (id, _), _) :: _ -> id

let ocaml_funcl_match ctx (FCL_aux (FCL_funcl (id, pexp), _)) = ocaml_pexp ctx pexp

let rec ocaml_funcl_matches ctx = function
  | [] -> failwith "Ocaml: empty function"
  | [clause] -> ocaml_funcl_match ctx clause
  | clause :: clauses -> ocaml_funcl_match ctx clause ^/^ ocaml_funcl_matches ctx clauses

let ocaml_funcls ctx =
  (* Create functions string_of_arg and string_of_ret that print the argument and return types of the function respectively *)
  let trace_info typ1 typ2 =
    let arg_sym = gensym () in
    let ret_sym = gensym () in
    let kids = KidSet.union (tyvars_of_typ typ1) (tyvars_of_typ typ2) in
    let foralls =
      if KidSet.is_empty kids then empty else separate space (List.map zencode_kid (KidSet.elements kids)) ^^ dot
    in
    let string_of_arg =
      separate space
        [
          function_header ();
          arg_sym;
          colon;
          foralls;
          ocaml_typ ctx typ1;
          string "-> string = fun arg ->";
          ocaml_string_typ typ1 (string "arg");
        ]
    in
    let string_of_ret =
      separate space
        [
          function_header ();
          ret_sym;
          colon;
          foralls;
          ocaml_typ ctx typ2;
          string "-> string = fun arg ->";
          ocaml_string_typ typ2 (string "arg");
        ]
    in
    (arg_sym, string_of_arg, ret_sym, string_of_ret)
  in
  let sail_call id arg_sym pat_sym ret_sym =
    if !opt_trace_ocaml then
      separate space
        [string "sail_trace_call"; string_lit (string_of_id id); parens (arg_sym ^^ space ^^ pat_sym); ret_sym]
    else separate space [string "sail_call"]
  in
  let ocaml_funcl call string_of_arg string_of_ret =
    if !opt_trace_ocaml then call ^^ twice hardline ^^ string_of_arg ^^ twice hardline ^^ string_of_ret else call
  in
  function
  | [] -> failwith "Ocaml: empty function"
  | [FCL_aux (FCL_funcl (id, pexp), _)] ->
      if Bindings.mem id ctx.externs then
        string ("(* Omitting externed function " ^ string_of_id id ^ " *)") ^^ hardline
      else (
        let arg_typs, ret_typ =
          match Bindings.find id ctx.val_specs with
          | Typ_aux (Typ_fn (typs, typ), _) -> (typs, typ)
          | _ -> failwith "Found val spec which was not a function!"
          | exception Not_found -> failwith ("No val spec found for " ^ string_of_id id)
        in
        (* Any remaining type variables after simple_typ rewrite should
           indicate Type-polymorphism. If we have it, we need to generate
           explicit type signatures with universal quantification. *)
        let kids = List.fold_left KidSet.union (tyvars_of_typ ret_typ) (List.map tyvars_of_typ arg_typs) in
        let pat_sym = gensym () in
        let pat, guard, exp =
          match pexp with
          | Pat_aux (Pat_exp (pat, exp), _) -> (pat, None, exp)
          | Pat_aux (Pat_when (pat, guard, exp), _) -> (pat, Some guard, exp)
        in
        let ocaml_guarded_exp ctx exp = function
          | Some guard ->
              separate space
                [
                  string "if";
                  ocaml_exp ctx guard;
                  string "then";
                  parens (ocaml_exp ctx exp);
                  string "else";
                  Printf.ksprintf string "failwith \"Pattern match failure in %s\"" (string_of_id id);
                ]
          | None -> ocaml_exp ctx exp
        in
        let annot_pat =
          let pat =
            if KidSet.is_empty kids then
              parens (ocaml_pat ctx pat ^^ space ^^ colon ^^ space ^^ ocaml_typ ctx (mk_typ (Typ_tuple arg_typs)))
            else ocaml_pat ctx pat
          in
          if !opt_trace_ocaml then parens (separate space [pat; string "as"; pat_sym]) else pat
        in
        let call_header = function_header () in
        let arg_sym, string_of_arg, ret_sym, string_of_ret = trace_info (mk_typ (Typ_tuple arg_typs)) ret_typ in
        let call =
          if KidSet.is_empty kids then
            separate space
              [
                call_header;
                zencode ctx id;
                annot_pat;
                colon;
                ocaml_typ ctx ret_typ;
                equals;
                sail_call id arg_sym pat_sym ret_sym;
                string "(fun r ->";
              ]
            ^//^ ocaml_guarded_exp ctx exp guard ^^ rparen
          else
            separate space
              [
                call_header;
                zencode ctx id;
                colon;
                separate space (List.map zencode_kid (KidSet.elements kids)) ^^ dot;
                ocaml_typ ctx (mk_typ (Typ_tuple arg_typs));
                string "->";
                ocaml_typ ctx ret_typ;
                equals;
                string "fun";
                annot_pat;
                string "->";
                sail_call id arg_sym pat_sym ret_sym;
                string "(fun r ->";
              ]
            ^//^ ocaml_guarded_exp ctx exp guard ^^ rparen
        in
        ocaml_funcl call string_of_arg string_of_ret
      )
  | funcls ->
      let id = funcls_id funcls in
      if Bindings.mem id ctx.externs then
        string ("(* Omitting externed function " ^ string_of_id id ^ " *)") ^^ hardline
      else (
        let arg_typs, ret_typ =
          match Bindings.find id ctx.val_specs with
          | Typ_aux (Typ_fn (typs, typ), _) -> (typs, typ)
          | _ -> failwith "Found val spec which was not a function!"
        in
        let kids = List.fold_left KidSet.union (tyvars_of_typ ret_typ) (List.map tyvars_of_typ arg_typs) in
        if not (KidSet.is_empty kids) then failwith "Cannot handle polymorphic multi-clause function in OCaml backend"
        else ();
        let pat_sym = gensym () in
        let call_header = function_header () in
        let arg_sym, string_of_arg, ret_sym, string_of_ret = trace_info (mk_typ (Typ_tuple arg_typs)) ret_typ in
        let call =
          separate space
            [
              call_header;
              zencode ctx id;
              parens (pat_sym ^^ space ^^ colon ^^ space ^^ ocaml_typ ctx (mk_typ (Typ_tuple arg_typs)));
              equals;
              sail_call id arg_sym pat_sym ret_sym;
              string "(fun r ->";
            ]
          ^//^ (separate space [string "match"; pat_sym; string "with"] ^^ hardline ^^ ocaml_funcl_matches ctx funcls)
          ^^ rparen
        in
        ocaml_funcl call string_of_arg string_of_ret
      )

let ocaml_fundef ctx (FD_aux (FD_function (_, _, funcls), _)) = ocaml_funcls ctx funcls

let rec ocaml_fields ctx =
  let ocaml_field typ id = separate space [zencode ctx id; colon; ocaml_typ ctx typ] in
  function
  | [(typ, id)] -> ocaml_field typ id
  | (typ, id) :: fields -> ocaml_field typ id ^^ semi ^/^ ocaml_fields ctx fields
  | [] -> empty

let rec ocaml_cases polymorphic_variant ctx =
  let ocaml_case (Tu_aux (Tu_ty_id (typ, id), _)) =
    let name = if polymorphic_variant then string "`" ^^ zencode_upper ctx id else zencode_upper ctx id in
    separate space [bar; name; string "of"; ocaml_typ ctx typ]
  in
  function
  | [tu] -> ocaml_case tu | tu :: tus -> ocaml_case tu ^/^ ocaml_cases polymorphic_variant ctx tus | [] -> empty

let rec ocaml_exceptions ctx =
  let ocaml_exception (Tu_aux (Tu_ty_id (typ, id), _)) =
    separate space [string "exception"; zencode_upper ctx id; string "of"; ocaml_typ ctx typ]
  in
  function
  | [tu] -> ocaml_exception tu
  | tu :: tus -> ocaml_exception tu ^^ string ";;" ^^ hardline ^^ ocaml_exceptions ctx tus
  | [] -> empty

let rec ocaml_enum ctx = function
  | [id] -> zencode_upper ctx id
  | id :: ids -> zencode_upper ctx id ^/^ bar ^^ space ^^ ocaml_enum ctx ids
  | [] -> empty

(* We generate a string_of_X ocaml function for each type X, to be used for debugging purposes *)

let ocaml_def_end = string ";;" ^^ twice hardline

let ocaml_string_of_enum ctx id ids =
  let ocaml_case id = separate space [bar; zencode_upper ctx id; string "->"; string ("\"" ^ string_of_id id ^ "\"")] in
  separate space [string "let"; ocaml_string_of id; equals; string "function"] ^//^ separate_map hardline ocaml_case ids

let ocaml_struct_type ctx id = zencode_upper ctx id ^^ dot ^^ zencode ctx id

let ocaml_string_of_struct ctx struct_id typq fields =
  let arg = gensym () in
  let ocaml_field (typ, id) =
    separate space
      [
        string (string_of_id id ^ " = \"");
        string "^";
        ocaml_string_typ typ (arg ^^ dot ^^ zencode_upper ctx struct_id ^^ dot ^^ zencode ctx id);
      ]
  in
  separate space
    [
      string "let";
      ocaml_string_of struct_id;
      parens (arg ^^ space ^^ colon ^^ space ^^ ocaml_typquant typq ^^ space ^^ ocaml_struct_type ctx struct_id);
      equals;
    ]
  ^//^ string "\"{"
  ^^ separate_map (hardline ^^ string "^ \", ") ocaml_field fields
  ^^ string " ^ \"}\""

let ocaml_string_of_abbrev ctx id typq typ =
  let arg = gensym () in
  separate space [string "let"; ocaml_string_of id; parens (arg ^^ space ^^ colon ^^ space ^^ zencode ctx id); equals]
  ^//^ ocaml_string_typ typ arg

let ocaml_string_of_variant ctx id typq cases =
  separate space [string "let"; ocaml_string_of id; string "_"; equals; string "\"VARIANT\""]

let ocaml_typedef ctx (TD_aux (td_aux, (l, _))) =
  match td_aux with
  | TD_record (id, typq, fields, _) ->
      (separate space [string "module"; zencode_upper ctx id; equals; string "struct"]
      ^//^ ((separate space [string "type"; ocaml_typquant typq; zencode ctx id; equals; lbrace]
            ^//^ ocaml_fields ctx fields
            )
           ^/^ rbrace
           )
      ^/^ string "end"
      )
      ^^ ocaml_def_end
      ^^ ocaml_string_of_struct ctx id typq fields
      ^^ ocaml_def_end
  | TD_variant (id, _, cases, _) when string_of_id id = "exception" -> ocaml_exceptions ctx cases ^^ ocaml_def_end
  | TD_variant (id, typq, cases, _) ->
      ( if List.length cases > ocaml_variant_max_constructors then
          separate space [string "type"; ocaml_typquant typq; zencode ctx id; equals; string "["]
          ^//^ ocaml_cases true ctx cases ^/^ string "]"
        else
          separate space [string "type"; ocaml_typquant typq; zencode ctx id; equals] ^//^ ocaml_cases false ctx cases
      )
      ^^ ocaml_def_end
      ^^ ocaml_string_of_variant ctx id typq cases
      ^^ ocaml_def_end
  | TD_enum (id, ids, _) ->
      (separate space [string "type"; zencode ctx id; equals] ^//^ bar ^^ space ^^ ocaml_enum ctx ids)
      ^^ ocaml_def_end ^^ ocaml_string_of_enum ctx id ids ^^ ocaml_def_end
  | TD_abbrev (id, typq, A_aux (A_typ typ, _)) ->
      separate space [string "type"; ocaml_typquant typq; zencode ctx id; equals; ocaml_typ ctx typ]
      ^^ ocaml_def_end ^^ ocaml_string_of_abbrev ctx id typq typ ^^ ocaml_def_end
  | TD_abbrev _ -> empty
  | TD_bitfield _ -> Reporting.unreachable l __POS__ "Bitfield should be re-written"

let get_externs defs =
  let extern_id (VS_aux (VS_val_spec (typschm, id, exts), _)) =
    match Ast_util.extern_assoc "ocaml" exts with None -> [] | Some ext -> [(id, mk_id ext)]
  in
  let rec extern_ids = function
    | DEF_aux (DEF_val vs, _) :: defs -> extern_id vs :: extern_ids defs
    | def :: defs -> extern_ids defs
    | [] -> []
  in
  List.fold_left (fun exts (id, name) -> Bindings.add id name exts) Bindings.empty (List.concat (extern_ids defs))

let nf_group doc =
  first_function := true;
  group doc

let ocaml_def ctx (DEF_aux (aux, _)) =
  match aux with
  | DEF_register ds -> nf_group (ocaml_dec_spec ctx ds) ^^ ocaml_def_end
  | DEF_fundef fd -> group (ocaml_fundef ctx fd) ^^ twice hardline
  | DEF_internal_mutrec fds ->
      separate_map (twice hardline) (fun fd -> group (ocaml_fundef ctx fd)) fds ^^ twice hardline
  | DEF_type td -> nf_group (ocaml_typedef ctx td)
  | DEF_let lb -> nf_group (string "let" ^^ space ^^ ocaml_letbind ctx lb) ^^ ocaml_def_end
  | _ -> empty

let val_spec_typs defs =
  let typs = ref Bindings.empty in
  let val_spec_typ (VS_aux (vs_aux, _)) =
    match vs_aux with VS_val_spec (TypSchm_aux (TypSchm_ts (_, typ), _), id, _) -> typs := Bindings.add id typ !typs
  in
  let rec vs_typs = function
    | DEF_aux (DEF_val vs, _) :: defs ->
        val_spec_typ vs;
        vs_typs defs
    | _ :: defs -> vs_typs defs
    | [] -> []
  in
  ignore (vs_typs defs);
  !typs

(* Code to produce test value generators for a given set of types.

   This needs type definitions from the initial type checked Sail so that the
   full type information is available.  For example, vectors are simplified to
   lists, so to produce lists of the right length we need to know what the
   size of the vector is.
*)

let orig_types_for_ocaml_generator defs =
  List.filter_map (function DEF_aux (DEF_type td, _) -> Some td | _ -> None) defs

let ocaml_pp_generators ctx defs orig_types required =
  let add_def typemap td = Bindings.add (id_of_type_def td) td typemap in
  let typemap = List.fold_left add_def Bindings.empty orig_types in
  let required = IdSet.of_list required in
  let rec always_add_req_from_id required id =
    match Bindings.find id typemap with
    | td -> add_req_from_td (IdSet.add id required) td
    | exception Not_found ->
        if Bindings.mem id Type_check.Env.builtin_typs then IdSet.add id required
        else raise (Reporting.err_general (id_loc id) ("Required generator of unknown type " ^ string_of_id id))
  and add_req_from_id required id = if IdSet.mem id required then required else always_add_req_from_id required id
  and add_req_from_typ required (Typ_aux (typ, _) as full_typ) =
    match typ with
    | Typ_id id -> add_req_from_id required id
    | Typ_var _ -> required
    | Typ_internal_unknown | Typ_fn _ | Typ_bidir _ ->
        raise
          (Reporting.err_unreachable (typ_loc full_typ) __POS__
             ("Required generator for type that should not appear: " ^ string_of_typ full_typ)
          )
    | Typ_tuple typs -> List.fold_left add_req_from_typ required typs
    | Typ_exist _ ->
        raise
          (Reporting.err_todo (typ_loc full_typ)
             ("Generators for existential types not yet supported: " ^ string_of_typ full_typ)
          )
    | Typ_app (id, args) -> List.fold_left add_req_from_typarg (add_req_from_id required id) args
  and add_req_from_typarg required (A_aux (arg, _)) =
    match arg with A_typ typ -> add_req_from_typ required typ | A_nexp _ | A_bool _ -> required
  and add_req_from_td required (TD_aux (td, (l, _))) =
    match td with
    | TD_abbrev (_, _, A_aux (A_typ typ, _)) -> add_req_from_typ required typ
    | TD_abbrev _ -> required
    | TD_record (_, _, fields, _) -> List.fold_left (fun req (typ, _) -> add_req_from_typ req typ) required fields
    | TD_variant (_, _, variants, _) ->
        List.fold_left (fun req (Tu_aux (Tu_ty_id (typ, _), _)) -> add_req_from_typ req typ) required variants
    | TD_enum _ -> required
    | TD_bitfield _ -> raise (Reporting.err_todo l "Generators for bitfields not yet supported")
  in
  let required = IdSet.fold (fun id req -> always_add_req_from_id req id) required required in
  let type_name id = zencode_string (string_of_id id) in
  let make_gen_field id =
    let allquants =
      match Bindings.find id typemap with
      | TD_aux (td, _) -> (
          match td with
          | TD_abbrev (_, tqs, A_aux (A_typ _, _)) -> tqs
          | TD_record (_, tqs, _, _) -> tqs
          | TD_variant (_, tqs, _, _) -> tqs
          | TD_enum _ -> TypQ_aux (TypQ_no_forall, Unknown)
          | TD_abbrev (_, _, _) -> assert false
          | TD_bitfield _ -> assert false
        )
      | exception Not_found -> Bindings.find id Type_check.Env.builtin_typs
    in
    let tquants = quant_kopts allquants in
    let gen_tyvars = List.map (fun k -> kopt_kid k |> zencode_kid) (List.filter is_typ_kopt tquants) in
    let print_quant kindedid =
      if is_int_kopt kindedid then string "int"
      else parens (separate space [string "generators"; string "->"; zencode_kid (kopt_kid kindedid)])
    in
    let name = "gen_" ^ type_name id in
    let make_tyarg kindedid =
      if is_int_kopt kindedid then mk_typ_arg (A_nexp (nvar (kopt_kid kindedid)))
      else mk_typ_arg (A_typ (mk_typ (Typ_var (kopt_kid kindedid))))
    in
    let targs = List.map make_tyarg tquants in
    let gen_tyvars_pp = match gen_tyvars with [] -> empty | _ -> separate space gen_tyvars ^^ dot ^^ space in
    let out_typ = mk_typ (Typ_app (id, targs)) in
    let out_typ = Rewrites.simple_typ out_typ in
    let types = (string "generators" :: List.map print_quant tquants) @ [ocaml_typ ctx out_typ] in
    string name ^^ colon ^^ space ^^ gen_tyvars_pp ^^ separate (string " -> ") types
  in
  let fields = separate_map (string ";" ^^ break 1) make_gen_field (IdSet.elements required) in
  let gen_record_type_pp =
    string "type generators = {" ^^ group (nest 2 (break 0 ^^ fields) ^^ break 0) ^^ string "}"
  in
  let make_rand_gen id =
    if Bindings.mem id Type_check.Env.builtin_typs then empty
    else (
      let mk_arg kid = string (zencode_string (string_of_kid kid)) in
      let rec gen_type (Typ_aux (typ, l) as full_typ) =
        let typ_str, args_pp =
          match typ with
          | Typ_id id -> (type_name id, [string "g"])
          | Typ_app (id, args) -> (type_name id, string "g" :: List.map typearg args)
          | _ -> raise (Reporting.err_todo l ("Unsupported type for generators: " ^ string_of_typ full_typ))
        in
        let args_pp = match args_pp with [] -> empty | _ -> space ^^ separate space args_pp in
        string ("g.gen_" ^ typ_str) ^^ args_pp
      and typearg (A_aux (arg, l)) =
        match arg with
        | A_nexp (Nexp_aux (nexp, l) as full_nexp) -> (
            match nexp with
            | Nexp_constant c -> string (Big_int.to_string c) (* TODO: overflow *)
            | Nexp_var v -> mk_arg v
            | _ -> raise (Reporting.err_todo l ("Unsupported nexp for generators: " ^ string_of_nexp full_nexp))
          )
        | A_typ typ -> parens (string "fun g -> " ^^ gen_type typ)
        | A_bool nc ->
            raise (Reporting.err_todo l ("Unsupported constraint for generators: " ^ string_of_n_constraint nc))
      in
      let make_subgen (Typ_aux (typ, l) as full_typ) =
        let typ_str, args_pp =
          match typ with
          | Typ_id id -> (type_name id, [])
          | Typ_app (id, args) -> (type_name id, List.map typearg args)
          | _ -> raise (Reporting.err_todo l ("Unsupported type for generators: " ^ string_of_typ full_typ))
        in
        let args_pp = match args_pp with [] -> empty | _ -> space ^^ separate space args_pp in
        string ("g.gen_" ^ typ_str) ^^ space ^^ string "g" ^^ args_pp
      in
      let make_variant (Tu_aux (Tu_ty_id (typ, id), _)) =
        let arg_typs =
          match typ with Typ_aux (Typ_fn (typs, _), _) -> typs | Typ_aux (Typ_tuple typs, _) -> typs | _ -> [typ]
        in
        zencode_upper ctx id ^^ space ^^ parens (separate_map (string ", ") make_subgen arg_typs)
      in
      let rand_variant variant = parens (string "fun g -> " ^^ make_variant variant) in
      let variant_constructor (Tu_aux (Tu_ty_id (_, id), _)) = dquotes (string (string_of_id id)) in
      let build_constructor variant =
        separate space [bar; variant_constructor variant; string "->"; make_variant variant]
      in
      let enum_constructor id = dquotes (string (string_of_id id)) in
      let build_enum_constructor id =
        separate space [bar; dquotes (string (string_of_id id)); string "->"; zencode_upper ctx id]
      in
      let rand_field (typ, id) = zencode ctx id ^^ space ^^ equals ^^ space ^^ make_subgen typ in
      let make_args tqs =
        string "g"
        ^^
        match quant_kopts tqs with
        | [] -> empty
        | kopts -> space ^^ separate_map space (fun kdid -> mk_arg (kopt_kid kdid)) kopts
      in
      let tqs, body, constructors, builders =
        let (TD_aux (td, (l, _))) = Bindings.find id typemap in
        match td with
        | TD_abbrev (_, tqs, A_aux (A_typ typ, _)) -> (tqs, gen_type typ, None, None)
        | TD_variant (_, tqs, variants, _) ->
            ( tqs,
              string "let c = rand_choice ["
              ^^ group (nest 2 (break 0 ^^ separate_map (string ";" ^^ break 1) rand_variant variants) ^^ break 0)
              ^^ string "] in c g",
              Some (separate_map (string ";" ^^ break 1) variant_constructor variants),
              Some (separate_map (break 1) build_constructor variants)
            )
        | TD_enum (_, variants, _) ->
            ( TypQ_aux (TypQ_no_forall, Parse_ast.Unknown),
              string "rand_choice ["
              ^^ group (nest 2 (break 0 ^^ separate_map (string ";" ^^ break 1) (zencode_upper ctx) variants) ^^ break 0)
              ^^ string "]",
              Some (separate_map (string ";" ^^ break 1) enum_constructor variants),
              Some (separate_map (break 1) build_enum_constructor variants)
            )
        | TD_record (_, tqs, fields, _) ->
            (tqs, braces (separate_map (string ";" ^^ break 1) rand_field fields), None, None)
        | _ -> raise (Reporting.err_todo l "Generators for bitfields not yet supported")
      in
      let name = type_name id in
      let constructors_pp =
        match constructors with
        | None -> empty
        | Some pp ->
            nest 2
              (separate space [string "let"; string ("constructors_" ^ name); equals; lbracket]
              ^^ break 1 ^^ pp ^^ break 1 ^^ rbracket
              )
            ^^ hardline
      in
      let build_pp =
        match builders with
        | None -> empty
        | Some pp ->
            nest 2
              (separate space
                 [string "let"; string ("build_" ^ name); string "g"; string "c"; equals; string "match c with"]
              ^^ break 1 ^^ pp
              )
            ^^ hardline
      in
      nest 2 (separate space [string "let"; string ("rand_" ^ name); make_args tqs; equals] ^^ break 1 ^^ body)
      ^^ hardline ^^ constructors_pp ^^ build_pp
    )
  in
  let rand_record_pp =
    string "let rand_gens : generators = {"
    ^^ group
         (nest 2
            (break 0
            ^^ separate_map
                 (string ";" ^^ break 1)
                 (fun id ->
                   string ("gen_" ^ type_name id) ^^ space ^^ equals ^^ space ^^ string ("rand_" ^ type_name id)
                 )
                 (IdSet.elements required)
            )
         ^^ break 0
         )
    ^^ string "}" ^^ hardline
  in
  gen_record_type_pp ^^ hardline ^^ hardline
  ^^ separate_map hardline make_rand_gen (IdSet.elements required)
  ^^ hardline ^^ rand_record_pp

let ocaml_ast ast generator_info =
  let ctx =
    {
      register_inits = get_initialize_registers ast.defs;
      externs = get_externs ast.defs;
      val_specs = val_spec_typs ast.defs;
      records = record_ids ast.defs;
    }
  in
  let empty_reg_init =
    if ctx.register_inits = [] then
      separate space [string "let"; string "zinitializze_registers"; string "()"; equals; string "()"] ^^ ocaml_def_end
    else empty
  in
  let gen_pp =
    match generator_info with
    | None -> empty
    | Some (types, req) -> ocaml_pp_generators ctx ast.defs types (List.map mk_id req)
  in
  (string "open Sail_lib;;" ^^ hardline)
  ^^ (string "module Big_int = Nat_big_num" ^^ ocaml_def_end)
  ^^ concat (List.map (ocaml_def ctx) ast.defs)
  ^^ empty_reg_init ^^ gen_pp

let ocaml_main spec sail_dir =
  let lines = ref [] in
  let chan = open_in (sail_dir ^ "/lib/main.ml") in
  begin
    try
      while true do
        let line = input_line chan in
        lines := line :: !lines
      done
    with End_of_file ->
      close_in chan;
      lines := List.rev !lines
  end;
  (("open " ^ String.capitalize_ascii spec ^ ";;\n\n") :: !lines)
  @ [
      "  zinitializze_registers ();";
      (if !opt_trace_ocaml then "  Sail_lib.opt_trace := true;" else "  ();");
      "  Printexc.record_backtrace true;";
      "  try zmain () with exn -> (prerr_endline(\"Exiting due to uncaught exception:\\n\" ^ Printexc.to_string exn); \
       exit 1)\n";
    ]
  |> String.concat "\n"

let ocaml_pp_ast f ast generator_types = ToChannel.pretty 1. 80 f (ocaml_ast ast generator_types)

let system_checked str =
  match Unix.system str with
  | Unix.WEXITED 0 -> ()
  | Unix.WEXITED n ->
      prerr_endline (str ^ " terminated with code " ^ string_of_int n);
      exit 1
  | Unix.WSIGNALED _ ->
      prerr_endline (str ^ " was killed by a signal");
      exit 1
  | Unix.WSTOPPED _ ->
      prerr_endline (str ^ " was stopped by a signal");
      exit 1

let ocaml_compile default_sail_dir spec ast generator_types =
  let sail_dir = Reporting.get_sail_dir default_sail_dir in
  if Sys.file_exists !opt_ocaml_build_dir then () else Unix.mkdir !opt_ocaml_build_dir 0o775;
  let cwd = Unix.getcwd () in
  Unix.chdir !opt_ocaml_build_dir;
  let _ = Unix.system ("cp -r " ^ sail_dir ^ "/src/lib/elf_loader.ml .") in
  let _ = Unix.system ("cp -r " ^ sail_dir ^ "/src/lib/sail_lib.ml .") in
  let _ = Unix.system ("cp -r " ^ sail_dir ^ "/src/lib/util.ml .") in
  let tags_file = if !opt_ocaml_coverage then "_tags_coverage" else "_tags" in
  let _ = Unix.system ("cp -r " ^ sail_dir ^ "/lib/" ^ tags_file ^ " _tags") in
  let out_chan = open_out (spec ^ ".ml") in
  if !opt_ocaml_coverage then
    ignore (Unix.system ("cp -r " ^ sail_dir ^ "/lib/myocamlbuild_coverage.ml myocamlbuild.ml"));
  List.iter (fun w -> output_string out_chan (Printf.sprintf "[@@@warning \"-%d\"]\n" w)) [8; 9; 11; 23; 26];
  ocaml_pp_ast out_chan ast generator_types;
  close_out out_chan;
  if IdSet.mem (mk_id "main") (val_spec_ids ast.defs) then begin
    print_endline "Generating main";
    let out_chan = open_out "main.ml" in
    output_string out_chan (ocaml_main spec sail_dir);
    close_out out_chan;
    if not !opt_ocaml_nobuild then (
      if !opt_ocaml_coverage then
        system_checked
          "BISECT_COVERAGE=YES ocamlbuild -use-ocamlfind -plugin-tag 'package(bisect_ppx-ocamlbuild)' main.native"
      else system_checked "ocamlbuild -use-ocamlfind main.native";
      ignore (Unix.system ("cp main.native " ^ cwd ^ "/" ^ spec))
    )
  end
  else if not !opt_ocaml_nobuild then system_checked ("ocamlbuild -use-ocamlfind " ^ spec ^ ".cmo");
  Unix.chdir cwd
