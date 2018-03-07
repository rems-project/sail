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
open Type_check
open Util

module Big_int = Nat_big_num

(* Option to turn tracing features on or off *)
let opt_trace_ocaml = ref false

type ctx =
  { register_inits : tannot exp list;
    externs : id Bindings.t;
    val_specs : typ Bindings.t
  }

let empty_ctx =
  { register_inits = [];
    externs = Bindings.empty;
    val_specs = Bindings.empty
  }

let gensym_counter = ref 0

let gensym () =
  let gs = "gs" ^ string_of_int !gensym_counter in
  incr gensym_counter;
  string gs

let zencode ctx id =
  try string (string_of_id (Bindings.find id ctx.externs)) with
  | Not_found -> string (zencode_string (string_of_id id))

let zencode_upper ctx id =
  try string (string_of_id (Bindings.find id ctx.externs)) with
  | Not_found -> string (zencode_upper_string (string_of_id id))

let zencode_kid kid = string ("'" ^ zencode_string (string_of_id (id_of_kid kid)))

let ocaml_string_of id = string ("string_of_" ^ zencode_string (string_of_id id))

let ocaml_string_parens inside = string "\"(\" ^ " ^^ inside ^^ string " ^ \")\""

let ocaml_string_comma = string " ^ \", \" ^ "

let rec ocaml_string_typ (Typ_aux (typ_aux, _)) arg =
  match typ_aux with
  | Typ_id id when string_of_id id = "exception" -> string "Printexc.to_string" ^^ space ^^ arg
  | Typ_id id -> ocaml_string_of id ^^ space ^^ arg
  | Typ_app (id, []) -> ocaml_string_of id ^^ space ^^ arg
  | Typ_app (id, [Typ_arg_aux (Typ_arg_typ (Typ_aux (Typ_id eid, _)), _)])
       when string_of_id id = "list" && string_of_id eid = "bit" ->
     string "string_of_bits" ^^ space ^^ arg
  | Typ_app (id, [Typ_arg_aux (Typ_arg_typ typ, _)]) when string_of_id id = "list" ->
     let farg = gensym () in
     separate space [string "string_of_list \", \""; parens (separate space [string "fun"; farg; string "->"; ocaml_string_typ typ farg]); arg]
  | Typ_app (_, _) -> string "\"APP\""
  | Typ_tup typs ->
     let args = List.map (fun _ -> gensym ()) typs in
     let body =
       ocaml_string_parens (separate_map ocaml_string_comma (fun (typ, arg) -> ocaml_string_typ typ arg) (List.combine typs args))
     in
     parens (separate space [string "fun"; parens (separate (comma ^^ space) args); string "->"; body])
     ^^ space ^^ arg
  | Typ_fn (typ1, typ2, _) -> string "\"FN\""
  | Typ_var kid -> string "\"VAR\""
  | Typ_exist _ -> assert false

let ocaml_typ_id ctx = function
  | id when Id.compare id (mk_id "string") = 0 -> string "string"
  | id when Id.compare id (mk_id "list") = 0 -> string "list"
  | id when Id.compare id (mk_id "bit") = 0 -> string "bit"
  | id when Id.compare id (mk_id "int") = 0 -> string "Big_int.num"
  | id when Id.compare id (mk_id "nat") = 0 -> string "Big_int.num"
  | id when Id.compare id (mk_id "bool") = 0 -> string "bool"
  | id when Id.compare id (mk_id "unit") = 0 -> string "unit"
  | id when Id.compare id (mk_id "real") = 0 -> string "Rational.t"
  | id when Id.compare id (mk_id "exception") = 0 -> string "exn"
  | id when Id.compare id (mk_id "register") = 0 -> string "ref"
  | id when Id.compare id (mk_id "ref") = 0 -> string "ref"
  | id -> zencode ctx id

let rec ocaml_typ ctx (Typ_aux (typ_aux, _)) =
  match typ_aux with
  | Typ_id id -> ocaml_typ_id ctx id
  | Typ_app (id, []) -> ocaml_typ_id ctx id
  | Typ_app (id, typs) -> parens (separate_map (string " * ") (ocaml_typ_arg ctx) typs) ^^ space ^^ ocaml_typ_id ctx id
  | Typ_tup typs -> parens (separate_map (string " * ") (ocaml_typ ctx) typs)
  | Typ_fn (typ1, typ2, _) -> separate space [ocaml_typ ctx typ1; string "->"; ocaml_typ ctx typ2]
  | Typ_var kid -> zencode_kid kid
  | Typ_exist _ -> assert false
and ocaml_typ_arg ctx (Typ_arg_aux (typ_arg_aux, _) as typ_arg) =
  match typ_arg_aux with
  | Typ_arg_typ typ -> ocaml_typ ctx typ
  | _ -> failwith ("OCaml: unexpected type argument " ^ string_of_typ_arg typ_arg)

let ocaml_typquant typq =
  let ocaml_qi = function
    | QI_aux (QI_id kopt, _) -> zencode_kid (kopt_kid kopt)
    | QI_aux (QI_const _, _) -> failwith "Ocaml type quantifiers should no longer contain constraints"
  in
  match quant_items typq with
  | [] -> empty
  | [qi] -> ocaml_qi qi
  | qis -> parens (separate_map (string " * ") ocaml_qi qis)

let string_lit str = dquotes (string (String.escaped str))

let ocaml_lit (L_aux (lit_aux, _)) =
  match lit_aux with
  | L_unit -> string "()"
  | L_zero -> string "B0"
  | L_one -> string "B1"
  | L_true -> string "true"
  | L_false -> string "false"
  | L_num n -> parens (string "Big_int.of_string" ^^ space ^^ string ("\"" ^ Big_int.to_string n ^ "\""))
  | L_undef -> failwith "undefined should have been re-written prior to ocaml backend"
  | L_string str -> string_lit str
  | L_real str -> parens (string "real_of_string" ^^ space ^^ dquotes (string (String.escaped str)))
  | _ -> string "LIT"

let rec ocaml_pat ctx (P_aux (pat_aux, _) as pat) =
  match pat_aux with
  | P_id id ->
     begin
       match Env.lookup_id id (pat_env_of pat) with
       | Local (Immutable, _) | Unbound -> zencode ctx id
       | Enum _ -> zencode_upper ctx id
       | _ -> failwith ("Ocaml: Cannot pattern match on mutable variable or register:" ^ string_of_pat pat)
     end
  | P_lit lit -> ocaml_lit lit
  | P_typ (_, pat) -> ocaml_pat ctx pat
  | P_tup pats -> parens (separate_map (comma ^^ space) (ocaml_pat ctx) pats)
  | P_list pats -> brackets (separate_map (semi ^^ space) (ocaml_pat ctx) pats)
  | P_wild -> string "_"
  | P_as (pat, id) -> separate space [ocaml_pat ctx pat; string "as"; zencode ctx id]
  | P_app (id, pats) -> zencode_upper ctx id ^^ space ^^ parens (separate_map (comma ^^ space) (ocaml_pat ctx) pats)
  | _ -> string ("PAT<" ^ string_of_pat pat ^ ">")

let begin_end doc = group (string "begin" ^^ nest 2 (break 1 ^^ doc) ^/^ string "end")

(* Returns true if a type is a register being passed by name *)
let is_passed_by_name = function
  | (Typ_aux (Typ_app (tid, _), _)) -> string_of_id tid = "register"
  | _ -> false

let rec ocaml_exp ctx (E_aux (exp_aux, _) as exp) =
  match exp_aux with
  | E_app (f, [x]) when Env.is_union_constructor f (env_of exp) -> zencode_upper ctx f ^^ space ^^ ocaml_atomic_exp ctx x
  | E_app (f, [x]) -> zencode ctx f ^^ space ^^ ocaml_atomic_exp ctx x
  | E_app (f, xs) when Env.is_union_constructor f (env_of exp) ->
     zencode_upper ctx f ^^ space ^^ parens (separate_map (comma ^^ space) (ocaml_atomic_exp ctx) xs)
  (* Make sure we get the correct short circuiting semantics for and and or *)
  | E_app (f, [x; y]) when string_of_id f = "and_bool" ->
     separate space [ocaml_atomic_exp ctx x; string "&&"; ocaml_atomic_exp ctx y]
  | E_app (f, [x; y]) when string_of_id f = "or_bool" ->
     separate space [ocaml_atomic_exp ctx x; string "||"; ocaml_atomic_exp ctx y]
  | E_app (f, xs) ->
     zencode ctx f ^^ space ^^ parens (separate_map (comma ^^ space) (ocaml_atomic_exp ctx) xs)
  | E_vector_subrange (exp1, exp2, exp3) -> string "subrange" ^^ space ^^ parens (separate_map (comma ^^ space) (ocaml_atomic_exp ctx) [exp1; exp2; exp3])
  | E_return exp -> separate space [string "r.return"; ocaml_atomic_exp ctx exp]
  | E_assert (exp, _) -> separate space [string "assert"; ocaml_atomic_exp ctx exp]
  | E_cast (_, exp) -> ocaml_exp ctx exp
  | E_block [exp] -> ocaml_exp ctx exp
  | E_block [] -> string "()"
  | E_block exps -> begin_end (ocaml_block ctx exps)
  | E_field (exp, id) -> ocaml_atomic_exp ctx exp ^^ dot ^^ zencode ctx id
  | E_exit exp -> string "exit 0"
  | E_throw exp -> string "raise" ^^ space ^^ ocaml_atomic_exp ctx exp
  | E_case (exp, pexps) ->
     begin_end (separate space [string "match"; ocaml_atomic_exp ctx exp; string "with"]
                ^/^ ocaml_pexps ctx pexps)
  | E_try (exp, pexps) ->
     begin_end (separate space [string "try"; ocaml_atomic_exp ctx exp; string "with"]
                ^/^ ocaml_pexps ctx pexps)
  | E_assign (lexp, exp) -> ocaml_assignment ctx lexp exp
  | E_if (c, t, e) -> separate space [string "if"; ocaml_atomic_exp ctx c;
                                      string "then"; ocaml_atomic_exp ctx t;
                                      string "else"; ocaml_atomic_exp ctx e]
  | E_record (FES_aux (FES_Fexps (fexps, _), _)) ->
     enclose lbrace rbrace (group (separate_map (semi ^^ break 1) (ocaml_fexp ctx) fexps))
  | E_record_update (exp, FES_aux (FES_Fexps (fexps, _), _)) ->
     enclose lbrace rbrace (separate space [ocaml_atomic_exp ctx exp;
                                            string "with";
                                            separate_map (semi ^^ space) (ocaml_fexp ctx) fexps])
  | E_let (lb, exp) ->
     separate space [string "let"; ocaml_letbind ctx lb; string "in"]
     ^/^ ocaml_exp ctx exp
  | E_var (lexp, exp1, exp2) ->
     separate space [string "let"; ocaml_atomic_lexp ctx lexp;
                     equals; string "ref"; parens (ocaml_atomic_exp ctx exp1 ^^ space ^^ colon ^^ space ^^ ocaml_typ ctx (Rewrites.simple_typ (typ_of exp1))); string "in"]
     ^/^ ocaml_exp ctx exp2
  | E_loop (Until, cond, body) ->
     let loop_body =
       (ocaml_atomic_exp ctx body ^^ semi)
       ^/^
       separate space [string "if"; ocaml_atomic_exp ctx cond;
                       string "then loop ()";
                       string "else ()"]
     in
     (string "let rec loop () =" ^//^ loop_body)
     ^/^ string "in"
     ^/^ string "loop ()"
  | E_loop (While, cond, body) ->
     let loop_body =
       separate space [string "if"; ocaml_atomic_exp ctx cond;
                       string "then"; parens (ocaml_atomic_exp ctx body ^^ semi ^^ space ^^ string "loop ()");
                       string "else ()"]
     in
     (string "let rec loop () =" ^//^ loop_body)
     ^/^ string "in"
     ^/^ string "loop ()"
  | E_lit _ | E_list _ | E_id _ | E_tuple _ | E_ref _ -> ocaml_atomic_exp ctx exp
  | E_for (id, exp_from, exp_to, exp_step, ord, exp_body) ->
     let loop_var = separate space [string "let"; zencode ctx id; equals; string "ref"; ocaml_atomic_exp ctx exp_from; string "in"] in
     let loop_mod =
       match ord with
       | Ord_aux (Ord_inc, _) -> string "Big_int.add" ^^ space ^^ zencode ctx id ^^ space ^^ ocaml_atomic_exp ctx exp_step
       | Ord_aux (Ord_dec, _) -> string "Big_int.sub" ^^ space ^^ zencode ctx id ^^ space ^^ ocaml_atomic_exp ctx exp_step
       | Ord_aux (Ord_var _, _) -> failwith "Cannot have variable loop order!"
     in
     let loop_compare =
       match ord with
       | Ord_aux (Ord_inc, _) -> string "Big_int.less_equal"
       | Ord_aux (Ord_dec, _) -> string "Big_int.greater_equal"
       | Ord_aux (Ord_var _, _) -> failwith "Cannot have variable loop order!"
     in
     let loop_body =
       separate space [string "if"; loop_compare; zencode ctx id; ocaml_atomic_exp ctx exp_to]
       ^/^ separate space [string "then";
             parens (ocaml_atomic_exp ctx exp_body ^^ semi ^^ space ^^ string "loop" ^^ space ^^ parens loop_mod)]
       ^/^ string "else ()"
     in
     (string ("let rec loop " ^ zencode_string (string_of_id id) ^ " =") ^//^ loop_body)
     ^/^ string "in"
     ^/^ (string "loop" ^^ space ^^ ocaml_atomic_exp ctx exp_from)
  | _ -> string ("EXP(" ^ string_of_exp exp ^ ")")
and ocaml_letbind ctx (LB_aux (lb_aux, _)) =
  match lb_aux with
  | LB_val (pat, exp) -> separate space [ocaml_pat ctx pat; equals; ocaml_atomic_exp ctx exp]
and ocaml_pexps ctx = function
  | [pexp] -> ocaml_pexp ctx pexp
  | pexp :: pexps -> ocaml_pexp ctx pexp ^/^ ocaml_pexps ctx pexps
  | [] -> empty
and ocaml_pexp ctx = function
  | Pat_aux (Pat_exp (pat, exp), _) ->
     separate space [bar; ocaml_pat ctx pat; string "->"]
     ^//^ group (ocaml_exp ctx exp)
  | Pat_aux (Pat_when (pat, wh, exp), _) ->
     separate space [bar; ocaml_pat ctx pat; string "when"; ocaml_atomic_exp ctx wh; string "->"]
     ^//^ group (ocaml_exp ctx exp)
and ocaml_block ctx = function
  | [exp] -> ocaml_exp ctx exp
  | exp :: exps -> ocaml_exp ctx exp ^^ semi ^/^ ocaml_block ctx exps
  | _ -> assert false
and ocaml_fexp ctx (FE_aux (FE_Fexp (id, exp), _)) =
  separate space [zencode ctx id; equals; ocaml_exp ctx exp]
and ocaml_atomic_exp ctx (E_aux (exp_aux, _) as exp) =
  match exp_aux with
  | E_lit lit -> ocaml_lit lit
  | E_ref id -> zencode ctx id
  | E_id id ->
     begin
       match Env.lookup_id id (env_of exp) with
       | Local (Immutable, _) | Unbound -> zencode ctx id
       | Enum _ -> zencode_upper ctx id
       | Register _ when is_passed_by_name (typ_of exp) -> zencode ctx id
       | Register typ ->
          if !opt_trace_ocaml then
            let var = gensym () in
            let str_typ = parens (ocaml_string_typ (Rewrites.simple_typ typ) var) in
            parens (separate space [string "let"; var; equals; bang ^^ zencode ctx id; string "in";
                                    string "trace_read" ^^ space ^^ string_lit (string_of_id id) ^^ space ^^ str_typ ^^ semi; var])
          else bang ^^ zencode ctx id
       | Local (Mutable, _) -> bang ^^ zencode ctx id
     end
  | E_list exps -> enclose lbracket rbracket (separate_map (semi ^^ space) (ocaml_exp ctx) exps)
  | E_tuple exps -> parens (separate_map (comma ^^ space) (ocaml_exp ctx) exps)
  | _ -> parens (ocaml_exp ctx exp)
and ocaml_assignment ctx (LEXP_aux (lexp_aux, _) as lexp) exp =
  match lexp_aux with
  | LEXP_cast (_, id) | LEXP_id id ->
     begin
       match Env.lookup_id id (env_of exp) with
       | Register typ ->
          let var = gensym () in
          let traced_exp =
            if !opt_trace_ocaml then
              let var = gensym () in
              let str_typ = parens (ocaml_string_typ (Rewrites.simple_typ typ) var) in
              parens (separate space [string "let"; var; equals; ocaml_atomic_exp ctx exp; string "in";
                                      string "trace_write" ^^ space ^^ string_lit (string_of_id id) ^^ space ^^ str_typ ^^ semi; var])
            else ocaml_atomic_exp ctx exp
          in
          separate space [zencode ctx id; string ":="; traced_exp]
       | _ -> separate space [zencode ctx id; string ":="; ocaml_exp ctx exp]
     end
  | LEXP_deref ref_exp ->
     separate space [ocaml_atomic_exp ctx ref_exp; string ":="; ocaml_exp ctx exp]
  | _ -> string ("LEXP<" ^ string_of_lexp lexp ^ ">")
and ocaml_lexp ctx (LEXP_aux (lexp_aux, _) as lexp) =
  match lexp_aux with
  | LEXP_cast _ | LEXP_id _ -> ocaml_atomic_lexp ctx lexp
  | LEXP_deref exp -> ocaml_exp ctx exp
  | _ -> string ("LEXP<" ^ string_of_lexp lexp ^ ">")
and ocaml_atomic_lexp ctx (LEXP_aux (lexp_aux, _) as lexp) =
  match lexp_aux with
  | LEXP_cast (_, id) -> zencode ctx id
  | LEXP_id id -> zencode ctx id
  | _ -> parens (ocaml_lexp ctx lexp)

let rec get_initialize_registers = function
  | DEF_fundef (FD_aux (FD_function (_, _, _, [FCL_aux (FCL_Funcl (id, Pat_aux (Pat_exp (_, E_aux (E_block inits, _)),_)), _)]), _)) :: defs
       when Id.compare id (mk_id "initialize_registers") = 0 ->
     inits
  | _ :: defs -> get_initialize_registers defs
  | [] -> []

let initial_value_for id inits =
  let find_reg = function
    | E_aux (E_assign (LEXP_aux (LEXP_cast (_, reg_id), _), init), _) when Id.compare id reg_id = 0 -> Some init
    | _ -> None
  in
  match Util.option_first find_reg inits with
  | Some init -> init
  | None -> failwith ("No assignment to register ^ " ^ string_of_id id ^ " in initialize_registers")

let ocaml_dec_spec ctx (DEC_aux (reg, _)) =
  match reg with
  | DEC_reg (typ, id) ->
     separate space [string "let"; zencode ctx id; colon;
                     parens (ocaml_typ ctx typ); string "ref"; equals;
                     string "ref"; parens (ocaml_exp ctx (initial_value_for id ctx.register_inits))]
  | _ -> failwith "Unsupported register declaration"

let first_function = ref true

let function_header () =
  if !first_function
  then (first_function := false; string "let rec")
  else string "and"

let funcls_id = function
  | [] -> failwith "Ocaml: empty function"
  | FCL_aux (FCL_Funcl (id, _),_) :: _ -> id

let ocaml_funcl_match ctx (FCL_aux (FCL_Funcl (id, pexp), _)) =
  ocaml_pexp ctx pexp

let rec ocaml_funcl_matches ctx = function
  | [] -> failwith "Ocaml: empty function"
  | [clause] -> ocaml_funcl_match ctx clause
  | (clause :: clauses) -> ocaml_funcl_match ctx clause ^/^ ocaml_funcl_matches ctx clauses

let ocaml_funcls ctx =
  (* Create functions string_of_arg and string_of_ret that print the argument and return types of the function respectively *)
  let trace_info typ1 typ2 =
     let arg_sym = gensym () in
     let ret_sym = gensym () in
     let kids = KidSet.union (tyvars_of_typ typ1) (tyvars_of_typ typ2) in
     let foralls =
       if KidSet.is_empty kids then empty else
         separate space (List.map zencode_kid (KidSet.elements kids)) ^^ dot;
     in
     let string_of_arg =
       separate space [function_header (); arg_sym; colon; foralls; ocaml_typ ctx typ1; string "-> string = fun arg ->";
                       ocaml_string_typ typ1 (string "arg")]
     in
     let string_of_ret =
       separate space [function_header (); ret_sym; colon; foralls; ocaml_typ ctx typ2; string "-> string = fun arg ->";
                       ocaml_string_typ typ2 (string "arg")]
     in
     (arg_sym, string_of_arg, ret_sym, string_of_ret)
  in
  let sail_call id arg_sym pat_sym ret_sym =
    if !opt_trace_ocaml
    then separate space [string "sail_trace_call"; string_lit (string_of_id id); parens (arg_sym ^^ space ^^ pat_sym); ret_sym]
    else separate space [string "sail_call"]
  in
  let ocaml_funcl call string_of_arg string_of_ret =
    if !opt_trace_ocaml
    then (call ^^ twice hardline ^^ string_of_arg ^^ twice hardline ^^ string_of_ret)
    else call
  in
  function
  | [] -> failwith "Ocaml: empty function"
  | [FCL_aux (FCL_Funcl (id, pexp),_)] ->
     let typ1, typ2 =
       match Bindings.find id ctx.val_specs with
       | Typ_aux (Typ_fn (typ1, typ2, _), _) -> (typ1, typ2)
       | _ -> failwith "Found val spec which was not a function!"
     in
     (* Any remaining type variables after simple_typ rewrite should
        indicate Type-polymorphism. If we have it, we need to generate
        explicit type signatures with universal quantification. *)
     let kids = KidSet.union (tyvars_of_typ typ1) (tyvars_of_typ typ2) in
     let pat_sym = gensym () in
     let pat, exp =
       match pexp with
       | Pat_aux (Pat_exp (pat, exp),_) -> pat,exp
       | Pat_aux (Pat_when (pat, wh, exp),_) -> failwith "OCaml: top-level pattern guards not supported"
     in
     let annot_pat =
       let pat =
         if KidSet.is_empty kids then
           parens (ocaml_pat ctx pat ^^ space ^^ colon ^^ space ^^ ocaml_typ ctx typ1)
         else
           ocaml_pat ctx pat
       in
       if !opt_trace_ocaml
       then parens (separate space [pat; string "as"; pat_sym])
       else pat
     in
     let call_header = function_header () in
     let arg_sym, string_of_arg, ret_sym, string_of_ret = trace_info typ1 typ2 in
     let call =
       if KidSet.is_empty kids then
         separate space [call_header; zencode ctx id;
                         annot_pat; colon; ocaml_typ ctx typ2; equals;
                         sail_call id arg_sym pat_sym ret_sym; string "(fun r ->"]
         ^//^ ocaml_exp ctx exp
         ^^ rparen
       else
         separate space [call_header; zencode ctx id; colon;
                         separate space (List.map zencode_kid (KidSet.elements kids)) ^^ dot;
                         ocaml_typ ctx typ1; string "->"; ocaml_typ ctx typ2; equals;
                         string "fun"; annot_pat; string "->";
                         sail_call id arg_sym pat_sym ret_sym; string "(fun r ->"]
         ^//^ ocaml_exp ctx exp
         ^^ rparen
     in
     ocaml_funcl call string_of_arg string_of_ret
  | funcls ->
     let id = funcls_id funcls in
     let typ1, typ2 =
       match Bindings.find id ctx.val_specs with
       | Typ_aux (Typ_fn (typ1, typ2, _), _) -> (typ1, typ2)
       | _ -> failwith "Found val spec which was not a function!"
     in
     let kids = KidSet.union (tyvars_of_typ typ1) (tyvars_of_typ typ2) in
     if not (KidSet.is_empty kids) then failwith "Cannot handle polymorphic multi-clause function in OCaml backend" else ();
     let pat_sym = gensym () in
     let call_header = function_header () in
     let arg_sym, string_of_arg, ret_sym, string_of_ret = trace_info typ1 typ2 in
     let call =
       separate space [call_header; zencode ctx id; parens (pat_sym ^^ space ^^ colon ^^ space ^^ ocaml_typ ctx typ1); equals;
                       sail_call id arg_sym pat_sym ret_sym; string "(fun r ->"]
       ^//^ (separate space [string "match"; pat_sym; string "with"] ^^ hardline ^^ ocaml_funcl_matches ctx funcls)
       ^^ rparen
     in
     ocaml_funcl call string_of_arg string_of_ret

let ocaml_fundef ctx (FD_aux (FD_function (_, _, _, funcls), _)) =
  ocaml_funcls ctx funcls

let rec ocaml_fields ctx =
  let ocaml_field typ id =
    separate space [zencode ctx id; colon; ocaml_typ ctx typ]
  in
  function
  | [(typ, id)] -> ocaml_field typ id
  | (typ, id) :: fields -> ocaml_field typ id ^^ semi ^/^ ocaml_fields ctx fields
  | [] -> empty

let rec ocaml_cases ctx =
  let ocaml_case (Tu_aux (Tu_ty_id (typ, id), _)) =
    separate space [bar; zencode_upper ctx id; string "of"; ocaml_typ ctx typ]
  in
  function
  | [tu] -> ocaml_case tu
  | tu :: tus -> ocaml_case tu ^/^ ocaml_cases ctx tus
  | [] -> empty

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
  | id :: ids -> zencode_upper ctx id ^/^ (bar ^^ space ^^ ocaml_enum ctx ids)
  | [] -> empty

(* We generate a string_of_X ocaml function for each type X, to be used for debugging purposes *)

let ocaml_def_end = string ";;" ^^ twice hardline

let ocaml_string_of_enum ctx id ids =
  let ocaml_case id =
    separate space [bar; zencode_upper ctx id; string "->"; string ("\"" ^ string_of_id id ^ "\"")]
  in
  separate space [string "let"; ocaml_string_of id; equals; string "function"]
  ^//^ (separate_map hardline ocaml_case ids)

let ocaml_string_of_struct ctx id typq fields =
  let arg = gensym () in
  let ocaml_field (typ, id) =
    separate space [string (string_of_id id ^ " = \""); string "^"; ocaml_string_typ typ (arg ^^ string "." ^^ zencode ctx id)]
  in
  separate space [string "let"; ocaml_string_of id; parens (arg ^^ space ^^ colon ^^ space ^^ zencode ctx id); equals]
  ^//^ (string "\"{" ^^ separate_map (hardline ^^ string "^ \", ") ocaml_field fields ^^ string " ^ \"}\"")

let ocaml_string_of_abbrev ctx id typq typ =
  let arg = gensym () in
  separate space [string "let"; ocaml_string_of id; parens (arg ^^ space ^^ colon ^^ space ^^ zencode ctx id); equals]
  ^//^ ocaml_string_typ typ arg

let ocaml_string_of_variant ctx id typq cases =
  separate space [string "let"; ocaml_string_of id; string "_"; equals; string "\"VARIANT\""]

let ocaml_typedef ctx (TD_aux (td_aux, _)) =
  match td_aux with
  | TD_record (id, _, typq, fields, _) ->
     ((separate space [string "type"; ocaml_typquant typq; zencode ctx id; equals; lbrace]
       ^//^ ocaml_fields ctx fields)
      ^/^ rbrace)
     ^^ ocaml_def_end
     ^^ ocaml_string_of_struct ctx id typq fields
  | TD_variant (id, _, _, cases, _) when string_of_id id = "exception" ->
     ocaml_exceptions ctx cases
  | TD_variant (id, _, typq, cases, _) ->
     (separate space [string "type"; ocaml_typquant typq; zencode ctx id; equals]
      ^//^ ocaml_cases ctx cases)
     ^^ ocaml_def_end
     ^^ ocaml_string_of_variant ctx id typq cases
  | TD_enum (id, _, ids, _) ->
     (separate space [string "type"; zencode ctx id; equals]
      ^//^ (bar ^^ space ^^ ocaml_enum ctx ids))
     ^^ ocaml_def_end
     ^^ ocaml_string_of_enum ctx id ids
  | TD_abbrev (id, _, TypSchm_aux (TypSchm_ts (typq, typ), _)) ->
     separate space [string "type"; ocaml_typquant typq; zencode ctx id; equals; ocaml_typ ctx typ]
     ^^ ocaml_def_end
     ^^ ocaml_string_of_abbrev ctx id typq typ
 | _ -> failwith "Unsupported typedef"

let get_externs (Defs defs) =
  let extern_id (VS_aux (VS_val_spec (typschm, id, ext, _), _)) =
    match ext "ocaml" with
    | None -> []
    | Some ext -> [(id, mk_id ext)]
  in
  let rec extern_ids = function
    | DEF_spec vs :: defs -> extern_id vs :: extern_ids defs
    | def :: defs -> extern_ids defs
    | [] -> []
  in
  List.fold_left (fun exts (id, name) -> Bindings.add id name exts) Bindings.empty (List.concat (extern_ids defs))

let nf_group doc =
  first_function := true;
  group doc

let ocaml_def ctx def = match def with
  | DEF_reg_dec ds -> nf_group (ocaml_dec_spec ctx ds) ^^ ocaml_def_end
  | DEF_fundef fd -> group (ocaml_fundef ctx fd) ^^ twice hardline
  | DEF_internal_mutrec fds ->
     separate_map (twice hardline) (fun fd -> group (ocaml_fundef ctx fd)) fds ^^ twice hardline
  | DEF_type td -> nf_group (ocaml_typedef ctx td) ^^ ocaml_def_end
  | DEF_val lb -> nf_group (string "let" ^^ space ^^ ocaml_letbind ctx lb) ^^ ocaml_def_end
  | _ -> empty

let val_spec_typs (Defs defs) =
  let typs = ref (Bindings.empty) in
  let val_spec_typ (VS_aux (vs_aux, _)) =
    match vs_aux with
    | VS_val_spec (TypSchm_aux (TypSchm_ts (_, typ), _), id, _, _) -> typs := Bindings.add id typ !typs
  in
  let rec vs_typs = function
    | DEF_spec vs :: defs -> val_spec_typ vs; vs_typs defs
    | _ :: defs -> vs_typs defs
    | [] -> []
  in
  ignore (vs_typs defs);
  !typs

let ocaml_defs (Defs defs) =
  let ctx = { register_inits = get_initialize_registers defs;
              externs = get_externs (Defs defs);
              val_specs = val_spec_typs (Defs defs)
            }
  in
  let empty_reg_init =
    if ctx.register_inits = []
    then
      separate space [string "let"; string "zinitializze_registers"; string "()"; equals; string "()"]
      ^^ ocaml_def_end
    else empty
  in
  (string "open Sail_lib;;" ^^ hardline)
  ^^ (string "module Big_int = Nat_big_num" ^^ ocaml_def_end)
  ^^ concat (List.map (ocaml_def ctx) defs)
  ^^ empty_reg_init

let ocaml_main spec sail_dir =
  let lines = ref [] in
  let chan = open_in (sail_dir ^ "/lib/main.ml") in
  begin
    try
      while true do
        let line = input_line chan in
        lines := line :: !lines
      done;
    with
    | End_of_file -> close_in chan; lines := List.rev !lines
  end;
  (("open " ^ String.capitalize spec ^ ";;\n\n") :: !lines
   @ [ "  zinitializze_registers ();";
       if !opt_trace_ocaml then "  Sail_lib.opt_trace := true;" else "  ();";
       "  Printexc.record_backtrace true;";
       "  zmain ()\n";])
  |> String.concat "\n"

let ocaml_pp_defs f defs =
  ToChannel.pretty 1. 80 f (ocaml_defs defs)

let ocaml_compile spec defs =
  let sail_dir =
    try Sys.getenv "SAIL_DIR" with
    | Not_found -> failwith "Environment variable SAIL_DIR needs to be set"
  in
  if Sys.file_exists "_sbuild" then () else Unix.mkdir "_sbuild" 0o775;
  let cwd = Unix.getcwd () in
  Unix.chdir "_sbuild";
  let _ = Unix.system ("cp -r " ^ sail_dir ^ "/src/elf_loader.ml .") in
  let _ = Unix.system ("cp -r " ^ sail_dir ^ "/src/sail_lib.ml .") in
  let _ = Unix.system ("cp -r " ^ sail_dir ^ "/lib/_tags .") in
  let out_chan = open_out (spec ^ ".ml") in
  ocaml_pp_defs out_chan defs;
  close_out out_chan;
  if IdSet.mem (mk_id "main") (Initial_check.val_spec_ids defs)
  then
    begin
      print_endline "Generating main";
      let out_chan = open_out "main.ml" in
      output_string out_chan (ocaml_main spec sail_dir);
      close_out out_chan;
      let _ = Unix.system "ocamlbuild -use-ocamlfind main.native" in
      let _ = Unix.system ("cp main.native " ^ cwd ^ "/" ^ spec) in
      ()
    end
  else
    let _ = Unix.system ("ocamlbuild -use-ocamlfind " ^ spec ^ ".cmo") in
    ();
  Unix.chdir cwd
