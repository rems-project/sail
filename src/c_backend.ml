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
open Type_check
open PPrint
module Big_int = Nat_big_num

let c_verbosity = ref 1

let c_debug str =
  if !c_verbosity > 0 then prerr_endline str else ()

let zencode_id = function
  | Id_aux (Id str, l) -> Id_aux (Id (Util.zencode_string str), l)
  | Id_aux (DeIid str, l) -> Id_aux (Id (Util.zencode_string ("op " ^ str)), l)

let lvar_typ = function
  | Local (_, typ) -> typ
  | Register typ -> typ
  | Enum typ -> typ
  | _ -> assert false

(**************************************************************************)
(* 1. Conversion to A-normal form (ANF)                                   *)
(**************************************************************************)

(* The first step in compiling sail is converting the Sail expression
   grammar into A-normal form. Essentially this converts expressions
   such as f(g(x), h(y)) into something like:

   let v0 = g(x) in let v1 = h(x) in f(v0, v1)

   Essentially the arguments to every function must be trivial, and
   complex expressions must be let bound to new variables, or used in
   a block, assignment, or control flow statement (if, for, and
   while/until loops). The aexp datatype represents these expressions,
   while aval represents the trivial values.

   The X_aux construct in ast.ml isn't used here, but the typing
   information is collapsed into the aexp and aval types. The
   convention is that the type of an aexp is given by last argument to
   a constructor. It is omitted where it is obvious - for example all
   for loops have unit as their type. If some constituent part of the
   aexp has an annotation, the it refers to the previous argument, so
   in

   AE_let (id, typ1, _, body, typ2)

   typ1 is the type of the bound identifer, whereas typ2 is the type
   of the whole let expression (and therefore also the body).

   See Flanagan et al's 'The Essence of Compiling with Continuations' *)
type aexp =
  | AE_val of aval
  | AE_app of id * aval list * typ
  | AE_cast of aexp * typ
  | AE_assign of id * typ * aexp
  | AE_let of id * typ * aexp * aexp * typ
  | AE_block of aexp list * aexp * typ
  | AE_return of aval * typ
  | AE_throw of aval * typ
  | AE_if of aval * aexp * aexp * typ
  | AE_field of aval * id * typ
  | AE_case of aval * (apat * aexp * aexp) list * typ
  | AE_try of aexp * (apat * aexp * aexp) list * typ
  | AE_record_update of aval * aval Bindings.t * typ
  | AE_for of id * aexp * aexp * aexp * order * aexp
  | AE_loop of loop * aexp * aexp

and apat =
  | AP_tup of apat list
  | AP_id of id
  | AP_app of id * apat list
  | AP_wild

and aval =
  | AV_lit of lit * typ
  | AV_id of id * lvar
  | AV_ref of id * lvar
  | AV_tuple of aval list
  | AV_list of aval list * typ
  | AV_vector of aval list * typ
  | AV_C_fragment of string * typ

(* Map over all the avals in an aexp. *)
let rec map_aval f = function
  | AE_val v -> AE_val (f v)
  | AE_cast (aexp, typ) -> AE_cast (map_aval f aexp, typ)
  | AE_assign (id, typ, aexp) -> AE_assign (id, typ, map_aval f aexp)
  | AE_app (id, vs, typ) -> AE_app (id, List.map f vs, typ)
  | AE_let (id, typ1, aexp1, aexp2, typ2) ->
     AE_let (id, typ1, map_aval f aexp1, map_aval f aexp2, typ2)
  | AE_block (aexps, aexp, typ) -> AE_block (List.map (map_aval f) aexps, map_aval f aexp, typ)
  | AE_return (aval, typ) -> AE_return (f aval, typ)
  | AE_throw (aval, typ) -> AE_throw (f aval, typ)
  | AE_if (aval, aexp1, aexp2, typ2) ->
     AE_if (f aval, map_aval f aexp1, map_aval f aexp2, typ2)
  | AE_loop (loop_typ, aexp1, aexp2) -> AE_loop (loop_typ, map_aval f aexp1, map_aval f aexp2)
  | AE_for (id, aexp1, aexp2, aexp3, order, aexp4) ->
     AE_for (id, map_aval f aexp1, map_aval f aexp2, map_aval f aexp3, order, map_aval f aexp4)
  | AE_record_update (aval, updates, typ) ->
     AE_record_update (f aval, Bindings.map f updates, typ)
  | AE_field (aval, id, typ) ->
     AE_field (f aval, id, typ)
  | AE_case (aval, cases, typ) ->
     AE_case (f aval, List.map (fun (pat, aexp1, aexp2) -> pat, map_aval f aexp1, map_aval f aexp2) cases, typ)
  | AE_try (aexp, cases, typ) ->
     AE_try (map_aval f aexp, List.map (fun (pat, aexp1, aexp2) -> pat, map_aval f aexp1, map_aval f aexp2) cases, typ)

(* Map over all the functions in an aexp. *)
let rec map_functions f = function
  | AE_app (id, vs, typ) -> f id vs typ
  | AE_cast (aexp, typ) -> AE_cast (map_functions f aexp, typ)
  | AE_assign (id, typ, aexp) -> AE_assign (id, typ, map_functions f aexp)
  | AE_let (id, typ1, aexp1, aexp2, typ2) -> AE_let (id, typ1, map_functions f aexp1, map_functions f aexp2, typ2)
  | AE_block (aexps, aexp, typ) -> AE_block (List.map (map_functions f) aexps, map_functions f aexp, typ)
  | AE_if (aval, aexp1, aexp2, typ) ->
     AE_if (aval, map_functions f aexp1, map_functions f aexp2, typ)
  | AE_loop (loop_typ, aexp1, aexp2) -> AE_loop (loop_typ, map_functions f aexp1, map_functions f aexp2)
  | AE_for (id, aexp1, aexp2, aexp3, order, aexp4) ->
     AE_for (id, map_functions f aexp1, map_functions f aexp2, map_functions f aexp3, order, map_functions f aexp4)
  | AE_case (aval, cases, typ) ->
     AE_case (aval, List.map (fun (pat, aexp1, aexp2) -> pat, map_functions f aexp1, map_functions f aexp2) cases, typ)
  | AE_try (aexp, cases, typ) ->
     AE_try (map_functions f aexp, List.map (fun (pat, aexp1, aexp2) -> pat, map_functions f aexp1, map_functions f aexp2) cases, typ)
  | AE_field _ | AE_record_update _ | AE_val _ | AE_return _ | AE_throw _ as v -> v

(* For debugging we provide a pretty printer for ANF expressions. *)

let pp_id ?color:(color=Util.green) id =
  string (string_of_id id |> color |> Util.clear)

let pp_lvar lvar doc =
  match lvar with
  | Register typ ->
     string "[R/" ^^ string (string_of_typ typ |> Util.yellow |> Util.clear) ^^ string "]" ^^ doc
  | Local (Mutable, typ) ->
     string "[M/" ^^ string (string_of_typ typ |> Util.yellow |> Util.clear) ^^ string "]" ^^ doc
  | Local (Immutable, typ) ->
     string "[I/" ^^ string (string_of_typ typ |> Util.yellow |> Util.clear) ^^ string "]" ^^ doc
  | Enum typ ->
     string "[E/" ^^ string (string_of_typ typ |> Util.yellow |> Util.clear) ^^ string "]" ^^ doc
  | Union (typq, typ) ->
     string "[U/" ^^ string (string_of_typquant typq ^ "/" ^ string_of_typ typ |> Util.yellow |> Util.clear) ^^ string "]" ^^ doc
  | Unbound -> string "[?]" ^^ doc

let pp_annot typ doc =
  string "[" ^^ string (string_of_typ typ |> Util.yellow |> Util.clear) ^^ string "]" ^^ doc

let pp_order = function
  | Ord_aux (Ord_inc, _) -> string "inc"
  | Ord_aux (Ord_dec, _) -> string "dec"
  | _ -> assert false (* Order types have been specialised, so no polymorphism in C backend. *)

let rec pp_aexp = function
  | AE_val v -> pp_aval v
  | AE_cast (aexp, typ) ->
     pp_annot typ (string "$" ^^ pp_aexp aexp)
  | AE_assign (id, typ, aexp) ->
     pp_annot typ (pp_id id) ^^ string " := " ^^ pp_aexp aexp
  | AE_app (id, args, typ) ->
     pp_annot typ (pp_id ~color:Util.red id ^^ parens (separate_map (comma ^^ space) pp_aval args))
  | AE_let (id, id_typ, binding, body, typ) -> group
     begin
       match binding with
       | AE_let _ ->
          (pp_annot typ (separate space [string "let"; pp_annot id_typ (pp_id id); string "="])
           ^^ hardline ^^ nest 2 (pp_aexp binding))
          ^^ hardline ^^ string "in" ^^ space ^^ pp_aexp body
       | _ ->
          pp_annot typ (separate space [string "let"; pp_annot id_typ (pp_id id); string "="; pp_aexp binding; string "in"])
          ^^ hardline ^^ pp_aexp body
     end
  | AE_if (cond, then_aexp, else_aexp, typ) ->
     pp_annot typ (separate space [ string "if"; pp_aval cond;
                                    string "then"; pp_aexp then_aexp;
                                    string "else"; pp_aexp else_aexp ])
  | AE_block (aexps, aexp, typ) ->
     pp_annot typ (surround 2 0 lbrace (pp_block (aexps @ [aexp])) rbrace)
  | AE_return (v, typ) -> pp_annot typ (string "return" ^^ parens (pp_aval v))
  | AE_throw (v, typ) -> pp_annot typ (string "throw" ^^ parens (pp_aval v))
  | AE_loop (While, aexp1, aexp2) ->
     separate space [string "while"; pp_aexp aexp1; string "do"; pp_aexp aexp2]
  | AE_loop (Until, aexp1, aexp2) ->
     separate space [string "repeat"; pp_aexp aexp2; string "until"; pp_aexp aexp1]
  | AE_for (id, aexp1, aexp2, aexp3, order, aexp4) ->
     let header =
       string "foreach" ^^ space ^^
         group (parens (separate (break 1)
                                 [ pp_id id;
                                   string "from " ^^ pp_aexp aexp1;
                                   string "to " ^^ pp_aexp aexp2;
                                   string "by " ^^ pp_aexp aexp3;
                                   string "in " ^^ pp_order order ]))
     in
     header ^//^ pp_aexp aexp4
  | AE_field _ -> string "FIELD"
  | AE_case (aval, cases, typ) ->
     pp_annot typ (separate space [string "match"; pp_aval aval; pp_cases cases])
  | AE_try (aexp, cases, typ) ->
     pp_annot typ (separate space [string "try"; pp_aexp aexp; pp_cases cases])
  | AE_record_update (_, _, typ) -> pp_annot typ (string "RECORD UPDATE")

and pp_apat = function
  | AP_wild -> string "_"
  | AP_id id -> pp_id id
  | AP_tup apats -> parens (separate_map (comma ^^ space) pp_apat apats)
  | AP_app (id, apats) -> pp_id id ^^ parens (separate_map (comma ^^ space) pp_apat apats)

and pp_cases cases = surround 2 0 lbrace (separate_map (comma ^^ hardline) pp_case cases) rbrace

and pp_case (apat, guard, body) =
  separate space [pp_apat apat; string "if"; pp_aexp guard; string "=>"; pp_aexp body]

and pp_block = function
  | [] -> string "()"
  | [aexp] -> pp_aexp aexp
  | aexp :: aexps -> pp_aexp aexp ^^ semi ^^ hardline ^^ pp_block aexps

and pp_aval = function
  | AV_lit (lit, typ) -> pp_annot typ (string (string_of_lit lit))
  | AV_id (id, lvar) -> pp_lvar lvar (pp_id id)
  | AV_tuple avals -> parens (separate_map (comma ^^ space) pp_aval avals)
  | AV_ref (id, lvar) -> string "ref" ^^ space ^^ pp_lvar lvar (pp_id id)
  | AV_C_fragment (str, typ) -> pp_annot typ (string (str |> Util.cyan |> Util.clear))
  | AV_vector (avals, typ) ->
     pp_annot typ (string "[" ^^ separate_map (comma ^^ space) pp_aval avals ^^ string "]")
  | AV_list (avals, typ) ->
     pp_annot typ (string "[|" ^^ separate_map (comma ^^ space) pp_aval avals ^^ string "|]")

let ae_lit lit typ = AE_val (AV_lit (lit, typ))

(** GLOBAL: gensym_counter is used to generate fresh identifiers where
   needed. It should be safe to reset between top level
   definitions. **)
let gensym_counter = ref 0

let gensym () =
  let id = mk_id ("gs#" ^ string_of_int !gensym_counter) in
  incr gensym_counter;
  id

let rec split_block = function
  | [exp] -> [], exp
  | exp :: exps ->
     let exps, last = split_block exps in
     exp :: exps, last
  | [] -> failwith "empty block"

let rec anf_pat (P_aux (p_aux, _) as pat) =
  match p_aux with
  | P_id id -> AP_id id
  | P_wild -> AP_wild
  | P_tup pats -> AP_tup (List.map anf_pat pats)
  | P_app (id, pats) -> AP_app (id, List.map anf_pat pats)
  | _ -> failwith ("anf_pat: " ^ string_of_pat pat)

let rec anf (E_aux (e_aux, exp_annot) as exp) =
  let to_aval = function
    | AE_val v -> (v, fun x -> x)
    | AE_app (_, _, typ)
      | AE_let (_, _, _, _, typ)
      | AE_return (_, typ)
      | AE_throw (_, typ)
      | AE_cast (_, typ)
      | AE_if (_, _, _, typ)
      | AE_field (_, _, typ)
      | AE_case (_, _, typ)
      | AE_try (_, _, typ)
      | AE_record_update (_, _, typ)
      as aexp ->
       let id = gensym () in
       (AV_id (id, Local (Immutable, typ)), fun x -> AE_let (id, typ, aexp, x, typ_of exp))
    | AE_assign _ | AE_block _ | AE_for _ | AE_loop _ as aexp ->
       let id = gensym () in
       (AV_id (id, Local (Immutable, unit_typ)), fun x -> AE_let (id, unit_typ, aexp, x, typ_of exp))
  in
  match e_aux with
  | E_lit lit -> ae_lit lit (typ_of exp)

  | E_block exps ->
     let exps, last = split_block exps in
     let aexps = List.map anf exps in
     let alast = anf last in
     AE_block (aexps, alast, typ_of exp)

  | E_assign (LEXP_aux (LEXP_id id, _), exp) ->
     let aexp = anf exp in
     AE_assign (id, lvar_typ (Env.lookup_id id (env_of exp)), aexp)

  | E_loop (loop_typ, cond, exp) ->
     let acond = anf cond in
     let aexp = anf exp in
     AE_loop (loop_typ, acond, aexp)

  | E_for (id, exp1, exp2, exp3, order, body) ->
     let aexp1, aexp2, aexp3, abody = anf exp1, anf exp2, anf exp3, anf body in
     AE_for (id, aexp1, aexp2, aexp3, order, abody)

  | E_if (cond, then_exp, else_exp) ->
     let cond_val, wrap = to_aval (anf cond) in
     let then_aexp = anf then_exp in
     let else_aexp = anf else_exp in
     wrap (AE_if (cond_val, then_aexp, else_aexp, typ_of then_exp))

  | E_app_infix (x, Id_aux (Id op, l), y) ->
     anf (E_aux (E_app (Id_aux (DeIid op, l), [x; y]), exp_annot))
  | E_app_infix (x, Id_aux (DeIid op, l), y) ->
     anf (E_aux (E_app (Id_aux (Id op, l), [x; y]), exp_annot))

  | E_vector exps ->
     let aexps = List.map anf exps in
     let avals = List.map to_aval aexps in
     let wrap = List.fold_left (fun f g x -> f (g x)) (fun x -> x) (List.map snd avals) in
     wrap (AE_val (AV_vector (List.map fst avals, typ_of exp)))

  | E_list exps ->
     let aexps = List.map anf exps in
     let avals = List.map to_aval aexps in
     let wrap = List.fold_left (fun f g x -> f (g x)) (fun x -> x) (List.map snd avals) in
     wrap (AE_val (AV_list (List.map fst avals, typ_of exp)))

  | E_field (exp, id) ->
     let aval, wrap = to_aval (anf exp) in
     wrap (AE_field (aval, id, typ_of exp))

  | E_record_update (exp, FES_aux (FES_Fexps (fexps, _), _)) ->
    let anf_fexp (FE_aux (FE_Fexp (id, exp), _)) =
      let aval, wrap = to_aval (anf exp) in
      (id, aval), wrap
    in
    let aval, exp_wrap = to_aval (anf exp) in
    let fexps = List.map anf_fexp fexps in
    let wrap = List.fold_left (fun f g x -> f (g x)) (fun x -> x) (List.map snd fexps) in
    let record = List.fold_left (fun r (id, aval) -> Bindings.add id aval r) Bindings.empty (List.map fst fexps) in
    exp_wrap (wrap (AE_record_update (aval, record, typ_of exp)))

  | E_app (id, exps) ->
     let aexps = List.map anf exps in
     let avals = List.map to_aval aexps in
     let wrap = List.fold_left (fun f g x -> f (g x)) (fun x -> x) (List.map snd avals) in
     wrap (AE_app (id, List.map fst avals, typ_of exp))

  | E_throw exp ->
     let aexp = anf exp in
     let aval, wrap = to_aval aexp in
     wrap (AE_throw (aval, unit_typ))

  | E_exit exp ->
     let aexp = anf exp in
     let aval, wrap = to_aval aexp in
     wrap (AE_app (mk_id "exit", [aval], unit_typ))

  | E_return exp ->
     let aexp = anf exp in
     let aval, wrap = to_aval aexp in
     wrap (AE_return (aval, unit_typ))

  | E_assert (exp1, exp2) ->
     let aexp1 = anf exp1 in
     let aexp2 = anf exp2 in
     let aval1, wrap1 = to_aval aexp1 in
     let aval2, wrap2 = to_aval aexp2 in
     wrap1 (wrap2 (AE_app (mk_id "assert", [aval1; aval2], unit_typ)))

  | E_cons (exp1, exp2) ->
     let aexp1 = anf exp1 in
     let aexp2 = anf exp2 in
     let aval1, wrap1 = to_aval aexp1 in
     let aval2, wrap2 = to_aval aexp2 in
     wrap1 (wrap2 (AE_app (mk_id "cons", [aval1; aval2], unit_typ)))

  | E_id id ->
     let lvar = Env.lookup_id id (env_of exp) in
     AE_val (AV_id (id, lvar))

  | E_ref id ->
     let lvar = Env.lookup_id id (env_of exp) in
     AE_val (AV_ref (id, lvar))

  | E_return exp ->
     let aval, wrap = to_aval (anf exp) in
     wrap (AE_return (aval, typ_of exp))

  | E_case (match_exp, pexps) ->
     let match_aval, match_wrap = to_aval (anf match_exp) in
     let anf_pexp (Pat_aux (pat_aux, _)) =
       match pat_aux with
       | Pat_when (pat, guard, body) ->
          (anf_pat pat, anf guard, anf body)
       | Pat_exp (pat, body) ->
          (anf_pat pat, AE_val (AV_lit (mk_lit (L_true), bool_typ)), anf body)
     in
     match_wrap (AE_case (match_aval, List.map anf_pexp pexps, typ_of exp))

  | E_try (match_exp, pexps) ->
     let match_aexp = anf match_exp in
     let anf_pexp (Pat_aux (pat_aux, _)) =
       match pat_aux with
       | Pat_when (pat, guard, body) ->
          (anf_pat pat, anf guard, anf body)
       | Pat_exp (pat, body) ->
          (anf_pat pat, AE_val (AV_lit (mk_lit (L_true), bool_typ)), anf body)
     in
     AE_try (match_aexp, List.map anf_pexp pexps, typ_of exp)

  | E_var (LEXP_aux (LEXP_id id, _), binding, body)
  | E_var (LEXP_aux (LEXP_cast (_, id), _), binding, body)
  | E_let (LB_aux (LB_val (P_aux (P_id id, _), binding), _), body) ->
     let env = env_of body in
     let lvar = Env.lookup_id id env in
     AE_let (id, lvar_typ lvar, anf binding, anf body, typ_of exp)

  | E_let (LB_aux (LB_val (pat, binding), _), body) ->
     anf (E_aux (E_case (binding, [Pat_aux (Pat_exp (pat, body), (Parse_ast.Unknown, None))]), exp_annot))

  | E_tuple exps ->
     let aexps = List.map anf exps in
     let avals = List.map to_aval aexps in
     let wrap = List.fold_left (fun f g x -> f (g x)) (fun x -> x) (List.map snd avals) in
     wrap (AE_val (AV_tuple (List.map fst avals)))

  | E_cast (typ, exp) -> AE_cast (anf exp, typ)

  | E_vector_access _ | E_vector_subrange _ | E_vector_update _ | E_vector_update_subrange _ | E_vector_append _ ->
     (* Should be re-written by type checker *)
     failwith "encountered raw vector operation when converting to ANF"

  | E_internal_value _ ->
     (* Interpreter specific *)
     failwith "encountered E_internal_value when converting to ANF"

  | E_sizeof _ | E_constraint _ ->
     (* Sizeof nodes removed by sizeof rewriting pass *)
     failwith "encountered E_sizeof or E_constraint node when converting to ANF"

  | E_nondet _ ->
     (* We don't compile E_nondet nodes *)
     failwith "encountered E_nondet node when converting to ANF"

  | _ -> failwith ("Cannot convert to ANF: " ^ string_of_exp exp)

(**************************************************************************)
(* 2. Converting sail types to C types                                    *)
(**************************************************************************)

let max_int64 = Big_int.of_int64 Int64.max_int
let min_int64 = Big_int.of_int64 Int64.min_int

type ctyp =
  (* Arbitrary precision GMP integer, mpz_t in C. *)
  | CT_mpz
  (* Variable length bitvector - flag represents direction, inc or dec *)
  | CT_bv of bool
  (* Fixed length bitvector that fits within a 64-bit word. - int
     represents length, and flag is the same as CT_bv. *)
  | CT_uint64 of int * bool
  | CT_int
  (* Used for (signed) integers that fit within 64-bits. *)
  | CT_int64
  (* unit is a value in sail, so we represent it as a one element type
     here too for clarity but we actually compile it to an int which
     is always 0. *)
  | CT_unit
  | CT_bool
  (* Abstractly represent how all the Sail user defined types get
     mapped into C. We don't fully worry about precise implementation
     details at this point, as C doesn't have variants or tuples
     natively, but these need to be encoded. *)
  | CT_tup of ctyp list
  | CT_struct of id * ctyp Bindings.t
  | CT_enum of id * IdSet.t
  | CT_variant of id * ctyp Bindings.t
  | CT_string

type ctx =
  { records : (ctyp Bindings.t) Bindings.t;
    enums : IdSet.t Bindings.t;
    variants : (ctyp Bindings.t) Bindings.t;
    tc_env : Env.t
  }

let initial_ctx env =
  { records = Bindings.empty;
    enums = Bindings.empty;
    variants = Bindings.empty;
    tc_env = env
  }

let rec ctyp_equal ctyp1 ctyp2 =
  match ctyp1, ctyp2 with
  | CT_mpz, CT_mpz -> true
  | CT_bv d1, CT_bv d2 -> d1 = d2
  | CT_uint64 (m1, d1), CT_uint64 (m2, d2) -> m1 = m2 && d1 = d2
  | CT_int, CT_int -> true
  | CT_int64, CT_int64 -> true
  | CT_unit, CT_unit -> true
  | CT_bool, CT_bool -> true
  | CT_struct (id1, _), CT_struct (id2, _) -> Id.compare id1 id2 = 0
  | CT_enum (id1, _), CT_enum (id2, _) -> Id.compare id1 id2 = 0
  | CT_variant (id1, _), CT_variant (id2, _) -> Id.compare id1 id2 = 0
  | CT_tup ctyps1, CT_tup ctyps2 -> List.for_all2 ctyp_equal ctyps1 ctyps2
  | CT_string, CT_string -> true
  | _, _ -> false

let rec string_of_ctyp = function
  | CT_mpz -> "mpz_t"
  | CT_bv true -> "bv_t<dec>"
  | CT_bv false -> "bv_t<inc>"
  | CT_uint64 (n, true) -> "uint64_t<" ^ string_of_int n ^ ", dec>"
  | CT_uint64 (n, false) -> "uint64_t<" ^ string_of_int n ^ ", int>"
  | CT_int64 -> "int64_t"
  | CT_int -> "int"
  | CT_unit -> "unit"
  | CT_bool -> "bool"
  | CT_tup ctyps -> "(" ^ Util.string_of_list ", " string_of_ctyp ctyps ^ ")"
  | CT_struct (id, _) | CT_enum (id, _) | CT_variant (id, _) -> string_of_id id
  | CT_string -> "string"

(* Convert a sail type into a C-type *)
let rec ctyp_of_typ ctx typ =
  let Typ_aux (typ_aux, _) as typ = Env.expand_synonyms ctx.tc_env typ in
  match typ_aux with
  | Typ_id id when string_of_id id = "bit" -> CT_int
  | Typ_id id when string_of_id id = "bool" -> CT_bool
  | Typ_id id when string_of_id id = "int" -> CT_mpz
  | Typ_app (id, _) when string_of_id id = "range" || string_of_id id = "atom" ->
     begin
       match destruct_range typ with
       | None -> assert false (* Checked if range type in guard *)
       | Some (n, m) ->
          match nexp_simp n, nexp_simp m with
          | Nexp_aux (Nexp_constant n, _), Nexp_aux (Nexp_constant m, _)
               when Big_int.less_equal min_int64 n && Big_int.less_equal m max_int64 ->
             CT_int64
          | _ -> CT_mpz
     end
  | Typ_app (id, [Typ_arg_aux (Typ_arg_nexp n, _);
                  Typ_arg_aux (Typ_arg_order ord, _);
                  Typ_arg_aux (Typ_arg_typ (Typ_aux (Typ_id vtyp_id, _)), _)])
       when string_of_id id = "vector" && string_of_id vtyp_id = "bit" ->
     begin
       let direction = match ord with Ord_aux (Ord_dec, _) -> true | Ord_aux (Ord_inc, _) -> false | _ -> assert false in
       match nexp_simp n with
       | Nexp_aux (Nexp_constant n, _) when Big_int.less_equal n (Big_int.of_int 64) -> CT_uint64 (Big_int.to_int n, direction)
       | _ -> CT_bv direction
     end
  | Typ_id id when string_of_id id = "unit" -> CT_unit
  | Typ_id id when string_of_id id = "string" -> CT_string

  | Typ_id id | Typ_app (id, _) when Bindings.mem id ctx.records -> CT_struct (id, Bindings.find id ctx.records)
  | Typ_id id | Typ_app (id, _) when Bindings.mem id ctx.variants -> CT_variant (id, Bindings.find id ctx.variants)
  | Typ_id id when Bindings.mem id ctx.enums -> CT_enum (id, Bindings.find id ctx.enums)

  | Typ_tup typs -> CT_tup (List.map (ctyp_of_typ ctx) typs)

  | Typ_exist (_, _, typ) -> ctyp_of_typ ctx typ

  | _ -> failwith ("No C-type for type " ^ string_of_typ typ)

let rec is_stack_ctyp ctyp = match ctyp with
  | CT_uint64 _ | CT_int64 | CT_int | CT_unit | CT_bool | CT_enum _ -> true
  | CT_bv _ | CT_mpz | CT_string _ -> false
  | CT_struct (_, fields) -> Bindings.for_all (fun _ ctyp -> is_stack_ctyp ctyp) fields
  | CT_variant (_, ctors) -> Bindings.for_all (fun _ ctyp -> is_stack_ctyp ctyp) ctors
  | CT_tup ctyps -> List.for_all is_stack_ctyp ctyps

let is_stack_typ ctx typ = is_stack_ctyp (ctyp_of_typ ctx typ)

(**************************************************************************)
(* 3. Optimization of primitives and literals                             *)
(**************************************************************************)

let literal_to_cstring (L_aux (l_aux, _) as lit) =
  match l_aux with
  | L_num n when Big_int.less_equal min_int64 n && Big_int.less_equal n max_int64 ->
     Some (Big_int.to_string n ^ "L")
  | L_hex str when String.length str <= 16 ->
     let padding = 16 - String.length str in
     Some ("0x" ^ String.make padding '0' ^ str ^ "ul")
  | L_unit -> Some "UNIT"
  | L_true -> Some "true"
  | L_false -> Some "false"
  | _ -> None

let c_literals ctx =
  let rec c_literal = function
    | AV_lit (lit, typ) as v when is_stack_ctyp (ctyp_of_typ ctx typ) ->
       begin
         match literal_to_cstring lit with
         | Some str -> AV_C_fragment (str, typ)
         | None -> v
       end
    | AV_tuple avals -> AV_tuple (List.map c_literal avals)
    | v -> v
  in
  map_aval c_literal

let mask m =
  if Big_int.less_equal m (Big_int.of_int 64) then
    let n = Big_int.to_int m in
    if n mod 4 == 0
    then "0x" ^ String.make (16 - n / 4) '0' ^ String.make (n / 4) 'F' ^ "ul"
    else "0b" ^ String.make (64 - n) '0' ^ String.make n '1' ^ "ul"
  else
    failwith "Tried to create a mask literal for a vector greater than 64 bits."

let rec c_aval ctx = function
  | AV_lit (lit, typ) as v ->
     begin
       match literal_to_cstring lit with
       | Some str -> AV_C_fragment (str, typ)
       | None -> v
     end
  | AV_C_fragment (str, typ) -> AV_C_fragment (str, typ)
  (* An id can be converted to a C fragment if it's type can be stack-allocated. *)
  | AV_id (id, lvar) as v ->
     begin
       match lvar with
       | Local (_, typ) when is_stack_typ ctx typ ->
          AV_C_fragment (Util.zencode_string (string_of_id id), typ)
       | _ -> v
     end
  | AV_tuple avals -> AV_tuple (List.map (c_aval ctx) avals)

let is_c_fragment = function
  | AV_C_fragment _ -> true
  | _ -> false

let c_fragment_string = function
  | AV_C_fragment (str, _) -> str
  | _ -> assert false

let analyze_primop' ctx id args typ =
  let no_change = AE_app (id, args, typ) in

  (* primops add_range and add_atom *)
  if string_of_id id = "add_range" || string_of_id id = "add_atom" then
    begin
      let n, m, x, y = match destruct_range typ, args with
        | Some (n, m), [x; y] -> n, m, x, y
        | _ -> failwith ("add_range has incorrect return type or arity ^ " ^ string_of_typ typ)
      in
      match nexp_simp n, nexp_simp m with
      | Nexp_aux (Nexp_constant n, _), Nexp_aux (Nexp_constant m, _) ->
         if Big_int.less_equal min_int64 n && Big_int.less_equal m max_int64 then
           let x, y = c_aval ctx x, c_aval ctx y in
           if is_c_fragment x && is_c_fragment y then
             AE_val (AV_C_fragment (c_fragment_string x ^ " + " ^ c_fragment_string y, typ))
           else
             no_change
         else
           no_change
      | _ -> no_change
    end

  else if string_of_id id = "eq_range" || string_of_id id = "eq_atom" then
    begin
      match List.map (c_aval ctx) args with
      | [x; y] when is_c_fragment x && is_c_fragment y ->
         AE_val (AV_C_fragment ("(" ^ c_fragment_string x ^ " == " ^ c_fragment_string y ^ ")", typ))
      | _ ->
         no_change
    end

  else if string_of_id id = "xor_vec" then
    begin
      let n, x, y = match typ, args with
        | Typ_aux (Typ_app (id, [Typ_arg_aux (Typ_arg_nexp n, _); _; _]), _), [x; y]
             when string_of_id id = "vector" -> n, x, y
        | _ -> failwith ("xor_vec has incorrect return type or arity " ^ string_of_typ typ)
      in
      match nexp_simp n with
      | Nexp_aux (Nexp_constant n, _) when Big_int.less_equal n (Big_int.of_int 64) ->
         let x, y = c_aval ctx x, c_aval ctx y in
         if is_c_fragment x && is_c_fragment y then
           AE_val (AV_C_fragment (c_fragment_string x ^ " ^ " ^ c_fragment_string y, typ))
         else
           no_change
      | _ -> no_change
    end

  else if string_of_id id = "add_vec" then
    begin
      let n, x, y = match typ, args with
        | Typ_aux (Typ_app (id, [Typ_arg_aux (Typ_arg_nexp n, _); _; _]), _), [x; y]
             when string_of_id id = "vector" -> n, x, y
        | _ -> failwith ("add_vec has incorrect return type or arity " ^ string_of_typ typ)
      in
      match nexp_simp n with
      | Nexp_aux (Nexp_constant n, _) when Big_int.less_equal n (Big_int.of_int 64) ->
         let x, y = c_aval ctx x, c_aval ctx y in
         if is_c_fragment x && is_c_fragment y then
           AE_val (AV_C_fragment ("(" ^ c_fragment_string x ^ " + " ^ c_fragment_string y ^ ") & " ^ mask n, typ))
         else
           no_change
      | _ -> no_change
    end

  else
    no_change

let analyze_primop ctx id args typ =
  let no_change = AE_app (id, args, typ) in
  try analyze_primop' ctx id args typ with
  | Failure _ -> no_change

(**************************************************************************)
(* 4. Conversion to low-level AST                                         *)
(**************************************************************************)

(** We now define a low-level AST that is only slightly abstracted
   away from C. To be succint in comments we usually refer to this as
   LLcode rather than low-level AST repeatedly.

   The general idea is ANF expressions are converted into lists of
   instructions (type instr) where allocations and deallocations are
   now made explicit. ANF values (aval) are mapped to the cval type,
   which is even simpler still. Some things are still more abstract
   than in C, so the type definitions follow the sail type definition
   structure, just with typ (from ast.ml) replaced with
   ctyp. Top-level declarations that have no meaning for the backend
   are not included at this level.

   The convention used here is that functions of the form compile_X
   compile the type X into types in this AST, so compile_aval maps
   avals into cvals. Note that the return types for these functions
   are often quite complex, and they usually return some tuple
   containing setup instructions (to allocate memory for the
   expression), cleanup instructions (to deallocate that memory) and
   possibly typing information about what has been translated. **)

type ctype_def =
   | CTD_enum of id * IdSet.t
   | CTD_record of id * ctyp Bindings.t
   | CTD_variant of id * ctyp Bindings.t

let ctype_def_ctyps = function
  | CTD_enum _ -> []
  | CTD_record (_, fields) -> List.map snd (Bindings.bindings fields)
  | CTD_variant (_, ctors) -> List.map snd (Bindings.bindings ctors)

type cval =
  | CV_id of id * ctyp
  | CV_C_fragment of string * ctyp

let cval_ctyp = function
  | CV_id (_, ctyp) -> ctyp
  | CV_C_fragment (_, ctyp) -> ctyp

type clexp =
  | CL_id of id
  | CL_field of id * id
  | CL_addr of clexp

type instr =
  | I_decl of ctyp * id
  | I_alloc of ctyp * id
  | I_init of ctyp * id * cval
  | I_if of cval * instr list * instr list * ctyp
  | I_funcall of clexp * id * cval list * ctyp
  | I_convert of clexp * ctyp * id * ctyp
  | I_assign of id * cval
  | I_copy of clexp * cval
  | I_clear of ctyp * id
  | I_throw of cval
  | I_return of cval
  | I_block of instr list
  | I_try_block of instr list
  | I_comment of string
  | I_label of string
  | I_goto of string
  | I_raw of string

let rec map_instrs f instr =
  match instr with
  | I_decl _ | I_alloc _ | I_init _ -> instr
  | I_if (cval, instrs1, instrs2, ctyp) ->
     I_if (cval, f (List.map (map_instrs f) instrs1), f (List.map (map_instrs f) instrs2), ctyp)
  | I_funcall _ | I_convert _ | I_assign _ | I_copy _ | I_clear _ | I_throw _ | I_return _ -> instr
  | I_block instrs -> I_block (f (List.map (map_instrs f) instrs))
  | I_try_block instrs -> I_try_block (f (List.map (map_instrs f) instrs))
  | I_comment _ | I_label _ | I_goto _ | I_raw _ -> instr

type cdef =
  | CDEF_reg_dec of ctyp * id
  | CDEF_fundef of id * id option * id list * instr list
  | CDEF_type of ctype_def

let rec instr_ctyps = function
  | I_decl (ctyp, _) | I_alloc (ctyp, _) | I_clear (ctyp, _) -> [ctyp]
  | I_init (ctyp, _, cval) -> [ctyp; cval_ctyp cval]
  | I_if (cval, instrs1, instrs2, ctyp) ->
     ctyp :: cval_ctyp cval :: List.concat (List.map instr_ctyps instrs1 @ List.map instr_ctyps instrs2)
  | I_funcall (_, _, cvals, ctyp) ->
     ctyp :: List.map cval_ctyp cvals
  | I_convert (_, ctyp1, _, ctyp2) -> [ctyp1; ctyp2]
  | I_assign (_, cval) | I_copy (_, cval) -> [cval_ctyp cval]
  | I_block instrs | I_try_block instrs -> List.concat (List.map instr_ctyps instrs)
  | I_throw cval | I_return cval -> [cval_ctyp cval]
  | I_comment _ | I_label _ | I_goto _ | I_raw _ -> []

let cdef_ctyps = function
  | CDEF_reg_dec (ctyp, _) -> [ctyp]
  | CDEF_fundef (_, _, _, instrs) -> List.concat (List.map instr_ctyps instrs)
  | CDEF_type tdef -> ctype_def_ctyps tdef

(* For debugging we define a pretty printer for LLcode instructions *)

let pp_ctyp ctyp =
  string (string_of_ctyp ctyp |> Util.yellow |> Util.clear)

let pp_keyword str =
  string ((str |> Util.red |> Util.clear) ^ "$")

let pp_cval = function
  | CV_id (id, ctyp) -> parens (pp_ctyp ctyp) ^^ (pp_id id)
  | CV_C_fragment (str, ctyp) -> parens (pp_ctyp ctyp) ^^ (string (str |> Util.cyan |> Util.clear))

let rec pp_clexp = function
  | CL_id id -> pp_id id
  | CL_field (id, field) -> pp_id id ^^ string "." ^^ pp_id field
  | CL_addr clexp -> string "*" ^^ pp_clexp clexp

let rec pp_instr = function
  | I_decl (ctyp, id) ->
     parens (pp_ctyp ctyp) ^^ space ^^ pp_id id
  | I_if (cval, then_instrs, else_instrs, ctyp) ->
     let pp_if_block instrs = surround 2 0 lbrace (separate_map hardline pp_instr instrs) rbrace in
     parens (pp_ctyp ctyp) ^^ space
     ^^ pp_keyword "IF" ^^ pp_cval cval
     ^^ pp_keyword "THEN" ^^ pp_if_block then_instrs
     ^^ pp_keyword "ELSE" ^^ pp_if_block else_instrs
  | I_block instrs ->
     surround 2 0 lbrace (separate_map hardline pp_instr instrs) rbrace
  | I_try_block instrs ->
     pp_keyword "TRY" ^^ surround 2 0 lbrace (separate_map hardline pp_instr instrs) rbrace
  | I_alloc (ctyp, id) ->
     pp_keyword "ALLOC" ^^ parens (pp_ctyp ctyp) ^^ space ^^ pp_id id
  | I_init (ctyp, id, cval) ->
     pp_keyword "INIT" ^^ pp_ctyp ctyp ^^ parens (pp_id id ^^ string ", " ^^ pp_cval cval)
  | I_funcall (x, f, args, ctyp2) ->
     separate space [ pp_clexp x; string ":=";
                      pp_id ~color:Util.red f ^^ parens (separate_map (string ", ") pp_cval args);
                      string "->"; pp_ctyp ctyp2 ]
  | I_convert (x, ctyp1, y, ctyp2) ->
     separate space [ pp_clexp x; string ":=";
                      pp_keyword "CONVERT" ^^ pp_ctyp ctyp2 ^^ parens (pp_id y);
                      string "->"; pp_ctyp ctyp1 ]
  | I_assign (id, cval) ->
     separate space [pp_id id; string ":="; pp_cval cval]
  | I_copy (clexp, cval) ->
     separate space [string "let"; pp_clexp clexp; string "="; pp_cval cval]
  | I_clear (ctyp, id) ->
     pp_keyword "CLEAR" ^^ pp_ctyp ctyp ^^ parens (pp_id id)
  | I_return cval ->
     pp_keyword "RETURN" ^^ pp_cval cval
  | I_throw cval ->
     pp_keyword "THROW" ^^ pp_cval cval
  | I_comment str ->
     string ("// " ^ str)
  | I_label str ->
     string (str ^ ":")
  | I_goto str ->
     pp_keyword "GOTO" ^^ string str
  | I_raw str ->
     pp_keyword "C" ^^ string str

let is_ct_enum = function
  | CT_enum _ -> true
  | _ -> false

let is_ct_tup = function
  | CT_tup _ -> true
  | _ -> false

let rec compile_aval ctx = function
  | AV_C_fragment (code, typ) ->
     [], CV_C_fragment (code, ctyp_of_typ ctx typ), []

  | AV_id (id, typ) ->
     begin
       match ctyp_of_typ ctx (lvar_typ typ) with
       | CT_enum (_, elems) when IdSet.mem id elems ->
          [], CV_C_fragment (Util.zencode_upper_string (string_of_id id), ctyp_of_typ ctx (lvar_typ typ)), []
       | _ ->
          [], CV_id (id, ctyp_of_typ ctx (lvar_typ typ)), []
     end

  | AV_lit (L_aux (L_string str, _), typ) ->
     [], CV_C_fragment ("\"" ^ str ^ "\"", ctyp_of_typ ctx typ), []

  | AV_lit (L_aux (L_num n, _), typ) when Big_int.less_equal min_int64 n && Big_int.less_equal n max_int64 ->
     let gs = gensym () in
     [I_decl (CT_mpz, gs);
      I_init (CT_mpz, gs, CV_C_fragment (Big_int.to_string n ^ "L", CT_int64))],
     CV_id (gs, CT_mpz),
     [I_clear (CT_mpz, gs)]

  | AV_lit (L_aux (L_num n, _), typ) ->
     let gs = gensym () in
     [ I_decl (CT_mpz, gs);
       I_init (CT_mpz, gs, CV_C_fragment ("\"" ^ Big_int.to_string n ^ "\"", CT_string)) ],
     CV_id (gs, CT_mpz),
     [I_clear (CT_mpz, gs)]

  | AV_tuple avals ->
     let elements = List.map (compile_aval ctx) avals in
     let cvals = List.map (fun (_, cval, _) -> cval) elements in
     let setup = List.concat (List.map (fun (setup, _, _) -> setup) elements) in
     let cleanup = List.concat (List.rev (List.map (fun (_, _, cleanup) -> cleanup) elements)) in
     let tup_ctyp = CT_tup (List.map cval_ctyp cvals) in
     let gs = gensym () in
     setup
     @ [I_decl (tup_ctyp, gs)]
     @ List.mapi (fun n cval -> I_copy (CL_field (gs, mk_id ("tup" ^ string_of_int n)), cval)) cvals,
     CV_id (gs, CT_tup (List.map cval_ctyp cvals)),
     cleanup

let compile_funcall ctx id args typ =
  let setup = ref [] in
  let cleanup = ref [] in

  let _, Typ_aux (fn_typ, _) = Env.get_val_spec id ctx.tc_env in
  let arg_typs, ret_typ = match fn_typ with
    | Typ_fn (Typ_aux (Typ_tup arg_typs, _), ret_typ, _) -> arg_typs, ret_typ
    | Typ_fn (arg_typ, ret_typ, _) -> [arg_typ], ret_typ
    | _ -> assert false
  in
  let arg_ctyps, ret_ctyp = List.map (ctyp_of_typ ctx) arg_typs, ctyp_of_typ ctx ret_typ in
  let final_ctyp = ctyp_of_typ ctx typ in

  let setup_arg ctyp aval =
    let arg_setup, cval, arg_cleanup = compile_aval ctx aval in
    setup := List.rev arg_setup @ !setup;
    cleanup := arg_cleanup @ !cleanup;
    let have_ctyp = cval_ctyp cval in
    if ctyp_equal ctyp have_ctyp then
      cval
    else if is_stack_ctyp have_ctyp && not (is_stack_ctyp ctyp) then
      let gs = gensym () in
      setup := I_decl (ctyp, gs) :: !setup;
      setup := I_init (ctyp, gs, cval) :: !setup;
      cleanup := I_clear (ctyp, gs) :: !cleanup;
      CV_id (gs, ctyp)
    else
      assert false
  in

  let sargs = List.map2 setup_arg arg_ctyps args in

  let call =
    if ctyp_equal final_ctyp ret_ctyp then
      fun ret -> I_funcall (ret, id, sargs, ret_ctyp)
    else if not (is_stack_ctyp ret_ctyp) && is_stack_ctyp final_ctyp then
      let gs = gensym () in
      setup := I_alloc (ret_ctyp, gs) :: !setup;
      setup := I_funcall (CL_id gs, id, sargs, ret_ctyp) :: !setup;
      cleanup := I_clear (ret_ctyp, gs) :: !cleanup;
      fun ret -> I_convert (ret, final_ctyp, gs, ret_ctyp)
    else
      assert false
  in

  (List.rev !setup, final_ctyp, call, !cleanup)

let rec compile_match ctx apat cval case_label =
  match apat, cval with
  | AP_id pid, CV_C_fragment (code, ctyp) when is_ct_enum ctyp ->
     [ I_if (CV_C_fragment (Util.zencode_upper_string (string_of_id pid) ^ " != " ^ code, CT_bool), [I_goto case_label], [], CT_unit) ]
  | AP_id pid, CV_id (id, ctyp) when is_ct_enum ctyp ->
     [ I_if (CV_C_fragment (Util.zencode_upper_string (string_of_id pid) ^ " != " ^ Util.zencode_string (string_of_id id), CT_bool), [I_goto case_label], [], CT_unit) ]
  | AP_id pid, CV_C_fragment (code, ctyp) ->
     [ I_decl (cval_ctyp cval, pid); I_copy (CL_id pid, cval) ]
  | AP_id pid, CV_id _ ->
     [ I_decl (cval_ctyp cval, pid); I_copy (CL_id pid, cval) ]
  | AP_tup apats, CV_id (id, ctyp) ->
     begin
       let get_tup n ctyp = CV_C_fragment (Util.zencode_string (string_of_id id) ^ ".ztup" ^ string_of_int n, ctyp) in
       match ctyp with
       | CT_tup ctyps ->
          fst (List.fold_left2 (fun (instrs, n) apat ctyp -> instrs @ compile_match ctx apat (get_tup n ctyp) case_label, n + 1) ([], 0) apats ctyps)
       | _ -> assert false
     end
  | _, _ -> []

let unit_fragment = CV_C_fragment ("UNIT", CT_unit)

(** GLOBAL: label_counter is used to make sure all labels have unique
   names. Like gensym_counter it should be safe to reset between
   top-level definitions. **)
let label_counter = ref 0

let label str =
  let str = str ^ string_of_int !label_counter in
  incr label_counter;
  str

let rec compile_aexp ctx = function
  | AE_let (id, _, binding, body, typ) ->
     let setup, ctyp, call, cleanup = compile_aexp ctx binding in
     let letb1, letb1c =
       if is_stack_ctyp ctyp then
         [I_decl (ctyp, id); call (CL_id id)], []
       else
         [I_alloc (ctyp, id); call (CL_id id)], [I_clear (ctyp, id)]
     in
     let letb2 = setup @ letb1 @ cleanup in
     let setup, ctyp, call, cleanup = compile_aexp ctx body in
     letb2 @ setup, ctyp, call, cleanup @ letb1c

  | AE_app (id, vs, typ) ->
     compile_funcall ctx id vs typ

  | AE_val aval ->
     let setup, cval, cleanup = compile_aval ctx aval in
     setup, cval_ctyp cval, (fun clexp -> I_copy (clexp, cval)), cleanup

  (* Compile case statements *)
  | AE_case (aval, cases, typ) ->
     let ctyp = ctyp_of_typ ctx typ in
     let aval_setup, cval, aval_cleanup = compile_aval ctx aval in
     let case_return_id = gensym () in
     let finish_match_label = label "finish_match_" in
     let compile_case (apat, guard, body) =
       let trivial_guard = match guard with
         | AE_val (AV_lit (L_aux (L_true, _), _))
         | AE_val (AV_C_fragment ("true", _)) -> true
         | _ -> false
       in
       let case_label = label "case_" in
       let destructure = compile_match ctx apat cval case_label in
       let guard_setup, _, guard_call, guard_cleanup = compile_aexp ctx guard in
       let body_setup, _, body_call, body_cleanup = compile_aexp ctx body in
       let gs = gensym () in
       let case_instrs =
         destructure @ [I_comment "end destructuring"]
         @ (if not trivial_guard then
              guard_setup @ [I_decl (CT_bool, gs); guard_call (CL_id gs)] @ guard_cleanup
              @ [I_if (CV_C_fragment (Printf.sprintf "!%s" (Util.zencode_string (string_of_id gs)), CT_bool), [I_goto case_label], [], CT_unit)]
              @ [I_comment "end guard"]
            else [])
         @ body_setup @ [body_call (CL_id case_return_id)] @ body_cleanup
         @ [I_goto finish_match_label]
       in
       [I_block case_instrs; I_label case_label]
     in
     [I_comment "begin match"]
     @ aval_setup @ [I_decl (ctyp, case_return_id)]
     @ List.concat (List.map compile_case cases)
     @ [I_raw "sail_match_failure();"]
     @ [I_label finish_match_label],
     ctyp,
     (fun clexp -> I_copy (clexp, CV_id (case_return_id, ctyp))),
     aval_cleanup
     @ [I_comment "end match"]

  (* Compile try statement *)
  | AE_try (aexp, cases, typ) ->
     let aexp_setup, ctyp, aexp_call, aexp_cleanup = compile_aexp ctx aexp in
     let case_return_id = gensym () in
     let handled_exception_label = label "handled_exception_" in
     let compile_case (apat, guard, body) =
       let trivial_guard = match guard with
         | AE_val (AV_lit (L_aux (L_true, _), _))
         | AE_val (AV_C_fragment ("true", _)) -> true
         | _ -> false
       in
       let try_label = label "try_" in
       let exn_cval = CV_C_fragment ("*current_exception", ctyp_of_typ ctx (mk_typ (Typ_id (mk_id "exception")))) in
       let destructure = compile_match ctx apat exn_cval try_label in
       let guard_setup, _, guard_call, guard_cleanup = compile_aexp ctx guard in
       let body_setup, _, body_call, body_cleanup = compile_aexp ctx body in
       let gs = gensym () in
       let case_instrs =
         destructure @ [I_comment "end destructuring"]
         @ (if not trivial_guard then
              guard_setup @ [I_decl (CT_bool, gs); guard_call (CL_id gs)] @ guard_cleanup
              @ [I_if (CV_C_fragment (Printf.sprintf "!%s" (Util.zencode_string (string_of_id gs)), CT_bool), [I_goto try_label], [], CT_unit)]
              @ [I_comment "end guard"]
            else [])
         @ body_setup @ [body_call (CL_id case_return_id)] @ body_cleanup
         @ [I_goto handled_exception_label]
       in
       [I_block case_instrs; I_label try_label]
     in
     [],
     ctyp,
     (fun clexp -> I_try_block (aexp_setup @ [aexp_call clexp] @ aexp_cleanup)),
     [I_if (CV_C_fragment ("!have_exception", CT_bool), [I_goto handled_exception_label], [], CT_unit)]
     @ List.concat (List.map compile_case cases)
     @ [I_raw "sail_match_failure();"]
     @ [I_label handled_exception_label]

  | AE_if (aval, then_aexp, else_aexp, if_typ) ->
     let if_ctyp = ctyp_of_typ ctx if_typ in
     let compile_branch aexp =
       let setup, ctyp, call, cleanup = compile_aexp ctx aexp in
       fun clexp -> setup @ [call clexp] @ cleanup
     in
     let setup, ctyp, call, cleanup = compile_aexp ctx (AE_val aval) in
     let gs = gensym () in
     setup @ [I_decl (ctyp, gs); call (CL_id gs)],
     if_ctyp,
     (fun clexp -> I_if (CV_id (gs, ctyp),
                         compile_branch then_aexp clexp,
                         compile_branch else_aexp clexp,
                         if_ctyp)),
     cleanup

  | AE_record_update (aval, fields, typ) ->
     let update_field (prev_setup, prev_calls, prev_cleanup) (field, aval) =
       let setup, _, call, cleanup = compile_aexp ctx (AE_val aval) in
       prev_setup @ setup, call :: prev_calls, cleanup @ prev_cleanup
     in
     let setup, calls, cleanup = List.fold_left update_field ([], [], []) (Bindings.bindings fields) in
     let ctyp = ctyp_of_typ ctx typ in
     let gs = gensym () in
     [I_alloc (ctyp, gs)] @ setup @ List.map (fun call -> call (CL_id gs)) calls,
     ctyp,
     (fun clexp -> I_copy (clexp, CV_id (gs, ctyp))),
     cleanup @ [I_clear (ctyp, gs)]

  | AE_assign (id, assign_typ, aexp) ->
     (* assign_ctyp is the type of the C variable we are assigning to,
        ctyp is the type of the C expression being assigned. These may
        be different. *)
     let assign_ctyp = ctyp_of_typ ctx assign_typ in
     let setup, ctyp, call, cleanup = compile_aexp ctx aexp in
     let comment = "assign " ^ string_of_ctyp assign_ctyp ^ " := " ^ string_of_ctyp ctyp in
     if ctyp_equal assign_ctyp ctyp then
       setup @ [call (CL_id id)], CT_unit, (fun clexp -> I_copy (clexp, unit_fragment)), cleanup
     else if not (is_stack_ctyp assign_ctyp) && is_stack_ctyp ctyp then
       let gs = gensym () in
       setup @ [ I_comment comment;
                 I_decl (ctyp, gs);
                 call (CL_id gs);
                 I_convert (CL_id id, assign_ctyp, gs, ctyp)
               ],
       CT_unit,
       (fun clexp -> I_copy (clexp, unit_fragment)),
       cleanup
     else
       failwith comment

  | AE_block (aexps, aexp, _) ->
     let block = compile_block ctx aexps in
     let setup, ctyp, call, cleanup = compile_aexp ctx aexp in
     block @ setup, ctyp, call, cleanup

  | AE_loop (While, cond, body) ->
     let loop_start_label = label "while_" in
     let loop_end_label = label "wend_" in
     let cond_setup, _, cond_call, cond_cleanup = compile_aexp ctx cond in
     let body_setup, _, body_call, body_cleanup = compile_aexp ctx body in
     let gs = gensym () in
     let unit_gs = gensym () in
     let loop_test = CV_C_fragment (Printf.sprintf "!%s" (Util.zencode_string (string_of_id gs)), CT_bool) in
     cond_setup @ [I_decl (CT_bool, gs); I_decl (CT_unit, unit_gs)]
     @ [I_label loop_start_label]
     @ [I_block ([cond_call (CL_id gs); I_if (loop_test, [I_goto loop_end_label], [], CT_unit)]
                 @ body_setup
                 @ [body_call (CL_id unit_gs)]
                 @ body_cleanup
                 @ [I_goto loop_start_label])]
     @ [I_label loop_end_label],
     CT_unit,
     (fun clexp -> I_copy (clexp, unit_fragment)),
     cond_cleanup

  | AE_cast (aexp, typ) -> compile_aexp ctx aexp

  | AE_return (aval, typ) ->
     (* Cleanup info will be re-added by fix_early_return *)
     let return_setup, cval, _ = compile_aval ctx aval in
     return_setup @ [I_return cval],
     CT_unit,
     (fun clexp -> I_copy (clexp, unit_fragment)),
     []

  | AE_throw (aval, typ) ->
     (* Cleanup info will be handled by fix_exceptions *)
     let throw_setup, cval, _ = compile_aval ctx aval in
     throw_setup @ [I_throw cval],
     CT_unit,
     (fun clexp -> I_copy (clexp, unit_fragment)),
     []

  | aexp -> failwith ("Cannot compile ANF expression: " ^ Pretty_print_sail.to_string (pp_aexp aexp))

and compile_block ctx = function
  | [] -> []
  | exp :: exps ->
     let setup, _, call, cleanup = compile_aexp ctx exp in
     let rest = compile_block ctx exps in
     let gs = gensym () in
     setup @ [I_decl (CT_unit, gs); call (CL_id gs)] @ cleanup @ rest

let rec pat_ids (P_aux (p_aux, _) as pat) =
  match p_aux with
  | P_id id -> [id]
  | P_tup pats -> List.concat (List.map pat_ids pats)
  | P_lit (L_aux (L_unit, _)) -> let gs = gensym () in [gs]
  | P_wild -> let gs = gensym () in [gs]
  | _ -> failwith ("Bad pattern " ^ string_of_pat pat)

(** Compile a sail type definition into a LLcode one. Most of the
   actual work of translating the typedefs into C is done by the code
   generator, as it's easy to keep track of structs, tuples and unions
   in their sail form at this level, and leave the fiddly details of
   how they get mapped to C in the next stage. This function also adds
   details of the types it compiles to the context, ctx, which is why
   it returns a ctypdef * ctx pair. **)
let compile_type_def ctx (TD_aux (type_def, _)) =
  match type_def with
  | TD_enum (id, _, ids, _) ->
     CTD_enum (id, IdSet.of_list ids),
     { ctx with enums = Bindings.add id (IdSet.of_list ids) ctx.enums }

  | TD_record (id, _, _, ctors, _) ->
     let ctors = List.fold_left (fun ctors (typ, id) -> Bindings.add id (ctyp_of_typ ctx typ) ctors) Bindings.empty ctors in
     CTD_record (id, ctors),
     { ctx with records = Bindings.add id ctors ctx.records }

  | TD_variant (id, _, _, tus, _) ->
     c_debug ("Compiling variant " ^ string_of_id id);
     let compile_tu (Tu_aux (tu_aux, _)) =
       match tu_aux with
       | Tu_id id -> CT_unit, id
       | Tu_ty_id (typ, id) -> ctyp_of_typ ctx typ, id
     in
     let ctus = List.fold_left (fun ctus (ctyp, id) -> Bindings.add id ctyp ctus) Bindings.empty (List.map compile_tu tus) in
     CTD_variant (id, ctus),
     { ctx with variants = Bindings.add id ctus ctx.variants }

  (* Will be re-written before here, see bitfield.ml *)
  | TD_bitfield _ -> failwith "Cannot compile TD_bitfield"
  (* All type abbreviations are filtered out in compile_def  *)
  | TD_abbrev _ -> assert false

let instr_split_at f =
  let rec instr_split_at' f before = function
    | [] -> (List.rev before, [])
    | instr :: instrs when f instr -> (List.rev before, instr :: instrs)
    | instr :: instrs -> instr_split_at' f (instr :: before) instrs
  in
  instr_split_at' f []

let generate_cleanup instrs =
  let generate_cleanup' = function
    | I_decl (ctyp, id) when not (is_stack_ctyp ctyp) -> [(id, I_clear (ctyp, id))]
    | I_alloc (ctyp, id) when not (is_stack_ctyp ctyp) -> [(id, I_clear (ctyp, id))]
    | _ -> []
  in
  let is_clear ids = function
    | I_clear (_, id) -> IdSet.add id ids
    | _ -> ids
  in
  let cleaned = List.fold_left is_clear IdSet.empty instrs in
  instrs
  |> List.map generate_cleanup'
  |> List.concat
  |> List.filter (fun (id, _) -> not (IdSet.mem id cleaned))
  |> List.map snd

(** Functions that have heap-allocated return types are implemented by
   passing a pointer a location where the return value should be
   stored. The ANF -> LLcode pass for expressions simply outputs an
   I_return instruction for any return value, so this function walks
   over the LLcode ast for expressions and modifies the return
   statements into code that sets that pointer, as well as adds extra
   control flow to cleanup heap-allocated variables correctly when a
   function terminates early. See the generate_cleanup function for
   how this is done. *)
let fix_early_return ret ctx instrs =
  let end_function_label = label "end_function_" in
  let is_return_recur = function
    | I_return _ | I_if _ | I_block _ -> true
    | _ -> false
  in
  let rec rewrite_return pre_cleanup instrs =
    match instr_split_at is_return_recur instrs with
    | instrs, [] -> instrs
    | before, I_block instrs :: after ->
       before
       @ [I_block (rewrite_return (pre_cleanup @ generate_cleanup before) instrs)]
       @ rewrite_return pre_cleanup after
    | before, I_if (cval, then_instrs, else_instrs, ctyp) :: after ->
       let cleanup = pre_cleanup @ generate_cleanup before in
       before
       @ [I_if (cval, rewrite_return cleanup then_instrs, rewrite_return cleanup else_instrs, ctyp)]
       @ rewrite_return pre_cleanup after
    | before, I_return cval :: after ->
       let cleanup_label = label "cleanup_" in
       let end_cleanup_label = label "end_cleanup_" in
       before
       @ [I_copy (ret, cval);
          I_goto cleanup_label]
       (* This is probably dead code until cleanup_label, but how can we be sure there are no jumps into it? *)
       @ rewrite_return pre_cleanup after
       @ [I_goto end_cleanup_label]
       @ [I_label cleanup_label]
       @ pre_cleanup
       @ generate_cleanup before
       @ [I_goto end_function_label]
       @ [I_label end_cleanup_label]
    | _, _ -> assert false
  in
  rewrite_return [] instrs
  @ [I_label end_function_label]

(** Compile a Sail toplevel definition into an LLcode definition **)
let compile_def ctx = function
  | DEF_reg_dec (DEC_aux (DEC_reg (typ, id), _)) ->
     [CDEF_reg_dec (ctyp_of_typ ctx typ, id)], ctx
  | DEF_reg_dec _ -> failwith "Unsupported register declaration" (* FIXME *)

  | DEF_spec _ -> [], ctx

  | DEF_fundef (FD_aux (FD_function (_, _, _, [FCL_aux (FCL_Funcl (id, pexp), _)]), _)) ->
     begin
       match pexp with
       | Pat_aux (Pat_exp (pat, exp), _) ->
          let aexp = map_functions (analyze_primop ctx) (c_literals ctx (anf exp)) in
          prerr_endline (Pretty_print_sail.to_string (pp_aexp aexp));
          let setup, ctyp, call, cleanup = compile_aexp ctx aexp in
          let gs = gensym () in
          if is_stack_ctyp ctyp then
            let instrs = [I_decl (ctyp, gs)] @ setup @ [call (CL_id gs)] @ cleanup @ [I_return (CV_id (gs, ctyp))] in
            [CDEF_fundef (id, None, pat_ids pat, instrs)], ctx
          else
            let instrs = setup @ [call (CL_addr (CL_id gs))] @ cleanup in
            let instrs = fix_early_return (CL_addr (CL_id gs)) ctx instrs in
            [CDEF_fundef (id, Some gs, pat_ids pat, instrs)], ctx
       | _ -> assert false
     end

  (* All abbreviations should expanded by the typechecker, so we don't
     need to translate type abbreviations into C typedefs. *)
  | DEF_type (TD_aux (TD_abbrev _, _)) -> [], ctx

  | DEF_type type_def ->
     let tdef, ctx = compile_type_def ctx type_def in
     [CDEF_type tdef], ctx

  (* Only DEF_default that matters is default Order, but all order
     polymorphism is specialised by this point. *)
  | DEF_default _ -> [], ctx

  (* Overloading resolved by type checker *)
  | DEF_overload _ -> [], ctx

  (* Only the parser and sail pretty printer care about this. *)
  | DEF_fixity _ -> [], ctx

  | _ -> assert false

(** To keep things neat we use GCC's local labels extension to limit
   the scope of labels. We do this by iterating over all the blocks
   and adding a __label__ declaration with all the labels local to
   that block. The add_local_labels function is called by the code
   generator just before it outputs C.

   See https://gcc.gnu.org/onlinedocs/gcc/Local-Labels.html **)
let add_local_labels' instrs =
  let is_label = function
    | I_label str -> [str]
    | _ -> []
  in
  let labels = List.concat (List.map is_label instrs) in
  let local_label_decl = I_raw ("__label__ " ^ String.concat ", " labels ^ ";\n") in
  if labels = [] then
    instrs
  else
    local_label_decl :: instrs

let add_local_labels instrs =
  match map_instrs add_local_labels' (I_block instrs) with
  | I_block instrs -> instrs
  | _ -> assert false

(**************************************************************************)
(* 5. Code generation                                                     *)
(**************************************************************************)

let sgen_id id = Util.zencode_string (string_of_id id)
let codegen_id id = string (sgen_id id)

let upper_sgen_id id = Util.zencode_upper_string (string_of_id id)
let upper_codegen_id id = string (upper_sgen_id id)

let sgen_ctyp = function
  | CT_unit -> "unit"
  | CT_int -> "int"
  | CT_bool -> "bool"
  | CT_uint64 _ -> "uint64_t"
  | CT_int64 -> "int64_t"
  | CT_mpz -> "mpz_t"
  | CT_bv _ -> "bv_t"
  | CT_tup _ as tup -> "struct " ^ Util.zencode_string ("tuple_" ^ string_of_ctyp tup)
  | CT_struct (id, _) -> "struct " ^ sgen_id id
  | CT_enum (id, _) -> "enum " ^ sgen_id id
  | CT_variant (id, _) -> "struct " ^ sgen_id id
  | CT_string -> "sail_string"

let sgen_ctyp_name = function
  | CT_unit -> "unit"
  | CT_int -> "int"
  | CT_bool -> "bool"
  | CT_uint64 _ -> "uint64_t"
  | CT_int64 -> "int64_t"
  | CT_mpz -> "mpz_t"
  | CT_bv _ -> "bv_t"
  | CT_tup _ as tup -> Util.zencode_string ("tuple_" ^ string_of_ctyp tup)
  | CT_struct (id, _) -> sgen_id id
  | CT_enum (id, _) -> sgen_id id
  | CT_variant (id, _) -> sgen_id id
  | CT_string -> "sail_string"

let sgen_cval = function
  | CV_C_fragment (c, _) -> c
  | CV_id (id, _) -> sgen_id id
  | _ -> "CVAL??"

let sgen_clexp = function
  | CL_id id -> "&" ^ sgen_id id
  | CL_field (id, field) -> "&(" ^ sgen_id id ^ "." ^ sgen_id field ^ ")"
  | CL_addr (CL_id id) -> sgen_id id
  | _ -> assert false

let sgen_clexp_pure = function
  | CL_id id -> sgen_id id
  | CL_field (id, field) -> sgen_id id ^ "." ^ sgen_id field
  | _ -> assert false

let rec codegen_instr ctx = function
  | I_decl (ctyp, id) ->
     string (Printf.sprintf "  %s %s;" (sgen_ctyp ctyp) (sgen_id id))
  | I_copy (clexp, cval) ->
     let ctyp = cval_ctyp cval in
     if is_stack_ctyp ctyp then
       string (Printf.sprintf "  %s = %s;" (sgen_clexp_pure clexp) (sgen_cval cval))
     else
       string (Printf.sprintf "  set_%s(%s, %s);" (sgen_ctyp_name ctyp) (sgen_clexp clexp) (sgen_cval cval))
  | I_if (cval, [then_instr], [], ctyp) ->
     string (Printf.sprintf "  if (%s)" (sgen_cval cval)) ^^ hardline
     ^^ twice space ^^ codegen_instr ctx then_instr
  | I_if (cval, then_instrs, else_instrs, ctyp) ->
     string "  if" ^^ space ^^ parens (string (sgen_cval cval)) ^^ space
     ^^ surround 2 0 lbrace (separate_map hardline (codegen_instr ctx) then_instrs) (twice space ^^ rbrace)
     ^^ space ^^ string "else" ^^ space
     ^^ surround 2 0 lbrace (separate_map hardline (codegen_instr ctx) else_instrs) (twice space ^^ rbrace)
  | I_block instrs ->
     string "  {"
     ^^ jump 2 2 (separate_map hardline (codegen_instr ctx) instrs) ^^ hardline
     ^^ string "  }"
  | I_try_block instrs ->
     string "  { /* try */"
     ^^ jump 2 2 (separate_map hardline (codegen_instr ctx) instrs) ^^ hardline
     ^^ string "  }"
  | I_funcall (x, f, args, ctyp) ->
     let args = Util.string_of_list ", " sgen_cval args in
     let fname = if Env.is_extern f ctx.tc_env "c" then Env.get_extern f ctx.tc_env "c" else sgen_id f in
     if is_stack_ctyp ctyp then
       string (Printf.sprintf "  %s = %s(%s);" (sgen_clexp_pure x) fname args)
     else
       string (Printf.sprintf "  %s(%s, %s);" fname (sgen_clexp x) args)
  | I_clear (ctyp, id) ->
     string (Printf.sprintf "  clear_%s(&%s);" (sgen_ctyp_name ctyp) (sgen_id id))
  | I_init (ctyp, id, cval) ->
     string (Printf.sprintf "  init_%s_of_%s(&%s, %s);"
                            (sgen_ctyp_name ctyp)
                            (sgen_ctyp_name (cval_ctyp cval))
                            (sgen_id id)
                            (sgen_cval cval))
  | I_alloc (ctyp, id) ->
     string (Printf.sprintf "  %s %s;" (sgen_ctyp ctyp) (sgen_id id))
     ^^ hardline
     ^^ string (Printf.sprintf "  init_%s(&%s);" (sgen_ctyp_name ctyp) (sgen_id id))
  | I_convert (x, ctyp1, y, ctyp2) ->
     if is_stack_ctyp ctyp1 then
       string (Printf.sprintf "  %s = convert_%s_of_%s(%s);"
                 (sgen_clexp_pure x)
                 (sgen_ctyp_name ctyp1)
                 (sgen_ctyp_name ctyp2)
                 (sgen_id y))
     else
       string (Printf.sprintf "  convert_%s_of_%s(%s, %s);"
                 (sgen_ctyp_name ctyp1)
                 (sgen_ctyp_name ctyp2)
                 (sgen_clexp x)
                 (sgen_id y))
  | I_return cval ->
     string (Printf.sprintf "  return %s;" (sgen_cval cval))
  | I_throw cval ->
     string "  THROW"
  | I_comment str ->
     string ("  /* " ^ str ^ " */")
  | I_label str ->
     string (str ^ ": ;")
  | I_goto str ->
     string (Printf.sprintf "  goto %s;" str)
  | I_raw str ->
     string ("  " ^ str)

let codegen_type_def ctx = function
  | CTD_enum (id, ids) ->
     string (Printf.sprintf "// enum %s" (string_of_id id)) ^^ hardline
     ^^ separate space [string "enum"; codegen_id id; lbrace; separate_map (comma ^^ space) upper_codegen_id (IdSet.elements ids); rbrace ^^ semi]

  | CTD_record (id, ctors) ->
     (* Generate a set_T function for every struct T *)
     let codegen_set (id, ctyp) =
       if is_stack_ctyp ctyp then
         string (Printf.sprintf "rop->%s = op.%s;" (sgen_id id) (sgen_id id))
       else
         string (Printf.sprintf "set_%s(&rop->%s, op.%s);" (sgen_ctyp_name ctyp) (sgen_id id) (sgen_id id))
     in
     let codegen_setter id ctors =
       string (let n = sgen_id id in Printf.sprintf "void set_%s(struct %s *rop, const struct %s op)" n n n) ^^ space
       ^^ surround 2 0 lbrace
                   (separate_map hardline codegen_set (Bindings.bindings ctors))
                   rbrace
     in
     (* Generate an init/clear_T function for every struct T *)
     let codegen_field_init f (id, ctyp) =
       if not (is_stack_ctyp ctyp) then
         [string (Printf.sprintf "%s_%s(&op->%s);" f (sgen_ctyp_name ctyp) (sgen_id id))]
       else []
     in
     let codegen_init f id ctors =
       string (let n = sgen_id id in Printf.sprintf "void %s_%s(struct %s *op)" f n n) ^^ space
       ^^ surround 2 0 lbrace
                   (separate hardline (Bindings.bindings ctors |> List.map (codegen_field_init f) |> List.concat))
                   rbrace
     in
     (* Generate the struct and add the generated functions *)
     let codegen_ctor (id, ctyp) =
       string (sgen_ctyp ctyp) ^^ space ^^ codegen_id id
     in
     string (Printf.sprintf "// struct %s" (string_of_id id)) ^^ hardline
     ^^ string "struct" ^^ space ^^ codegen_id id ^^ space
     ^^ surround 2 0 lbrace
                 (separate_map (semi ^^ hardline) codegen_ctor (Bindings.bindings ctors) ^^ semi)
                 rbrace
     ^^ semi ^^ twice hardline
     ^^ codegen_setter id ctors
     ^^ twice hardline
     ^^ codegen_init "init" id ctors
     ^^ twice hardline
     ^^ codegen_init "clear" id ctors

  | CTD_variant (id, tus) ->
     let codegen_tu (id, ctyp) =
       separate space [string "struct"; lbrace; string (sgen_ctyp ctyp); codegen_id id ^^ semi; rbrace]
     in
     string (Printf.sprintf "// union %s" (string_of_id id)) ^^ hardline
     ^^ string "enum" ^^ space
     ^^ string ("kind_" ^ sgen_id id) ^^ space
     ^^ separate space [ lbrace;
                         separate_map (comma ^^ space) (fun id -> string ("Kind_" ^ sgen_id id)) (List.map fst (Bindings.bindings tus));
                         rbrace ^^ semi ]
     ^^ hardline ^^ hardline
     ^^ string "struct" ^^ space ^^ codegen_id id ^^ space
     ^^ surround 2 0 lbrace
                 (separate space [string "enum"; string ("kind_" ^ sgen_id id); string "kind" ^^ semi]
                  ^^ hardline
                  ^^ string "union" ^^ space
                  ^^ surround 2 0 lbrace
                              (separate_map (semi ^^ hardline) codegen_tu (Bindings.bindings tus) ^^ semi)
                              rbrace
                  ^^ semi)
                 rbrace
     ^^ semi
     (* If this is the exception type, then we setup up some global variables to deal with exceptions. *)
     ^^ if string_of_id id = "exception" then
          hardline ^^ hardline
          ^^ separate space [string "struct"; codegen_id id; string "*current_exception = NULL;"]
          ^^ hardline
          ^^ string "bool have_exception = false;"
        else
          empty

(** GLOBAL: because C doesn't have real anonymous tuple types
   (anonymous structs don't quite work the way we need) every tuple
   type in the spec becomes some generated named struct in C. This is
   done in such a way that every possible tuple type has a unique name
   associated with it. This global variable keeps track of these
   generated struct names, so we never generate two copies of the
   struct that is used to represent them in C.

   The way this works is that codegen_def scans each definition's type
   annotations for tuple types and generates the required structs
   using codegen_type_def before the actual definition is generated by
   codegen_def'.

   This variable should be reset to empty only when the entire AST has
   been translated to C. **)
let generated_tuples = ref IdSet.empty

let codegen_tup ctx ctyps =
  let id = mk_id ("tuple_" ^ string_of_ctyp (CT_tup ctyps)) in
  if IdSet.mem id !generated_tuples then
    empty
  else
    let _, fields = List.fold_left (fun (n, fields) ctyp -> n + 1, Bindings.add (mk_id ("tup" ^ string_of_int n)) ctyp fields)
                                   (0, Bindings.empty)
                                   ctyps
    in
    generated_tuples := IdSet.add id !generated_tuples;
    codegen_type_def ctx (CTD_record (id, fields)) ^^ twice hardline

let codegen_def' ctx = function
  | CDEF_reg_dec (ctyp, id) ->
     string (Printf.sprintf "// register %s" (string_of_id id)) ^^ hardline
     ^^ string (Printf.sprintf "%s %s;" (sgen_ctyp ctyp) (sgen_id id))

  | CDEF_fundef (id, ret_arg, args, instrs) ->
     let instrs = add_local_labels instrs in
     List.iter (fun instr -> prerr_endline (Pretty_print_sail.to_string (pp_instr instr))) instrs;
     let _, Typ_aux (fn_typ, _) = Env.get_val_spec id ctx.tc_env in
     let arg_typs, ret_typ = match fn_typ with
       | Typ_fn (Typ_aux (Typ_tup arg_typs, _), ret_typ, _) -> arg_typs, ret_typ
       | Typ_fn (arg_typ, ret_typ, _) -> [arg_typ], ret_typ
       | _ -> assert false
     in
     let arg_ctyps, ret_ctyp = List.map (ctyp_of_typ ctx) arg_typs, ctyp_of_typ ctx ret_typ in
     let args = Util.string_of_list ", " (fun x -> x) (List.map2 (fun ctyp arg -> sgen_ctyp ctyp ^ " " ^ sgen_id arg) arg_ctyps args) in
     let function_header =
       match ret_arg with
       | None ->
          assert (is_stack_ctyp ret_ctyp);
          string (sgen_ctyp ret_ctyp) ^^ space ^^ codegen_id id ^^ parens (string args) ^^ hardline
       | Some gs ->
          assert (not (is_stack_ctyp ret_ctyp));
          string "void" ^^ space ^^ codegen_id id
          ^^ parens (string (sgen_ctyp ret_ctyp ^ " *" ^ sgen_id gs ^ ", ") ^^ string args)
          ^^ hardline
     in
     function_header
     ^^ string "{"
     ^^ jump 0 2 (separate_map hardline (codegen_instr ctx) instrs) ^^ hardline
     ^^ string "}"

  | CDEF_type ctype_def ->
     codegen_type_def ctx ctype_def

let codegen_def ctx def =
  let untup = function
    | CT_tup ctyps -> ctyps
    | _ -> assert false
  in
  let tups = List.filter is_ct_tup (cdef_ctyps def) in
  let tups = List.map (fun ctyp -> codegen_tup ctx (untup ctyp)) tups in
  concat tups
  ^^ codegen_def' ctx def

let compile_ast ctx (Defs defs) =
  try
    let chunks, ctx = List.fold_left (fun (chunks, ctx) def -> let defs, ctx = compile_def ctx def in defs :: chunks, ctx) ([], ctx) defs in
    let cdefs = List.concat (List.rev chunks) in
    let docs = List.map (codegen_def ctx) cdefs in

    let preamble = separate hardline
                            [ string "#include \"sail.h\"" ]
    in

    let postamble = separate hardline
                             [ string "int main(void)";
                               string "{";
                               string "  zmain(UNIT);";
                               string "}" ]
    in

    let hlhl = hardline ^^ hardline in

    Pretty_print_sail.to_string (preamble ^^ hlhl ^^ separate hlhl docs ^^ hlhl ^^ postamble)
    |> print_endline
  with
    Type_error (l, err) -> prerr_endline ("Unexpected type error when compiling to C:\n" ^ string_of_type_error err)

let print_compiled (setup, ctyp, call, cleanup) =
  List.iter (fun instr -> print_endline (Pretty_print_sail.to_string (pp_instr instr))) setup;
  print_endline (Pretty_print_sail.to_string (pp_instr (call (CL_id (mk_id ("?" ^ string_of_ctyp ctyp))))));
  List.iter (fun instr -> print_endline (Pretty_print_sail.to_string (pp_instr instr))) cleanup

let compile_exp ctx exp =
  let aexp = anf exp in
  let aexp = c_literals ctx aexp in
  let aexp = map_functions (analyze_primop ctx) aexp in
  print_endline "\n###################### COMPILED ######################\n";
  print_compiled (compile_aexp ctx aexp);
  print_endline "\n###################### ANF ######################\n";
  aexp


(*

{
  uint64_t zx = 0x000000000000F000L;
  uint64_t v0 = (zx + 0x000000000000000FL) & 0x000000000000FFFFL;
  uint64_t res = (v0 + 0x000000000000FFFFL) & 0x000000000000FFFFL;
  return res;
}

*)
