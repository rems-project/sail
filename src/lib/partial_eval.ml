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
(*  SPDX-License-Identifier: BSD-2-Clause                                   *)
(****************************************************************************)

open Ast
open Ast_compare
open Ast_defs
open Ast_util

open Extraction.ZAst

module StringMap = Util.StringMap

let fallthrough () =
  let open Type_check in
  let open Type_error in
  try
    let env = initial_env |> Env.add_scattered_variant (mk_id "exception") [] in
    check_case env exc_typ
      (mk_pexp (Pat_exp (mk_pat (P_id (mk_id "exn")), mk_exp (E_throw (mk_exp (E_id (mk_id "exn")))))))
      unit_typ
    |> Option.get
  with Type_error (l, err) -> Reporting.unreachable l __POS__ (fst (string_of_type_error err))

module Tannot = struct
  open Extraction.TypeAnnot.Types

  type t = Type_check.tannot

  let get_type tannot =
    let typ = Type_check.typ_of_tannot tannot in
    typ

  let get_id_type tannot id =
    let env = Type_check.env_of_tannot tannot in
    match Type_check.Env.lookup_id id env with
    | Register _ -> Global_register
    | Local _ | Unbound _ -> Local_variable
    | Enum _ -> Enum_member

  let get_split tannot =
    let env = Type_check.env_of_tannot tannot in
    let typ = Type_check.typ_of_tannot tannot in
    match Type_check.destruct_vector env typ with
    | Some (Nexp_aux (Nexp_constant n, _), _) -> Split n
    | _ -> (
        match Type_check.destruct_bitvector env typ with
        | Some (Nexp_aux (Nexp_constant n, _)) -> Split n
        | _ -> No_split
      )

  let is_bitvector tannot = is_bitvector_typ (Type_check.typ_of_tannot tannot)

  let fallthrough () = fallthrough ()
end

module B = Extraction.ZAst.ExpBuilder (Tannot)

module Zinterp = Extraction.ZAst.Make (Tannot) (B)

module Lattice = Zinterp.R.L

type gstate = {
  primops : (Lattice.value list -> Lattice.value) StringMap.t;
  fundefs : Type_check.tannot fundef Bindings.t;
  typecheck_env : Type_check.Env.t;
}

let initial_gstate ~typecheck_env ~ast =
  let gstate = { primops = StringMap.empty; fundefs = Bindings.empty; typecheck_env } in
  let add_function gstate = function
    | DEF_aux (DEF_fundef fdef, _) -> { gstate with fundefs = Bindings.add (id_of_fundef fdef) fdef gstate.fundefs }
    | _ -> gstate
  in
  let gstate = List.fold_left add_function gstate ast.defs in
  gstate

let zexp_aux_parent = function
  | Z_single (p, _)
  | Z_return p
  | Z_exit p
  | Z_pair_1 (p, _, _)
  | Z_pair_2 (p, _, _)
  | Z_list (p, _, _, _)
  | Z_app (p, _, _, _)
  | Z_block (p, _, _)
  | Z_if_cond (p, _, _)
  | Z_if_then (p, _, _)
  | Z_if_else (p, _, _)
  | Z_match_head (p, _, _, _)
  | Z_match_arms_guard (p, _, _, _, _, _, _, _, _)
  | Z_match_arms_body (p, _, _, _, _, _, _, _)
  | Z_assign_left (p, _, _, _, _)
  | Z_assign_right (p, _, _)
  | Z_var_left (p, _, _, _, _, _)
  | Z_var_right (p, _, _, _)
  | Z_var_body (p, _, _, _) ->
      p

module Pretty = struct
  open PPrint
  open Pretty_print_sail

  let prepend c cs = c ^^ hardline ^^ twice space ^^ cs

  let truncate_str n s = if String.length s > n + 3 then String.sub s 0 n ^ "..." else s

  let hole n = string Util.(clear @@ magenta @@ string_of_int n)

  let doc_exp exp = string Util.(clear @@ blue @@ truncate_str 10 (string_of_exp exp))

  let char_of_bit = function
    | Extraction.Bit.Three.B0 -> '0'
    | Extraction.Bit.Three.B1 -> '1'
    | Extraction.Bit.Three.BU -> '?'

  let string_of_bitvector bv =
    let buf = Buffer.create (List.length bv) in
    Buffer.add_string buf "0b";
    let rec go = function
      | [] -> ()
      | b :: bs ->
          Buffer.add_char buf (char_of_bit b);
          go bs
    in
    go (List.rev bv);
    Buffer.contents buf

  let rec string_of_value (v : Lattice.value) =
    match v with
    | V_bot -> "bot"
    | V_top -> "top"
    | V_int intv -> (
        match intv with
        | Empty -> "empty"
        | Ends (Coq_exist (lo, hi)) -> (
            match (lo, hi) with
            | None, None -> "(-inf,inf)"
            | Some lo, None -> Printf.sprintf "[%s,inf)" (Z.to_string lo)
            | None, Some hi -> Printf.sprintf "(-inf,%s]" (Z.to_string hi)
            | Some lo, Some hi ->
                if Z.equal lo hi then Z.to_string lo else Printf.sprintf "[%s,%s]" (Z.to_string lo) (Z.to_string hi)
          )
      )
    | V_bitvector bitv -> (
        match Extraction.AbsBitvector.Dom.to_bv_list bitv with
        | None -> "bvtop"
        | Some bvs -> (
            match bvs with
            | [] -> "bvbot"
            | [bv] -> string_of_bitvector bv
            | _ -> "{" ^ Util.string_of_list "," string_of_bitvector bvs ^ "}"
          )
      )
    | V_unit -> "()"
    | V_string str -> "\"" ^ String.escaped str ^ "\""
    | V_bool b -> if b then "true" else "false"
    | V_tuple values -> Util.string_of_list ", " string_of_value values
    | _ -> "?"

  let doc_residual ?(show_partial = false) (r : Zinterp.R.t) =
    let p_doc = if show_partial then hardline ^^ Pretty_print_sail.doc_exp (Type_check.strip_exp (snd r)) else empty in
    let v = fst r in
    let this_doc =
      match v.this with
      | None -> string Util.(clear @@ green ".")
      | Some v -> string Util.(clear @@ green @@ string_of_value v)
    in
    let exn_doc =
      match v.exn with
      | None -> string Util.(clear @@ red ".")
      | Some v -> string Util.(clear @@ red @@ string_of_value v)
    in
    this_doc ^^ space ^^ exn_doc ^^ space ^^ string Util.(clear @@ yellow @@ string_of_bool v.eff) ^^ p_doc

  let doc_pair c l r =
    match c with
    | Assert -> string "assert" ^^ parens (l ^^ comma ^^ space ^^ r)
    | Vector_append -> separate space [l; char '@'; r]
    | Cons -> separate space [l; string "::"; r]

  let doc_list c docs =
    let l, r =
      match c with List -> (string "[|", string "|]") | Tuple -> (char '(', char ')') | Vector -> (char '[', char ']')
    in
    l ^^ separate (comma ^^ space) docs ^^ r

  let doc_match c head_doc body =
    match c with
    | Try ->
        separate space [string "try"; head_doc; string "catch"]
        ^^ space
        ^^ group (lbrace ^^ break 1 ^^ nest 4 body ^^ break 1 ^^ rbrace)
    | Match | Letbind | Internal_plet ->
        string "match" ^^ space ^^ head_doc ^^ space ^^ group (lbrace ^^ break 1 ^^ nest 4 body ^^ break 1 ^^ rbrace)

  let doc_ite idoc tdoc edoc = separate space [string "if"; idoc; string "then"; tdoc; string "else"; edoc]

  let docs (zexp : Zinterp.t) =
    let s = Stack.create () in
    let rec go n = function
      | Z_top -> ()
      | Z_aux (aux, _) ->
          let child =
            match aux with
            | Z_single (parent, c) -> (
                match c with
                | Field fld -> hole n ^^ dot ^^ doc_id fld
                | Internal_assume nc -> separate space [string "internal_assume"; doc_nc nc; string "in"; hole n]
                | Internal_return -> string "internal_return" ^^ space ^^ hole n
                | Throw -> string "throw" ^^ space ^^ hole n
                | Typ typ -> separate space [hole n; colon; doc_typ typ]
              )
            | Z_return parent -> string "return" ^^ space ^^ hole n
            | Z_exit parent -> string "exit" ^^ space ^^ hole n
            | Z_pair_1 (parent, c, exp) -> doc_pair c (hole n) (doc_exp exp)
            | Z_pair_2 (parent, c, r) -> doc_pair c (doc_residual r) (hole n)
            | Z_list (parent, c, rs, exps) ->
                doc_list c (List.rev_map doc_residual rs @ [hole n] @ List.map doc_exp exps)
            | Z_app (parent, id, rs, exps) ->
                doc_id id
                ^^ parens (separate (comma ^^ space) (List.rev_map doc_residual rs @ [hole n] @ List.map doc_exp exps))
            | Z_block (parent, rs, exps) ->
                group
                  (lbrace
                  ^^ nest 4
                       (break 1
                       ^^ separate (semi ^^ break 1) (List.rev_map doc_residual rs @ [hole n] @ List.map doc_exp exps)
                       )
                  ^^ break 1 ^^ rbrace
                  )
            | Z_if_cond (_, t, e) -> doc_ite (hole n) (doc_exp t) (doc_exp e)
            | Z_if_then (_, (_, i), e) -> doc_ite (doc_residual i) (hole n) (doc_exp e)
            | Z_if_else (_, i, (_, t)) -> doc_ite (doc_residual i) (doc_residual t) (hole n)
            | Z_match_head (_, c, r_arms, arms) -> doc_match c (hole n) (string "...")
            | Z_match_arms_guard (_, c, _, (_, head), r_arms, pat, _, body, arms) ->
                doc_match c (doc_residual head)
                  (concat
                     (List.rev_map
                        (fun (((_, pat), guard_opt), body) ->
                          separate space [doc_pat (Type_check.strip_pat pat); string "=>"; string "..."]
                          ^^ semi ^^ break 1
                        )
                        r_arms
                     )
                  ^^ separate space [doc_pat (Type_check.strip_pat pat); string "if"; hole n; string "=>"; doc_exp body]
                  ^^ semi
                  ^^ match arms with None -> empty | Some _ -> break 1 ^^ string "..."
                  )
            | Z_match_arms_body (_, c, _, (_, head), r_arms, pat, guard_opt, arms) ->
                doc_match c (doc_residual head)
                  (concat
                     (List.rev_map
                        (fun (((_, pat), guard_opt), body) ->
                          separate space [doc_pat (Type_check.strip_pat pat); string "=>"; string "..."]
                          ^^ semi ^^ break 1
                        )
                        r_arms
                     )
                  ^^ separate space [doc_pat (Type_check.strip_pat pat); string "=>"; hole n]
                  ^^ semi
                  ^^ match arms with None -> empty | Some _ -> break 1 ^^ string "..."
                  )
            | Z_assign_left _ | Z_assign_right _ | Z_var_left _ | Z_var_right _ | Z_var_body _ -> string "?"
          in
          Stack.push child s;
          go (n + 1) (zexp_aux_parent aux)
    in
    go 0 zexp;
    List.of_seq @@ Stack.to_seq s
end

type partial_state = {
  ctx : Zinterp.t;
  state : Zinterp.R.state;
  focus : (Tannot.t exp, Zinterp.R.t) Extraction.Datatypes.sum;
}

let partial_state_ctx p = p.ctx

let dest_focus f g = function
  | { focus = Extraction.Datatypes.Coq_inl l; _ } -> f l
  | { focus = Extraction.Datatypes.Coq_inr r; _ } -> g r

let string_of_focus p =
  let open Pretty_print_sail in
  dest_focus (fun exp -> doc_exp (Type_check.strip_exp exp)) (fun r -> Pretty.doc_residual ~show_partial:true r) p
  |> Document.to_string

let from_exp exp = { ctx = Z_top; state = Zinterp.R.empty; focus = Extraction.Datatypes.Coq_inl exp }

let unaux_id = function Id_aux (id, _) -> id

let exp_of_value v = E_aux (E_internal_value v, (Parse_ast.Unknown, Type_check.empty_tannot))

let arms_of_fundef (FD_aux (FD_function (_, _, funcls), annot)) =
  let destruct_pexp = function
    | Pat_aux (Pat_exp (pat, exp), _) -> ((pat, None), exp)
    | Pat_aux (Pat_when (pat, guard, exp), _) -> ((pat, Some guard), exp)
  in
  let pexp_of_funcl (FCL_aux (FCL_funcl (_, pexp), _)) = destruct_pexp pexp in
  (List.map pexp_of_funcl funcls, annot)

let is_finished { ctx; state = _; focus } =
  match (ctx, focus) with Z_top, Extraction.Datatypes.Coq_inr (v, _) -> Some v | _ -> None

let mk_interpreter gstate =
  let open Zinterp.Monad in
  let stack = Stack.create () in

  let step p =
    let rec go = function
      | Pure ((ctx, state), focus) -> (
          match is_finished { ctx; state; focus } with
          | Some v -> (
              match Stack.pop_opt stack with Some cont -> go (cont v) | None -> { ctx; state; focus }
            )
          | None -> { ctx; state; focus }
        )
      | Early_return _ -> failwith "early return"
      | Exit _ -> failwith "exit"
      | Call (id, args, cont) -> (
          match Util.option_all (List.map (fun r -> r.Zinterp.R.this) args) with
          | Some args' ->
              if Type_check.Env.is_outcome id gstate.typecheck_env then
                go (cont { this = Some (Lattice.mk_ctor (unaux_id id) args'); exn = None; eff = false })
              else if Type_check.Env.is_extern id gstate.typecheck_env "interpreter" then (
                let extern = Type_check.Env.get_extern id gstate.typecheck_env "interpreter" in
                match StringMap.find_opt extern gstate.primops with
                | Some op -> go (cont { this = Some (op args'); exn = None; eff = false })
                | None -> failwith "no primop"
              )
              else (
                let arg = if List.length args != 1 then Lattice.V_tuple args' else List.hd args' in
                let arms, annot = arms_of_fundef (Bindings.find id gstate.fundefs) in
                Stack.push cont stack;
                {
                  ctx = Z_aux (Z_match_head (Z_top, Match, [], Some arms), annot);
                  state = Zinterp.R.empty;
                  focus =
                    Extraction.Datatypes.Coq_inr
                      ({ this = Some arg; exn = None; eff = false }, B.mk_id annot (mk_id "funarg#"));
                }
              )
          | None -> failwith "bad call"
        )
      | Get_config (_, cont) -> failwith "get_config"
      | Runtime_type_error l -> raise (Reporting.err_general l "Type error")
      | Get_undefined (_, cont) -> go (cont { this = Some Lattice.V_top; exn = None; eff = false })
    in
    go (Zinterp.step p.ctx p.state p.focus)
  in
  step
