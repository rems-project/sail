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
module Big_int = Nat_big_num
open PPrint

let pipe = string "|"
let arrow = string "->"
let bidir = string "<->"
let dotdot = string ".."
let coloncolon = string "::"
let coloneq = string ":="
let lsquarebar = string "[|"
let rsquarebar = string "|]"
let squarebars = enclose lsquarebar rsquarebar
let lsquarebarbar = string "[||"
let rsquarebarbar = string "||]"
let squarebarbars = enclose lsquarebarbar rsquarebarbar
let lsquarecolon = string "[:"
let rsquarecolon = string ":]"
let squarecolons = enclose lsquarecolon rsquarecolon
let lcomment = string "(*"
let rcomment = string "*)"
let comment = enclose lcomment rcomment
let string_lit = enclose dquote dquote
let spaces op = enclose space space op
let semi_sp = semi ^^ space
let comma_sp = comma ^^ space
let colon_sp = spaces colon

let doc_var (Kid_aux(Var v,_)) = string v
let doc_int i = string (Big_int.to_string i)
let doc_op symb a b = infix 2 1 symb a b
let doc_unop symb a = prefix 2 1 symb a

let doc_id (Id_aux(i,_)) =
  match i with
  | Id i -> string i
  | DeIid x ->
      (* add an extra space through empty to avoid a closing-comment
       * token in case of x ending with star. *)
      parens (separate space [string "deinfix"; string x; empty])

let rec doc_range (BF_aux(r,_)) = match r with
  | BF_single i -> doc_int i
  | BF_range(i1,i2) -> doc_op dotdot (doc_int i1) (doc_int i2)
  | BF_concat(ir1,ir2) -> (doc_range ir1) ^^ comma ^^ (doc_range ir2)

let doc_effect (BE_aux (e,_)) =
  string (match e with
  | BE_rreg -> "rreg"
  | BE_wreg -> "wreg"
  | BE_rmem -> "rmem"
  | BE_rmemt -> "rmemt"
  | BE_wmem -> "wmem"
  | BE_wmv  -> "wmv"
  | BE_wmvt  -> "wmvt"
  (*| BE_lset -> "lset"
  | BE_lret -> "lret"*)
  | BE_eamem -> "eamem"
  | BE_exmem -> "exmem"
  | BE_barr -> "barr"
  | BE_depend -> "depend"
  | BE_escape -> "escape"
  | BE_undef -> "undef"
  | BE_unspec -> "unspec"
  | BE_nondet -> "nondet"
  | BE_config -> "config")

let doc_effects (Effect_aux(e,_)) = match e with
  | Effect_set [] -> string "pure"
  | Effect_set s -> braces (separate_map comma_sp doc_effect s)

let doc_ord (Ord_aux(o,_)) = match o with
  | Ord_var v -> doc_var v
  | Ord_inc -> string "inc"
  | Ord_dec -> string "dec"

let doc_typ, doc_atomic_typ, doc_nexp, doc_nexp_constraint =
  (* following the structure of parser for precedence *)
  let rec typ ty = fn_typ ty
  and fn_typ ((Typ_aux (t, _)) as ty) = match t with
  | Typ_fn(arg,ret,efct) ->
     separate space [tup_typ arg; arrow; fn_typ ret; string "effect"; doc_effects efct]
  | Typ_bidir (t1, t2) ->
     separate space [tup_typ t1; bidir; tup_typ t2]
  | _ -> tup_typ ty
  and tup_typ ((Typ_aux (t, _)) as ty) = match t with
  | Typ_exist (kids, nc, ty) ->
     separate space [string "exist"; separate_map space doc_var kids ^^ comma; nexp_constraint nc ^^ dot; typ ty]
  | Typ_tup typs -> parens (separate_map comma_sp app_typ typs)
  | _ -> app_typ ty
  and app_typ ((Typ_aux (t, _)) as ty) = match t with
  | Typ_app(Id_aux (Id "range", _), [
    Typ_arg_aux(Typ_arg_nexp (Nexp_aux(Nexp_constant n, _)), _);
    Typ_arg_aux(Typ_arg_nexp m, _);]) ->
    (squarebars (if Big_int.equal n Big_int.zero then nexp m else doc_op colon (doc_int n) (nexp m)))
  | Typ_app(Id_aux (Id "atom", _), [Typ_arg_aux(Typ_arg_nexp n,_)]) ->
     (squarecolons (nexp n))
  | Typ_app(id,args) ->
      (* trailing space to avoid >> token in case of nested app types *)
      (doc_id id) ^^ (angles (separate_map comma_sp doc_typ_arg args)) ^^ space
  | _ -> atomic_typ ty (* for simplicity, skip vec_typ - which is only sugar *)
  and atomic_typ ((Typ_aux (t, _)) as ty) = match t with
  | Typ_id id  -> doc_id id
  | Typ_var v  -> doc_var v
  | Typ_app _ | Typ_tup _ | Typ_fn _ | Typ_bidir _ | Typ_exist _ ->
      (* exhaustiveness matters here to avoid infinite loops
       * if we add a new Typ constructor *)
     group (parens (typ ty))
  | Typ_internal_unknown -> string "UNKNOWN"

  and doc_typ_arg (Typ_arg_aux(t,_)) = match t with
  (* Be careful here because typ_arg is implemented as nexp in the
   * parser - in practice falling through app_typ after all the proper nexp
   * cases; so Typ_arg_typ has the same precedence as a Typ_app *)
  | Typ_arg_typ t -> app_typ t
  | Typ_arg_nexp n -> nexp n
  | Typ_arg_order o -> doc_ord o

  (* same trick to handle precedence of nexp *)
  and nexp ne = sum_typ ne
  and sum_typ ((Nexp_aux(n,_)) as ne) = match n with
  | Nexp_sum(n1,n2) -> doc_op plus (sum_typ n1) (star_typ n2)
  | Nexp_minus(n1,n2) -> doc_op minus (sum_typ n1) (star_typ n2)
  | _ -> star_typ ne
  and star_typ ((Nexp_aux(n,_)) as ne) = match n with
  | Nexp_times(n1,n2) -> doc_op star (star_typ n1) (exp_typ n2)
  | _ -> exp_typ ne
  and exp_typ ((Nexp_aux(n,_)) as ne) = match n with
  | Nexp_exp n1 -> doc_unop (string "2**") (atomic_nexp_typ n1)
  | _ -> neg_typ ne
  and neg_typ ((Nexp_aux(n,_)) as ne) = match n with
  | Nexp_neg n1 ->
      (* XXX this is not valid Sail, only an internal representation -
       * work around by commenting it *)
      let minus = concat [string "(*"; minus; string "*)"] in
      minus ^^ (atomic_nexp_typ n1)
  | _ -> atomic_nexp_typ ne
  and atomic_nexp_typ ((Nexp_aux(n,_)) as ne) = match n with
    | Nexp_var v -> doc_var v
    | Nexp_id i  -> braces (doc_id i)
    | Nexp_app (op, args) -> doc_id op ^^ parens (separate_map (comma ^^ space) nexp args)
    | Nexp_constant i -> if Big_int.less i Big_int.zero then parens(doc_int i) else doc_int i
    | Nexp_neg _ | Nexp_exp _ | Nexp_times _ | Nexp_sum _ | Nexp_minus _->
      group (parens (nexp ne))

  and nexp_constraint (NC_aux(nc,_)) = match nc with
    | NC_equal(n1,n2) -> doc_op equals (nexp n1) (nexp n2)
    | NC_not_equal (n1, n2) -> doc_op (string "!=") (nexp n1) (nexp n2)
    | NC_bounded_ge(n1,n2) -> doc_op (string ">=") (nexp n1) (nexp n2)
    | NC_bounded_le(n1,n2) -> doc_op (string "<=") (nexp n1) (nexp n2)
    | NC_set(v,bounds) ->
       doc_op (string "IN") (doc_var v)
              (braces (separate_map comma_sp doc_int bounds))
    | NC_or (nc1, nc2) ->
       parens (separate space [nexp_constraint nc1; string "|"; nexp_constraint nc2])
    | NC_and (nc1, nc2) ->
       separate space [nexp_constraint nc1; string "&"; nexp_constraint nc2]
    | NC_true -> string "true"
    | NC_false -> string "false"

  (* expose doc_typ, doc_atomic_typ, doc_nexp and doc_nexp_constraint *)
  in typ, atomic_typ, nexp, nexp_constraint

let pp_format_id (Id_aux(i,_)) =
  match i with
  | Id(i) -> i
  | DeIid(x) -> "(deinfix " ^ x ^ ")"

let rec list_format (sep : string) (fmt : 'a -> string) (ls : 'a list) : string =
  match ls with
  | [] -> ""
  | [a] -> fmt a
  | a::ls -> (fmt a) ^ sep ^ (list_format sep fmt ls)

let print ?(len=100) channel doc = ToChannel.pretty 1. len channel doc
let to_buf ?(len=100) buf doc = ToBuffer.pretty 1. len buf doc
