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

open PPrint
open Util
open Ast
open Ast_util
open Type_check

let bullet f xs =
  group (separate_map hardline (fun x -> string "* " ^^ nest 2 (f x)) xs)

let pp_nexp, pp_n_constraint =
  let rec string_of_nexp = function
    | Nexp_aux (nexp, _) -> string_of_nexp_aux nexp
  and string_of_nexp_aux = function
    | Nexp_id id -> string_of_id id
    | Nexp_var kid -> string_of_kid kid
    | Nexp_constant c -> Big_int.to_string c
    | Nexp_times (n1, n2) -> "(" ^ string_of_nexp n1 ^ " * " ^ string_of_nexp n2 ^ ")"
    | Nexp_sum (n1, n2) -> "(" ^ string_of_nexp n1 ^ " + " ^ string_of_nexp n2 ^ ")"
    | Nexp_minus (n1, n2) -> "(" ^ string_of_nexp n1 ^ " - " ^ string_of_nexp n2 ^ ")"
    | Nexp_app (id, nexps) -> string_of_id id ^ "(" ^ string_of_list ", " string_of_nexp nexps ^ ")"
    | Nexp_exp n -> "2 ^ " ^ string_of_nexp n
    | Nexp_neg n -> "- " ^ string_of_nexp n
  in

  let string_of_n_constraint = function
    | NC_aux (NC_equal (n1, n2), _) -> string_of_nexp n1 ^ " = " ^ string_of_nexp n2
    | NC_aux (NC_not_equal (n1, n2), _) -> string_of_nexp n1 ^ " != " ^ string_of_nexp n2
    | NC_aux (NC_bounded_ge (n1, n2), _) -> string_of_nexp n1 ^ " >= " ^ string_of_nexp n2
    | NC_aux (NC_bounded_le (n1, n2), _) -> string_of_nexp n1 ^ " <= " ^ string_of_nexp n2
    | NC_aux (NC_or (nc1, nc2), _) ->
       "(" ^ string_of_n_constraint nc1 ^ " | " ^ string_of_n_constraint nc2 ^ ")"
    | NC_aux (NC_and (nc1, nc2), _) ->
       "(" ^ string_of_n_constraint nc1 ^ " & " ^ string_of_n_constraint nc2 ^ ")"
    | NC_aux (NC_set (kid, ns), _) ->
       string_of_kid kid ^ " in {" ^ string_of_list ", " Big_int.to_string ns ^ "}"
    | NC_aux (NC_true, _) -> "true"
    | NC_aux (NC_false, _) -> "false"
  in

  let pp_nexp' nexp =
    string (string_of_nexp nexp)
  in

  let pp_n_constraint' nc =
    string (string_of_n_constraint nc)
  in

  pp_nexp', pp_n_constraint'

let rec pp_type_error = function
  | Err_no_casts (exp, typ_from, typ_to, trigger, _) ->
     let coercion =
       group (string "Tried performing type coercion from" ^/^ Pretty_print_sail.doc_typ typ_from
              ^/^ string "to" ^/^ Pretty_print_sail.doc_typ typ_to
              ^/^ string "on" ^/^ Pretty_print_sail.doc_exp exp)
     in
     coercion ^^ hardline ^^ (string "Failed because" ^/^ pp_type_error trigger)

  | Err_no_overloading (id, errs) ->
     string ("No overloadings for " ^ string_of_id id ^ ", tried:") ^//^
       group (separate_map hardline (fun (id, err) -> string (string_of_id id) ^^ colon ^//^ pp_type_error err) errs)

  | Err_subtype (typ1, typ2, constrs, locs) ->
     enclose (string (Util.termcode 1)) (string (Util.termcode 21))
             (separate space [ string (string_of_typ typ1);
                               string "is not a subtype of";
                               string (string_of_typ typ2) ])
     ^/^ string "in context"
     ^/^ bullet pp_n_constraint constrs
     ^/^ string "where"
     ^/^ bullet (fun (kid, l) -> string (string_of_kid kid ^ " bound at " ^ Reporting_basic.loc_to_string l ^ "\n")) (KBindings.bindings locs)

  | Err_no_num_ident id ->
     string "No num identifier" ^^ space ^^ string (string_of_id id)

  | Err_unresolved_quants (id, quants) ->
     string "Could not resolve quantifiers for" ^^ space ^^ string (string_of_id id)
     ^//^ group (separate_map hardline (fun quant -> string (string_of_quant_item quant)) quants)

  | Err_other str -> string str

let rec string_of_type_error err =
  let open PPrint in
  let b = Buffer.create 20 in
  ToBuffer.pretty 1. 400 b (pp_type_error err);
  "\n" ^ Buffer.contents b

let check : 'a. Env.t -> 'a defs -> tannot defs * Env.t =
  fun env defs ->
  try Type_check.check env defs with
  | Type_error (l, err) -> raise (Reporting_basic.err_typ l (string_of_type_error err))
