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

open Type_internal
open Ast
open Pretty_print_common
open Big_int

(* **************************************************************************
 * pp from tannot to ASCII source, for pp of built-in type environment
 *)

let rec pp_format_t_ascii t =
  match t.t with
    | Tid i -> i
    | Tvar i -> "'" ^ i
    | Tfn(t1,t2,_,e) -> (pp_format_t_ascii t1) ^ " -> " ^ (pp_format_t_ascii t2) ^ (match e.effect with Eset [] -> "" | _ -> " effect " ^ pp_format_e_ascii e)
    | Ttup(tups) -> "(" ^ (list_format ", " pp_format_t_ascii tups) ^ ")"
    | Tapp(i,args) ->  i ^ "<" ^  list_format ", " pp_format_targ_ascii args ^ ">"
    | Tabbrev(ti,ta) -> (pp_format_t_ascii ti) (* (pp_format_t_ascii ta) *)
    | Tuvar(_) -> failwith "Tuvar in pp_format_t_ascii"
    | Toptions _ -> failwith "Toptions in pp_format_t_ascii"
and pp_format_targ_ascii = function
  | TA_typ t ->  pp_format_t_ascii t
  | TA_nexp n -> pp_format_n_ascii n
  | TA_eft e ->  pp_format_e_ascii e
  | TA_ord o ->  pp_format_o_ascii o
and pp_format_n_ascii n =
  match n.nexp with
  | Nid (i, n) -> i (* from an abbreviation *)
  | Nvar i -> "'" ^ i
  | Nconst i -> (string_of_int (int_of_big_int i))
  | Npos_inf -> "infinity"
  | Nadd(n1,n2) -> (pp_format_n_ascii n1) ^ "+" ^ (pp_format_n_ascii n2)
  | Nsub(n1,n2) -> (pp_format_n_ascii n1) ^ "-" ^ (pp_format_n_ascii n2)
  | Nmult(n1,n2) -> (pp_format_n_ascii n1) ^ "*" ^ (pp_format_n_ascii n2)
  | N2n(n,_) -> "2**"^(pp_format_n_ascii n) (* string_of_big_int i ^ *)
  | Nneg n -> "-" ^ (pp_format_n_ascii n) 
  | Nuvar _ -> failwith "Nuvar in pp_format_n_ascii"
  | Nneg_inf -> "-infinity"
  | Npow _ -> failwith "Npow in pp_format_n_ascii"
  | Ninexact -> failwith "Ninexact in pp_format_n_ascii"
and pp_format_e_ascii e =
  match e.effect with
  | Evar i -> "'" ^ i
  | Eset es -> "{" ^
                  (list_format ", " pp_format_base_effect_ascii es) ^ "}"
  | Euvar(_) -> failwith "Euvar in pp_format_e_ascii"
and pp_format_o_ascii o =
  match o.order with
  | Ovar i -> "'" ^ i
  | Oinc -> "inc"
  | Odec -> "dec"
  | Ouvar(_) -> failwith "Ouvar in pp_format_o_ascii"
and pp_format_base_effect_ascii (BE_aux(e,l)) =
  match e with
    | BE_rreg -> "rreg"
    | BE_wreg -> "wreg"
    | BE_rmem -> "rmem"
    | BE_wmem -> "wmem"
    | BE_wmv  -> "wmv"
    | BE_eamem -> "eamem"
    | BE_barr -> "barr"
    | BE_depend -> "depend"
    | BE_undef -> "undef"
    | BE_unspec -> "unspec"
    | BE_nondet -> "nondet"
    | BE_lset -> "lset"
    | BE_lret -> "lret"
    | BE_escape -> "escape"

and pp_format_nes_ascii nes =
  list_format ", " pp_format_ne_ascii nes

and pp_format_ne_ascii ne =
  match ne with
  | Lt(_,_,n1,n2) -> pp_format_n_ascii n1 ^ " < " ^ pp_format_n_ascii n2
  | LtEq(_,_,n1,n2) -> pp_format_n_ascii n1 ^ " <= " ^ pp_format_n_ascii n2
  | NtEq(_,n1,n2) ->   pp_format_n_ascii n1 ^ " != " ^ pp_format_n_ascii n2
  | Eq(_,n1,n2) ->   pp_format_n_ascii n1 ^ " = " ^ pp_format_n_ascii n2
  | GtEq(_,_,n1,n2) -> pp_format_n_ascii n1 ^ " >= " ^ pp_format_n_ascii n2
  | Gt(_,_,n1,n2) -> pp_format_n_ascii n1 ^ " > " ^ pp_format_n_ascii n2
  | In(_,i,ns) | InS(_,{nexp=Nvar i},ns) ->
  i ^ " IN {" ^ (list_format ", " string_of_int ns)^ "}"
  | InS(_,_,ns)  -> (* when the variable has been replaced by a unification variable, we use this *)
  failwith "InS in pp_format_nes_ascii" (*"(Nec_in \"fresh\" [" ^ (list_format "; " string_of_int ns)^ "])"*)
  | Predicate(_,n1,n2) -> "flow_constraints(" ^ pp_format_ne_ascii n1 ^", "^ pp_format_ne_ascii n2 ^")"
  | CondCons(_,_,_,nes_c,nes_t) ->
  failwith "CondCons in pp_format_nes_ascii" (*"(Nec_cond " ^ (pp_format_nes nes_c) ^ " " ^ (pp_format_nes nes_t) ^ ")"*)
  | BranchCons(_,_,nes_b) ->
  failwith "BranchCons in pp_format_nes_ascii" (*"(Nec_branch " ^ (pp_format_nes nes_b) ^ ")"*)

let rec pp_format_annot_ascii = function
  | NoTyp -> "Nothing"
  | Base((targs,t),tag,nes,efct,efctsum,_) ->
    (*TODO print out bindings for use in pattern match in interpreter*)
      (match tag with External (Some s) -> "("^s^") " | _ -> "") ^
      (match (targs,nes) with ([],[]) -> "\n" | _ -> 
        "forall " ^ list_format ", " (function (i,k) -> kind_to_string k ^" '"^ i) targs ^ 
        (match nes with [] -> "" | _ -> ", " ^ pp_format_nes_ascii nes)
        ^ ".\n") ^ "     "
      ^ pp_format_t_ascii t 
      ^ "\n"
(*
^ " ********** " ^ pp_format_tag tag ^ ", " ^ pp_format_nes nes ^ ", " ^
       pp_format_e_lem efct ^ ", " ^ pp_format_e_lem efctsum ^ "))"
*)
  | Overload (tannot, return_type_overloading_allowed, tannots) -> 
  (*pp_format_annot_ascii tannot*) "\n" ^ String.concat "" (List.map (function tannot' -> "   " ^ pp_format_annot_ascii tannot' ) tannots)

