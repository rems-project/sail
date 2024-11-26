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
(*    Louis-Emile Ploix                                                     *)
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

(** This file defines an intermediate representation that is roughly
    equivalent to the subset of SystemVerilog that we target. This
    enables us to perform SystemVerilog to SystemVerilog rewrites -
    for this purpose we also define a vistor-pattern rewriter
    [svir_visitor], much like it's [jib_visitor] equivalent. *)

open Libsail

open Jib_visitor
open Smt_exp

type sv_name = SVN_id of Ast.id | SVN_string of string

module SVName : sig
  type t = sv_name
  val compare : sv_name -> sv_name -> int
end

module SVNameMap : sig
  include Map.S with type key = sv_name
end

val modify_sv_name : ?prefix:string -> ?suffix:string -> sv_name -> sv_name

val string_of_sv_name : sv_name -> string

type sv_module_port = { name : Jib.name; external_name : string; typ : Jib.ctyp }

val mk_port : Jib.name -> Jib.ctyp -> sv_module_port

type sv_module = {
  name : sv_name;
  recursive : bool;
  input_ports : sv_module_port list;
  output_ports : sv_module_port list;
  defs : sv_def list;
}

and sv_function = {
  function_name : sv_name;
  return_type : Jib.ctyp option;
  params : (Ast.id * Jib.ctyp) list;
  body : sv_statement;
}

and sv_def = SVD_aux of sv_def_aux * Ast.l

and sv_def_aux =
  | SVD_null
  | SVD_type of Jib.ctype_def
  | SVD_module of sv_module
  | SVD_var of Jib.name * Jib.ctyp
  | SVD_fundef of sv_function
  | SVD_instantiate of {
      module_name : sv_name;
      instance_name : string;
      input_connections : smt_exp list;
      output_connections : sv_place list;
    }
  | SVD_always_comb of sv_statement
  | SVD_initial of sv_statement
  | SVD_always_ff of sv_statement
  | SVD_dpi_function of { function_name : sv_name; return_type : Jib.ctyp option; param_types : Jib.ctyp list }

and sv_place =
  | SVP_id of Jib.name
  | SVP_index of sv_place * smt_exp
  | SVP_field of sv_place * Ast.id
  | SVP_multi of sv_place list
  | SVP_void of Jib.ctyp

and sv_for_modifier = SVF_increment of Jib.name | SVF_decrement of Jib.name

and sv_for = { for_var : Jib.name * Jib.ctyp * smt_exp; for_cond : smt_exp; for_modifier : sv_for_modifier }

and sv_statement = SVS_aux of sv_statement_aux * Ast.l

and sv_statement_aux =
  | SVS_comment of string
  | SVS_skip
  | SVS_split_comb
  | SVS_var of Jib.name * Jib.ctyp * smt_exp option
  | SVS_return of smt_exp
  | SVS_assign of sv_place * smt_exp
  | SVS_continuous_assign of sv_place * smt_exp
  | SVS_call of sv_place * sv_name * smt_exp list
  | SVS_case of { head_exp : smt_exp; cases : (smt_exp * sv_statement) list; fallthrough : sv_statement option }
  | SVS_if of smt_exp * sv_statement option * sv_statement option
  | SVS_block of sv_statement list
  | SVS_assert of smt_exp * smt_exp
  | SVS_foreach of sv_name * smt_exp * sv_statement
  | SVS_for of sv_for * sv_statement
  | SVS_raw of string * Jib.name list * Jib.name list

val svs_raw : ?inputs:Jib.name list -> ?outputs:Jib.name list -> string -> sv_statement_aux

val is_split_comb : sv_statement -> bool

val is_null_def : sv_def -> bool

val is_skip : sv_statement -> bool

val filter_skips : sv_statement list -> sv_statement list

val svs_block : sv_statement list -> sv_statement_aux

val mk_def : ?loc:Parse_ast.l -> sv_def_aux -> sv_def

val mk_statement : ?loc:Parse_ast.l -> sv_statement_aux -> sv_statement

val is_typedef : sv_def -> bool

class type svir_visitor = object
  (** Note that despite inheriting from common_visitor, we don't use
      [vid]. Instead specific types of identifiers should be
      re-written by matching on their containing node. *)
  inherit common_visitor

  method vsmt_exp : smt_exp -> smt_exp visit_action
  method vplace : sv_place -> sv_place visit_action
  method vstatement : sv_statement -> sv_statement visit_action
  method vdef : sv_def -> sv_def visit_action
end

class empty_svir_visitor : svir_visitor

val visit_smt_exp : svir_visitor -> smt_exp -> smt_exp

val visit_sv_place : svir_visitor -> sv_place -> sv_place

val visit_sv_statement : svir_visitor -> sv_statement -> sv_statement

val visit_sv_def : svir_visitor -> sv_def -> sv_def

val visit_sv_defs : svir_visitor -> sv_def list -> sv_def list
