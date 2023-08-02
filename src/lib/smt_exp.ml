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

open Ast_util

type smt_typ =
  | Bitvec of int
  | Bool
  | String
  | Real
  | Datatype of string * (string * (string * smt_typ) list) list
  | Tuple of smt_typ list
  | Array of smt_typ * smt_typ

type smt_exp =
  | Bool_lit of bool
  | Bitvec_lit of Sail2_values.bitU list
  | Real_lit of string
  | String_lit of string
  | Var of Jib.name
  | Shared of string
  | Read_res of string
  | Enum of string
  | Fn of string * smt_exp list
  | Ctor of string * smt_exp list
  | Ite of smt_exp * smt_exp * smt_exp
  | SignExtend of int * int * smt_exp
  | ZeroExtend of int * int * smt_exp
  | Extract of int * int * smt_exp
  | Tester of string * smt_exp
  | Unwrap of Ast.id * smt_exp
  | Struct of string * (string * smt_exp) list
  | Field of Ast.id * Ast.id * smt_exp

let rec fold_smt_exp f = function
  | Fn (name, args) -> f (Fn (name, List.map (fold_smt_exp f) args))
  | Ctor (name, args) -> f (Ctor (name, List.map (fold_smt_exp f) args))
  | Ite (cond, t, e) -> f (Ite (fold_smt_exp f cond, fold_smt_exp f t, fold_smt_exp f e))
  | SignExtend (len, n, exp) -> f (SignExtend (len, n, fold_smt_exp f exp))
  | ZeroExtend (len, n, exp) -> f (ZeroExtend (len, n, fold_smt_exp f exp))
  | Extract (n, m, exp) -> f (Extract (n, m, fold_smt_exp f exp))
  | Tester (ctor, exp) -> f (Tester (ctor, fold_smt_exp f exp))
  | Unwrap (ctor, exp) -> f (Unwrap (ctor, fold_smt_exp f exp))
  | Field (struct_id, field_id, exp) -> f (Field (struct_id, field_id, fold_smt_exp f exp))
  | Struct (name, fields) -> f (Struct (name, List.map (fun (field, exp) -> (field, fold_smt_exp f exp)) fields))
  | (Bool_lit _ | Bitvec_lit _ | Real_lit _ | String_lit _ | Var _ | Shared _ | Read_res _ | Enum _) as exp -> f exp

let smt_conj = function [] -> Bool_lit true | [x] -> x | xs -> Fn ("and", xs)

let smt_disj = function [] -> Bool_lit false | [x] -> x | xs -> Fn ("or", xs)

let extract i j x = Extract (i, j, x)

let bvnot x = Fn ("bvnot", [x])
let bvand x y = Fn ("bvand", [x; y])
let bvor x y = Fn ("bvor", [x; y])
let bvneg x = Fn ("bvneg", [x])
let bvadd x y = Fn ("bvadd", [x; y])
let bvmul x y = Fn ("bvmul", [x; y])
let bvudiv x y = Fn ("bvudiv", [x; y])
let bvurem x y = Fn ("bvurem", [x; y])
let bvshl x y = Fn ("bvshl", [x; y])
let bvlshr x y = Fn ("bvlshr", [x; y])
let bvult x y = Fn ("bvult", [x; y])

let bvzero n = Bitvec_lit (Sail2_operators_bitlists.zeros (Big_int.of_int n))

let bvones n = Bitvec_lit (Sail2_operators_bitlists.ones (Big_int.of_int n))

let bvone n =
  if n > 0 then Bitvec_lit (Sail2_operators_bitlists.zeros (Big_int.of_int (n - 1)) @ [Sail2_values.B1])
  else Bitvec_lit []
