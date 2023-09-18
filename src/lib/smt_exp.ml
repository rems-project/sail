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
  | Array of smt_typ * smt_typ

let mk_enum name elems = Datatype (name, List.map (fun elem -> (elem, [])) elems)

let mk_record name fields = Datatype (name, [(name, fields)])

let mk_variant name ctors = Datatype (name, List.map (fun (ctor, ty) -> (ctor, [("un" ^ ctor, ty)])) ctors)

type smt_array_info = Fixed of int

type smt_exp =
  | Bool_lit of bool
  | Bitvec_lit of Sail2_values.bitU list
  | Real_lit of string
  | String_lit of string
  | Var of Jib.name
  | Enum of string
  | Fn of string * smt_exp list
  | Ite of smt_exp * smt_exp * smt_exp
  | SignExtend of int * int * smt_exp
  | ZeroExtend of int * int * smt_exp
  | Extract of int * int * smt_exp
  | Tester of string * smt_exp
  | Unwrap of Ast.id * bool * smt_exp
  | Field of Ast.id * Ast.id * smt_exp
  | Store of smt_array_info * string * smt_exp * smt_exp * smt_exp
  | Empty_list
  | Hd of string * smt_exp
  | Tl of string * smt_exp

let rec fold_smt_exp f = function
  | Fn (name, args) -> f (Fn (name, List.map (fold_smt_exp f) args))
  | Ite (cond, t, e) -> f (Ite (fold_smt_exp f cond, fold_smt_exp f t, fold_smt_exp f e))
  | SignExtend (len, n, exp) -> f (SignExtend (len, n, fold_smt_exp f exp))
  | ZeroExtend (len, n, exp) -> f (ZeroExtend (len, n, fold_smt_exp f exp))
  | Extract (n, m, exp) -> f (Extract (n, m, fold_smt_exp f exp))
  | Tester (ctor, exp) -> f (Tester (ctor, fold_smt_exp f exp))
  | Unwrap (ctor, b, exp) -> f (Unwrap (ctor, b, fold_smt_exp f exp))
  | Field (struct_id, field_id, exp) -> f (Field (struct_id, field_id, fold_smt_exp f exp))
  | Store (info, store_fn, arr, index, x) ->
      f (Store (info, store_fn, fold_smt_exp f arr, fold_smt_exp f index, fold_smt_exp f x))
  | Hd (hd_op, xs) -> f (Hd (hd_op, fold_smt_exp f xs))
  | Tl (hd_op, xs) -> f (Tl (hd_op, fold_smt_exp f xs))
  | (Bool_lit _ | Bitvec_lit _ | Real_lit _ | String_lit _ | Var _ | Enum _ | Empty_list) as exp -> f exp

let smt_conj = function [] -> Bool_lit true | [x] -> x | xs -> Fn ("and", xs)

let smt_disj = function [] -> Bool_lit false | [x] -> x | xs -> Fn ("or", xs)

let extract i j x = Extract (i, j, x)

let bvnot x = Fn ("bvnot", [x])
let bvand x y = Fn ("bvand", [x; y])
let bvor x y = Fn ("bvor", [x; y])
let bvneg x = Fn ("bvneg", [x])
let bvadd x y = Fn ("bvadd", [x; y])
let bvsub x y = Fn ("bvsub", [x; y])
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

let rec simp exp =
  let open Sail2_operators_bitlists in
  match exp with
  | Fn (f, args) ->
      let args = List.map simp args in
      begin
        match (f, args) with
        | "contents", [Fn ("Bits", [_; bv])] -> bv
        | "len", [Fn ("Bits", [len; _])] -> len
        | "concat", _ ->
            let chunks, bv =
              List.fold_left
                (fun (chunks, current_literal) arg ->
                  match (current_literal, arg) with
                  | Some bv1, Bitvec_lit bv2 -> (chunks, Some (bv1 @ bv2))
                  | None, Bitvec_lit bv -> (chunks, Some bv)
                  | Some bv, exp -> (exp :: Bitvec_lit bv :: chunks, None)
                  | None, exp -> (exp :: chunks, None)
                )
                ([], None) args
            in
            begin
              match (chunks, bv) with
              | [], Some bv -> Bitvec_lit bv
              | chunks, Some bv -> Fn ("concat", List.rev (Bitvec_lit bv :: chunks))
              | chunks, None -> Fn ("concat", List.rev chunks)
            end
        | "bvnot", [Bitvec_lit bv] -> Bitvec_lit (not_vec bv)
        | "bvand", [Bitvec_lit lhs; Bitvec_lit rhs] -> Bitvec_lit (and_vec lhs rhs)
        | "bvor", [Bitvec_lit lhs; Bitvec_lit rhs] -> Bitvec_lit (or_vec lhs rhs)
        | "bvxor", [Bitvec_lit lhs; Bitvec_lit rhs] -> Bitvec_lit (xor_vec lhs rhs)
        | "bvshl", [Bitvec_lit lhs; Bitvec_lit rhs] -> begin
            match sint_maybe rhs with Some shift -> Bitvec_lit (shiftl lhs shift) | None -> Fn (f, args)
          end
        | "bvlshr", [Bitvec_lit lhs; Bitvec_lit rhs] -> begin
            match sint_maybe rhs with Some shift -> Bitvec_lit (shiftr lhs shift) | None -> Fn (f, args)
          end
        | "bvashr", [Bitvec_lit lhs; Bitvec_lit rhs] -> begin
            match sint_maybe rhs with Some shift -> Bitvec_lit (shiftr lhs shift) | None -> Fn (f, args)
          end
        | f, args -> Fn (f, args)
      end
  | ZeroExtend (to_len, from_len, arg) ->
      let arg = simp arg in
      begin
        match arg with
        | Bitvec_lit bv -> Bitvec_lit (zero_extend bv (Big_int.of_int to_len))
        | _ -> ZeroExtend (to_len, from_len, arg)
      end
  | SignExtend (to_len, from_len, arg) ->
      let arg = simp arg in
      begin
        match arg with
        | Bitvec_lit bv -> Bitvec_lit (sign_extend bv (Big_int.of_int to_len))
        | _ -> SignExtend (to_len, from_len, arg)
      end
  | Extract (n, m, arg) -> begin
      match simp arg with
      | Bitvec_lit bv -> Bitvec_lit (subrange_vec_dec bv (Big_int.of_int n) (Big_int.of_int m))
      | exp -> Extract (n, m, exp)
    end
  | Store (info, store_fn, arr, i, x) -> Store (info, store_fn, simp arr, simp i, simp x)
  | exp -> exp

type smt_def =
  | Define_fun of string * (string * smt_typ) list * smt_typ * smt_exp
  | Declare_fun of string * smt_typ list * smt_typ
  | Declare_const of string * smt_typ
  | Define_const of string * smt_typ * smt_exp
  | Declare_datatypes of string * (string * (string * smt_typ) list) list
  | Assert of smt_exp

let declare_datatypes = function Datatype (name, ctors) -> Declare_datatypes (name, ctors) | _ -> assert false
