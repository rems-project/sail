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
open Ast_util

type smt_typ =
  | Bitvec of int
  | Bool
  | String
  | Real
  | Datatype of string * (string * (string * smt_typ) list) list
  | Tuple of smt_typ list
  | Array of smt_typ * smt_typ

let rec smt_typ_compare t1 t2 =
  match (t1, t2) with
  | Bitvec n, Bitvec m -> compare n m
  | Bool, Bool -> 0
  | String, String -> 0
  | Real, Real -> 0
  | Datatype (name1, _), Datatype (name2, _) -> String.compare name1 name2
  | Tuple ts1, Tuple ts2 -> Util.lex_ord_list smt_typ_compare ts1 ts2
  | Array (t11, t12), Array (t21, t22) ->
      let c = smt_typ_compare t11 t21 in
      if c = 0 then smt_typ_compare t12 t22 else c
  | Bitvec _, _ -> 1
  | _, Bitvec _ -> -1
  | Bool, _ -> 1
  | _, Bool -> -1
  | String, _ -> 1
  | _, String -> -1
  | Real, _ -> 1
  | _, Real -> -1
  | Datatype _, _ -> 1
  | _, Datatype _ -> -1
  | Tuple _, _ -> 1
  | _, Tuple _ -> -1

let rec smt_typ_equal t1 t2 =
  match (t1, t2) with
  | Bitvec n, Bitvec m -> n = m
  | Bool, Bool -> true
  | Datatype (name1, ctors1), Datatype (name2, ctors2) ->
      let field_equal (field_name1, typ1) (field_name2, typ2) = field_name1 = field_name2 && smt_typ_equal typ1 typ2 in
      let ctor_equal (ctor_name1, fields1) (ctor_name2, fields2) =
        ctor_name1 = ctor_name2
        && List.length fields1 = List.length fields2
        && List.for_all2 field_equal fields1 fields2
      in
      name1 = name2 && List.length ctors1 = List.length ctors2 && List.for_all2 ctor_equal ctors1 ctors2
  | _, _ -> false

let mk_enum name elems = Datatype (name, List.map (fun elem -> (elem, [])) elems)

let mk_record name fields = Datatype (name, [(name, fields)])

let mk_variant name ctors = Datatype (name, List.map (fun (ctor, ty) -> (ctor, [("un" ^ ctor, ty)])) ctors)

type smt_exp =
  | Bool_lit of bool
  | Bitvec_lit of Sail2_values.bitU list
  | Real_lit of string
  | String_lit of string
  | Var of string
  | Shared of string
  | Read_res of string
  | Enum of string
  | Fn of string * smt_exp list
  | Ctor of string * smt_exp list
  | Ite of smt_exp * smt_exp * smt_exp
  | SignExtend of int * smt_exp
  | Extract of int * int * smt_exp
  | Tester of string * smt_exp
  | Syntactic of smt_exp * smt_exp list
  | Struct of string * (string * smt_exp) list
  | Field of string * smt_exp
  (* Used by sail-axiomatic, should never be generated by sail -smt! *)
  | Forall of (string * smt_typ) list * smt_exp

let rec fold_smt_exp f = function
  | Fn (name, args) -> f (Fn (name, List.map (fold_smt_exp f) args))
  | Ctor (name, args) -> f (Ctor (name, List.map (fold_smt_exp f) args))
  | Ite (cond, t, e) -> f (Ite (fold_smt_exp f cond, fold_smt_exp f t, fold_smt_exp f e))
  | SignExtend (n, exp) -> f (SignExtend (n, fold_smt_exp f exp))
  | Extract (n, m, exp) -> f (Extract (n, m, fold_smt_exp f exp))
  | Tester (ctor, exp) -> f (Tester (ctor, fold_smt_exp f exp))
  | Forall (binders, exp) -> f (Forall (binders, fold_smt_exp f exp))
  | Syntactic (exp, exps) -> f (Syntactic (fold_smt_exp f exp, List.map (fold_smt_exp f) exps))
  | Field (name, exp) -> f (Field (name, fold_smt_exp f exp))
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

let simp_equal x y =
  match (x, y) with Bitvec_lit bv1, Bitvec_lit bv2 -> Some (Sail2_operators_bitlists.eq_vec bv1 bv2) | _, _ -> None

let simp_and xs =
  let xs = List.filter (function Bool_lit true -> false | _ -> true) xs in
  match xs with
  | [] -> Bool_lit true
  | [x] -> x
  | _ -> if List.exists (function Bool_lit false -> true | _ -> false) xs then Bool_lit false else Fn ("and", xs)

let simp_or xs =
  let xs = List.filter (function Bool_lit false -> false | _ -> true) xs in
  match xs with
  | [] -> Bool_lit false
  | [x] -> x
  | _ -> if List.exists (function Bool_lit true -> true | _ -> false) xs then Bool_lit true else Fn ("or", xs)

let rec all_bitvec_lit = function Bitvec_lit _ :: rest -> all_bitvec_lit rest | [] -> true | _ :: _ -> false

let rec merge_bitvec_lit = function
  | Bitvec_lit b :: rest -> b @ merge_bitvec_lit rest
  | [] -> []
  | _ :: _ -> assert false

let simp_fn = function
  | Fn ("not", [Fn ("not", [exp])]) -> exp
  | Fn ("not", [Bool_lit b]) -> Bool_lit (not b)
  | Fn ("contents", [Fn ("Bits", [_; contents])]) -> contents
  | Fn ("len", [Fn ("Bits", [len; _])]) -> len
  | Fn ("or", xs) -> simp_or xs
  | Fn ("and", xs) -> simp_and xs
  | Fn ("=>", [Bool_lit true; y]) -> y
  | Fn ("=>", [Bool_lit false; y]) -> Bool_lit true
  | Fn ("bvsub", [Bitvec_lit bv1; Bitvec_lit bv2]) -> Bitvec_lit (Sail2_operators_bitlists.sub_vec bv1 bv2)
  | Fn ("bvadd", [Bitvec_lit bv1; Bitvec_lit bv2]) -> Bitvec_lit (Sail2_operators_bitlists.add_vec bv1 bv2)
  | Fn ("concat", xs) when all_bitvec_lit xs -> Bitvec_lit (merge_bitvec_lit xs)
  | Fn ("=", [x; y]) as exp -> begin match simp_equal x y with Some b -> Bool_lit b | None -> exp end
  | exp -> exp

let simp_ite = function
  | Ite (cond, Bool_lit true, Bool_lit false) -> cond
  | Ite (cond, Bool_lit x, Bool_lit y) when x = y -> Bool_lit x
  | Ite (_, Var v, Var v') when v = v' -> Var v
  | Ite (Bool_lit true, then_exp, _) -> then_exp
  | Ite (Bool_lit false, _, else_exp) -> else_exp
  | exp -> exp

let rec simp_smt_exp vars kinds = function
  | Var v -> begin match Hashtbl.find_opt vars v with Some exp -> simp_smt_exp vars kinds exp | None -> Var v end
  | (Read_res _ | Shared _ | Enum _ | Bitvec_lit _ | Bool_lit _ | String_lit _ | Real_lit _) as exp -> exp
  | Field (field, exp) ->
      let exp = simp_smt_exp vars kinds exp in
      begin
        match exp with Struct (_, fields) -> List.assoc field fields | _ -> Field (field, exp)
      end
  | Struct (name, fields) -> Struct (name, List.map (fun (field, exp) -> (field, simp_smt_exp vars kinds exp)) fields)
  | Fn (f, exps) ->
      let exps = List.map (simp_smt_exp vars kinds) exps in
      simp_fn (Fn (f, exps))
  | Ctor (f, exps) ->
      let exps = List.map (simp_smt_exp vars kinds) exps in
      simp_fn (Ctor (f, exps))
  | Ite (cond, t, e) ->
      let cond = simp_smt_exp vars kinds cond in
      let t = simp_smt_exp vars kinds t in
      let e = simp_smt_exp vars kinds e in
      simp_ite (Ite (cond, t, e))
  | Extract (i, j, exp) ->
      let exp = simp_smt_exp vars kinds exp in
      begin
        match exp with
        | Bitvec_lit bv ->
            Bitvec_lit (Sail2_operators_bitlists.subrange_vec_dec bv (Big_int.of_int i) (Big_int.of_int j))
        | _ -> Extract (i, j, exp)
      end
  | Tester (str, exp) ->
      let exp = simp_smt_exp vars kinds exp in
      begin
        match exp with
        | Var v -> begin
            match Hashtbl.find_opt kinds v with
            | Some str' when str = str' -> Bool_lit true
            | Some str' -> Bool_lit false
            | None -> Tester (str, exp)
          end
        | _ -> Tester (str, exp)
      end
  | Syntactic (exp, _) -> exp
  | SignExtend (i, exp) ->
      let exp = simp_smt_exp vars kinds exp in
      begin
        match exp with
        | Bitvec_lit bv -> Bitvec_lit (Sail2_operators_bitlists.sign_extend bv (Big_int.of_int (i + List.length bv)))
        | _ -> SignExtend (i, exp)
      end
  | Forall (binders, exp) -> Forall (binders, exp)

type read_info = {
  name : string;
  node : int;
  active : smt_exp;
  kind : smt_exp;
  addr_type : smt_typ;
  addr : smt_exp;
  ret_type : smt_typ;
  doc : string;
}

type write_info = {
  name : string;
  node : int;
  active : smt_exp;
  kind : smt_exp;
  addr_type : smt_typ;
  addr : smt_exp;
  data_type : smt_typ;
  data : smt_exp;
  doc : string;
}

type barrier_info = { name : string; node : int; active : smt_exp; kind : smt_exp; doc : string }

type branch_info = { name : string; node : int; active : smt_exp; addr_type : smt_typ; addr : smt_exp; doc : string }

type cache_op_info = {
  name : string;
  node : int;
  active : smt_exp;
  kind : smt_exp;
  addr_type : smt_typ;
  addr : smt_exp;
  doc : string;
}

type smt_def =
  | Define_fun of string * (string * smt_typ) list * smt_typ * smt_exp
  | Declare_fun of string * smt_typ list * smt_typ
  | Declare_const of string * smt_typ
  | Define_const of string * smt_typ * smt_exp
  (* Same as Define_const, but it'll never be removed by simplification *)
  | Preserve_const of string * smt_typ * smt_exp
  | Write_mem of write_info
  | Write_mem_ea of string * int * smt_exp * smt_exp * smt_exp * smt_typ * smt_exp * smt_typ
  | Read_mem of read_info
  | Barrier of barrier_info
  | Branch_announce of branch_info
  | Cache_maintenance of cache_op_info
  | Excl_res of string * int * smt_exp
  | Declare_datatypes of string * (string * (string * smt_typ) list) list
  | Declare_tuple of int
  | Assert of smt_exp

let smt_def_map_exp f = function
  | Define_fun (name, args, ty, exp) -> Define_fun (name, args, ty, f exp)
  | Declare_fun (name, args, ty) -> Declare_fun (name, args, ty)
  | Declare_const (name, ty) -> Declare_const (name, ty)
  | Define_const (name, ty, exp) -> Define_const (name, ty, f exp)
  | Preserve_const (name, ty, exp) -> Preserve_const (name, ty, f exp)
  | Write_mem w -> Write_mem { w with active = f w.active; kind = f w.kind; addr = f w.addr; data = f w.data }
  | Write_mem_ea (name, node, active, wk, addr, addr_ty, data_size, data_size_ty) ->
      Write_mem_ea (name, node, f active, f wk, f addr, addr_ty, f data_size, data_size_ty)
  | Read_mem r -> Read_mem { r with active = f r.active; kind = f r.kind; addr = f r.addr }
  | Barrier b -> Barrier { b with active = f b.active; kind = f b.kind }
  | Cache_maintenance m -> Cache_maintenance { m with active = f m.active; kind = f m.kind; addr = f m.addr }
  | Branch_announce c -> Branch_announce { c with active = f c.active; addr = f c.addr }
  | Excl_res (name, node, active) -> Excl_res (name, node, f active)
  | Declare_datatypes (name, ctors) -> Declare_datatypes (name, ctors)
  | Declare_tuple n -> Declare_tuple n
  | Assert exp -> Assert (f exp)

let smt_def_iter_exp f = function
  | Define_fun (name, args, ty, exp) -> f exp
  | Define_const (name, ty, exp) -> f exp
  | Preserve_const (name, ty, exp) -> f exp
  | Write_mem w ->
      f w.active;
      f w.kind;
      f w.addr;
      f w.data
  | Write_mem_ea (name, node, active, wk, addr, addr_ty, data_size, data_size_ty) ->
      f active;
      f wk;
      f addr;
      f data_size
  | Read_mem r ->
      f r.active;
      f r.kind;
      f r.addr
  | Barrier b ->
      f b.active;
      f b.kind
  | Cache_maintenance m ->
      f m.active;
      f m.kind;
      f m.addr
  | Branch_announce c ->
      f c.active;
      f c.addr
  | Excl_res (name, node, active) -> f active
  | Assert exp -> f exp
  | Declare_fun _ | Declare_const _ | Declare_tuple _ | Declare_datatypes _ -> ()

let declare_datatypes = function Datatype (name, ctors) -> Declare_datatypes (name, ctors) | _ -> assert false

(** For generating SMT with multiple threads (i.e. for litmus tests),
   we suffix all the variables in the generated SMT with a thread
   identifier to avoid any name clashes between the two threads. *)

let suffix_variables_exp sfx =
  fold_smt_exp (function Var v -> Var (v ^ sfx) | Read_res v -> Read_res (v ^ sfx) | exp -> exp)

let suffix_variables_read_info sfx (r : read_info) =
  let suffix exp = suffix_variables_exp sfx exp in
  { r with name = r.name ^ sfx; active = suffix r.active; kind = suffix r.kind; addr = suffix r.addr }

let suffix_variables_write_info sfx (w : write_info) =
  let suffix exp = suffix_variables_exp sfx exp in
  {
    w with
    name = w.name ^ sfx;
    active = suffix w.active;
    kind = suffix w.kind;
    addr = suffix w.addr;
    data = suffix w.data;
  }

let suffix_variables_barrier_info sfx (b : barrier_info) =
  let suffix exp = suffix_variables_exp sfx exp in
  { b with name = b.name ^ sfx; active = suffix b.active; kind = suffix b.kind }

let suffix_variables_branch_info sfx (c : branch_info) =
  let suffix exp = suffix_variables_exp sfx exp in
  { c with name = c.name ^ sfx; active = suffix c.active; addr = suffix c.addr }

let suffix_variables_cache_op_info sfx (m : cache_op_info) =
  let suffix exp = suffix_variables_exp sfx exp in
  { m with name = m.name ^ sfx; kind = suffix m.kind; active = suffix m.active; addr = suffix m.addr }

let suffix_variables_def sfx = function
  | Define_fun (name, args, ty, exp) ->
      Define_fun (name ^ sfx, List.map (fun (arg, ty) -> (sfx ^ arg, ty)) args, ty, suffix_variables_exp sfx exp)
  | Declare_fun (name, tys, ty) -> Declare_fun (name ^ sfx, tys, ty)
  | Declare_const (name, ty) -> Declare_const (name ^ sfx, ty)
  | Define_const (name, ty, exp) -> Define_const (name ^ sfx, ty, suffix_variables_exp sfx exp)
  | Preserve_const (name, ty, exp) -> Preserve_const (name, ty, suffix_variables_exp sfx exp)
  | Write_mem w -> Write_mem (suffix_variables_write_info sfx w)
  | Write_mem_ea (name, node, active, wk, addr, addr_ty, data_size, data_size_ty) ->
      Write_mem_ea
        ( name ^ sfx,
          node,
          suffix_variables_exp sfx active,
          suffix_variables_exp sfx wk,
          suffix_variables_exp sfx addr,
          addr_ty,
          suffix_variables_exp sfx data_size,
          data_size_ty
        )
  | Read_mem r -> Read_mem (suffix_variables_read_info sfx r)
  | Barrier b -> Barrier (suffix_variables_barrier_info sfx b)
  | Cache_maintenance m -> Cache_maintenance (suffix_variables_cache_op_info sfx m)
  | Branch_announce c -> Branch_announce (suffix_variables_branch_info sfx c)
  | Excl_res (name, node, active) -> Excl_res (name ^ sfx, node, suffix_variables_exp sfx active)
  | Declare_datatypes (name, ctors) -> Declare_datatypes (name, ctors)
  | Declare_tuple n -> Declare_tuple n
  | Assert exp -> Assert (suffix_variables_exp sfx exp)

let pp_sfun str docs =
  let open PPrint in
  parens (separate space (string str :: docs))

let rec pp_smt_typ =
  let open PPrint in
  function
  | Bool -> string "Bool"
  | String -> string "String"
  | Real -> string "Real"
  | Bitvec n -> string (Printf.sprintf "(_ BitVec %d)" n)
  | Datatype (name, _) -> string name
  | Tuple tys -> pp_sfun ("Tup" ^ string_of_int (List.length tys)) (List.map pp_smt_typ tys)
  | Array (ty1, ty2) -> pp_sfun "Array" [pp_smt_typ ty1; pp_smt_typ ty2]

let pp_str_smt_typ (str, ty) =
  let open PPrint in
  parens (string str ^^ space ^^ pp_smt_typ ty)

let rec pp_smt_exp =
  let open PPrint in
  function
  | Bool_lit b -> string (string_of_bool b)
  | Real_lit str -> string str
  | String_lit str -> string ("\"" ^ str ^ "\"")
  | Bitvec_lit bv -> string (Sail2_values.show_bitlist_prefix '#' bv)
  | Var str -> string str
  | Shared str -> string str
  | Read_res str -> string (str ^ "_ret")
  | Enum str -> string str
  | Fn (str, exps) -> parens (string str ^^ space ^^ separate_map space pp_smt_exp exps)
  | Field (str, exp) -> parens (string str ^^ space ^^ pp_smt_exp exp)
  | Struct (str, fields) -> parens (string str ^^ space ^^ separate_map space (fun (_, exp) -> pp_smt_exp exp) fields)
  | Ctor (str, exps) -> parens (string str ^^ space ^^ separate_map space pp_smt_exp exps)
  | Ite (cond, then_exp, else_exp) ->
      parens (separate space [string "ite"; pp_smt_exp cond; pp_smt_exp then_exp; pp_smt_exp else_exp])
  | Extract (i, j, exp) -> parens (string (Printf.sprintf "(_ extract %d %d)" i j) ^^ space ^^ pp_smt_exp exp)
  | Tester (kind, exp) -> parens (string (Printf.sprintf "(_ is %s)" kind) ^^ space ^^ pp_smt_exp exp)
  | SignExtend (i, exp) -> parens (string (Printf.sprintf "(_ sign_extend %d)" i) ^^ space ^^ pp_smt_exp exp)
  | Syntactic (exp, _) -> pp_smt_exp exp
  | Forall (binders, exp) ->
      parens (string "forall" ^^ space ^^ parens (separate_map space pp_str_smt_typ binders) ^^ space ^^ pp_smt_exp exp)

let pp_smt_def =
  let open PPrint in
  let open Printf in
  function
  | Define_fun (name, args, ty, exp) ->
      parens
        (string "define-fun" ^^ space ^^ string name ^^ space
        ^^ parens (separate_map space pp_str_smt_typ args)
        ^^ space ^^ pp_smt_typ ty ^//^ pp_smt_exp exp
        )
  | Declare_fun (name, args, ty) ->
      parens
        (string "declare-fun" ^^ space ^^ string name ^^ space
        ^^ parens (separate_map space pp_smt_typ args)
        ^^ space ^^ pp_smt_typ ty
        )
  | Declare_const (name, ty) -> pp_sfun "declare-const" [string name; pp_smt_typ ty]
  | Define_const (name, ty, exp) | Preserve_const (name, ty, exp) ->
      pp_sfun "define-const" [string name; pp_smt_typ ty; pp_smt_exp exp]
  | Write_mem w ->
      pp_sfun "define-const" [string (w.name ^ "_kind"); string "Zwrite_kind"; pp_smt_exp w.kind]
      ^^ hardline
      ^^ pp_sfun "define-const" [string (w.name ^ "_active"); pp_smt_typ Bool; pp_smt_exp w.active]
      ^^ hardline
      ^^ pp_sfun "define-const" [string (w.name ^ "_data"); pp_smt_typ w.data_type; pp_smt_exp w.data]
      ^^ hardline
      ^^ pp_sfun "define-const" [string (w.name ^ "_addr"); pp_smt_typ w.addr_type; pp_smt_exp w.addr]
      ^^ hardline
      ^^ pp_sfun "declare-const" [string (w.name ^ "_ret"); pp_smt_typ Bool]
  | Write_mem_ea (name, _, active, wk, addr, addr_ty, data_size, data_size_ty) ->
      pp_sfun "define-const" [string (name ^ "_kind"); string "Zwrite_kind"; pp_smt_exp wk]
      ^^ hardline
      ^^ pp_sfun "define-const" [string (name ^ "_active"); pp_smt_typ Bool; pp_smt_exp active]
      ^^ hardline
      ^^ pp_sfun "define-const" [string (name ^ "_size"); pp_smt_typ data_size_ty; pp_smt_exp data_size]
      ^^ hardline
      ^^ pp_sfun "define-const" [string (name ^ "_addr"); pp_smt_typ addr_ty; pp_smt_exp addr]
  | Read_mem r ->
      pp_sfun "define-const" [string (r.name ^ "_kind"); string "Zread_kind"; pp_smt_exp r.kind]
      ^^ hardline
      ^^ pp_sfun "define-const" [string (r.name ^ "_active"); pp_smt_typ Bool; pp_smt_exp r.active]
      ^^ hardline
      ^^ pp_sfun "define-const" [string (r.name ^ "_addr"); pp_smt_typ r.addr_type; pp_smt_exp r.addr]
      ^^ hardline
      ^^ pp_sfun "declare-const" [string (r.name ^ "_ret"); pp_smt_typ r.ret_type]
  | Barrier b ->
      pp_sfun "define-const" [string (b.name ^ "_kind"); string "Zbarrier_kind"; pp_smt_exp b.kind]
      ^^ hardline
      ^^ pp_sfun "define-const" [string (b.name ^ "_active"); pp_smt_typ Bool; pp_smt_exp b.active]
  | Cache_maintenance m ->
      pp_sfun "define-const" [string (m.name ^ "_active"); pp_smt_typ Bool; pp_smt_exp m.active]
      ^^ hardline
      ^^ pp_sfun "define-const" [string (m.name ^ "_kind"); string "Zcache_op_kind"; pp_smt_exp m.kind]
      ^^ hardline
      ^^ pp_sfun "define-const" [string (m.name ^ "_addr"); pp_smt_typ m.addr_type; pp_smt_exp m.addr]
  | Branch_announce c ->
      pp_sfun "define-const" [string (c.name ^ "_active"); pp_smt_typ Bool; pp_smt_exp c.active]
      ^^ hardline
      ^^ pp_sfun "define-const" [string (c.name ^ "_addr"); pp_smt_typ c.addr_type; pp_smt_exp c.addr]
  | Excl_res (name, _, active) ->
      pp_sfun "declare-const" [string (name ^ "_res"); pp_smt_typ Bool]
      ^^ hardline
      ^^ pp_sfun "define-const" [string (name ^ "_active"); pp_smt_typ Bool; pp_smt_exp active]
  | Declare_datatypes (name, ctors) ->
      let pp_ctor (ctor_name, fields) =
        match fields with [] -> parens (string ctor_name) | _ -> pp_sfun ctor_name (List.map pp_str_smt_typ fields)
      in
      pp_sfun "declare-datatypes"
        [Printf.ksprintf string "((%s 0))" name; parens (parens (separate_map space pp_ctor ctors))]
  | Declare_tuple n ->
      let par = separate_map space string (Util.list_init n (fun i -> "T" ^ string_of_int i)) in
      let fields = separate space (Util.list_init n (fun i -> Printf.ksprintf string "(tup_%d_%d T%d)" n i i)) in
      pp_sfun "declare-datatypes"
        [
          Printf.ksprintf string "((Tup%d %d))" n n;
          parens
            (parens
               (separate space
                  [string "par"; parens par; parens (parens (ksprintf string "tup%d" n ^^ space ^^ fields))]
               )
            );
        ]
  | Assert exp -> pp_sfun "assert" [pp_smt_exp exp]

let string_of_smt_def def = Pretty_print_sail.to_string (pp_smt_def def)

let output_smt_defs out_chan smt = List.iter (fun def -> output_string out_chan (string_of_smt_def def ^ "\n")) smt

(**************************************************************************)
(* 2. Parser for SMT solver output                                        *)
(**************************************************************************)

(* Output format from each SMT solver does not seem to be completely
   standardised, unlike the SMTLIB input format, but usually is some
   form of s-expression based representation. Therefore we define a
   simple parser for s-expressions using monadic parser combinators. *)

type sexpr = List of sexpr list | Atom of string

let rec string_of_sexpr = function
  | List sexprs -> "(" ^ Util.string_of_list " " string_of_sexpr sexprs ^ ")"
  | Atom str -> str

open Parser_combinators

let lparen = token (function Str.Delim "(" -> Some () | _ -> None)
let rparen = token (function Str.Delim ")" -> Some () | _ -> None)
let atom = token (function Str.Text str -> Some str | _ -> None)

let rec sexp toks =
  let parse =
    pchoose
      (atom >>= fun str -> preturn (Atom str))
      ( lparen >>= fun _ ->
        plist sexp >>= fun xs ->
        rparen >>= fun _ -> preturn (List xs)
      )
  in
  parse toks

let parse_sexps input =
  let delim = Str.regexp "[ \n\t]+\\|(\\|)" in
  let tokens = Str.full_split delim input in
  let non_whitespace = function Str.Delim d when String.trim d = "" -> false | _ -> true in
  let tokens = List.filter non_whitespace tokens in
  match plist sexp tokens with Ok (result, _) -> result | Fail -> failwith "Parse failure"

let value_of_sexpr sexpr =
  let open Jib in
  let open Value in
  function
  | CT_fbits n -> begin
      match sexpr with
      | List [Atom "_"; Atom v; Atom m] when int_of_string m = n && String.length v > 2 && String.sub v 0 2 = "bv" ->
          let v = String.sub v 2 (String.length v - 2) in
          mk_vector (Sail_lib.get_slice_int' (n, Big_int.of_string v, 0))
      | Atom v when String.length v > 2 && String.sub v 0 2 = "#b" ->
          let v = String.sub v 2 (String.length v - 2) in
          mk_vector (Sail_lib.get_slice_int' (n, Big_int.of_string ("0b" ^ v), 0))
      | Atom v when String.length v > 2 && String.sub v 0 2 = "#x" ->
          let v = String.sub v 2 (String.length v - 2) in
          mk_vector (Sail_lib.get_slice_int' (n, Big_int.of_string ("0x" ^ v), 0))
      | _ -> failwith ("Cannot parse sexpr as ctyp: " ^ string_of_sexpr sexpr)
    end
  | cty -> failwith ("Unsupported type in sexpr: " ^ Jib_util.string_of_ctyp cty)

let rec find_arg id ctyp arg_smt_names = function
  | List [Atom "define-fun"; Atom str; List []; _; value] :: _
    when Util.assoc_compare_opt Id.compare id arg_smt_names = Some (Some str) ->
      (id, value_of_sexpr value ctyp)
  | _ :: sexps -> find_arg id ctyp arg_smt_names sexps
  | [] -> (id, V_unit)

let build_counterexample args arg_ctyps arg_smt_names model =
  List.map2 (fun id ctyp -> find_arg id ctyp arg_smt_names model) args arg_ctyps

let rec run frame =
  match frame with
  | Interpreter.Done (state, v) -> Some v
  | Interpreter.Step (lazy_str, _, _, _) -> run (Interpreter.eval_frame frame)
  | Interpreter.Break frame -> run (Interpreter.eval_frame frame)
  | Interpreter.Fail (_, _, _, _, msg) -> None
  | Interpreter.Effect_request (out, state, stack, eff) -> run (Interpreter.default_effect_interp state eff)

let check_counterexample ast env fname function_id args arg_ctyps arg_smt_names =
  let open Printf in
  prerr_endline ("Checking counterexample: " ^ fname);
  let in_chan = ksprintf Unix.open_process_in "cvc4 --lang=smt2.6 %s" fname in
  let lines = ref [] in
  begin
    try
      while true do
        lines := input_line in_chan :: !lines
      done
    with End_of_file -> ()
  end;
  let solver_output = List.rev !lines |> String.concat "\n" |> parse_sexps in
  begin
    match solver_output with
    | Atom "sat" :: List (Atom "model" :: model) :: _ ->
        let open Value in
        let open Interpreter in
        prerr_endline (sprintf "Solver found counterexample: %s" Util.("ok" |> green |> clear));
        let counterexample = build_counterexample args arg_ctyps arg_smt_names model in
        List.iter (fun (id, v) -> prerr_endline ("  " ^ string_of_id id ^ " -> " ^ string_of_value v)) counterexample;
        let istate = initial_state ast env !primops in
        let annot = (Parse_ast.Unknown, Type_check.mk_tannot env bool_typ) in
        let call =
          E_aux
            ( E_app
                ( function_id,
                  List.map
                    (fun (_, v) -> E_aux (E_internal_value v, (Parse_ast.Unknown, Type_check.empty_tannot)))
                    counterexample
                ),
              annot
            )
        in
        let result = run (Step (lazy "", istate, return call, [])) in
        begin
          match result with
          | Some (V_bool false) | None ->
              ksprintf prerr_endline "Replaying counterexample: %s" Util.("ok" |> green |> clear)
          | _ -> ()
        end
    | _ -> prerr_endline "Solver could not find counterexample"
  end;
  let status = Unix.close_process_in in_chan in
  ()
