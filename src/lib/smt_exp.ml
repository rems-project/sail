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
open Jib_util

module IntSet = Util.IntSet

let zencode_id id = Util.zencode_string (string_of_id id)
let zencode_upper_id id = Util.zencode_upper_string (string_of_id id)
let zencode_name id = Jib_util.string_of_name ~deref_current_exception:false ~zencode:true id

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

type smt_array_info = Fixed of int * Jib.ctyp

type smt_exp =
  | Bool_lit of bool
  | Bitvec_lit of Sail2_values.bitU list
  | Real_lit of string
  | String_lit of string
  | Var of Jib.name
  | Unit
  | Member of Ast.id
  | Fn of string * smt_exp list
  | Ite of smt_exp * smt_exp * smt_exp
  | SignExtend of int * int * smt_exp
  | ZeroExtend of int * int * smt_exp
  | Extract of int * int * smt_exp
  | Tester of string * smt_exp
  | Unwrap of Ast.id * bool * smt_exp
  | Field of Ast.id * Ast.id * smt_exp
  | Struct of Ast.id * (Ast.id * smt_exp) list
  | Store of smt_array_info * string * smt_exp * smt_exp * smt_exp
  | Empty_list
  | Hd of string * smt_exp
  | Tl of string * smt_exp

let rec pp_smt_exp =
  let open PPrint in
  function
  | Bool_lit b -> string (string_of_bool b)
  | Real_lit str -> string str
  | String_lit str -> string ("\"" ^ str ^ "\"")
  | Bitvec_lit bv -> string (Sail2_values.show_bitlist_prefix '#' bv)
  | Var id -> string (zencode_name id)
  | Member id -> string (zencode_id id)
  | Unit -> string "unit"
  | Fn (str, exps) -> parens (string str ^^ space ^^ separate_map space pp_smt_exp exps)
  | Field (struct_id, field_id, exp) ->
      parens (string (zencode_upper_id struct_id ^ "_" ^ zencode_id field_id) ^^ space ^^ pp_smt_exp exp)
  | Struct (struct_id, fields) ->
      parens (string (zencode_upper_id struct_id) ^^ space ^^ separate_map space (fun (_, exp) -> pp_smt_exp exp) fields)
  | Unwrap (ctor, _, exp) -> parens (string ("un" ^ zencode_id ctor) ^^ space ^^ pp_smt_exp exp)
  | Ite (cond, then_exp, else_exp) ->
      parens (separate space [string "ite"; pp_smt_exp cond; pp_smt_exp then_exp; pp_smt_exp else_exp])
  | Extract (i, j, exp) -> parens (string (Printf.sprintf "(_ extract %d %d)" i j) ^^ space ^^ pp_smt_exp exp)
  | Tester (kind, exp) -> parens (string (Printf.sprintf "(_ is %s)" kind) ^^ space ^^ pp_smt_exp exp)
  | SignExtend (_, i, exp) -> parens (string (Printf.sprintf "(_ sign_extend %d)" i) ^^ space ^^ pp_smt_exp exp)
  | ZeroExtend (_, i, exp) -> parens (string (Printf.sprintf "(_ zero_extend %d)" i) ^^ space ^^ pp_smt_exp exp)
  | Store (_, _, arr, index, x) -> parens (string "store" ^^ space ^^ separate_map space pp_smt_exp [arr; index; x])
  | Hd (op, exp) | Tl (op, exp) -> parens (string op ^^ space ^^ pp_smt_exp exp)
  | Empty_list -> string "empty_list"

let var_id id = Var (Name (id, -1))

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
  | Tl (tl_op, xs) -> f (Tl (tl_op, fold_smt_exp f xs))
  | Struct (struct_id, fields) ->
      f (Struct (struct_id, List.map (fun (field_id, exp) -> (field_id, fold_smt_exp f exp)) fields))
  | (Bool_lit _ | Bitvec_lit _ | Real_lit _ | String_lit _ | Var _ | Unit | Member _ | Empty_list) as exp -> f exp

let rec iter_smt_exp f exp =
  f exp;
  match exp with
  | Fn (_, args) -> List.iter (iter_smt_exp f) args
  | Ite (i, t, e) ->
      iter_smt_exp f i;
      iter_smt_exp f t;
      iter_smt_exp f e
  | SignExtend (_, _, exp)
  | ZeroExtend (_, _, exp)
  | Extract (_, _, exp)
  | Tester (_, exp)
  | Unwrap (_, _, exp)
  | Hd (_, exp)
  | Tl (_, exp)
  | Field (_, _, exp) ->
      iter_smt_exp f exp
  | Store (_, _, arr, index, exp) ->
      iter_smt_exp f arr;
      iter_smt_exp f index;
      iter_smt_exp f exp
  | Struct (_, fields) -> List.iter (fun (_, field) -> iter_smt_exp f field) fields
  | Bool_lit _ | Bitvec_lit _ | Real_lit _ | String_lit _ | Var _ | Unit | Member _ | Empty_list -> ()

let rec smt_exp_size = function
  | Fn (_, args) -> 1 + List.fold_left (fun n arg -> n + smt_exp_size arg) 0 args
  | Ite (i, t, e) -> 1 + smt_exp_size i + smt_exp_size t + smt_exp_size e
  | SignExtend (_, _, exp)
  | ZeroExtend (_, _, exp)
  | Extract (_, _, exp)
  | Tester (_, exp)
  | Unwrap (_, _, exp)
  | Hd (_, exp)
  | Tl (_, exp)
  | Field (_, _, exp) ->
      1 + smt_exp_size exp
  | Store (_, _, arr, index, exp) -> 1 + smt_exp_size arr + smt_exp_size index + smt_exp_size exp
  | Struct (_, fields) -> 1 + List.fold_left (fun n (_, field) -> n + smt_exp_size field) 0 fields
  | Bool_lit _ | Bitvec_lit _ | Real_lit _ | String_lit _ | Var _ | Unit | Member _ | Empty_list -> 1

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

let bvone' n = if n > 0 then Sail2_operators_bitlists.zeros (Big_int.of_int (n - 1)) @ [Sail2_values.B1] else []

let bvone n = Bitvec_lit (bvone' n)

let bv_is_zero = List.for_all (function Sail2_values.B0 -> true | _ -> false)

let smt_conj = function [] -> Bool_lit true | [x] -> x | xs -> Fn ("and", xs)

let smt_disj = function [] -> Bool_lit false | [x] -> x | xs -> Fn ("or", xs)

let is_literal = function Member _ | Bool_lit _ | Bitvec_lit _ | String_lit _ | Unit -> true | _ -> false

module SimpSet = struct
  module SimpVar = struct
    type t = Var of Jib.name | Field of Ast.id * Ast.id * t

    let rec compare v1 v2 =
      match (v1, v2) with
      | Var n1, Var n2 -> Name.compare n1 n2
      | Field (struct_id1, field1, v1), Field (struct_id2, field2, v2) ->
          let c1 = Id.compare struct_id1 struct_id2 in
          if c1 = 0 then (
            let c2 = Id.compare field1 field2 in
            if c2 = 0 then compare v1 v2 else c2
          )
          else c1
      | Var _, Field _ -> -1
      | Field _, Var _ -> 1
  end

  let rec is_simp_var = function Var _ -> true | Field (_, _, exp) -> is_simp_var exp | _ -> false

  let rec to_simp_var = function
    | Var v -> Some (SimpVar.Var v)
    | Field (struct_id, field, exp) -> Option.map (fun v -> SimpVar.Field (struct_id, field, v)) (to_simp_var exp)
    | _ -> None

  module SimpVarMap = Map.Make (SimpVar)
  module SimpVarSet = Set.Make (SimpVar)

  type t = {
    var_fn : Jib.name -> smt_exp option;
    vars : smt_exp SimpVarMap.t;
    inequalities : smt_exp list SimpVarMap.t;
    is_ctor : string NameMap.t;
  }

  let empty =
    { var_fn = (fun _ -> None); vars = SimpVarMap.empty; inequalities = SimpVarMap.empty; is_ctor = NameMap.empty }

  let from_function f = { empty with var_fn = f }

  let add_var v exp simpset =
    match to_simp_var v with None -> simpset | Some v -> { simpset with vars = SimpVarMap.add v exp simpset.vars }

  let add_var_inequality v exp simpset =
    match to_simp_var v with
    | None -> simpset
    | Some v ->
        {
          simpset with
          inequalities =
            SimpVarMap.update v (function None -> Some [exp] | Some exps -> Some (exp :: exps)) simpset.inequalities;
        }

  let add_var_is_ctor v ctor simpset = { simpset with is_ctor = NameMap.add v ctor simpset.is_ctor }

  let is_ctor v ctor simpset =
    match NameMap.find_opt v simpset.is_ctor with Some ctor' -> Some (ctor = ctor') | None -> None

  let find_opt v simpset =
    match to_simp_var v with
    | Some (SimpVar.Var v) -> begin
        match SimpVarMap.find_opt (SimpVar.Var v) simpset.vars with Some exp -> Some exp | None -> simpset.var_fn v
      end
    | Some v -> SimpVarMap.find_opt v simpset.vars
    | None -> None

  let inequalities v simpset =
    match to_simp_var v with
    | None -> []
    | Some v -> Option.value ~default:[] (SimpVarMap.find_opt v simpset.inequalities)
end

let and_prefer = function
  | Var _ -> Some 0
  | Tester (_, Var _) -> Some 1
  | Fn ("=", [lit; Var _]) when is_literal lit -> Some 1
  | Fn ("=", [Var _; lit]) when is_literal lit -> Some 1
  | Fn ("not", [Fn ("=", [Var _; lit])]) when is_literal lit -> Some 2
  | _ -> None

let and_order x y =
  match (and_prefer x, and_prefer y) with
  | Some a, Some b -> a - b
  | Some _, None -> -1
  | None, Some _ -> 1
  | None, None -> 0

let or_prefer = function Var _ -> Some 0 | _ -> None

let or_order x y =
  match (or_prefer x, or_prefer y) with
  | Some a, Some b -> a - b
  | Some _, None -> -1
  | None, Some _ -> 1
  | None, None -> 0

let rec identical x y =
  match (x, y) with
  | Var x, Var y -> Name.compare x y = 0
  | Fn (f1, args1), Fn (f2, args2) ->
      String.compare f1 f2 = 0 && List.compare_lengths args1 args2 = 0 && List.for_all2 identical args1 args2
  | Tester (sx, x), Tester (sy, y) -> String.compare sx sy = 0 && identical x y
  | Ite (ix, tx, ex), Ite (iy, ty, ey) -> identical ix iy && identical tx ty && identical ex ey
  | _ -> false

let simp_eq x y =
  match (x, y) with
  | Bool_lit x, Bool_lit y -> Some (x = y)
  | Bitvec_lit x, Bitvec_lit y -> Some (x = y)
  | Var x, Var y when Jib_util.Name.compare x y = 0 -> Some true
  | Member x, Member y -> Some (Id.compare x y = 0)
  | Unit, Unit -> Some true
  | _ -> None

module Simplifier = struct
  type rule = NoChange | Change of int * smt_exp | Reconstruct of int * SimpSet.t * smt_exp * (smt_exp -> smt_exp)

  let change exp = Change (1, exp)

  type strategy = Skip | Rule of string * (SimpSet.t -> smt_exp -> rule) | Repeat of strategy | Then of strategy list

  let mk_simple_rule loc f = Rule (loc, fun _ -> f)
  let mk_rule loc f = Rule (loc, f)

  let rec run_strategy simpset exp = function
    | Skip -> NoChange
    | Rule (name, f) -> f simpset exp
    | Repeat strategy ->
        let exp = ref exp in
        let simpset = ref simpset in
        let changes = ref 0 in
        let changed = ref false in
        let continue = ref true in
        let reconstructor = ref None in
        while !continue do
          match run_strategy !simpset !exp strategy with
          | Change (n, exp') ->
              changed := true;
              changes := !changes + n;
              exp := exp'
          | Reconstruct (n, simpset', exp', f) ->
              changed := true;
              changes := !changes + n;
              (reconstructor :=
                 let g = !reconstructor in
                 Some (fun exp -> Option.value ~default:(fun e -> e) g (f exp))
              );
              simpset := simpset';
              exp := exp'
          | NoChange -> continue := false
        done;
        if !changed then (
          match !reconstructor with
          | Some f -> Reconstruct (!changes, !simpset, !exp, f)
          | None -> Change (!changes, !exp)
        )
        else NoChange
    | Then strategies ->
        let exp = ref exp in
        let simpset = ref simpset in
        let changes = ref 0 in
        let changed = ref false in
        let reconstructor = ref None in
        List.iter
          (fun strategy ->
            match run_strategy !simpset !exp strategy with
            | Change (n, exp') ->
                changed := true;
                changes := !changes + n;
                exp := exp'
            | Reconstruct (n, simpset', exp', f) ->
                changed := true;
                changes := !changes + n;
                (reconstructor :=
                   let g = !reconstructor in
                   Some (fun exp -> Option.value ~default:(fun e -> e) g (f exp))
                );
                simpset := simpset';
                exp := exp'
            | NoChange -> ()
          )
          strategies;
        if !changed then (
          match !reconstructor with
          | Some f -> Reconstruct (!changes, !simpset, !exp, f)
          | None -> Change (!changes, !exp)
        )
        else NoChange

  let append_to_or or_cond cond =
    match or_cond with Fn ("or", conds) -> Fn ("or", conds @ [cond]) | _ -> Fn ("or", [or_cond; cond])

  let append_to_and and_cond cond =
    match and_cond with Fn ("and", conds) -> Fn ("and", conds @ [cond]) | _ -> Fn ("and", [and_cond; cond])

  let rule_squash_ite =
    mk_simple_rule __LOC__ @@ function
    | Ite (cond, x, Ite (cond', y, z)) when identical x z -> change (Ite (Fn ("and", [cond'; Fn ("not", [cond])]), y, x))
    | Ite (cond, x, Ite (cond', y, z)) when identical x y -> change (Ite (append_to_or cond cond', x, z))
    | Ite (cond, Ite (cond', x, y), z) when identical x z -> change (Ite (Fn ("or", [Fn ("not", [cond]); cond']), x, y))
    | Ite (cond, Ite (cond', x, y), z) when identical y z -> change (Ite (append_to_and cond cond', x, z))
    | _ -> NoChange

  let rule_chain_right_ite =
    mk_simple_rule __LOC__ @@ function
    | Ite (cond, Ite (cond', x, y), z) ->
        change (Ite (Fn ("and", [cond; cond']), x, Ite (Fn ("and", [cond; Fn ("not", [cond'])]), y, z)))
    | _ -> NoChange

  let rule_same_ite =
    mk_simple_rule __LOC__ @@ function
    | Ite (cond, x, y) -> (
        match simp_eq x y with Some true -> change x | _ -> NoChange
      )
    | _ -> NoChange

  let rule_ite_literal =
    mk_simple_rule __LOC__ @@ function Ite (Bool_lit b, x, y) -> change (if b then x else y) | _ -> NoChange

  let rec remove_duplicates = function
    | x :: xs ->
        let xs' = List.filter (fun x' -> not (identical x x')) xs in
        x :: remove_duplicates xs'
    | [] -> []

  let rule_and_duplicates =
    mk_simple_rule __LOC__ @@ function Fn ("and", xs) -> Change (0, Fn ("and", remove_duplicates xs)) | _ -> NoChange

  let rule_or_duplicates =
    mk_simple_rule __LOC__ @@ function Fn ("or", xs) -> Change (0, Fn ("or", remove_duplicates xs)) | _ -> NoChange

  let rule_and_inequalities =
    mk_simple_rule __LOC__ @@ function
    | Fn ("and", xs) ->
        let open Util.Option_monad in
        let open Sail2_operators_bitlists in
        let inequalities, others =
          List.fold_left
            (fun (inequalities, others) x ->
              match inequalities with
              | Some (var, size, lits) -> begin
                  match x with
                  | Fn ("not", [Fn ("=", [Var var'; Bitvec_lit bv])])
                    when Name.compare var var' = 0 && List.length bv = size ->
                      (Some (var, size, bv :: lits), others)
                  | _ -> (inequalities, x :: others)
                end
              | None -> begin
                  match x with
                  | Fn ("not", [Fn ("=", [Var var; Bitvec_lit bv])]) -> (Some (var, List.length bv, [bv]), others)
                  | _ -> (None, x :: others)
                end
            )
            (None, []) xs
        in
        let check_inequalities =
          let* var, size, lits = inequalities in
          let* max = if size <= 6 then Some (Util.power 2 size - 1) else None in
          let* lits = List.map uint_maybe lits |> Util.option_all in
          let lits = List.fold_left (fun set i -> IntSet.add (Big_int.to_int i) set) IntSet.empty lits in
          let unused = ref IntSet.empty in
          for v = 0 to max do
            if not (IntSet.mem v lits) then unused := IntSet.add v !unused
          done;
          if IntSet.cardinal !unused < IntSet.cardinal lits then
            Some
              (List.map
                 (fun i ->
                   let bv = add_vec_int (zeros (Big_int.of_int size)) (Big_int.of_int i) in
                   Fn ("=", [Var var; Bitvec_lit bv])
                 )
                 (IntSet.elements !unused)
              )
          else None
        in
        begin
          match check_inequalities with
          | Some equalities -> change (smt_conj (smt_disj equalities :: others))
          | None -> NoChange
        end
    | _ -> NoChange

  let rule_or_equalities =
    mk_simple_rule __LOC__ @@ function
    | Fn ("or", xs) ->
        let open Util.Option_monad in
        let open Sail2_operators_bitlists in
        let equalities, others =
          List.fold_left
            (fun (equalities, others) x ->
              match equalities with
              | Some (var, size, lits) -> begin
                  match x with
                  | Fn ("=", [Var var'; Bitvec_lit bv]) when Name.compare var var' = 0 && List.length bv = size ->
                      (Some (var, size, bv :: lits), others)
                  | _ -> (equalities, x :: others)
                end
              | None -> begin
                  match x with
                  | Fn ("=", [Var var; Bitvec_lit bv]) -> (Some (var, List.length bv, [bv]), others)
                  | _ -> (None, x :: others)
                end
            )
            (None, []) xs
        in
        let check_equalities =
          let* var, size, lits = equalities in
          let* max = if size <= 6 then Some (Util.power 2 size - 1) else None in
          let* lits = List.map uint_maybe lits |> Util.option_all in
          let lits = List.fold_left (fun set i -> IntSet.add (Big_int.to_int i) set) IntSet.empty lits in
          let unused = ref IntSet.empty in
          for v = 0 to max do
            if not (IntSet.mem v lits) then unused := IntSet.add v !unused
          done;
          if IntSet.cardinal !unused < IntSet.cardinal lits then
            Some
              (List.map
                 (fun i ->
                   let bv = add_vec_int (zeros (Big_int.of_int size)) (Big_int.of_int i) in
                   Fn ("not", [Fn ("=", [Var var; Bitvec_lit bv])])
                 )
                 (IntSet.elements !unused)
              )
          else None
        in
        begin
          match check_equalities with
          | Some inequalities -> change (smt_disj (smt_conj inequalities :: others))
          | None -> NoChange
        end
    | _ -> NoChange

  let rule_or_ite =
    mk_simple_rule __LOC__ @@ function
    | Ite (Fn ("or", xs), y, z) -> Change (0, Ite (Fn ("and", List.map (fun x -> Fn ("not", [x])) xs), z, y))
    | _ -> NoChange

  (* Simplify ite expressions with a boolean literal as either the then or else branch *)
  let rule_ite_lit =
    mk_simple_rule __LOC__ @@ function
    | Ite (i, Bool_lit true, e) -> change (Fn ("or", [i; e]))
    | Ite (i, Bool_lit false, e) -> change (Fn ("and", [Fn ("not", [i]); e]))
    | Ite (i, t, Bool_lit true) -> change (Fn ("or", [Fn ("not", [i]); t]))
    | Ite (i, t, Bool_lit false) -> change (Fn ("and", [i; t]))
    | _ -> NoChange

  let rule_concat_literal_eq =
    mk_simple_rule __LOC__ @@ function
    | Fn ("=", [Fn ("concat", [Bitvec_lit xs; exp]); Bitvec_lit ys]) ->
        let ys_prefix, ys_suffix = Util.split_after (List.length xs) ys in
        if xs = ys_prefix then change (Fn ("=", [exp; Bitvec_lit ys_suffix])) else change (Bool_lit false)
    | _ -> NoChange

  let rule_flatten_and =
    mk_simple_rule __LOC__ @@ function
    | Fn ("and", xs) ->
        let nested_and = List.exists (function Fn ("and", _) -> true | _ -> false) xs in
        if nested_and then (
          let xs = List.map (function Fn ("and", xs) -> xs | x -> [x]) xs |> List.concat in
          change (Fn ("and", xs))
        )
        else NoChange
    | _ -> NoChange

  let rule_flatten_or =
    mk_simple_rule __LOC__ @@ function
    | Fn ("or", xs) ->
        let nested_or = List.exists (function Fn ("or", _) -> true | _ -> false) xs in
        if nested_or then (
          let xs = List.map (function Fn ("or", xs) -> xs | x -> [x]) xs |> List.concat in
          change (Fn ("or", xs))
        )
        else NoChange
    | _ -> NoChange

  let rule_false_and =
    mk_simple_rule __LOC__ @@ function
    | Fn ("and", xs) when List.exists (function Bool_lit false -> true | _ -> false) xs -> change (Bool_lit false)
    | _ -> NoChange

  let rule_true_and =
    mk_simple_rule __LOC__ @@ function
    | Fn ("and", xs) ->
        let filtered = ref false in
        let xs =
          List.filter
            (function
              | Bool_lit true ->
                  filtered := true;
                  false
              | _ -> true
              )
            xs
        in
        begin
          match xs with
          | [] -> change (Bool_lit true)
          | [x] -> change x
          | _ when !filtered -> change (Fn ("and", xs))
          | _ -> NoChange
        end
    | _ -> NoChange

  let rule_true_or =
    mk_simple_rule __LOC__ @@ function
    | Fn ("or", xs) when List.exists (function Bool_lit true -> true | _ -> false) xs -> change (Bool_lit true)
    | _ -> NoChange

  let rule_false_or =
    mk_simple_rule __LOC__ @@ function
    | Fn ("or", xs) ->
        let filtered = ref false in
        let xs =
          List.filter
            (function
              | Bool_lit false ->
                  filtered := true;
                  false
              | _ -> true
              )
            xs
        in
        begin
          match xs with
          | [] -> change (Bool_lit false)
          | [x] -> change x
          | _ when !filtered -> change (Fn ("or", xs))
          | _ -> NoChange
        end
    | _ -> NoChange

  let rule_order_and =
    mk_simple_rule __LOC__ @@ function
    | Fn ("and", xs) -> Change (0, Fn ("and", List.stable_sort and_order xs))
    | _ -> NoChange

  let rule_order_or =
    mk_simple_rule __LOC__ @@ function
    | Fn ("or", xs) -> Change (0, Fn ("or", List.stable_sort or_order xs))
    | _ -> NoChange

  let add_to_and x = function Fn ("and", xs) -> Fn ("and", x :: xs) | y -> Fn ("and", [x; y])

  let rule_and_assume =
    mk_rule __LOC__ @@ fun simpset -> function
    | Fn ("and", v :: xs) when SimpSet.is_simp_var v ->
        Reconstruct (0, SimpSet.add_var v (Bool_lit true) simpset, smt_conj xs, add_to_and v)
    | Fn ("and", (Fn ("=", [v; lit]) as x) :: xs) when is_literal lit && SimpSet.is_simp_var v ->
        Reconstruct (0, SimpSet.add_var v lit simpset, smt_conj xs, add_to_and x)
    | Fn ("and", (Fn ("=", [lit; v]) as x) :: xs) when is_literal lit && SimpSet.is_simp_var v ->
        Reconstruct (0, SimpSet.add_var v lit simpset, smt_conj xs, add_to_and x)
    | Fn ("and", (Fn ("not", [Fn ("=", [v; lit])]) as x) :: xs) when is_literal lit && SimpSet.is_simp_var v ->
        Reconstruct (0, SimpSet.add_var_inequality v lit simpset, smt_conj xs, add_to_and x)
    | Fn ("and", (Fn ("not", [Fn ("=", [lit; v])]) as x) :: xs) when is_literal lit && SimpSet.is_simp_var v ->
        Reconstruct (0, SimpSet.add_var_inequality v lit simpset, smt_conj xs, add_to_and x)
    | Fn ("and", (Tester (ctor, Var v) as x) :: xs) ->
        Reconstruct (0, SimpSet.add_var_is_ctor v ctor simpset, smt_conj xs, add_to_and x) | _ -> NoChange

  let is_equality = function
    | Fn ("=", [v; lit]) when is_literal lit && SimpSet.is_simp_var v -> Some (v, lit)
    | _ -> None

  let apply_equality (v, exp) = fold_smt_exp (fun exp' -> if identical v exp' then exp else exp')

  let rule_distribute_or_equality_in_and =
    let module Vars = SimpSet.SimpVarSet in
    mk_simple_rule __LOC__ @@ function
    | Fn ("and", xs) -> begin
        let vars = ref Vars.empty in
        List.iter
          (fun x ->
            iter_smt_exp
              (fun exp -> match SimpSet.to_simp_var exp with Some v -> vars := Vars.add v !vars | None -> ())
              x
          )
          xs;
        if Vars.cardinal !vars = 1 then (
          let or_equalities, others =
            Util.map_split
              (function
                | Fn ("or", ys) as other -> (
                    match Util.option_all (List.map is_equality ys) with Some ys -> Ok ys | None -> Error other
                  )
                | other -> Error other
                )
              xs
          in
          match List.stable_sort List.compare_lengths or_equalities with
          | [] -> NoChange
          | or_equality :: rest ->
              let mk_eq (v, exp) = Fn ("=", [v; exp]) in
              let rest = List.map (fun eqs -> Fn ("or", List.map mk_eq eqs)) rest in
              let others = rest @ others in
              change
                (Fn ("or", List.map (fun eq -> Fn ("and", mk_eq eq :: List.map (apply_equality eq) others)) or_equality))
        )
        else NoChange
      end
    | _ -> NoChange

  let add_to_or x = function Fn ("or", xs) -> Fn ("or", x :: xs) | y -> Fn ("or", [x; y])

  let rule_or_assume =
    mk_rule __LOC__ @@ fun simpset -> function
    | Fn ("or", v :: xs) when SimpSet.is_simp_var v ->
        Reconstruct (0, SimpSet.add_var v (Bool_lit false) simpset, smt_disj xs, add_to_or v) | _ -> NoChange

  let rule_var =
    mk_rule __LOC__ @@ fun simpset -> function
    | v when SimpSet.is_simp_var v -> (
        match SimpSet.find_opt v simpset with Some exp -> change exp | None -> NoChange
      ) | _ -> NoChange

  let rule_tester =
    mk_rule __LOC__ @@ fun simpset -> function
    | Tester (ctor, Var v) -> (
        match SimpSet.is_ctor v ctor simpset with Some b -> change (Bool_lit b) | _ -> NoChange
      ) | _ -> NoChange

  let rule_access_ite =
    mk_simple_rule __LOC__ @@ function
    | Field (struct_id, field, Ite (i, t, e)) ->
        change (Ite (i, Field (struct_id, field, t), Field (struct_id, field, e)))
    | Unwrap (ctor, b, Ite (i, t, e)) -> change (Ite (i, Unwrap (ctor, b, t), Unwrap (ctor, b, e)))
    | Tester (ctor, Ite (i, t, e)) -> change (Ite (i, Tester (ctor, t), Tester (ctor, e)))
    | Fn ("select", [Ite (i, t, e); ix]) -> change (Ite (i, Fn ("select", [t; ix]), Fn ("select", [e; ix])))
    | _ -> NoChange

  let rule_inequality =
    mk_rule __LOC__ @@ fun simpset -> function
    | Fn ("=", [v; lit]) when is_literal lit && SimpSet.is_simp_var v ->
        let inequal = ref false in
        List.iter
          (fun exp -> match simp_eq lit exp with Some true -> inequal := true | _ -> ())
          (SimpSet.inequalities v simpset);
        if !inequal then change (Bool_lit false) else NoChange
    | Fn ("not", [Fn ("=", [v; lit])]) when is_literal lit && SimpSet.is_simp_var v ->
        if
          List.exists
            (fun exp -> match simp_eq lit exp with Some true -> true | _ -> false)
            (SimpSet.inequalities v simpset)
        then change (Bool_lit true)
        else NoChange | _ -> NoChange

  let rule_not_not = mk_simple_rule __LOC__ @@ function Fn ("not", [Fn ("not", [exp])]) -> change exp | _ -> NoChange

  let rule_not_push =
    mk_simple_rule __LOC__ @@ function
    | Fn ("not", [Fn ("or", xs)]) -> change (Fn ("and", List.map (fun x -> Fn ("not", [x])) xs))
    | Fn ("not", [Fn ("and", xs)]) -> change (Fn ("or", List.map (fun x -> Fn ("not", [x])) xs))
    | Fn ("not", [Ite (i, t, e)]) -> change (Ite (i, Fn ("not", [t]), Fn ("not", [e])))
    | Fn ("not", [Bool_lit b]) -> change (Bool_lit (not b))
    | Fn ("not", [Fn ("bvslt", [x; y])]) -> change (Fn ("bvsge", [x; y]))
    | Fn ("not", [Fn ("bvsle", [x; y])]) -> change (Fn ("bvsgt", [x; y]))
    | Fn ("not", [Fn ("bvsgt", [x; y])]) -> change (Fn ("bvsle", [x; y]))
    | Fn ("not", [Fn ("bvsge", [x; y])]) -> change (Fn ("bvslt", [x; y]))
    | _ -> NoChange

  let is_bvfunction = function
    | "bvnot" | "bvand" | "bvor" | "bvxor" | "bvshl" | "bvlshr" | "bvashr" -> true
    | _ -> false

  let rule_bvfunction_literal =
    let open Sail2_operators_bitlists in
    mk_simple_rule __LOC__ @@ function
    | Fn (f, args) -> (
        match (f, args) with
        | "bvnot", [Bitvec_lit bv] -> change (Bitvec_lit (not_vec bv))
        | "bvand", [Bitvec_lit lhs; Bitvec_lit rhs] -> change (Bitvec_lit (and_vec lhs rhs))
        | "bvor", [Bitvec_lit lhs; Bitvec_lit rhs] -> change (Bitvec_lit (or_vec lhs rhs))
        | "bvxor", [Bitvec_lit lhs; Bitvec_lit rhs] -> change (Bitvec_lit (xor_vec lhs rhs))
        | "bvshl", [lhs; Bitvec_lit rhs] when bv_is_zero rhs -> change lhs
        | "bvshl", [Bitvec_lit lhs; Bitvec_lit rhs] -> begin
            match sint_maybe rhs with Some shift -> change (Bitvec_lit (shiftl lhs shift)) | None -> NoChange
          end
        | "bvlshr", [lhs; Bitvec_lit rhs] when bv_is_zero rhs -> change lhs
        | "bvlshr", [Bitvec_lit lhs; Bitvec_lit rhs] -> begin
            match sint_maybe rhs with Some shift -> change (Bitvec_lit (shiftr lhs shift)) | None -> NoChange
          end
        | "bvashr", [lhs; Bitvec_lit rhs] when bv_is_zero rhs -> change lhs
        | "bvashr", [Bitvec_lit lhs; Bitvec_lit rhs] -> begin
            match sint_maybe rhs with Some shift -> change (Bitvec_lit (arith_shiftr lhs shift)) | None -> NoChange
          end
        | _ -> NoChange
      )
    | _ -> NoChange

  let rule_extend_literal =
    mk_simple_rule __LOC__ @@ function
    | ZeroExtend (to_len, by_len, Bitvec_lit bv) ->
        change (Bitvec_lit (Sail2_operators_bitlists.zero_extend bv (Big_int.of_int to_len)))
    | SignExtend (to_len, by_len, Bitvec_lit bv) ->
        change (Bitvec_lit (Sail2_operators_bitlists.sign_extend bv (Big_int.of_int to_len)))
    | _ -> NoChange

  let rule_extract =
    mk_simple_rule __LOC__ @@ function
    | Extract (n, m, Bitvec_lit bv) ->
        change (Bitvec_lit (Sail2_operators_bitlists.subrange_vec_dec bv (Big_int.of_int n) (Big_int.of_int m)))
    | _ -> NoChange

  let rule_simp_eq =
    mk_simple_rule __LOC__ @@ function
    | Fn ("=", [x; y]) -> begin match simp_eq x y with Some b -> change (Bool_lit b) | None -> NoChange end
    | _ -> NoChange

  let rule_do_nothing = mk_simple_rule __LOC__ (fun _ -> NoChange)

  let apply simpset f exp =
    let open Jib_visitor in
    let changes = ref 0 in
    let rec go simpset exp =
      match f simpset exp with
      | Change (n, exp) ->
          changes := !changes + n;
          children simpset exp
      | Reconstruct (n, simpset', exp, recon) ->
          changes := !changes + n;
          children simpset (recon (go simpset' exp))
      | NoChange -> children simpset exp
    and children simpset no_change =
      match no_change with
      | Fn (f, args) ->
          let args' = map_no_copy (go simpset) args in
          if args == args' then no_change else Fn (f, args')
      | Hd (f, exp) ->
          let exp' = go simpset exp in
          if exp == exp' then no_change else Tl (f, exp')
      | Tl (f, exp) ->
          let exp' = go simpset exp in
          if exp == exp' then no_change else Hd (f, exp')
      | Ite (i, t, e) ->
          let i' = go simpset i in
          let t' = go simpset t in
          let e' = go simpset e in
          if i == i' && t == t' && e == e' then no_change else Ite (i', t', e')
      | ZeroExtend (n, m, exp) ->
          let exp' = go simpset exp in
          if exp == exp' then no_change else ZeroExtend (n, m, exp')
      | SignExtend (n, m, exp) ->
          let exp' = go simpset exp in
          if exp == exp' then no_change else SignExtend (n, m, exp')
      | Extract (n, m, exp) ->
          let exp' = go simpset exp in
          if exp == exp' then no_change else Extract (n, m, exp')
      | Store (info, store_fn, arr, i, x) ->
          let arr' = go simpset arr in
          let i' = go simpset i in
          let x' = go simpset x in
          if arr == arr' && i == i' && x == x' then no_change else Store (info, store_fn, arr', i', x')
      | Unwrap (ctor, b, exp) ->
          let exp' = go simpset exp in
          if exp == exp' then no_change else Unwrap (ctor, b, exp')
      | Tester (ctor, exp) ->
          let exp' = go simpset exp in
          if exp == exp' then no_change else Tester (ctor, exp')
      | Field (struct_id, field_id, exp) ->
          let exp' = go simpset exp in
          if exp == exp' then no_change else Field (struct_id, field_id, exp')
      | Struct (struct_id, fields) ->
          let fields' = map_no_copy (fun (field_id, exp) -> (field_id, go simpset exp)) fields in
          if fields == fields' then no_change else Struct (struct_id, fields')
      | Bool_lit _ | Bitvec_lit _ | Real_lit _ | String_lit _ | Var _ | Unit | Member _ | Empty_list -> no_change
    in
    let exp = go simpset exp in
    (!changes, exp)
end

let count = ref 0

let simp simpset exp =
  let open Simplifier in
  let visit simpset exp =
    match exp with
    | Ite _ ->
        run_strategy simpset exp
          (Then [rule_same_ite; Repeat rule_squash_ite; rule_or_ite; rule_ite_lit; rule_ite_literal])
    | Fn ("and", _) ->
        run_strategy simpset exp
          (Then
             [
               rule_flatten_and;
               rule_false_and;
               rule_true_and;
               rule_and_duplicates;
               rule_and_inequalities;
               rule_order_and;
               Repeat rule_and_assume;
               rule_distribute_or_equality_in_and;
             ]
          )
    | Fn ("or", _) ->
        run_strategy simpset exp
          (Then
             [
               rule_flatten_or;
               rule_true_or;
               rule_false_or;
               rule_or_duplicates;
               rule_or_equalities;
               rule_order_or;
               Repeat rule_or_assume;
             ]
          )
    | Var _ -> run_strategy simpset exp rule_var
    | Fn ("=", _) -> run_strategy simpset exp (Then [rule_inequality; rule_simp_eq; rule_concat_literal_eq])
    | Fn ("not", _) -> run_strategy simpset exp (Then [Repeat rule_not_not; Repeat rule_not_push; rule_inequality])
    | Fn ("select", _) -> run_strategy simpset exp rule_access_ite
    | Fn (bvf, _) when is_bvfunction bvf -> run_strategy simpset exp rule_bvfunction_literal
    | ZeroExtend _ -> run_strategy simpset exp rule_extend_literal
    | SignExtend _ -> run_strategy simpset exp rule_extend_literal
    | Extract _ -> run_strategy simpset exp rule_extract
    | Field _ -> run_strategy simpset exp rule_access_ite
    | Unwrap _ -> run_strategy simpset exp rule_access_ite
    | Tester _ -> run_strategy simpset exp (Then [rule_tester; rule_access_ite])
    | exp -> NoChange
  in
  let rec go exp =
    let changes, exp = apply simpset visit exp in
    if changes > 0 then go exp else exp
  in
  go exp

type smt_def =
  | Define_fun of string * (string * smt_typ) list * smt_typ * smt_exp
  | Declare_fun of string * smt_typ list * smt_typ
  | Declare_const of Jib.name * smt_typ
  | Define_const of Jib.name * smt_typ * smt_exp
  | Declare_datatypes of string * (string * (string * smt_typ) list) list
  | Assert of smt_exp

let declare_datatypes = function Datatype (name, ctors) -> Declare_datatypes (name, ctors) | _ -> assert false

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
  | Array (ty1, ty2) -> pp_sfun "Array" [pp_smt_typ ty1; pp_smt_typ ty2]

let pp_str_smt_typ (str, ty) =
  let open PPrint in
  parens (string str ^^ space ^^ pp_smt_typ ty)

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
  | Declare_const (name, ty) -> pp_sfun "declare-const" [string (zencode_name name); pp_smt_typ ty]
  | Define_const (name, ty, exp) -> pp_sfun "define-const" [string (zencode_name name); pp_smt_typ ty; pp_smt_exp exp]
  | Declare_datatypes (name, ctors) ->
      let pp_ctor (ctor_name, fields) =
        match fields with [] -> parens (string ctor_name) | _ -> pp_sfun ctor_name (List.map pp_str_smt_typ fields)
      in
      pp_sfun "declare-datatypes"
        [Printf.ksprintf string "((%s 0))" name; parens (parens (separate_map space pp_ctor ctors))]
  | Assert exp -> pp_sfun "assert" [pp_smt_exp exp]

let string_of_smt_def def = Pretty_print_sail.Document.to_string (pp_smt_def def)

(**************************************************************************)
(* 2. Parser for SMT solver output                                        *)
(**************************************************************************)

(* Output format from each SMT solver does not seem to be completely
   standardised, unlike the SMTLIB input format, but usually is some
   form of s-expression based representation. Therefore we define a
   simple parser for s-expressions using monadic parser combinators. *)

type counterexample_solver = Cvc5 | Cvc4 | Z3

let counterexample_command = function Cvc5 -> "cvc5 --lang=smt2.6" | Cvc4 -> "cvc4 --lang=smt2.6" | Z3 -> "z3"

let counterexample_solver_from_name name =
  match String.lowercase_ascii name with "cvc4" -> Some Cvc4 | "cvc5" -> Some Cvc5 | "z3" -> Some Z3 | _ -> None

module type COUNTEREXAMPLE_CONFIG = sig
  val max_unknown_integer_width : int
end

module Counterexample (Config : COUNTEREXAMPLE_CONFIG) = struct
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
    match plist sexp tokens with Ok (result, _) -> Some result | Fail -> None

  let parse_sexpr_int width = function
    | List [Atom "_"; Atom v; Atom m] when int_of_string m = width && String.length v > 2 && String.sub v 0 2 = "bv" ->
        let v = String.sub v 2 (String.length v - 2) in
        Some (Big_int.of_string v)
    | Atom v when String.length v > 2 && String.sub v 0 2 = "#b" ->
        let v = String.sub v 2 (String.length v - 2) in
        Some (Big_int.of_string ("0b" ^ v))
    | Atom v when String.length v > 2 && String.sub v 0 2 = "#x" ->
        let v = String.sub v 2 (String.length v - 2) in
        Some (Big_int.of_string ("0x" ^ v))
    | _ -> None

  let rec value_of_sexpr sexpr =
    let open Jib in
    let open Value in
    function
    | CT_fbits width -> begin
        match parse_sexpr_int width sexpr with
        | Some value -> mk_vector (Sail_lib.get_slice_int' (width, value, 0))
        | None -> failwith ("Cannot parse sexpr as bitvector: " ^ string_of_sexpr sexpr)
      end
    | CT_struct (_, fields) -> begin
        match sexpr with
        | List (Atom name :: smt_fields) ->
            V_record
              (List.fold_left2
                 (fun m (field_id, ctyp) sexpr -> StringMap.add (string_of_id field_id) (value_of_sexpr sexpr ctyp) m)
                 StringMap.empty fields smt_fields
              )
        | _ -> failwith ("Cannot parse sexpr as struct " ^ string_of_sexpr sexpr)
      end
    | CT_enum (_, members) -> begin
        match sexpr with
        | Atom name -> begin
            match List.find_opt (fun member -> Util.zencode_string (string_of_id member) = name) members with
            | Some member -> V_member (string_of_id member)
            | None ->
                failwith
                  ("Could not find enum member for " ^ name ^ " in " ^ Util.string_of_list ", " string_of_id members)
          end
        | _ -> failwith ("Cannot parse sexpr as enum " ^ string_of_sexpr sexpr)
      end
    | CT_bool -> begin
        match sexpr with
        | Atom "true" -> V_bool true
        | Atom "false" -> V_bool false
        | _ -> failwith ("Cannot parse sexpr as bool " ^ string_of_sexpr sexpr)
      end
    | CT_fint width -> begin
        match parse_sexpr_int width sexpr with
        | Some value -> V_int value
        | None -> failwith ("Cannot parse sexpr as fixed-width integer: " ^ string_of_sexpr sexpr)
      end
    | CT_lint -> begin
        match parse_sexpr_int Config.max_unknown_integer_width sexpr with
        | Some value -> V_int value
        | None -> failwith ("Cannot parse sexpr as integer: " ^ string_of_sexpr sexpr)
      end
    | ctyp -> failwith ("Unsupported type in sexpr: " ^ Jib_util.string_of_ctyp ctyp)

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
    | Interpreter.Done (state, v) -> Result.Ok v
    | Interpreter.Step (lazy_str, _, _, _) -> run (Interpreter.eval_frame frame)
    | Interpreter.Break frame -> run (Interpreter.eval_frame frame)
    | Interpreter.Fail (_, _, _, _, msg) -> Result.Error msg
    | Interpreter.Effect_request (out, state, stack, eff) -> run (Interpreter.default_effect_interp state eff)

  let check ~env ~ast ~solver ~file_name ~function_id ~args ~arg_ctyps ~arg_smt_names =
    let open Printf in
    let open Ast in
    print_endline ("Checking counterexample: " ^ file_name);
    let in_chan = ksprintf Unix.open_process_in "%s %s" (counterexample_command solver) file_name in
    let lines = ref [] in
    begin
      try
        while true do
          lines := input_line in_chan :: !lines
        done
      with End_of_file -> ()
    end;
    let solver_output = List.rev !lines |> String.concat "\n" in
    begin
      match parse_sexps solver_output with
      | Some (Atom "sat" :: (List (Atom "model" :: model) | List model) :: _) ->
          let open Value in
          let open Interpreter in
          print_endline (sprintf "Solver found counterexample: %s" Util.("ok" |> green |> clear));
          let counterexample = build_counterexample args arg_ctyps arg_smt_names model in
          List.iter (fun (id, v) -> print_endline ("  " ^ string_of_id id ^ " -> " ^ string_of_value v)) counterexample;
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
            | Result.Ok (V_bool false) | Result.Ok V_unit ->
                ksprintf print_endline "Replaying counterexample: %s" Util.("ok" |> green |> clear)
            | Result.Ok (V_bool true) ->
                ksprintf print_endline "Failed to replay counterexample: %s\n  Function returned true"
                  Util.("error" |> red |> clear)
            | Result.Error msg ->
                ksprintf print_endline "Failed to replay counterexample: %s\n  %s" Util.("error" |> red |> clear) msg
            | _ -> ()
          end
      | Some (Atom "unsat" :: _) ->
          print_endline "Solver could not find counterexample";
          print_endline "Solver output:";
          print_endline solver_output
      | _ ->
          print_endline "Unexpected solver output:";
          print_endline solver_output
    end;
    let _ = Unix.close_process_in in_chan in
    ()
end
