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

module Big_int = Nat_big_num
open Util

(* ===== Integer Constraints ===== *)

type nexp_op = string

type nexp =
  | NFun of (nexp_op * nexp list)
  | N2n of nexp
  | NConstant of Big_int.num
  | NVar of int

let big_int_op : nexp_op -> (Big_int.num -> Big_int.num -> Big_int.num) option = function
  | "+" -> Some Big_int.add
  | "-" -> Some Big_int.sub
  | "*" -> Some Big_int.mul
  | _ -> None

let rec arith constr =
  let constr' = match constr with
    | NFun (op, [x; y]) -> NFun (op, [arith x; arith y])
    | N2n c -> N2n (arith c)
    | c -> c
  in
  match constr' with
  | NFun (op, [NConstant x; NConstant y]) as c ->
     begin
       match big_int_op op with
       | Some op -> NConstant (op x y)
       | None -> c
     end
  | N2n (NConstant x) -> NConstant (Big_int.pow_int_positive 2 (Big_int.to_int x))
  | c -> c

(* ===== Boolean Constraints ===== *)

type constraint_bool_op = And | Or

type constraint_compare_op = Gt | Lt | GtEq | LtEq | Eq | NEq

let negate_comparison = function
  | Gt -> LtEq
  | Lt -> GtEq
  | GtEq -> Lt
  | LtEq -> Gt
  | Eq -> NEq
  | NEq -> Eq

type 'a constraint_bool =
  | BFun of (constraint_bool_op * 'a constraint_bool * 'a constraint_bool)
  | Not of 'a constraint_bool
  | CFun of (constraint_compare_op * 'a * 'a)
  | Forall of (int list * 'a constraint_bool)
  | Boolean of bool

let rec pairs (xs : 'a list) (ys : 'a list) : ('a * 'b) list =
  match xs with
  | [] -> []
  | (x :: xs) -> List.map (fun y -> (x, y)) ys @ pairs xs ys

(* Get a set of variables from a constraint *)
module IntSet = Set.Make(
  struct
    let compare = Pervasives.compare
    type t = int
  end)

let rec nexp_vars : nexp -> IntSet.t = function
  | NConstant _ -> IntSet.empty
  | NVar v -> IntSet.singleton v
  | NFun (_, xs) -> List.fold_left IntSet.union IntSet.empty (List.map nexp_vars xs)
  | N2n x -> nexp_vars x

let rec constraint_vars : nexp constraint_bool -> IntSet.t = function
  | BFun (_, x, y) -> IntSet.union (constraint_vars x) (constraint_vars y)
  | Not x -> constraint_vars x
  | CFun (_, x, y) -> IntSet.union (nexp_vars x) (nexp_vars y)
  | Forall (vars, x) -> IntSet.diff (constraint_vars x) (IntSet.of_list vars)
  | Boolean _ -> IntSet.empty

(* SMTLIB v2.0 format is based on S-expressions so we have a
   lightweight representation of those here. *)
type sexpr = List of (sexpr list) | Atom of string

let sfun (fn : string) (xs : sexpr list) : sexpr = List (Atom fn :: xs)

let rec pp_sexpr : sexpr -> string = function
  | List xs -> "(" ^ string_of_list " " pp_sexpr xs ^ ")"
  | Atom x -> x

let var_decs constr =
  constraint_vars constr
  |> IntSet.elements
  |> List.map (fun var -> sfun "declare-const" [Atom ("v" ^ string_of_int var); Atom "Int"])
  |> string_of_list "\n" pp_sexpr

let cop_sexpr op x y =
  match op with
  | Gt -> sfun ">" [x; y]
  | Lt -> sfun "<" [x; y]
  | GtEq -> sfun ">=" [x; y]
  | LtEq -> sfun "<=" [x; y]
  | Eq -> sfun "=" [x; y]
  | NEq -> sfun "not" [sfun "=" [x; y]]

let rec sexpr_of_nexp = function
  | NFun (op, xs) -> sfun op (List.map sexpr_of_nexp xs)
  | N2n x -> sfun "^" [Atom "2"; sexpr_of_nexp x]
  | NConstant c -> Atom (Big_int.to_string c) (* CHECK: do we do negative constants right? *)
  | NVar var -> Atom ("v" ^ string_of_int var)

let rec sexpr_of_constraint = function
  | BFun (And, x, y) -> sfun "and" [sexpr_of_constraint x; sexpr_of_constraint y]
  | BFun (Or, x, y) -> sfun "or" [sexpr_of_constraint x; sexpr_of_constraint y]
  | Not x -> sfun "not" [sexpr_of_constraint x]
  | CFun (op, x, y) -> cop_sexpr op (sexpr_of_nexp (arith x)) (sexpr_of_nexp (arith y))
  | Forall (vars, x) ->
     sfun "forall" [List (List.map (fun v -> List [Atom ("v" ^ string_of_int v); Atom "Int"]) vars); sexpr_of_constraint x]
  | Boolean true -> Atom "true"
  | Boolean false -> Atom "false"

let smtlib_of_constraints ?get_model:(get_model=false) constr : string =
  "(push)\n"
  ^ var_decs constr ^ "\n"
  ^ pp_sexpr (sfun "define-fun" [Atom "constraint"; List []; Atom "Bool"; sexpr_of_constraint constr])
  ^ "\n(assert constraint)\n(check-sat)"
  ^ (if get_model then "\n(get-model)" else "")
  ^ "\n(pop)"

type t = nexp constraint_bool

type smt_result = Unknown | Sat | Unsat

module DigestMap = Map.Make(Digest)

let known_problems = ref (DigestMap.empty)

let load_digests_err () =
  let in_chan = open_in_bin "z3_problems" in
  let rec load () =
    let digest = Digest.input in_chan in
    let result = input_byte in_chan in
    begin
      match result with
      | 0 -> known_problems := DigestMap.add digest Unknown !known_problems
      | 1 -> known_problems := DigestMap.add digest Sat !known_problems
      | 2 -> known_problems := DigestMap.add digest Unsat !known_problems
      | _ -> assert false
    end;
    load ()
  in
  try load () with
  | End_of_file -> close_in in_chan

let load_digests () =
  try load_digests_err () with
  | Sys_error _ -> ()

let save_digests () =
  let out_chan = open_out_bin "z3_problems" in
  let output digest result =
    Digest.output out_chan digest;
    match result with
    | Unknown -> output_byte out_chan 0
    | Sat -> output_byte out_chan 1
    | Unsat -> output_byte out_chan 2
  in
  DigestMap.iter output !known_problems;
  close_out out_chan

let rec call_z3 constraints : smt_result =
  let problems = [constraints] in
  let z3_file = smtlib_of_constraints constraints in

  (* prerr_endline (Printf.sprintf "SMTLIB2 constraints are: \n%s%!" z3_file); *)

  let rec input_lines chan = function
    | 0 -> []
    | n ->
       begin
         let l = input_line chan in
         let ls = input_lines chan (n - 1) in
         l :: ls
       end
  in

  let digest = Digest.string z3_file in
  try
    let result = DigestMap.find digest !known_problems in
    result
  with
  | Not_found ->
    begin
      let (input_file, tmp_chan) = Filename.open_temp_file "constraint_" ".sat" in
      output_string tmp_chan z3_file;
      close_out tmp_chan;
      let z3_chan = Unix.open_process_in ("z3 -t:1000 -T:10 " ^ input_file) in
      let z3_output = List.combine problems (input_lines z3_chan (List.length problems)) in
      let _ = Unix.close_process_in z3_chan in
      Sys.remove input_file;
      try
        let (problem, _) = List.find (fun (_, result) -> result = "unsat") z3_output in
        known_problems := DigestMap.add digest Unsat !known_problems;
        Unsat
      with
      | Not_found ->
         let unsolved = List.filter (fun (_, result) -> result = "unknown") z3_output in
         if unsolved == []
         then (known_problems := DigestMap.add digest Sat !known_problems; Sat)
         else (known_problems := DigestMap.add digest Unknown !known_problems; Unknown)
    end

let rec solve_z3 constraints var =
  let problems = [constraints] in
  let z3_file = smtlib_of_constraints ~get_model:true constraints in

  (* prerr_endline (Printf.sprintf "SMTLIB2 constraints are: \n%s%!" z3_file); *)

  let rec input_all chan =
    try
      let l = input_line chan in
      let ls = input_all chan in
      l :: ls
    with
      End_of_file -> []
  in

  let (input_file, tmp_chan) = Filename.open_temp_file "constraint_" ".sat" in
  output_string tmp_chan z3_file;
  close_out tmp_chan;
  let z3_chan = Unix.open_process_in ("z3 -t:1000 -T:10 " ^ input_file) in
  let z3_output = String.concat " " (input_all z3_chan) in
  let _ = Unix.close_process_in z3_chan in
  Sys.remove input_file;
  let regexp = {|(define-fun v|} ^ string_of_int var ^ {| () Int[ ]+\([0-9]+\))|} in
  try
    let _ = Str.search_forward (Str.regexp regexp) z3_output 0 in
    let result = Big_int.of_string (Str.matched_group 1 z3_output) in
    begin match call_z3 (BFun (And, constraints, CFun (NEq, NConstant result, NVar var))) with
    | Unsat -> Some result
    | _ -> None
    end
  with
    Not_found -> None

let string_of constr = smtlib_of_constraints constr

(* ===== Abstract API for building constraints ===== *)

(* These functions are exported from constraint.mli, and ensure that
   the internal representation of constraints remains opaque. *)

let implies (x : t) (y : t) : t =
  BFun (Or, Not x, y)

let conj (x : t) (y : t) : t =
  BFun (And, x, y)

let disj (x : t) (y : t) : t =
  BFun (Or, x, y)

let forall (vars : int list) (x : t) : t =
  if vars = [] then x else Forall (vars, x)

let negate (x : t) : t = Not x

let literal (b : bool) : t = Boolean b

let lt x y : t = CFun (Lt, x, y)

let lteq x y : t = CFun (LtEq, x, y)

let gt x y : t = CFun (Gt, x, y)

let gteq x y : t = CFun (GtEq, x, y)

let eq x y : t = CFun (Eq, x, y)

let neq x y : t = CFun (NEq, x, y)

let pow2 x : nexp = N2n x

let add x y : nexp = NFun ("+", [x; y])

let sub x y : nexp = NFun ("-", [x; y])

let mult x y : nexp = NFun ("*", [x; y])

let app f xs : nexp = NFun (f, xs)

let constant (x : Big_int.num) : nexp = NConstant x

let variable (v : int) : nexp = NVar v
