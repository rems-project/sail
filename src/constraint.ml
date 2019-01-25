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
open Ast
open Ast_util
open Util

(* SMTLIB v2.0 format is based on S-expressions so we have a
   lightweight representation of those here. *)
type sexpr = List of (sexpr list) | Atom of string

let sfun (fn : string) (xs : sexpr list) : sexpr = List (Atom fn :: xs)

let rec pp_sexpr : sexpr -> string = function
  | List xs -> "(" ^ string_of_list " " pp_sexpr xs ^ ")"
  | Atom x -> x

(** Each non-Type/Order kind in Sail mapes to a type in the SMT solver *)
let smt_type l = function
  | K_int -> Atom "Int"
  | K_bool -> Atom "Bool"
  | _ -> raise (Reporting.err_unreachable l __POS__ "Tried to pass Type or Order kinded variable to SMT solver")

let to_smt l vars constr =
  (* Numbering all SMT variables v0, ... vn, rather than generating
     names based on their Sail names (e.g. using zencode) ensures that
     alpha-equivalent constraints generate the same SMT problem, which
     is important for the SMT memoisation to work properly. *)
  let var_map = ref KBindings.empty in
  let vnum = ref (-1) in
  let smt_var v =
    match KBindings.find_opt v !var_map with
    | Some n -> Atom ("v" ^ string_of_int n)
    | None ->
       let n = !vnum + 1 in
       var_map := KBindings.add v n !var_map;
       vnum := n;
       Atom ("v" ^ string_of_int n)
  in

  (* var_decs outputs the list of variables to be used by the SMT
     solver in SMTLIB v2.0 format. It takes a kind_aux KBindings, as
     returned by Type_check.get_typ_vars *)
  let var_decs l (vars : kind_aux KBindings.t) : string =
    vars
    |> KBindings.bindings
    |> List.map (fun (v, k) -> sfun "declare-const" [smt_var v; smt_type l k])
    |> string_of_list "\n" pp_sexpr
  in
  let rec smt_nexp (Nexp_aux (aux, l) : nexp) : sexpr =
    match aux with
    | Nexp_id id -> Atom (Util.zencode_string (string_of_id id))
    | Nexp_var v -> smt_var v
    | Nexp_constant c -> Atom (Big_int.to_string c)
    | Nexp_app (id, nexps) -> sfun (string_of_id id) (List.map smt_nexp nexps)
    | Nexp_times (nexp1, nexp2) -> sfun "*" [smt_nexp nexp1; smt_nexp nexp2]
    | Nexp_sum (nexp1, nexp2) -> sfun "+" [smt_nexp nexp1; smt_nexp nexp2]
    | Nexp_minus (nexp1, nexp2) -> sfun "-" [smt_nexp nexp1; smt_nexp nexp2]
    | Nexp_exp (Nexp_aux (Nexp_constant c, _)) when Big_int.greater c Big_int.zero ->
       Atom (Big_int.to_string (Big_int.pow_int_positive 2 (Big_int.to_int c)))
    | Nexp_exp nexp -> sfun "^" [Atom "2"; smt_nexp nexp]
    | Nexp_neg nexp -> sfun "-" [smt_nexp nexp]
  in
  let rec smt_constraint (NC_aux (aux, l) : n_constraint) : sexpr =
    match aux with
    | NC_equal (nexp1, nexp2) -> sfun "=" [smt_nexp nexp1; smt_nexp nexp2]
    | NC_bounded_le (nexp1, nexp2) -> sfun "<=" [smt_nexp nexp1; smt_nexp nexp2]
    | NC_bounded_ge (nexp1, nexp2) -> sfun ">=" [smt_nexp nexp1; smt_nexp nexp2]
    | NC_not_equal (nexp1, nexp2) -> sfun "not" [sfun "=" [smt_nexp nexp1; smt_nexp nexp2]]
    | NC_set (v, ints) ->
       sfun "or" (List.map (fun i -> sfun "=" [smt_var v; Atom (Big_int.to_string i)]) ints)
    | NC_or (nc1, nc2) -> sfun "or" [smt_constraint nc1; smt_constraint nc2]
    | NC_and (nc1, nc2) -> sfun "and" [smt_constraint nc1; smt_constraint nc2]
    | NC_app (id, args) ->
       sfun (string_of_id id) (List.map smt_typ_arg args)
    | NC_true -> Atom "true"
    | NC_false -> Atom "false"
    | NC_var v -> smt_var v
  and smt_typ_arg (A_aux (aux, l) : typ_arg) : sexpr =
    match aux with
    | A_nexp nexp -> smt_nexp nexp
    | A_bool nc -> smt_constraint nc
    | _ ->
       raise (Reporting.err_unreachable l __POS__ "Tried to pass Type or Order kind to SMT function")
  in
  var_decs l vars, smt_constraint constr, smt_var

let smtlib_of_constraints ?get_model:(get_model=false) l vars constr : string * (kid -> sexpr) =
  let variables, problem, var_map = to_smt l vars constr in
  "(push)\n"
  ^ variables ^ "\n"
  ^ pp_sexpr (sfun "define-fun" [Atom "constraint"; List []; Atom "Bool"; problem])
  ^ "\n(assert constraint)\n(check-sat)"
  ^ (if get_model then "\n(get-model)" else "")
  ^ "\n(pop)",
  var_map

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

let call_z3' l vars constraints : smt_result =
  let problems = [constraints] in
  let z3_file, _ = smtlib_of_constraints l vars constraints in

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

let call_z3 l vars constraints =
  let t = Profile.start_z3 () in
  let result = call_z3' l vars constraints in
  Profile.finish_z3 t;
  result

let rec solve_z3 l vars constraints var =
  let z3_file, smt_var = smtlib_of_constraints ~get_model:true l vars constraints in
  let z3_var = pp_sexpr (smt_var var) in

  (* prerr_endline (Printf.sprintf "SMTLIB2 constraints are: \n%s%!" z3_file);
     prerr_endline ("Solving for " ^ z3_var); *)

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
  let regexp = {|(define-fun |} ^ z3_var ^ {| () Int[ ]+\([0-9]+\))|} in
  try
    let _ = Str.search_forward (Str.regexp regexp) z3_output 0 in
    let result = Big_int.of_string (Str.matched_group 1 z3_output) in
    begin match call_z3 l vars (nc_and constraints (nc_neq (nconstant result) (nvar var))) with
    | Unsat -> Some result
    | _ -> None
    end
  with
    Not_found -> None
