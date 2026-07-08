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
(*  SPDX-License-Identifier: BSD-2-Clause                                   *)
(****************************************************************************)

open Ast
open Ast_defs
open Ast_util
open Printf

module StringMap = Util.StringMap

let opt_interactive = ref false

module State = struct
  type istate = {
    ctx : Initial_check.ctx;
    ast : Type_check.typed_ast;
    effect_info : Effects.side_effect_info;
    env : Type_check.Env.t;
    options : (Arg.key * Arg.spec * Arg.doc) list;
    default_sail_dir : string;
    config : Yojson.Safe.t option;
  }
end

open State

let arg str = "<" ^ str ^ ">" |> Util.yellow |> Util.clear

let command str = str |> Util.green |> Util.clear

type action =
  | ArgString of string * (string -> action)
  | ArgInt of string * (int -> action)
  | Action of string option * (Sail_file.position * string * State.istate -> State.istate option)

let unit_action f =
  Action
    ( None,
      fun _ ->
        f ();
        None
    )

module Arg = struct
  type (_, _) t =
    | String : string -> (string, action) t
    | Int : string -> (int, action) t
    | Rest : string -> (Sail_file.position * string * State.istate, State.istate option) t
    | Update : (State.istate, State.istate) t
    | Get : (State.istate, unit) t
end

let ( let@ ) : type a b. (a, b) Arg.t -> (a -> b) -> action = function
  | Arg.String s -> fun f -> ArgString (s, f)
  | Arg.Int s -> fun f -> ArgInt (s, f)
  | Arg.Rest s -> fun f -> Action (Some s, f)
  | Arg.Update -> fun f -> Action (None, fun (_, _, istate) -> Some (f istate))
  | Arg.Get ->
      fun f ->
        Action
          ( None,
            fun (_, _, istate) ->
              f istate;
              None
          )

type command = See of string | Command of { help : string; shortname : string option; action : action }

let commands = ref StringMap.empty

let rec get_command cmd =
  match StringMap.find_opt cmd !commands with
  | None -> None
  | Some (Command { help; shortname = _; action }) -> Some (help, action)
  | Some (See cmd') -> get_command (":" ^ cmd')

let all_commands () =
  List.filter_map
    (fun (name, cmd) ->
      match cmd with Command { help; shortname; action } -> Some (name, (help, shortname, action)) | See _ -> None
    )
    (StringMap.bindings !commands)

let generate_help name help action =
  let rec args = function
    | ArgString (hint, next) -> arg hint :: args (next "")
    | ArgInt (hint, next) -> arg hint :: args (next 0)
    | Action (Some hint, _) -> [arg hint]
    | Action (None, _) -> []
  in
  let args = args action in
  let help =
    match String.split_on_char ':' help with
    | [] -> assert false
    | prefix :: splits ->
        List.map
          (fun split ->
            match String.split_on_char ' ' split with
            | [] -> assert false
            | subst :: rest ->
                if Str.string_match (Str.regexp "^[0-9]+") subst 0 then (
                  let num_str = Str.matched_string subst in
                  let num_end = Str.match_end () in
                  let punct = String.sub subst num_end (String.length subst - num_end) in
                  List.nth args (int_of_string num_str) ^ punct ^ " " ^ String.concat " " rest
                )
                else command (":" ^ subst) ^ " " ^ String.concat " " rest
          )
          splits
        |> String.concat ""
        |> fun rest -> prefix ^ rest
  in
  (Util.(name |> green |> clear), String.concat ", " args, help)

let split_on_first c s =
  match String.index_opt s c with
  | None -> (s, None)
  | Some i ->
      let before = String.sub s 0 i in
      let after = String.sub s (i + 1) (String.length s - i - 1) in
      (before, Some after)

let run_action istate cmd pos argument action =
  let rec call argument action =
    match (argument, action) with
    | Some argument, ArgString (_, next) ->
        let s, rest = split_on_first ',' argument in
        call rest (next (String.trim s))
    | Some argument, ArgInt (hint, next) ->
        let s, rest = split_on_first ',' argument in
        if Str.string_match (Str.regexp "^[0-9]+$") s 0 then call rest (next (int_of_string s))
        else failwith (sprintf "%s argument %s must be an non-negative integer" (command cmd) (arg hint))
    | _, Action (_, act) -> act (pos, Option.value ~default:"" argument, istate)
    | _, _ -> failwith (sprintf "Bad arguments for %s, see (%s %s)" (command cmd) (command ":help") (command cmd))
  in
  match call (Some argument) action with None -> istate | Some istate -> istate

let register_command ~name ?shortname ~help action =
  commands := StringMap.add (":" ^ name) (Command { help; shortname; action }) !commands;
  match shortname with None -> () | Some s -> commands := StringMap.add (":" ^ s) (See name) !commands
