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

open Ast
open Ast_defs
open Ast_util
open Printf

let opt_interactive = ref false

type istate = {
  ast : Type_check.tannot ast;
  effect_info : Effects.side_effect_info;
  env : Type_check.Env.t;
  default_sail_dir : string;
  config : Yojson.Basic.t option;
}

let initial_istate config default_sail_dir =
  {
    ast = empty_ast;
    effect_info = Effects.empty_side_effect_info;
    env = Type_check.initial_env;
    default_sail_dir;
    config;
  }

let arg str = "<" ^ str ^ ">" |> Util.yellow |> Util.clear

let command str = str |> Util.green |> Util.clear

type action =
  | ArgString of string * (string -> action)
  | ArgInt of string * (int -> action)
  | Action of (istate -> istate)
  | ActionUnit of (istate -> unit)

let commands = ref []

let get_command cmd = List.assoc_opt cmd !commands

let all_commands () = !commands

let reflect_typ action =
  let open Type_check in
  let rec arg_typs = function
    | ArgString (_, next) -> string_typ :: arg_typs (next "")
    | ArgInt (_, next) -> int_typ :: arg_typs (next 0)
    | Action _ -> []
    | ActionUnit _ -> []
  in
  match action with Action _ -> function_typ [unit_typ] unit_typ | _ -> function_typ (arg_typs action) unit_typ

let generate_help name help action =
  let rec args = function
    | ArgString (hint, next) -> arg hint :: args (next "")
    | ArgInt (hint, next) -> arg hint :: args (next 0)
    | Action _ -> []
    | ActionUnit _ -> []
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
  sprintf "%s %s - %s" Util.(name |> green |> clear) (String.concat ", " args) help

let run_action istate cmd argument action =
  let args = String.split_on_char ',' argument in
  let rec call args action =
    match (args, action) with
    | x :: xs, ArgString (hint, next) -> call xs (next (String.trim x))
    | x :: xs, ArgInt (hint, next) ->
        let x = String.trim x in
        if Str.string_match (Str.regexp "^[0-9]+$") x 0 then call xs (next (int_of_string x))
        else failwith (sprintf "%s argument %s must be an non-negative integer" (command cmd) (arg hint))
    | _, Action act -> act istate
    | _, ActionUnit act ->
        act istate;
        istate
    | _, _ -> failwith (sprintf "Bad arguments for %s, see (%s %s)" (command cmd) (command ":help") (command cmd))
  in
  call args action

let register_command ~name ~help action = commands := (":" ^ name, (help, action)) :: !commands
