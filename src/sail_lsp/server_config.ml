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

open Libsail
open Util.Result_monad

type 'a flag_setting = Explicit of 'a | Implicit of 'a

let unwrap_flag_setting = function Explicit v -> v | Implicit v -> v

let with_flag flg get cfg =
  match flg with
  | Explicit v -> Ok v
  | Implicit v -> (
      let* res = get cfg in
      match res with Some cfg_v -> Ok cfg_v | None -> Ok v
    )

let get_home_dir () =
  match Sys.getenv_opt "HOME" with
  | Some h -> Ok h
  | None -> (
      (* For Windows *)
      match Sys.getenv_opt "USERPROFILE" with
      | Some u -> Ok u
      | None -> Error "Could not determine home directory (HOME/USERPROFILE unset)"
    )

let get_windows_config_dir home_dir =
  match Sys.getenv_opt "APPDATA" with
  | Some appdata -> appdata
  | None ->
      (* If for some reason APPDATA isn't set *)
      Filename.concat home_dir (Filename.concat "AppData" "Roaming")

let get_xdg_config_dir home_dir =
  match Sys.getenv_opt "XDG_CONFIG_HOME" with Some dir when dir <> "" -> dir | _ -> Filename.concat home_dir ".config"

let get_config_dir () =
  let* home_dir = get_home_dir () in
  let cfg_dir = if Sys.win32 then get_windows_config_dir home_dir else get_xdg_config_dir home_dir in
  Ok (Filename.concat cfg_dir "sail_lsp")

let read_process_stdout cmd =
  let ic = Unix.open_process_in cmd in
  let buf = Buffer.create 256 in
  ( try
      while true do
        Buffer.add_channel buf ic 1
      done
    with End_of_file -> ()
  );
  let status = Unix.close_process_in ic in
  match status with
  | Unix.WEXITED 0 -> Ok (Buffer.contents buf)
  | Unix.WEXITED n -> Error (Printf.sprintf "Command %s exited with code %d" cmd n)
  | Unix.WSIGNALED n -> Error (Printf.sprintf "Command %s killed by signal %d" cmd n)
  | Unix.WSTOPPED n -> Error (Printf.sprintf "Command %s stopped by signal %d" cmd n)

let get_sail_dir_from_sail () = Result.map String.trim (read_process_stdout "sail --dir")

type t = { default_sail_dir : string; highlight : bool; folding : bool }

module From_json = struct
  let assoc msg = function `Assoc obj -> Ok obj | _ -> Error (Printf.sprintf "Expected JSON object %s" msg)

  let string msg = function `String str -> Ok str | _ -> Error (Printf.sprintf "Expected JSON string %s" msg)

  let boolean msg = function `Bool b -> Ok b | _ -> Error (Printf.sprintf "Expected JSON boolean %S" msg)

  let sail_dir json =
    let* obj = assoc "at root" json in
    match List.assoc_opt "sail_dir" obj with
    | Some json -> string "as sail_dir value" json
    | None -> get_sail_dir_from_sail ()

  let optional_toggle name json =
    let* obj = assoc "at root" json in
    match List.assoc_opt name obj with
    | Some json ->
        let* v = boolean ("as " ^ name ^ " value") json in
        Ok (Some v)
    | None -> Ok None
end

let config_from_json ~highlight ~folding json =
  let* default_sail_dir = From_json.sail_dir json in
  let* highlight = with_flag highlight (From_json.optional_toggle "highlight") json in
  let* folding = with_flag folding (From_json.optional_toggle "folding") json in
  Ok { default_sail_dir; highlight; folding }

let get_config ~highlight ~folding =
  let* cfg_dir = get_config_dir () in
  let cfg_file = Filename.concat cfg_dir "config.json" in
  if not (Sys.file_exists cfg_file) then
    let* sail_dir = get_sail_dir_from_sail () in
    Ok { default_sail_dir = sail_dir; highlight = unwrap_flag_setting highlight; folding = unwrap_flag_setting folding }
  else (
    let json = Yojson.Safe.from_file ~fname:"config.json" cfg_file in
    config_from_json ~highlight ~folding json
  )
