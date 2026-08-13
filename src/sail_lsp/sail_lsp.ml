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

let opt_highlight = ref (Server_config.Implicit false)
let opt_folding = ref (Server_config.Implicit false)

let toggle_option name desc opt =
  [
    ("--" ^ name, Arg.Unit (fun () -> opt := Server_config.Explicit true), " Enable " ^ desc ^ ".");
    ("--no-" ^ name, Arg.Unit (fun () -> opt := Server_config.Explicit false), " Disable " ^ desc ^ ".");
  ]

let speclist =
  [
    ("--stdio", Arg.Unit (fun () -> ()), " Use stdin/stdout for IO (default).");
    ("--log-file", Arg.String (fun s -> Log.opt_file := Some (open_out s)), " Log to a file rather than stderr");
  ]
  @ toggle_option "highlight" "full semantic highlighting" opt_highlight
  @ toggle_option "folding" "code folding" opt_folding

let anon_fun _ = ()

let main () =
  Arg.parse_argv Sys.argv speclist anon_fun "sail_lsp [--stdio]";

  Util.opt_colors := false;

  match Server_config.get_config ~highlight:!opt_highlight ~folding:!opt_folding with
  | Ok config -> Server.run ~config ()
  | Error msg ->
      prerr_endline msg;
      exit 1

let () =
  try Libsail.Parmap.toplevel_handler main with
  | Arg.Bad msg ->
      prerr_endline msg;
      exit 1
  | Arg.Help msg ->
      print_endline msg;
      exit 0
