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

open Arg

type t = {
  prefix : string list;
  hide_prefix : bool;
  debug : bool;
  hide : bool;
  arg : string option;
  override : string option;
  key : string;
}

let create ?(prefix = []) ?(hide_prefix = false) ?(debug = false) ?(hide = false) ?arg ?override key =
  { prefix; hide_prefix; debug; hide; arg; override; key }

let underscore_sep = Util.string_of_list "_" (fun s -> s)

let to_arg (flag, spec, doc) =
  let apply_prefix key =
    match flag.prefix with [] -> key | _ when flag.hide_prefix -> key | _ -> underscore_sep flag.prefix ^ "_" ^ key
  in
  let key =
    if Option.is_some flag.override then Option.get flag.override
    else if flag.key = "" then underscore_sep flag.prefix
    else apply_prefix flag.key
  in
  let key_prefix = "-" ^ if flag.debug then "d" else "" in
  let arg_prefix = match flag.arg with Some desc -> "<" ^ desc ^ "> " | None -> " " in
  let doc = if flag.hide then "" else arg_prefix ^ (if flag.debug then "(debug) " else "") ^ doc in
  (key_prefix ^ key, spec, doc)
