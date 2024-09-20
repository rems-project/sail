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

type 'a parse_result = Ok of 'a * Str.split_result list | Fail

type 'a parser = Str.split_result list -> 'a parse_result

let ( >>= ) (m : 'a parser) (f : 'a -> 'b parser) (toks : Str.split_result list) =
  match m toks with Ok (r, toks) -> f r toks | Fail -> Fail

let pmap f m toks = match m toks with Ok (r, toks) -> Ok (f r, toks) | Fail -> Fail

let token f = function tok :: toks -> begin match f tok with Some x -> Ok (x, toks) | None -> Fail end | [] -> Fail

let preturn x toks = Ok (x, toks)

let rec plist m toks =
  match m toks with
  | Ok (x, toks) -> begin match plist m toks with Ok (xs, toks) -> Ok (x :: xs, toks) | Fail -> Fail end
  | Fail -> Ok ([], toks)

let pchoose m n toks = match m toks with Fail -> n toks | Ok (x, toks) -> Ok (x, toks)

let parse p delim_regexp input =
  let delim = Str.regexp delim_regexp in
  let tokens = Str.full_split delim input in
  let non_whitespace = function Str.Delim d when String.trim d = "" -> false | _ -> true in
  let tokens = List.filter non_whitespace tokens in
  match p tokens with Ok (result, []) -> Some result | Ok (_, _) -> None | Fail -> None
