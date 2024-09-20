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

module type CONVERTER = sig
  type config

  val default_config : loc:Parse_ast.l -> config

  val convert : config -> string -> string
end

module IdentityConverter : CONVERTER = struct
  type config = unit

  let default_config ~loc:_ = ()

  let convert _ comment = comment
end

module AsciidocConverter : CONVERTER = struct
  open Printf
  open Omd

  type config = { this : Ast.id option; loc : Parse_ast.l; list_depth : int }

  let default_config ~loc = { this = None; loc; list_depth = 1 }

  let rec format_elem (conf : config) = function
    | Paragraph elems -> format conf elems ^ "\n\n"
    | Text str -> str
    | Emph elems -> sprintf "_%s_" (format conf elems)
    | Bold elems -> sprintf "*%s*" (format conf elems)
    | Code (_, code) -> sprintf "`%s`" code
    | Code_block (lang, code) -> sprintf "[source,%s]\n----\n%s\n----\n\n" lang code
    | Br -> "\n"
    | NL -> "\n"
    | H1 header -> "= " ^ format conf header ^ "\n"
    | H2 header -> "== " ^ format conf header ^ "\n"
    | H3 header -> "=== " ^ format conf header ^ "\n"
    | H4 header -> "==== " ^ format conf header ^ "\n"
    | Ul list | Ulp list ->
        Util.string_of_list ""
          (fun item ->
            let new_conf = { conf with list_depth = conf.list_depth + 1 } in
            "\n" ^ String.make conf.list_depth '*' ^ " " ^ format new_conf item
          )
          list
    | _ -> raise (Reporting.err_general conf.loc "Cannot convert markdown element to Asciidoc")

  and format conf elems = String.concat "" (List.map (format_elem conf) elems)

  let convert conf comment = format conf (Omd.of_string comment)
end
