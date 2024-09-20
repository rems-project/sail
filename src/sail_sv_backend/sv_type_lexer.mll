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
(*    Louis-Emile Ploix                                                     *)
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

{

open Libsail

open Sv_type_parser

module M = Map.Make (String)

let kw_table =
  List.fold_left
    (fun r (x, y) -> M.add x y r)
    M.empty
    [
      ("bit",       (fun _ -> Bit));
      ("int",       (fun _ -> Int));
      ("logic",     (fun _ -> Logic));
      ("string",    (fun _ -> String));
      ("sail_bits", (fun _ -> SailBits));
      ("sail_int",  (fun _ -> SailInt));
      ("sail_list", (fun _ -> SailList));
    ]

}

let wsc = [' ''\t']
let ws = wsc+
let letter = ['a'-'z''A'-'Z']
let digit = ['0'-'9']
let alphanum = letter|digit
let startident = letter|'_'
let ident = alphanum|'_'

rule token = parse
  | ws                     { token lexbuf}
  | "\n"
  | "\r\n"                 { Lexing.new_line lexbuf; token lexbuf }
  | "["                    { Lsquare }
  | "]"                    { Rsquare }
  | "_"                    { Underscore }
  | ":"                    { Colon }
  | digit+ as n            { match int_of_string_opt n with
                             | Some n -> Nat n
                             | None ->
                                 raise (Reporting.err_lex (Lexing.lexeme_start_p lexbuf)
                                         (Printf.sprintf "Numeric literal too large: %s" n)) }
  | '#' (digit+ as n)      { match int_of_string_opt n with
                             | Some n -> HashNat n
                             | None ->
                                 raise (Reporting.err_lex (Lexing.lexeme_start_p lexbuf)
                                         (Printf.sprintf "Numeric literal too large: %s" n)) }
  | startident ident* as i { let p = Lexing.lexeme_start_p lexbuf in
                             match M.find_opt i kw_table with
                             | Some kw -> kw p
                             | None ->
                                 raise (Reporting.err_lex p ("Unknown keyword: " ^ i)) }
  | eof                    { Eof }
  | _  as c                { raise (Reporting.err_lex
                                     (Lexing.lexeme_start_p lexbuf)
                                     (Printf.sprintf "Unexpected character: %s" (Char.escaped c))) }
