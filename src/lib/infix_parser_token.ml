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

type token =
  | At
  | ColonColon
  | Eof
  | Exp of Parse_ast.exp
  | Gt
  | GtEq
  | In
  | Lt
  | LtEq
  | Minus
  | Op0 of Parse_ast.id
  | Op0l of Parse_ast.id
  | Op0r of Parse_ast.id
  | Op1 of Parse_ast.id
  | Op1l of Parse_ast.id
  | Op1r of Parse_ast.id
  | Op2 of Parse_ast.id
  | Op2l of Parse_ast.id
  | Op2r of Parse_ast.id
  | Op3 of Parse_ast.id
  | Op3l of Parse_ast.id
  | Op3r of Parse_ast.id
  | Op4 of Parse_ast.id
  | Op4l of Parse_ast.id
  | Op4r of Parse_ast.id
  | Op5 of Parse_ast.id
  | Op5l of Parse_ast.id
  | Op5r of Parse_ast.id
  | Op6 of Parse_ast.id
  | Op6l of Parse_ast.id
  | Op6r of Parse_ast.id
  | Op7 of Parse_ast.id
  | Op7l of Parse_ast.id
  | Op7r of Parse_ast.id
  | Op8 of Parse_ast.id
  | Op8l of Parse_ast.id
  | Op8r of Parse_ast.id
  | Op9 of Parse_ast.id
  | Op9l of Parse_ast.id
  | Op9r of Parse_ast.id
  | Plus
  | Star
  | TwoCaret
  | Typ of Parse_ast.atyp
