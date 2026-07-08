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
  | And
  | As
  | Assert
  | At
  | Attribute of string
  | BOOL
  | Backwards
  | Bar
  | Bidir
  | Bin of string
  | Bitfield
  | Bitone
  | Bitzero
  | By
  | Caret
  | Cast
  | Catch
  | Clause
  | Colon of string
  | ColonColon
  | Comma
  | Config
  | Configuration
  | Constant
  | Constraint
  | Dec
  | Default
  | Do
  | DocBlock of string
  | DocLine of string
  | Dot
  | DotDot
  | Downto
  | Effect
  | Else
  | End
  | Enum
  | Eof
  | Eq of string
  | EqGt of string
  | Exit
  | False
  | Fixity of Parse_ast.fixity_token
  | Forall
  | Foreach
  | Forwards
  | From
  | Function_
  | Hex of string
  | INT
  | Id of string
  | If_
  | Impl
  | Impure
  | In
  | Inc
  | Instantiation
  | InternalAssume
  | InternalPLet
  | InternalReturn
  | Lcurly
  | LcurlyBar
  | Let_
  | Lparen
  | Lsquare
  | LsquareBar
  | Mapping
  | Match
  | Minus
  | MinusGt
  | Monadic
  | MultilineString of string list
  | Mutual
  | NAT
  | Newtype
  | Num of Nat_big_num.num
  | ORDER
  | Op
  | OpId of string
  | Outcome
  | Overload
  | Pragma of (string * string)
  | Private
  | Pure
  | Rcurly
  | RcurlyBar
  | Real of string
  | Ref
  | Register
  | Repeat
  | Return
  | Rparen
  | Rsquare
  | RsquareBar
  | Scattered
  | Semi
  | Sizeof
  | Star
  | String of string
  | Struct
  | StructuredPragma of string
  | TYPE
  | TerminationMeasure
  | Then
  | Throw
  | To
  | True
  | Try
  | TwoCaret
  | TyVar of string
  | Typedef
  | Undefined
  | Under
  | Union
  | Unit of string
  | Until
  | Val
  | Var
  | When
  | While
  | With
